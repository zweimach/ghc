/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team, 1998-2018
 *
 * Non-moving garbage collector and allocator
 *
 * ---------------------------------------------------------------------------*/

#include "Rts.h"
#include "RtsUtils.h"
#include "NonMoving.h"
#include "Capability.h"
#include "Printer.h"

struct nonmoving_heap nonmoving_heap;

generation nonmoving_gen;

struct nonmoving_segment* nonmoving_todos = NULL;

#define MAX(h,i) ((h) > (i) ? (h) : (i))

// TODO: Forward-declare this more reasonably
void initGeneration (generation *gen, int g);

static void nonmoving_init_segment(struct nonmoving_segment *seg, uint8_t block_size)
{
    seg->link = NULL;
    seg->next_free = 0;
    seg->next_free_snap = 0;
    seg->block_size = block_size;
    nonmoving_clear_bitmap(seg);
}

/*
 * Request a fresh segment from the free segment list or allocate one of the
 * given node.
 *
 * Must hold sm_mutex.
 */
static struct nonmoving_segment *nonmoving_alloc_segment(uint32_t node)
{
    struct nonmoving_segment *ret;
    ACQUIRE_LOCK(&nonmoving_heap.mutex);
    if (nonmoving_heap.free) {
        ret = nonmoving_heap.free;
        nonmoving_heap.free = ret->link;
    } else {
        bdescr *bd = allocAlignedGroupOnNode(node, NONMOVING_SEGMENT_BLOCKS);
        initBdescr(bd, &nonmoving_gen, &nonmoving_gen);
        bd->flags = BF_NONMOVING;
        ret = (struct nonmoving_segment *)bd->start;
    }
    RELEASE_LOCK(&nonmoving_heap.mutex);
    // Check alignment
    ASSERT(((uintptr_t)ret % NONMOVING_SEGMENT_SIZE) == 0);
    return ret;
}

static inline unsigned long log2_floor(unsigned long x)
{
    return sizeof(unsigned long)*8 - 1 - __builtin_clzl(x);
}

static inline unsigned long log2_ceil(unsigned long x)
{
    unsigned long log = log2_floor(x);
    return (x - (1 << log)) ? log + 1 : log;
}

static void *nonmoving_allocate_block_from_segment(struct nonmoving_segment *seg)
{
    uint8_t *bitmap = seg->bitmap;
    for (unsigned int i = seg->next_free; i < nonmoving_segment_block_count(seg); i++) {
        if (!bitmap[i]) {
            seg->next_free = i + 1;
            return nonmoving_segment_get_block(seg, i);
        }
    }
    return 0;
}

/* sz is in words */
void *nonmoving_allocate(Capability *cap, StgWord sz)
{
    int allocator_idx = log2_ceil(sz) - NONMOVING_ALLOCA0 + log2_ceil(sizeof(StgWord));

    // break when allocator_idx == 2

    debugBelch("Allocating %lu words in nonmoving heap using allocator %d with %lu-word sized blocks\n",
               sz,
               allocator_idx,
               (1 << (NONMOVING_ALLOCA0 + allocator_idx)) / sizeof(W_));

    if (allocator_idx < 0) {
        allocator_idx = 0;
    } else if (allocator_idx > NONMOVING_ALLOCA_CNT) {
        // TODO: Allocate large object? Perhaps this should be handled elsewhere
        ASSERT(false);
    }

    struct nonmoving_allocator *alloca = nonmoving_heap.allocators[allocator_idx];

    // First try allocating into current segment
    while (true) {
        // First try allocating into current segment
        struct nonmoving_segment *current = alloca->current[cap->no];
        if (current) {
            void *ret = NULL;
            ret = nonmoving_allocate_block_from_segment(current);

            if (ret) {
                // add the segment to the todo list
                current->link = nonmoving_todos;
                nonmoving_todos = current;
                ASSERT(GET_CLOSURE_TAG(ret) == 0); // check alignment
                return ret;
            }
        }

        // Current segment is filled; look elsewhere
        if (alloca->active) {
            // We want to move the current segment to the filled list and pull a
            // new segment from active. This is a bit tricky in the face of
            // parallel allocation
            struct nonmoving_segment *new_current = alloca->active;
            struct nonmoving_segment *old_current = (struct nonmoving_segment *)
                cas((StgVolatilePtr) &alloca->current[cap->no],
                    (StgWord) current,
                    (StgWord) new_current);
            if (old_current == current) {
                // we have successfully locked the allocator; insert old current into filled list
                while (true) {
                    old_current->link = alloca->filled;
                    write_barrier(); // Ensure ->link update appears; TODO: Is this implied by CAS?
                    struct nonmoving_segment *out = (struct nonmoving_segment *)
                        cas((StgVolatilePtr) &alloca->filled,
                            (StgWord) old_current->link,
                            (StgWord) old_current);
                    if (out == old_current->link) {
                        break; // successful insert
                    }
                }
            } else {
                // someone else locked the allocator to perform the insertion
            }

        // There are no active segments, allocate more segments
        } else {
            // Lock the allocator by setting current=NULL while we request a new segment.
            struct nonmoving_segment *old_current = (struct nonmoving_segment *)
                cas((StgVolatilePtr) &alloca->current[cap->no],
                    (StgWord) current,
                    0);
            if (old_current == NULL) {
                // Wait until other thread has finished
                while (alloca->current[cap->no] == NULL) {}
            } else {
                struct nonmoving_segment *seg = nonmoving_alloc_segment(cap->node);
                nonmoving_init_segment(seg, allocator_idx);
                alloca->current[cap->no] = seg;
            }
        }
    }
}

/* Allocate a nonmoving_allocator */
static struct nonmoving_allocator *alloc_nonmoving_allocator(uint32_t n_caps)
{
    size_t allocator_sz =
        sizeof(struct nonmoving_allocator) +
        sizeof(void*) * n_caps; // current segment pointer for each capability
    struct nonmoving_allocator *alloc =
        stgMallocBytes(allocator_sz, "nonmoving_init");
    memset(alloc, 0, allocator_sz);
    return alloc;
}

void nonmoving_init(void)
{
    initMutex(&nonmoving_heap.mutex);
    initGeneration(&nonmoving_gen, RtsFlags.GcFlags.generations-1);
    for (unsigned int i = 0; i < NONMOVING_ALLOCA_CNT; i++) {
        nonmoving_heap.allocators[i] = alloc_nonmoving_allocator(n_capabilities);
    }
}

/*
 * Assumes that no garbage collector or mutator threads are running to safely
 * resize the nonmoving_allocators.
 *
 * Must hold sm_mutex.
 */
void nonmoving_add_capabilities(uint32_t new_n_caps)
{
    unsigned int old_n_caps = nonmoving_heap.n_caps;
    struct nonmoving_allocator **allocs = nonmoving_heap.allocators;

    for (unsigned int i = 0; i < NONMOVING_ALLOCA_CNT; i++) {
        struct nonmoving_allocator *old = allocs[i];
        allocs[i] = alloc_nonmoving_allocator(new_n_caps);

        // Copy the old state
        allocs[i]->filled = old->filled;
        allocs[i]->active = old->active;
        for (unsigned int j = 0; j < old_n_caps; j++) {
            allocs[i]->current[j] = old->current[j];
        }
        stgFree(old);

        // Initialize current segments for the new capabilities
        for (unsigned int j = old_n_caps; j < new_n_caps; j++) {
            allocs[i]->current[j] = nonmoving_alloc_segment(capabilities[j]->node);
            nonmoving_init_segment(allocs[i]->current[j], NONMOVING_ALLOCA0 + i);
            allocs[i]->current[j]->link = NULL;
        }
    }
    nonmoving_heap.n_caps = new_n_caps;
}

#if defined(DEBUG)

void nonmoving_print_segment(struct nonmoving_segment *seg)
{
    int num_blocks = nonmoving_segment_block_count(seg);

    debugBelch("Segment with %d blocks of size 2^%d (%d bytes, %lu words)\n",
               num_blocks,
               seg->block_size,
               1 << seg->block_size,
               ROUNDUP_BYTES_TO_WDS(1 << seg->block_size));

    for (nonmoving_block_idx p_idx = 0; p_idx < seg->next_free; ++p_idx) {
        StgClosure *p = (StgClosure*)nonmoving_segment_get_block(seg, p_idx);
        if (nonmoving_get_mark_bit(seg, p_idx)) {
            debugBelch("%d (%p)* :\t", p_idx, (void*)p);
        } else {
            debugBelch("%d (%p)  :\t", p_idx, (void*)p);
        }
        printClosure(p);
    }

    debugBelch("End of segment\n\n");
}

#endif
