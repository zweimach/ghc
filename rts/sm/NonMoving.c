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
#include "Storage.h"

struct nonmoving_heap nonmoving_heap;

struct nonmoving_segment* nonmoving_todos = NULL;

// Add a todo segment if it's not already in the list. Slow. FIXME
// We should probably mark block of the segment as "NONMOVING_IN_TODOS"
static void add_todo_segment(struct nonmoving_segment* seg)
{
    for (struct nonmoving_segment* todo = nonmoving_todos; todo != NULL; todo = todo->todo_link) {
        if (todo == seg)
            return;
    }
    seg->todo_link = nonmoving_todos;
    nonmoving_todos = seg;
}

static void nonmoving_init_segment(struct nonmoving_segment *seg, uint8_t block_size)
{
    seg->link = NULL;
    seg->todo_link = NULL;
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
        initBdescr(bd, oldest_gen, oldest_gen);
        for (StgWord32 i = 0; i < bd->blocks; ++i) {
            bd[i].flags = BF_NONMOVING;
            bd[i].gen = oldest_gen;
        }
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
    return NULL;
}

/* sz is in words */
void *nonmoving_allocate(Capability *cap, StgWord sz)
{
    int allocator_idx = log2_ceil(sz * sizeof(StgWord)) - NONMOVING_ALLOCA0;

    if (allocator_idx < 0) {
        allocator_idx = 0;
    } else if (allocator_idx > NONMOVING_ALLOCA_CNT) {
        // TODO: Allocate large object? Perhaps this should be handled elsewhere
        ASSERT(false);
    }

#ifdef DEBUG
    debugBelch("Allocating %lu words in nonmoving heap using allocator %d with %lu-word sized blocks\n",
               sz,
               allocator_idx,
               (1 << (NONMOVING_ALLOCA0 + allocator_idx)) / sizeof(W_));
#endif

    struct nonmoving_allocator *alloca = nonmoving_heap.allocators[allocator_idx];

    while (true) {
        // First try allocating into current segment
        struct nonmoving_segment *current = alloca->current[cap->no];
        ASSERT(current);
        void *ret = nonmoving_allocate_block_from_segment(current);
        if (ret) {
            add_todo_segment(current);
            ASSERT(GET_CLOSURE_TAG(ret) == 0); // check alignment
            return ret;
        }

        // current segment filled, link if to filled
        current->link = alloca->filled;
        alloca->filled = current;

        // check active
        if (alloca->active) {
            // remove an active, make it current
            struct nonmoving_segment *new_current = alloca->active;
            alloca->active = new_current->link;
            new_current->link = NULL;
            alloca->current[cap->no] = new_current;
        }

        // there are no active segments, allocate new segment
        else {
            struct nonmoving_segment *new_current = nonmoving_alloc_segment(cap->node);
            nonmoving_init_segment(new_current, NONMOVING_ALLOCA0 + allocator_idx);
            alloca->current[cap->no] = new_current;
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

void nonmoving_print_allocator(struct nonmoving_allocator *alloc)
{
    debugBelch("Allocator at %p\n", (void*)alloc);
    debugBelch("Filled segments:\n");
    for (struct nonmoving_segment *seg = alloc->filled; seg != NULL; seg = seg->link) {
        debugBelch("%p ", (void*)seg);
    }
    debugBelch("\nActive segments:\n");
    for (struct nonmoving_segment *seg = alloc->active; seg != NULL; seg = seg->link) {
        debugBelch("%p ", (void*)seg);
    }
    debugBelch("\nCurrent segments:\n");
    for (uint32_t i = 0; i < n_capabilities; ++i) {
        debugBelch("%p ", alloc->current[i]);
    }
    debugBelch("\n");
}

void locate_object(P_ obj)
{
    // Search allocators
    for (int alloca_idx = 0; alloca_idx < NONMOVING_ALLOCA_CNT; ++alloca_idx) {
        struct nonmoving_allocator *alloca = nonmoving_heap.allocators[alloca_idx];
        struct nonmoving_segment *seg = alloca->current[0]; // only one capability for now
        if (obj >= (P_)seg && obj < (((P_)seg) + NONMOVING_SEGMENT_SIZE)) {
            debugBelch("%p is in current segment of allocator %d\n", obj, alloca_idx);
            return;
        }
        int seg_idx = 0;
        seg = alloca->active;
        while (seg) {
            if (obj >= (P_)seg && obj < (((P_)seg) + NONMOVING_SEGMENT_SIZE)) {
                debugBelch("%p is in active segment %d of allocator %d\n", obj, seg_idx, alloca_idx);
                return;
            }
            seg_idx++;
            seg = seg->link;
        }

        seg_idx = 0;
        seg = alloca->filled;
        while (seg) {
            if (obj >= (P_)seg && obj < (((P_)seg) + NONMOVING_SEGMENT_SIZE)) {
                debugBelch("%p is in filled segment %d of allocator %d\n", obj, seg_idx, alloca_idx);
                return;
            }
            seg_idx++;
            seg = seg->link;
        }
    }

    struct nonmoving_segment *seg = nonmoving_heap.free;
    while (seg) {
        if (obj >= (P_)seg && obj < (((P_)seg) + NONMOVING_SEGMENT_SIZE)) {
            debugBelch("%p is in free segment %d\n", obj);
            return;
        }
    }

    // Search nurseries
    for (uint32_t nursery_idx = 0; nursery_idx < n_nurseries; ++nursery_idx) {
        bdescr *nursery_blocks = nurseries[nursery_idx].blocks;
        if (obj >= nursery_blocks->start && obj <= nursery_blocks->start + nursery_blocks->blocks*BLOCK_SIZE_W) {
            debugBelch("%p is in nursery %d\n", obj, nursery_idx);
            return;
        }
    }

    // Search generations
    // TODO
}

#endif
