/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team, 1998-2018
 *
 * Non-moving garbage collector and allocator
 *
 * ---------------------------------------------------------------------------*/

#include "Rts.h"
#include "NonMoving.h"

struct nonmoving_heap heap;

// Request a fresh segment from the free segment list
static struct nonmoving_segment *nonmoving_request_segment(uint32_t node)
{
    ACQUIRE_LOCK(&heap->mutex);
    if (heap->free) {
        struct nonmoving_segment *ret = heap->free;
        heap->free = ret->link;
        return ret;
    } else {
        // TODO Aligned block allocation
        bdescr *bd = allocGroupOnNode_lock(node, 2*NONMOVING_SEGMENT_BLOCKS - 1);
        initBdescr(db, 0xff, 0xff); // TODO: hmmmm, refactoring needed?
        bd->flags = BF_NONMOVING;
        // TODO allocation accounting?
        return res->start + NONMOVING_SEGMENT_SIZE - ((uintptr_t) res % NONMOVING_SEGMENT_SIZE); // XXX: yuck
    }
    RELEASE_LOCK(&heap->mutex);
}

static void nonmoving_clear_bitmap(struct nonmoving_segment *seg)
{
    unsigned int n = nonmoving_segment_block_count(seg);
    memset(seg->bitmap, 0, n);
}

static int log2_ceil(int x)
{
    int res = 0;
    while (x) {
        res++;
        x = x >> 1;
    }
    return res;
}

static void *nonmoving_allocate_block_from_segment(struct nonmoving_segment *seg)
{
    uint8_t *bitmap = seg->bitmap;
    for (int i=seg->next_free; i < nonmoving_segment_block_count(seg); i++) {
        if (!bitmap[i]) {
            seg->next_free = i + 1;
            return nonmoving_segment_get_block(seg, i);
        }
    }
    return 0;
}

void *nonmoving_allocate(Capability *cap, int sz)
{
    int allocator_idx = MAX(log2_ceil(sz), NONMOVING_ALLOCA0);
    if (allocator_idx < NONMOVING_ALLOCA0) {
        allocator_idx = NONMOVING_ALLOCA0;
    } else if (allocator_idx > NONMOVING_ALLOCA0 + NONMOVING_ALLOCA_CNT) {
        // TODO: Allocate large object? Perhaps this should be handled elsewhere
    }

    struct nonmoving_allocator *alloca = &heap->allocators[allocator_idx];

    // First try allocating into current segment
    while (true) {
        struct nonmoving_segment *current = alloca->current[cap->no];
        void *ret = nonmoving_allocate_block_from_segment(current);
        if (ret) {
            return ret;

        // Current segments is filled; look elsewhere
        } else if (alloca->active) {
            // We want to move the current segment to the filled list and pull a
            // new segment from active. This is a bit tricky in the face of
            // parallel allocation
            struct nonmoving_segment *new_current = alloca->active;
            struct nonmoving_segment *old_current = cas(&alloca->current[cap->no], current, new_current);
            if (old_current == current) {
                // we have successfully locked the allocator; insert old current into filled list
                while (true) {
                    old_current->link = alloca->filled;
                    write_barrier(); // Ensure ->link update appears; TODO: Is this implied by CAS?
                    struct nonmoving_segment *out = cas(&alloca->filled, old_current->link, old_current);
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
            struct nonmoving_segment *old_current = cas(&alloca->current[cap->no], current, NULL);
            if (old_current == NULL) {
                // Wait until other thread has finished
                while (alloca->current[cap->no] == NULL) {}
            } else {
                alloca->current[cap->no] = nonmoving_request_segment(heap);
            }
        }
    }
}

static struct nonmoving_allocator *alloc_nonmoving_allocators(int n_caps)
{
    int allocator_sz = sizeof(struct nonmoving_allocator) + sizeof(void*) * n_caps;
    return stgMallocBytes("nonmoving_init", allocator_sz * NONMOVING_ALLOCA_CNT);
}

void nonmoving_init()
{
    initMutex(&heap.mutex);
    heap.allocators = alloc_nonmoving_allocators(n_capabilities);
}

// Assumes that no garbage collector or mutator threads are running to safely
// resize the nonmoving_allocators.
void nonmoving_add_capabilities(int new_n_caps)
{
    unsigned int old_n_caps = heap.n_caps;
    struct nonmoving_allocator *old = heap.allocators;
    struct nonmoving_allocator *allocs = alloc_nonmoving_allocators(new_n_caps);

    for (int i = 0; i < NONMOVING_ALLOCA_CNT; i++) {
        // Copy the old state
        allocs[i].filled = old[i].filled;
        allocs[i].active = old[i].active;
        for (int j = 0; i < old_n_caps; i++) {
            allocs[i].current[j] = old[i].current[j];
        }

        // Initialize current segments for the new capabilities
        for (int j = old_n_caps; i < new_n_caps; i++) {
            if (allocs[i].free) {
                allocs[i].current[j] = allocs[i].free;
                allocs[i].free = allocs[i].current[j].link;
                allocs[i].current[j].link = NULL;
            } else{
                allocs[i].current[j] = nonmoving_request_segment();
            }
        }
    }
    heap.allocators = allocators;
    heap.n_caps = new_n_caps;
    if (old != NULL) {
        stgFree(old);
    }
}
