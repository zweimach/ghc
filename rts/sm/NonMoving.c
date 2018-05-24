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
#include "GCThread.h"
#include "GCTDecl.h"

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
        for (StgWord32 i = 0; i < bd->blocks; ++i) {
            initBdescr(&bd[i], oldest_gen, oldest_gen);
            bd[i].flags = BF_NONMOVING;
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

static void nonmoving_clear_segment_bitmaps(struct nonmoving_segment *seg)
{
    while (seg) {
        nonmoving_clear_bitmap(seg);
        seg = seg->link;
    }
}

void nonmoving_clear_all_bitmaps()
{
    for (int alloca_idx = 0; alloca_idx < NONMOVING_ALLOCA_CNT; ++alloca_idx) {
        struct nonmoving_allocator *alloca = nonmoving_heap.allocators[alloca_idx];
        nonmoving_clear_segment_bitmaps(alloca->filled);
        nonmoving_clear_segment_bitmaps(alloca->active);
        for (uint32_t cap_n = 0; cap_n < n_capabilities; ++cap_n) {
            nonmoving_clear_segment_bitmaps(alloca->current[cap_n]);
        }
    }
}

void assert_in_nonmoving_heap(StgPtr p)
{
    if (!HEAP_ALLOCED_GC(p))
        return;

    if (Bdescr(p)->flags | BF_LARGE)
        return;

    for (int alloca_idx = 0; alloca_idx < NONMOVING_ALLOCA_CNT; ++alloca_idx) {
        struct nonmoving_allocator *alloca = nonmoving_heap.allocators[alloca_idx];
        struct nonmoving_segment *seg = alloca->current[0]; // TODO: only one capability for now
        if (p >= (P_)seg && p < (((P_)seg) + NONMOVING_SEGMENT_SIZE_W)) {
            return;
        }
        int seg_idx = 0;
        seg = alloca->active;
        while (seg) {
            if (p >= (P_)seg && p < (((P_)seg) + NONMOVING_SEGMENT_SIZE_W)) {
                return;
            }
            seg_idx++;
            seg = seg->link;
        }

        seg_idx = 0;
        seg = alloca->filled;
        while (seg) {
            if (p >= (P_)seg && p < (((P_)seg) + NONMOVING_SEGMENT_SIZE_W)) {
                return;
            }
            seg_idx++;
            seg = seg->link;
        }
    }

    // We don't search free segments as they're unused

    barf("%p is not in nonmoving heap\n", (void*)p);
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
        struct nonmoving_segment *seg = alloca->current[0]; // TODO: only one capability for now
        if (obj >= (P_)seg && obj < (((P_)seg) + NONMOVING_SEGMENT_SIZE_W)) {
            debugBelch("%p is in current segment of allocator %d at %p\n", obj, alloca_idx, (void*)seg);
            return;
        }
        int seg_idx = 0;
        seg = alloca->active;
        while (seg) {
            if (obj >= (P_)seg && obj < (((P_)seg) + NONMOVING_SEGMENT_SIZE_W)) {
                debugBelch("%p is in active segment %d of allocator %d at %p\n", obj, seg_idx, alloca_idx, (void*)seg);
                return;
            }
            seg_idx++;
            seg = seg->link;
        }

        seg_idx = 0;
        seg = alloca->filled;
        while (seg) {
            if (obj >= (P_)seg && obj < (((P_)seg) + NONMOVING_SEGMENT_SIZE_W)) {
                debugBelch("%p is in filled segment %d of allocator %d at %p\n", obj, seg_idx, alloca_idx, (void*)seg);
                return;
            }
            seg_idx++;
            seg = seg->link;
        }
    }

    struct nonmoving_segment *seg = nonmoving_heap.free;
    int seg_idx = 0;
    while (seg) {
        if (obj >= (P_)seg && obj < (((P_)seg) + NONMOVING_SEGMENT_SIZE_W)) {
            debugBelch("%p is in free segment %d at %p\n", obj, seg_idx, (void*)seg);
            return;
        }
        seg_idx++;
        seg = seg->link;
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
    for (uint32_t g = 0; g < RtsFlags.GcFlags.generations - 1; ++g) {
        generation *gen = &generations[g];
        for (bdescr *blk = gen->blocks; blk; blk = blk->link) {
            if (obj >= blk->start && obj < blk->free) {
                debugBelch("%p is in generation %" FMT_Word32 " blocks\n", obj, g);
                return;
            }
        }
        for (bdescr *blk = gen->old_blocks; blk; blk = blk->link) {
            if (obj >= blk->start && obj < blk->free) {
                debugBelch("%p is in generation %" FMT_Word32 " old blocks\n", obj, g);
            }
            return;
        }
    }

    // Search workspaces FIXME only works in non-threaded runtime
#if !defined(THREADED_RTS)
    for (uint32_t g = 0; g < RtsFlags.GcFlags.generations - 1; ++ g) {
        gen_workspace *ws = &gct->gens[g];
        for (bdescr *blk = ws->todo_bd; blk; blk = blk->link) {
            if (obj >= blk->start && obj < blk->free) {
                debugBelch("%p is in generation %" FMT_Word32 " todo bds\n", obj, g);
            }
        }
        for (bdescr *blk = ws->scavd_list; blk; blk = blk->link) {
            if (obj >= blk->start && obj < blk->free) {
                debugBelch("%p is in generation %" FMT_Word32 " scavd bds\n", obj, g);
            }
        }
    }
#endif
}

void nonmoving_print_sweep_list()
{
    debugBelch("==== SWEEP LIST =====\n");
    int i = 0;
    for (struct nonmoving_segment *seg = nonmoving_heap.sweep_list; seg; seg = seg->link) {
        debugBelch("%d: %p\n", i++, (void*)seg);
    }
    debugBelch("= END OF SWEEP LIST =\n");
}

#endif
