/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team, 1998-2018
 *
 * Non-moving garbage collector and allocator: Sweep phase
 *
 * ---------------------------------------------------------------------------*/

#include "Rts.h"
#include "NonMovingSweep.h"
#include "NonMoving.h"
#include "NonMovingMark.h" // for nonmoving_is_alive
#include "Capability.h"
#include "GCThread.h" // for GCUtils.h
#include "GCUtils.h"

static void prepare_sweep(void)
{
    ASSERT(nonmoving_heap.sweep_list == NULL);

    // Move blocks in the allocators' filled lists into sweep_list
    for (int alloc_idx = 0; alloc_idx < NONMOVING_ALLOCA_CNT; alloc_idx++)
    {
        struct nonmoving_allocator *alloc = nonmoving_heap.allocators[alloc_idx];
        struct nonmoving_segment *filled = alloc->filled;
        alloc->filled = NULL;
        if (filled == NULL) {
            continue;
        }

        // Link filled to sweep_list
        struct nonmoving_segment *filled_head = filled;
        while (filled->link) {
            filled = filled->link;
        }
        filled->link = nonmoving_heap.sweep_list;
        nonmoving_heap.sweep_list = filled_head;
    }
}

// On which list should a particular segment be placed?
enum sweep_result {
    SEGMENT_FREE,     // segment is empty: place on free list
    SEGMENT_PARTIAL,  // segment is partially filled: place on active list
    SEGMENT_FILLED    // segment is full: place on filled list
};

// Add a segment to the free list.
// We will never run concurrently with the allocator (i.e. the nursery
// collector), so no synchronization is needed here.
static void push_free_segment(struct nonmoving_segment *seg)
{
    seg->link = nonmoving_heap.free;
    nonmoving_heap.free = seg;
    // TODO: free excess segments
}

// Add a segment to the appropriate active list.
// We will never run concurrently with the allocator (i.e. the nursery
// collector), so no synchronization is needed here.
static void push_active_segment(struct nonmoving_segment *seg)
{
    struct nonmoving_allocator *alloc =
        nonmoving_heap.allocators[seg->block_size - NONMOVING_ALLOCA0];
    seg->link = alloc->active;
    alloc->active = seg;
}

// Add a segment to the appropriate active list.
// We will never run concurrently with the allocator (i.e. the nursery
// collector), so no synchronization is needed here.
static void push_filled_segment(struct nonmoving_segment *seg)
{
    struct nonmoving_allocator *alloc =
        nonmoving_heap.allocators[seg->block_size - NONMOVING_ALLOCA0];
    seg->link = alloc->filled;
    alloc->filled = seg;
}

// Determine which list a marked segment should be placed on and initialize
// next_free indices as appropriate.
GNUC_ATTR_HOT static enum sweep_result
nonmoving_sweep_segment(struct nonmoving_segment *seg)
{
    bool found_free = false;
    bool found_live = false;

    for (nonmoving_block_idx i = 0;
         i < nonmoving_segment_block_count(seg);
         ++i)
    {
        if (seg->bitmap[i]) {
            found_live = true;
        } else if (!found_free) {
            found_free = true;
            seg->next_free = i;
            seg->next_free_snap = i;
            Bdescr((P_)seg)->u.scan = (P_)nonmoving_segment_get_block(seg, i);
        }

        if (found_free && found_live) {
            return SEGMENT_PARTIAL;
        }
    }

    if (found_live) {
        return SEGMENT_FILLED;
    } else {
        ASSERT(seg->next_free == 0);
        ASSERT(seg->next_free_snap == 0);
        return SEGMENT_FREE;
    }
}

#if defined(DEBUG)

static void
clear_segment(struct nonmoving_segment* seg)
{
    size_t end = ((size_t)seg) + NONMOVING_SEGMENT_SIZE;
    memset(&seg->bitmap, 0, end - (size_t)&seg->bitmap);
}

static void
clear_segment_free_blocks(struct nonmoving_segment* seg)
{
    unsigned int block_size = nonmoving_segment_block_size(seg);
    for (unsigned int p_idx = 0; p_idx < nonmoving_segment_block_count(seg); ++p_idx) {
        // after mark, so bit not set == dead
        if (!(nonmoving_get_mark_bit(seg, p_idx))) {
            memset(nonmoving_segment_get_block(seg, p_idx), 0, block_size);
        }
    }
}

#endif

GNUC_ATTR_HOT void nonmoving_sweep(void)
{
    prepare_sweep();

    while (nonmoving_heap.sweep_list) {
        struct nonmoving_segment *seg = nonmoving_heap.sweep_list;

        // Pushing the segment to one of the free/active/filled segments
        // updates the link field, so update sweep_list here
        nonmoving_heap.sweep_list = seg->link;

        enum sweep_result ret = nonmoving_sweep_segment(seg);

        switch (ret) {
        case SEGMENT_FREE:
            push_free_segment(seg);
            IF_DEBUG(sanity, clear_segment(seg));
            break;
        case SEGMENT_PARTIAL:
            push_active_segment(seg);
            IF_DEBUG(sanity, clear_segment_free_blocks(seg));
            break;
        case SEGMENT_FILLED:
            push_filled_segment(seg);
            break;
        default:
            barf("nonmoving_sweep: weird sweep return: %d\n", ret);
        }
    }
}

void nonmoving_sweep_mut_lists(HashTable *marked_objects)
{
      for (uint32_t n = 0; n < n_capabilities; n++) {
          Capability *cap = capabilities[n];
          bdescr *old_mut_list = cap->mut_lists[oldest_gen->no];
          cap->mut_lists[oldest_gen->no] = allocBlockOnNode_sync(cap->node);
          for (bdescr *bd = old_mut_list; bd; bd = bd->link) {
              for (StgPtr p = bd->start; p < bd->free; p++) {
                  StgClosure **q = (StgClosure**)p;
                  if (nonmoving_is_alive(marked_objects, *q)) {
                      recordMutableGen_GC(*q, oldest_gen->no);
                  }
              }
          }
          freeChain_sync(old_mut_list);
      }
}

void nonmoving_sweep_large_objects(HashTable *marked_objects)
{
    bdescr *free_blocks; // Blocks to be freed

    bdescr *next_large;
    for (bdescr *large = oldest_gen->scavenged_large_objects; large; large = next_large) {
        next_large = large->link;
        if (!lookupHashTable(marked_objects, (W_)large)) {
            dbl_link_remove(large, &oldest_gen->scavenged_large_objects);
            // update n_large_blocks again. this is slightly annoying, we
            // scavenge this object before mark phase and update the counter,
            // only to realize it's dead.
            oldest_gen->n_scavenged_large_blocks -= large->blocks;
            // Link the block to the chain of free blocks
            dbl_link_onto(large, &free_blocks);
        }
    }

    freeChain(free_blocks);
}
