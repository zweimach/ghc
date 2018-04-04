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
    // N.B. this function must be compiled with -funroll-loops to ensure
    // efficient code is produced for the loops below.

    // There are three possible cases here:
    //  a. the bitmap is all clear (a free segment)
    //  b. the bitmap is all set (a filled segment)
    //  c. the bitmap is partially set
    // This check allows us to quickly rule out (a) or (b).
    if (seg->bitmap[0]) {
        // We have at least one live object
        for (uint8_t *b = seg->bitmap;
             b < &seg->bitmap[nonmoving_segment_block_count(seg)];
             b++)
        {
            if (! *b) {
                // we found a free block...
                nonmoving_block_idx blk_idx = b - seg->bitmap;
                seg->next_free = blk_idx;
                seg->next_free_snap = blk_idx;
                return SEGMENT_PARTIAL;
            }
        }
        // We found no dead blocks therefore this segment is filled
        return SEGMENT_FILLED;

    } else {
        // Perhaps the block is completely free...
        for (uint8_t *b = seg->bitmap;
             b < &seg->bitmap[nonmoving_segment_block_count(seg)];
             b++)
        {
            if (*b) {
                // we found a live block...
                seg->next_free = 0;
                seg->next_free_snap = 0;
                return SEGMENT_PARTIAL;
            }
        }
        // We found no live blocks therefore this segment is free
        return SEGMENT_FREE;
    }
}

#if defined(DEBUG)

static void
clear_segment(struct nonmoving_segment* seg)
{
    unsigned int block_size = nonmoving_segment_block_size(seg);
    unsigned int block_count = nonmoving_segment_block_count(seg);

    size_t end = (size_t)nonmoving_segment_get_block(seg, block_count) + block_size;
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
    while (nonmoving_heap.mark_list != NULL) {
        struct nonmoving_segment *seg = nonmoving_heap.mark_list;
        nonmoving_heap.mark_list = seg->link;

        switch (nonmoving_sweep_segment(seg)) {
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
        }
    }
}
