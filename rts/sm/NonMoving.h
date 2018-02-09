/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team, 1998-2018
 *
 * Non-moving garbage collector and allocator
 *
 * ---------------------------------------------------------------------------*/

#pragma once

#include "BeginPrivate.h"
#include <string.h>

// Segments
#define NONMOVING_SEGMENT_BITS 15   // 2^15 = 32kByte
// Mask to find base of segment
#define NONMOVING_SEGMENT_MASK ((1 << NONMOVING_SEGMENT_BITS) - 1)
// In bytes
#define NONMOVING_SEGMENT_SIZE (1 << NONMOVING_SEGMENT_BITS)
// In blocks
#define NONMOVING_SEGMENT_BLOCKS (NONMOVING_SEGMENT_SIZE / BLOCK_SIZE)

_Static_assert(NONMOVING_SEGMENT_SIZE % BLOCK_SIZE == 0,
               "non-moving segment size must be multiple of block size");

// A non-moving heap segment
struct nonmoving_segment {
    struct nonmoving_segment *link;  // for linking together segments into lists
    uint16_t next_free;              // index of the next unallocated block
    uint16_t next_free_snap;         // snapshot of next_free
    uint8_t block_size;              // log2 of block size
    uint8_t bitmap[];                // liveness bitmap
};

// The index of a block within a segment
typedef uint32_t nonmoving_block_idx;

// A non-moving allocator for a particular block size
struct nonmoving_allocator {
    struct nonmoving_segment *filled;
    struct nonmoving_segment *active;
    struct nonmoving_segment *current[];
};

// first allocator is of size 2^NONMOVING_ALLOCA0
#define NONMOVING_ALLOCA0 3

// allocators cover block sizes of 2^NONMOVING_ALLOCA0 to
// 2^(NONMOVING_ALLOCA0 + NONMOVING_ALLOCA_CNT)
#define NONMOVING_ALLOCA_CNT 12

struct nonmoving_heap {
    struct nonmoving_allocator *allocators[NONMOVING_ALLOCA_CNT];
    struct nonmoving_segment *free; // free segment list
    Mutex mutex; // protects free list

    // records the current length of the nonmoving_allocator.current arrays
    unsigned int n_caps;

    // The set of segments being marked this GC (or NULL if no mark is active).
    struct nonmoving_segment *mark_list;
};

extern struct nonmoving_heap nonmoving_heap;

void nonmoving_init(void);
void *nonmoving_allocate(Capability *cap, int sz);
void nonmoving_add_capabilities(int new_n_caps);

// The block size of a given segment in bytes.
INLINE_HEADER unsigned int nonmoving_segment_block_size(struct nonmoving_segment *seg)
{
  ASSERT(seg->block_size != 0);
  return 1 << seg->block_size;
}

// How many blocks does the given segment contain?
INLINE_HEADER unsigned int nonmoving_segment_block_count(struct nonmoving_segment *seg)
{
  unsigned int sz = nonmoving_segment_block_size(seg);
  return (NONMOVING_SEGMENT_SIZE - sizeof(*seg)) / (sz + 1);
}

// Get a pointer to the given block index
INLINE_HEADER void *nonmoving_segment_get_block(struct nonmoving_segment *seg, nonmoving_block_idx i)
{
  int blk_size = nonmoving_segment_block_size(seg);
  int n = nonmoving_segment_block_count(seg);
  return ((uint8_t*) seg) + n + i * blk_size;
}

// Get the segment which a closure resides in. Assumes that pointer points into
// non-moving heap.
INLINE_HEADER struct nonmoving_segment *nonmoving_get_segment(StgPtr p)
{
    ASSERT(Bdescr(p)->flags & BF_NONMOVING);
    const uintptr_t mask = ~(NONMOVING_SEGMENT_MASK - 1);
    return (struct nonmoving_segment *) (((uintptr_t) p) & mask);
}

INLINE_HEADER nonmoving_block_idx nonmoving_get_block_idx(StgPtr p)
{
    ASSERT(Bdescr(p)->flags & BF_NONMOVING);
    struct nonmoving_segment *seg = nonmoving_get_segment(p);
    StgPtr blk0 = nonmoving_segment_get_block(seg, 0);
    unsigned int blk_size = nonmoving_segment_block_size(seg);
    ptrdiff_t offset = p - blk0;
    return (nonmoving_block_idx) (offset / blk_size);
}

INLINE_HEADER void nonmoving_clear_bitmap(struct nonmoving_segment *seg)
{
    unsigned int n = nonmoving_segment_block_count(seg);
    memset(seg->bitmap, 0, n);
}

INLINE_HEADER void nonmoving_set_mark_bit(struct nonmoving_segment *seg, nonmoving_block_idx i)
{
    seg->bitmap[i] = 1;
}

INLINE_HEADER bool nonmoving_get_mark_bit(struct nonmoving_segment *seg, nonmoving_block_idx i)
{
    return seg->bitmap[i];
}

#include "EndPrivate.h"
