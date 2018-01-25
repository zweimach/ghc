/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team, 1998-2018
 *
 * Non-moving garbage collector and allocator
 *
 * ---------------------------------------------------------------------------*/

#pragma once

#include "BeginPrivate.h"

// In bytes
#define NONMOVING_SEGMENT_SIZE (32*1024)
// In blocks
#define NONMOVING_SEGMENT_BLOCKS (NONMOVING_SEGMENT_SIZE / BLOCK_SIZE)

_Static_assert(NONMOVING_SEGMENT_SIZE % BLOCK_SIZE == 0,
               "non-moving segment size must be multiple of block size");

// A non-moving heap segment
struct nonmoving_segment {
    struct nonmoving_segment *link;
    uint16_t next_free;  // index of the next unallocated block
    uint8_t block_size;  // log2 of block size
    uint8_t bitmap[];    // liveness bitmap
};

// A non-moving allocator for a particular block size
struct nonmoving_allocator {
    struct nonmoving_segment *filled;
    struct nonmoving_segment *active;
    struct nonmoving_segment *current[];
};

// first allocator is of size 2^NONNOVING_ALLOCA0
#define NONMOVING_ALLOCA0 3

// allocators cover block sizes of 2^NONNOVING_ALLOCA0 to
// 2^(NONMOVING_ALLOCA0 + NONNOVING_ALLOCA_CNT)
#define NONMOVING_ALLOCA_CNT 12

struct nonmoving_heap {
    struct nonmoving_allocator *allocators[NONMOVING_ALLOCA_CNT];
    struct nonmoving_segment *free; // free segment list
    struct Mutex mutex; // protects free list
    unsigned int n_caps;
};

void nonmoving_init();
void *nonmoving_allocate(Capability *cap, int sz);
void nonmoving_add_capabilities(int new_n_caps);

#include "EndPrivate.h"
