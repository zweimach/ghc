/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team, 1998-2018
 *
 * Non-moving garbage collector and allocator: Mark phase
 *
 * ---------------------------------------------------------------------------*/

#pragma once

#include "BeginPrivate.h"

#include "Hash.h"

enum EntryType {
    NULL_ENTRY = 0,
    MARK_CLOSURE,
    MARK_ARRAY
};

typedef struct {
    enum EntryType type;
    // All pointers should be untagged
    union {
        struct {
            StgClosure *p;        // the object to be marked
            StgClosure *origin;   // the object where this reference was found
            StgWord origin_field; // field index where the reference was found
            StgClosure *origin_value;
        } mark_closure;
        struct {
            const StgMutArrPtrs *array;
            StgWord start_index;
        } mark_array;
    };
} MarkQueueEnt;

typedef struct {
    // index of first *unused* queue entry
    uint32_t head;

    MarkQueueEnt entries[];
} MarkQueueBlock;

#define MARK_PREFETCH_QUEUE_DEPTH 0 // TODO: 8

/* The mark queue is not capable of concurrent read or write.
 *
 * invariants:
 *
 *  a. top == blocks->start;
 *  b. there is always a valid MarkQueueChunk, although it may be empty
 *     (e.g. top->head == 0).
 */
typedef struct MarkQueue_ {
    // A singly link-list of blocks, each containing a MarkQueueChunk.
    bdescr *blocks;

    // Cached value of blocks->start.
    MarkQueueBlock *top;

    // Marked objects outside of nonmoving heap, namely large and static
    // objects.
    HashTable *marked_objects;

#if MARK_PREFETCH_QUEUE_DEPTH > 0
    // Prefetch queue ring buffer
    int prefetch_head;
    MarkQueueEnt prefetch_queue[MARK_PREFETCH_QUEUE_DEPTH];
#endif
} MarkQueue;

// The length of MarkQueueBlock.entries
#define MARK_QUEUE_BLOCK_ENTRIES ((BLOCK_SIZE - sizeof(MarkQueueBlock)) / sizeof(MarkQueueEnt))

extern bdescr *nonmoving_large_objects, *nonmoving_marked_large_objects;
extern memcount n_nonmoving_large_blocks, n_nonmoving_marked_large_blocks;

void mark_queue_add_root(MarkQueue* q, StgClosure** root);

void init_mark_queue(MarkQueue *queue);
void free_mark_queue(MarkQueue *queue);
void nonmoving_mark(struct MarkQueue_ *restrict queue);

bool nonmoving_mark_weaks(struct MarkQueue_ *queue);
void nonmoving_tidy_threads(void);
void nonmoving_mark_dead_weaks(struct MarkQueue_ *queue);
void nonmoving_resurrect_threads(struct MarkQueue_ *queue);
bool nonmoving_is_alive(StgClosure *p);
void nonmoving_mark_dead_weak(struct MarkQueue_ *queue, StgWeak *w);
void nonmoving_mark_live_weak(struct MarkQueue_ *queue, StgWeak *w);

void mark_queue_push(MarkQueue *q, const MarkQueueEnt *ent);
void mark_queue_push_closure(MarkQueue *q,
                             StgClosure *p,
                             StgClosure *origin_closure,
                             StgWord origin_field);
void mark_queue_push_closure_(MarkQueue *q, StgClosure *p);
void mark_queue_push_thunk_srt(MarkQueue *q, const StgInfoTable *info);
void mark_queue_push_fun_srt(MarkQueue *q, const StgInfoTable *info);
void mark_queue_push_array(MarkQueue *q, const StgMutArrPtrs *array, StgWord start_index);

#if defined(DEBUG)

void print_queue_ent(MarkQueueEnt *ent);
void print_mark_queue(MarkQueue *q);

#endif

#include "EndPrivate.h"
