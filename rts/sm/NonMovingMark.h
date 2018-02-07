/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team, 1998-2018
 *
 * Non-moving garbage collector and allocator: Mark phase
 *
 * ---------------------------------------------------------------------------*/

#pragma once

#include "BeginPrivate.h"

enum EntryType {
    NULL_ENTRY = 0,
    MARK_CLOSURE,
    MARK_SRT,
    MARK_FROM_SEL,
    MARK_ARRAY
};

typedef struct {
    enum EntryType type;
    union {
        struct {
            StgClosure *p;             // the object to be marked
            StgClosure *origin;        // the object where this reference was found
            StgClosure **origin_field; // pointer to field where the reference was found
            StgClosure *origin_value;
        } mark_closure;
        struct {
            const StgSRT *srt;
            uint32_t srt_bitmap;
        } mark_srt;
        struct {
            StgClosure *p;
            StgWord origin_field;    // index of the referencing field
            StgClosure *mark_indir;
        } mark_from_sel;
        struct {
            StgMutArrPtrs *array;
            StgWord start_index;
        } mark_array;
    };
} MarkQueueEnt;

typedef struct {
    // index of first unused queue entry
    uint32_t head;

    MarkQueueEnt entries[];
} MarkQueueBlock;

#define MARK_PREFETCH_QUEUE_DEPTH 8

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

#if MARK_PREFETCH_QUEUE_DEPTH > 0
    // Prefetch queue ring buffer
    int prefetch_head;
    MarkQueueEnt prefetch_queue[MARK_PREFETCH_QUEUE_DEPTH];
#endif
} MarkQueue;

// The length of MarkQueueBlock.entries
#define MARK_QUEUE_BLOCK_ENTRIES ((BLOCK_SIZE - sizeof(MarkQueueBlock)) / sizeof(MarkQueueEnt))

void init_mark_queue(struct MarkQueue_ *queue);
void nonmoving_prepare_mark(void);
void nonmoving_mark(struct MarkQueue_ *restrict queue);

void mark_queue_push(MarkQueue *q, const MarkQueueEnt *ent);
void mark_queue_push_closure(MarkQueue *q,
                             StgClosure *p,
                             StgClosure *origin_closure,
                             StgClosure **origin_field);
void mark_queue_push_srt(MarkQueue *q, const StgSRT *srt, uint32_t srt_bitmap);
void mark_queue_push_thunk_srt(MarkQueue *q, const StgInfoTable *info);
void mark_queue_push_fun_srt(MarkQueue *q, const StgInfoTable *info);
void mark_queue_push_array(MarkQueue *q, const StgMutArrPtrs *array, StgWord start_index);

#include "EndPrivate.h"
