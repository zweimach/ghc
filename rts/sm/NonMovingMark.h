/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team, 1998-2018
 *
 * Non-moving garbage collector and allocator: Mark phase
 *
 * ---------------------------------------------------------------------------*/

#pragma once

#include "Hash.h"
#include "Task.h"
#include "NonMoving.h"

#include "BeginPrivate.h"

enum EntryType {
    NULL_MARK_QUEUE_ENTRY = 0,
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

/* While it shares its representation with MarkQueue, UpdRemSet differs in
 * behavior when pushing; namely full chunks are immediately pushed to the
 * global update remembered set, not accumulated into a chain. We make this
 * distinction apparent in the types.
 */
typedef struct {
    MarkQueue queue;
} UpdRemSet;

// The length of MarkQueueBlock.entries
#define MARK_QUEUE_BLOCK_ENTRIES ((BLOCK_SIZE - sizeof(MarkQueueBlock)) / sizeof(MarkQueueEnt))

extern bool nonmoving_write_barrier_enabled;
extern MarkQueue *current_mark_queue;

// Defined in NonMovingMark.c
extern bdescr *upd_rem_set_block_list;

void nonmoving_mark_init_upd_rem_set(void);

void init_upd_rem_set(UpdRemSet *rset);
void upd_rem_set_push_thunk(Capability *cap, StgThunk *origin);
void upd_rem_set_push_thunk_(StgRegTable *reg, StgThunk *origin);
// Debug only -- count number of blocks in global UpdRemSet
int count_global_upd_rem_set_blocks(void);

#if defined(CONCURRENT_MARK)
void nonmoving_flush_cap_upd_rem_set_blocks(Capability *cap);
void nonmoving_begin_flush(Capability **cap, Task *task);
bool nonmoving_wait_for_flush(void);
void nonmoving_finish_flush(Capability *cap, Task *task);
#endif
void nonmoving_shutting_down(void);

void mark_queue_add_root(MarkQueue* q, StgClosure** root);

void init_mark_queue(MarkQueue *queue);
void free_mark_queue(MarkQueue *queue);
void nonmoving_mark(struct MarkQueue_ *restrict queue, bool can_yield);

bool nonmoving_mark_weaks(struct MarkQueue_ *queue);
void nonmoving_mark_threads(struct MarkQueue_ *queue);
void nonmoving_mark_dead_weaks(struct MarkQueue_ *queue);
void nonmoving_resurrect_threads(struct MarkQueue_ *queue);
bool nonmoving_is_alive(HashTable *marked_objects, StgClosure *p);
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

INLINE_HEADER bool mark_queue_is_empty(MarkQueue *q)
{
    return (q->blocks == NULL) || (q->top->head == 0 && q->blocks->link == NULL);
}

#if defined(DEBUG)

void print_queue_ent(MarkQueueEnt *ent);
void print_mark_queue(MarkQueue *q);

#endif

#include "EndPrivate.h"
