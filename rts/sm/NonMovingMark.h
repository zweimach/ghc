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

#include "Hash.h"

enum EntryType {
    NULL_ENTRY = 0,
    MARK_CLOSURE,
    MARK_ARRAY
};

/* Note [Origin references in the nonmoving collector]
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 *
 * To implement indirection short-cutting and the selector optimisation the
 * collector needs to know where it found references, so it can update the
 * reference if it later turns out that points to an indirection. For this
 * reason, each mark queue entry contains two things:
 *
 * - a pointer to the object to be marked (p), and
 *
 * - a pointer to the field where we found the reference (origin)
 *
 * Note that the origin pointer is an interior pointer: it points not to a
 * valid closure (with info table pointer) but rather to a field inside a closure.
 * Since such references can't be safely scavenged we establish the invariant
 * that the origin pointer may only point to a field of an object living in the
 * nonmoving heap, where no scavenging is needed.
 *
 */

typedef struct {
    enum EntryType type;
    // All pointers should be untagged
    union {
        struct {
            StgClosure *p;        // the object to be marked
            StgClosure **origin;  // field where this reference was found.
                                  // See Note [Origin references in the nonmoving collector]
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

    // Is this a mark queue or a capability-local update remembered set?
    bool is_upd_rem_set;

    // Marked objects outside of nonmoving heap, namely large and static
    // objects.
    HashTable *marked_objects;
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

extern bdescr *nonmoving_large_objects, *nonmoving_marked_large_objects;
extern memcount n_nonmoving_large_blocks, n_nonmoving_marked_large_blocks;

extern StgTSO *nonmoving_old_threads;
extern StgWeak *nonmoving_old_weak_ptr_list;
extern StgTSO *nonmoving_threads;
extern StgWeak *nonmoving_weak_ptr_list;

#if defined(DEBUG)
extern StgIndStatic *debug_caf_list_snapshot;
#endif

extern MarkQueue *current_mark_queue;
extern bdescr *upd_rem_set_block_list;
extern bool nonmoving_write_barrier_enabled;
void nonmoving_mark_init_upd_rem_set(void);

void init_upd_rem_set(UpdRemSet *rset);
void upd_rem_set_push_thunk(Capability *cap, StgThunk *origin);
void upd_rem_set_push_thunk_(StgRegTable *reg, StgThunk *origin);
void upd_rem_set_push_tso(Capability *cap, StgTSO *tso);
void upd_rem_set_push_stack(Capability *cap, StgStack *stack);
// Debug only -- count number of blocks in global UpdRemSet
int count_global_upd_rem_set_blocks(void);

#if defined(CONCURRENT_MARK)
void nonmoving_flush_cap_upd_rem_set_blocks(Capability *cap);
void nonmoving_begin_flush(Task *task);
bool nonmoving_wait_for_flush(void);
void nonmoving_finish_flush(Task *task);
#endif

void mark_queue_add_root(MarkQueue* q, StgClosure** root);

void init_mark_queue(MarkQueue *queue);
void free_mark_queue(MarkQueue *queue);
void nonmoving_mark(struct MarkQueue_ *restrict queue);

bool nonmoving_tidy_weaks(struct MarkQueue_ *queue);
void nonmoving_tidy_threads(void);
void nonmoving_mark_dead_weaks(struct MarkQueue_ *queue, StgWeak **dead_weak_ptr_list);
void nonmoving_resurrect_threads(struct MarkQueue_ *queue, StgTSO **resurrected_threads);
bool nonmoving_is_alive(StgClosure *p);
void nonmoving_mark_dead_weak(struct MarkQueue_ *queue, StgWeak *w);
void nonmoving_mark_live_weak(struct MarkQueue_ *queue, StgWeak *w);

void mark_queue_push(MarkQueue *q, const MarkQueueEnt *ent);
void mark_queue_push_closure(MarkQueue *q,
                             StgClosure *p,
                             StgClosure **origin);
void mark_queue_push_closure_(MarkQueue *q, StgClosure *p);
void mark_queue_push_thunk_srt(MarkQueue *q, const StgInfoTable *info);
void mark_queue_push_fun_srt(MarkQueue *q, const StgInfoTable *info);
void mark_queue_push_array(MarkQueue *q, const StgMutArrPtrs *array, StgWord start_index);
void upd_rem_set_push_thunk_eager(Capability *cap,
                                  const StgThunkInfoTable *orig_info,
                                  StgThunk *thunk);

INLINE_HEADER bool mark_queue_is_empty(MarkQueue *q)
{
    return (q->blocks == NULL) || (q->top->head == 0 && q->blocks->link == NULL);
}

#if defined(DEBUG)

void print_queue_ent(MarkQueueEnt *ent);
void print_mark_queue(MarkQueue *q);

#endif

#include "EndPrivate.h"
