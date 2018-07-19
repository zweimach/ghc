/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team, 1998-2018
 *
 * Non-moving garbage collector and allocator: Mark phase
 *
 * ---------------------------------------------------------------------------*/

#include "Rts.h"
#include "NonMovingMark.h"
#include "NonMoving.h"
#include "BlockAlloc.h"
#include "HeapAlloc.h"
#include "Task.h"
#include "HeapUtils.h"
#include "Printer.h"
#include "Schedule.h"
#include "Weak.h"
#include "MarkWeak.h"
#include "Evac.h"
#include "sm/Storage.h"

// Necessary to declare global register variable
#include "GCThread.h"
#include "GCTDecl.h"

// How many Array# entries to add to the mark queue at once?
#define MARK_ARRAY_CHUNK_LENGTH 128

static Mutex upd_rem_set_lock;
bdescr *upd_rem_set_block_list = NULL;

#if defined(CONCURRENT_MARK)
/* Used during the mark/sweep phase transition to track how many capabilities
 * have pushed their update remembered sets. Protected by upd_rem_set_lock.
 */
static volatile StgWord upd_rem_set_flush_count = 0;
#endif

/* Signaled by each capability when it has flushed its update remembered set */
static Condition upd_rem_set_flushed_cond;

/* Indicates to mutators that the write barrier must be respected. Set while
 * concurrent mark is running.
 */
bool nonmoving_write_barrier_enabled = false;

/* Used to provide the current mark queue to the young generation
 * collector for scavenging.
 */
MarkQueue *current_mark_queue = NULL;

static void mark_tso (MarkQueue *queue, StgTSO *tso);
static void mark_stack (MarkQueue *queue, StgStack *stack);

/* Initialise update remembered set data structures */
void nonmoving_mark_init_upd_rem_set() {
    initMutex(&upd_rem_set_lock);
    initCondition(&upd_rem_set_flushed_cond);
}

/* Note [Update remembered set]
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * The concurrent non-moving collector uses a remembered set to ensure
 * that its marking is consistent with the snapshot invariant defined in
 * the design. This remembered set, known as the update remembered set,
 * records all pointers that have been overwritten since the beginning
 * of the concurrent mark. It is maintained via a write barrier that
 * is enabled whenever a concurrent mark is active.
 *
 * The representation of the update remembered set is the same as that of
 * the mark queue. For efficiency, each capability maintains its own local
 * accumulator of remembered set entries. When a capability fills its
 * accumulator it is linked in to the global remembered set
 * (upd_rem_set_block_list), where it is consumed by the mark phase.
 *
 * The mark phase is responsible for freeing update remembered set block
 * allocations.
 *
 */

/* Transfers the given capability's update-remembered set to the global
 * remembered set.
 */
static void nonmoving_add_upd_rem_set_blocks(MarkQueue *rset)
{
    if (mark_queue_is_empty(rset)) return;

    // find the tail of the queue
    bdescr *start = rset->blocks;
    bdescr *end = start;
    while (end->link != NULL)
        end = end->link;

    // add the blocks to the global remembered set
    ACQUIRE_LOCK(&upd_rem_set_lock);
    end->link = upd_rem_set_block_list;
    upd_rem_set_block_list = start;
    RELEASE_LOCK(&upd_rem_set_lock);

    // Reset remembered set
    ACQUIRE_SM_LOCK;
    init_mark_queue(rset);
    RELEASE_SM_LOCK;
}

#if defined(CONCURRENT_MARK)
/* Called by capabilities to flush their update remembered sets when
 * synchronising with the non-moving collector as it transitions from mark to
 * sweep phase.
 */
void nonmoving_flush_cap_upd_rem_set_blocks(Capability *cap)
{
    if (! cap->upd_rem_set_syncd) {
        debugTrace(DEBUG_nonmoving_gc, "Capability %d flushing update remembered set", cap->no);
        nonmoving_add_upd_rem_set_blocks(&cap->upd_rem_set.queue);
        atomic_inc(&upd_rem_set_flush_count, 1);
        cap->upd_rem_set_syncd = true;
        signalCondition(&upd_rem_set_flushed_cond);
        // After this mutation will remain suspended until nonmoving_finish_flush
        // releases its capabilities.
    }
}

/* Request that all capabilities flush their update remembered sets and suspend
 * execution until the further notice.
 */
void nonmoving_begin_flush(Capability **cap, Task *task)
{
    debugTrace(DEBUG_nonmoving_gc, "Starting update remembered set flush...");
    for (unsigned int i = 0; i < n_capabilities; i++) {
        capabilities[i]->upd_rem_set_syncd = false;
    }
    upd_rem_set_flush_count = 0;
    nonmoving_flush_cap_upd_rem_set_blocks(*cap);
    stopAllCapabilitiesWith(cap, task, SYNC_FLUSH_UPD_REM_SET);

    // XXX: We may have been given a capability via releaseCapability (i.e. a
    // task suspended due to a foreign call) in which case our requestSync
    // logic won't have been hit. Make sure that everyone so far has flushed.
    // Ideally we want to mark asynchronously with syncing.
    for (unsigned int i = 0; i < n_capabilities; i++) {
        nonmoving_flush_cap_upd_rem_set_blocks(capabilities[i]);
    }
}

/* Wait until a capability has flushed its update remembered set. Returns true
 * if all capabilities have flushed.
 */
bool nonmoving_wait_for_flush()
{
    ACQUIRE_LOCK(&upd_rem_set_lock);
    debugTrace(DEBUG_nonmoving_gc, "Flush count %d", upd_rem_set_flush_count);
    bool finished = (upd_rem_set_flush_count == n_capabilities) || (sched_state == SCHED_SHUTTING_DOWN);
    if (!finished) {
        waitCondition(&upd_rem_set_flushed_cond, &upd_rem_set_lock);
    }
    RELEASE_LOCK(&upd_rem_set_lock);
    return finished;
}

/* Signal to the mark thread that the RTS is shutting down. */
void nonmoving_shutting_down()
{
    ASSERT(sched_state == SCHED_SHUTTING_DOWN);
    signalCondition(&upd_rem_set_flushed_cond);
}

/* Notify capabilities that the synchronisation is finished; they may resume
 * execution.
 */
void nonmoving_finish_flush(Capability *cap, Task *task)
{
    debugTrace(DEBUG_nonmoving_gc, "Finished update remembered set flush...");
    releaseAllCapabilities(n_capabilities, cap, task);
}
#else
void nonmoving_shutting_down() {}
#endif

/*********************************************************
 * Pushing to either the mark queue or remembered set
 *********************************************************/

STATIC_INLINE void push (MarkQueue *q, const MarkQueueEnt *ent)
{
    // Are we at the end of the block?
    if (q->top->head == MARK_QUEUE_BLOCK_ENTRIES) {
        // Yes, this block is full.
        if (q->is_upd_rem_set) {
            nonmoving_add_upd_rem_set_blocks(q);
        } else {
            // allocate a fresh block.
            bdescr *bd = allocGroup(1);
            bd->link = q->blocks;
            q->blocks = bd;
            q->top = (MarkQueueBlock *) bd->start;
            q->top->head = 0;
        }
    }

    q->top->entries[q->top->head] = *ent;
    q->top->head++;
}

STATIC_INLINE
void push_closure (MarkQueue *q,
                   StgClosure *p,
                   StgClosure *origin_closure,
                   StgWord origin_field)
{
    // TODO: Push this into callers where they already have the Bdescr
    if (HEAP_ALLOCED_GC(p) && (Bdescr((StgPtr) p)->gen != oldest_gen))
        return;

#if defined(DEBUG)
    LOOKS_LIKE_CLOSURE_PTR(p);
    LOOKS_LIKE_CLOSURE_PTR(origin_closure);
    assert_in_nonmoving_heap((P_)p);
    if (origin_closure) {
        assert_in_nonmoving_heap((P_)origin_closure);
    }
#endif

    MarkQueueEnt ent = {
        .type = MARK_CLOSURE,
        .mark_closure = {
            .p = UNTAG_CLOSURE(p),
            .origin = UNTAG_CLOSURE(origin_closure),
            .origin_field = origin_field,
            .origin_value = UNTAG_CLOSURE(p)
        }
    };
    push(q, &ent);
}

STATIC_INLINE
void push_array (MarkQueue *q,
                 const StgMutArrPtrs *array,
                 StgWord start_index)
{
    MarkQueueEnt ent = {
        .type = MARK_ARRAY,
        .mark_array = {
            .array = array,
            .start_index = start_index
        }
    };
    push(q, &ent);
}

STATIC_INLINE
void push_thunk_srt (MarkQueue *q, const StgInfoTable *info)
{
    const StgThunkInfoTable *thunk_info = itbl_to_thunk_itbl(info);
    if (thunk_info->i.srt) {
        push_closure(q, (StgClosure*)GET_SRT(thunk_info), NULL, 0);
    }
}

STATIC_INLINE
void push_fun_srt (MarkQueue *q, const StgInfoTable *info)
{
    const StgFunInfoTable *fun_info = itbl_to_fun_itbl(info);
    if (fun_info->i.srt) {
        push_closure(q, (StgClosure*)GET_FUN_SRT(fun_info), NULL, 0);
    }
}

/*********************************************************
 * Pushing to the update remembered set
 *********************************************************/

/* Push the free variables of a (now-evaluated) thunk to the
 * update remembered set.
 */
void upd_rem_set_push_thunk(Capability *cap, StgThunk *origin)
{
    // TODO: Eliminate this conditional once it's folded into codegen
    if (!nonmoving_write_barrier_enabled) return;
    const StgInfoTable *info = get_itbl((StgClosure*)origin);
    switch (info->type) {
    case THUNK:
    case THUNK_1_0:
    case THUNK_0_1:
    case THUNK_2_0:
    case THUNK_1_1:
    case THUNK_0_2:
    {
        MarkQueue *queue = &cap->upd_rem_set.queue;
        push_thunk_srt(queue, info);
        for (StgWord i = 0; i < info->layout.payload.ptrs; i++) {
            push_closure(queue,
                         origin->payload[i],
                         (StgClosure*)origin,
                         i);
        }
        break;
    }
    case THUNK_SELECTOR:
    case BLACKHOLE:
        // TODO: This is right, right?
        break;
    default:
        barf("upd_rem_set_push_thunk: invalid thunk pushed: p=%p, type=%d", origin, info->type);
    }

}

void upd_rem_set_push_thunk_(StgRegTable *reg, StgThunk *origin)
{
    // TODO: Eliminate this conditional once it's folded into codegen
    if (!nonmoving_write_barrier_enabled) return;
    upd_rem_set_push_thunk(regTableToCapability(reg), origin);
}

void upd_rem_set_push_closure_(StgRegTable *reg,
                               StgClosure *p,
                               StgClosure *origin_closure,
                               StgWord origin_field)
{
    // TODO: Eliminate this conditional once it's folded into codegen
    if (!nonmoving_write_barrier_enabled) return;
    MarkQueue *queue = &regTableToCapability(reg)->upd_rem_set.queue;
    push_closure(queue, p, origin_closure, origin_field);
}

void upd_rem_set_push_tso(Capability *cap, StgTSO *tso)
{
    // TODO: Eliminate this conditional once it's folded into codegen
    if (!nonmoving_write_barrier_enabled) return;
    if (Bdescr((StgPtr) tso)->gen != oldest_gen) return;
    if (nonmoving_get_closure_mark_bit((StgPtr) tso)) return;
    mark_tso(&cap->upd_rem_set.queue, tso);
}

void upd_rem_set_push_stack(Capability *cap, StgStack *stack)
{
    // TODO: Eliminate this conditional once it's folded into codegen
    if (!nonmoving_write_barrier_enabled) return;
    if (Bdescr((StgPtr) stack)->gen != oldest_gen) return;
    if (nonmoving_get_closure_mark_bit((StgPtr) stack)) return;
    mark_stack(&cap->upd_rem_set.queue, stack);
}

int count_global_upd_rem_set_blocks()
{
    return countBlocks(upd_rem_set_block_list);
}
/*********************************************************
 * Pushing to the mark queue
 *********************************************************/

void mark_queue_push (MarkQueue *q, const MarkQueueEnt *ent)
{
    push(q, ent);
}

void mark_queue_push_closure (MarkQueue *q,
                              StgClosure *p,
                              StgClosure *origin_closure,
                              StgWord origin_field)
{
    push_closure(q, p, origin_closure, origin_field);
}

/* TODO: Do we really never want to specify the origin here? */
void mark_queue_add_root(MarkQueue* q, StgClosure** root)
{
    mark_queue_push_closure(q, *root, NULL, 0);
}

/* Push a closure to the mark queue without origin information */
void mark_queue_push_closure_ (MarkQueue *q, StgClosure *p)
{
    mark_queue_push_closure(q, p, NULL, 0);
}

void mark_queue_push_fun_srt (MarkQueue *q, const StgInfoTable *info)
{
    push_fun_srt(q, info);
}

void mark_queue_push_thunk_srt (MarkQueue *q, const StgInfoTable *info)
{
    push_thunk_srt(q, info);
}

void mark_queue_push_array (MarkQueue *q,
                            const StgMutArrPtrs *array,
                            StgWord start_index)
{
    push_array(q, array, start_index);
}

/*********************************************************
 * Popping from the mark queue
 *********************************************************/

// Returns invalid MarkQueueEnt if queue is empty.
static MarkQueueEnt mark_queue_pop(MarkQueue *q)
{
    MarkQueueBlock *top;

again:
    top = q->top;

    // Are we at the beginning of the block?
    if (top->head == 0) {
        // Is this the first block of the queue?
        if (q->blocks->link == NULL) {
            // Yes, therefore queue is empty...
            MarkQueueEnt none = {};
            return none;
        } else {
            // No, unwind to the previous block and try popping again...
            bdescr *old_block = q->blocks;
            q->blocks = old_block->link;
            q->top = (MarkQueueBlock*)q->blocks->start;
            freeGroup(old_block); // TODO: hold on to a block to avoid repeated allocation/deallocation?
            goto again;
        }
    }

    q->top->head--;
    MarkQueueEnt ent = q->top->entries[q->top->head];

#if MARK_PREFETCH_QUEUE_DEPTH > 0
    // TODO
    int old_head = queue->prefetch_head;
    queue->prefetch_head = (queue->prefetch_head + 1) % MARK_PREFETCH_QUEUE_DEPTH;
    queue->prefetch_queue[old_head] = ent;
#endif

    return ent;
}

/*********************************************************
 * Creating and destroying MarkQueues and UpdRemSets
 *********************************************************/

/* Must hold sm_mutex. */
void init_mark_queue(MarkQueue *queue)
{
    bdescr *bd = allocGroup(1);
    queue->blocks = bd;
    queue->top = (MarkQueueBlock *) bd->start;
    queue->top->head = 0;
    queue->is_upd_rem_set = false;
    queue->marked_objects = allocHashTable();

#if MARK_PREFETCH_QUEUE_DEPTH > 0
    queue->prefetch_head = 0;
    memset(queue->prefetch_queue, 0,
           MARK_PREFETCH_QUEUE_DEPTH * sizeof(MarkQueueEnt));
#endif
}

/* Must hold sm_mutex. */
void init_upd_rem_set(UpdRemSet *rset)
{
    init_mark_queue(&rset->queue);
    rset->queue.is_upd_rem_set = true;
}

void free_mark_queue(MarkQueue *queue)
{
    bdescr* b = queue->blocks;
    while (b)
    {
        bdescr* b_ = b->link;
        freeGroup(b);
        b = b_;
    }
    freeHashTable(queue->marked_objects, NULL);
}

/*********************************************************
 * Marking
 *********************************************************/

static void mark_tso (MarkQueue *queue, StgTSO *tso)
{
    if (tso->bound != NULL) {
        mark_queue_push_closure_(queue, (StgClosure *) tso->bound->tso);
    }

    mark_queue_push_closure_(queue, (StgClosure *) tso->blocked_exceptions);
    mark_queue_push_closure_(queue, (StgClosure *) tso->bq);
    mark_queue_push_closure_(queue, (StgClosure *) tso->trec);
    mark_queue_push_closure_(queue, (StgClosure *) tso->stackobj);
    mark_queue_push_closure_(queue, (StgClosure *) tso->_link);
    if (   tso->why_blocked == BlockedOnMVar
        || tso->why_blocked == BlockedOnMVarRead
        || tso->why_blocked == BlockedOnBlackHole
        || tso->why_blocked == BlockedOnMsgThrowTo
        || tso->why_blocked == NotBlocked
        ) {
        mark_queue_push_closure_(queue, tso->block_info.closure);
    }
}

static void
do_push_closure(StgClosure **p, void *user)
{
    MarkQueue *queue = (MarkQueue *) user;
    // TODO: Origin? need reference to containing closure
    mark_queue_push_closure_(queue, *p);
}

static void
mark_large_bitmap (MarkQueue *queue,
                   StgClosure **p,
                   StgLargeBitmap *large_bitmap,
                   StgWord size)
{
    walk_large_bitmap(do_push_closure, p, large_bitmap, size, queue);
}

static void
mark_small_bitmap (MarkQueue *queue, StgClosure **p, StgWord size, StgWord bitmap)
{
    while (size > 0) {
        if ((bitmap & 1) == 0) {
            // TODO: Origin?
            mark_queue_push_closure(queue, *p, NULL, 0);
        }
        p++;
        bitmap = bitmap >> 1;
        size--;
    }
}

static GNUC_ATTR_HOT
void mark_PAP_payload (MarkQueue *queue,
                       StgClosure *fun,
                       StgClosure **payload,
                       StgWord size)
{
    const StgFunInfoTable *fun_info = get_fun_itbl(UNTAG_CONST_CLOSURE(fun));
    ASSERT(fun_info->i.type != PAP);
    StgPtr p = (StgPtr) payload;

    StgWord bitmap;
    switch (fun_info->f.fun_type) {
    case ARG_GEN:
        bitmap = BITMAP_BITS(fun_info->f.b.bitmap);
        goto small_bitmap;
    case ARG_GEN_BIG:
        mark_large_bitmap(queue, payload, GET_FUN_LARGE_BITMAP(fun_info), size);
        break;
    case ARG_BCO:
        mark_large_bitmap(queue, payload, BCO_BITMAP(fun), size);
        break;
    default:
        bitmap = BITMAP_BITS(stg_arg_bitmaps[fun_info->f.fun_type]);
    small_bitmap:
        mark_small_bitmap(queue, (StgClosure **) p, size, bitmap);
        break;
    }
}

/* Helper for mark_stack; returns next stack frame. */
static StgPtr
mark_arg_block (MarkQueue *queue, const StgFunInfoTable *fun_info, StgClosure **args)
{
    StgWord bitmap, size;

    StgPtr p = (StgPtr)args;
    switch (fun_info->f.fun_type) {
    case ARG_GEN:
        bitmap = BITMAP_BITS(fun_info->f.b.bitmap);
        size = BITMAP_SIZE(fun_info->f.b.bitmap);
        goto small_bitmap;
    case ARG_GEN_BIG:
        size = GET_FUN_LARGE_BITMAP(fun_info)->size;
        mark_large_bitmap(queue, (StgClosure**)p, GET_FUN_LARGE_BITMAP(fun_info), size);
        p += size;
        break;
    default:
        bitmap = BITMAP_BITS(stg_arg_bitmaps[fun_info->f.fun_type]);
        size = BITMAP_SIZE(stg_arg_bitmaps[fun_info->f.fun_type]);
    small_bitmap:
        mark_small_bitmap(queue, (StgClosure**)p, size, bitmap);
        p += size;
        break;
    }
    return p;
}

static GNUC_ATTR_HOT void
mark_stack_ (MarkQueue *queue, StgPtr sp, StgPtr spBottom)
{
    ASSERT(sp <= spBottom);

    while (sp < spBottom) {
        const StgRetInfoTable *info = get_ret_itbl((StgClosure *)sp);
        switch (info->i.type) {
        case UPDATE_FRAME:
        {
            // See Note [upd-black-hole] in rts/Scav.c
            StgUpdateFrame *frame = (StgUpdateFrame *) sp;
            mark_queue_push_closure_(queue, frame->updatee);
            sp += sizeofW(StgUpdateFrame);
            continue;
        }

            // small bitmap (< 32 entries, or 64 on a 64-bit machine)
        case CATCH_STM_FRAME:
        case CATCH_RETRY_FRAME:
        case ATOMICALLY_FRAME:
        case UNDERFLOW_FRAME:
        case STOP_FRAME:
        case CATCH_FRAME:
        case RET_SMALL:
        {
            StgWord bitmap = BITMAP_BITS(info->i.layout.bitmap);
            StgWord size   = BITMAP_SIZE(info->i.layout.bitmap);
            // NOTE: the payload starts immediately after the info-ptr, we
            // don't have an StgHeader in the same sense as a heap closure.
            sp++;
            mark_small_bitmap(queue, (StgClosure **) sp, size, bitmap);
            sp += size;
        }
        follow_srt:
            if (info->i.srt) {
                mark_queue_push_closure_(queue, (StgClosure*)GET_SRT(info));
            }
            continue;

        case RET_BCO: {
            sp++;
            mark_queue_push_closure_(queue, *(StgClosure**)sp);
            StgBCO *bco = (StgBCO *)*sp;
            sp++;
            StgWord size = BCO_BITMAP_SIZE(bco);
            mark_large_bitmap(queue, (StgClosure **) sp, BCO_BITMAP(bco), size);
            sp += size;
            continue;
        }

          // large bitmap (> 32 entries, or > 64 on a 64-bit machine)
        case RET_BIG:
        {
            StgWord size;

            size = GET_LARGE_BITMAP(&info->i)->size;
            sp++;
            mark_large_bitmap(queue, (StgClosure **) sp, GET_LARGE_BITMAP(&info->i), size);
            sp += size;
            // and don't forget to follow the SRT
            goto follow_srt;
        }

        case RET_FUN:
        {
            StgRetFun *ret_fun = (StgRetFun *)sp;
            const StgFunInfoTable *fun_info;

            mark_queue_push_closure_(queue, ret_fun->fun);
            fun_info = get_fun_itbl(UNTAG_CLOSURE(ret_fun->fun));
            sp = mark_arg_block(queue, fun_info, ret_fun->payload);
            goto follow_srt;
        }

        default:
            barf("mark_stack: weird activation record found on stack: %d", (int)(info->i.type));
        }
    }
}

static GNUC_ATTR_HOT void
mark_stack (MarkQueue *queue, StgStack *stack)
{
    mark_stack_(queue, stack->sp, stack->stack + stack->stack_size);
}

static GNUC_ATTR_HOT void
mark_closure (MarkQueue *queue, StgClosure *p)
{
    p = UNTAG_CLOSURE(p);
    ASSERTM(LOOKS_LIKE_CLOSURE_PTR(p), "invalid closure, info=%p", p->header.info);

#   define PUSH_FIELD(obj, field)                                \
        mark_queue_push_closure(queue,                           \
                                (StgClosure *) (obj)->field,     \
                                p,                               \
                                ((StgClosure **) &(obj)->field) - (StgClosure **) (obj))

    ASSERT(!IS_FORWARDING_PTR(p->header.info));

    if (!HEAP_ALLOCED_GC(p)) {
        const StgInfoTable *info = get_itbl(p);
        StgHalfWord type = info->type;

        if (type == CONSTR_0_1 || type == CONSTR_0_2 || type == CONSTR_NOCAF) {
            // no need to put these on the static linked list, they don't need
            // to be marked.
            return;
        }

        if (lookupHashTable(queue->marked_objects, (W_)p)) {
            // already marked
            return;
        }

        insertHashTable(queue->marked_objects, (W_)p, (P_)1);

        switch (type) {

        case THUNK_STATIC:
            if (info->srt != 0) {
                mark_queue_push_thunk_srt(queue, info); // TODO this function repeats the check above
            }
            return;

        case FUN_STATIC:
            if (info->srt != 0 || info->layout.payload.ptrs != 0) {
                mark_queue_push_fun_srt(queue, info); // TODO this function repeats the check above

                // a FUN_STATIC can also be an SRT, so it may have pointer
                // fields.  See Note [SRTs] in CmmBuildInfoTables, specifically
                // the [FUN] optimisation.
                // TODO (osa) I don't understand this comment
                for (StgHalfWord i = 0; i < info->layout.payload.ptrs; ++i) {
                    PUSH_FIELD(p, payload[i]);
                }
            }
            return;

        case IND_STATIC:
            StgInd *ind = (StgInd *)p;
            PUSH_FIELD(ind, indirectee);
            return;

        case CONSTR:
        case CONSTR_1_0:
        case CONSTR_2_0:
        case CONSTR_1_1:
            for (StgHalfWord i = 0; i < info->layout.payload.ptrs; ++i) {
                PUSH_FIELD(p, payload[i]);
            }
            return;

        default:
            barf("mark_closure(static): strange closure type %d", (int)(info->type));
        }
    }

    bdescr *bd = Bdescr((StgPtr) p);

    if (bd->flags & BF_NONMOVING) {

        if (bd->flags & BF_LARGE) {
            if (lookupHashTable(queue->marked_objects, (W_)bd)) {
                return;
            }
            insertHashTable(queue->marked_objects, (W_)bd, (P_)1);

            // Not seen before, object must be in one of these lists:
            //
            // * oldest_gen->large_objects:
            //     if it's not evacuated in this GC (was evacuated before)
            // * oldest_gen->scavenged_large_objects:
            //     if it's evacuated in this GC (must have been scavenged by scavenge_nonmoving_segment)
            //
            // If it's in large_objects we must move it to scavenged_large_objects,
            // which will be made large_objects by the end of this GC.

#if defined(DEBUG)
            bool found_it = false;
#endif
            for (bdescr *large = oldest_gen->large_objects; large; large = large->link) {
                if (large == bd) {
                    // remove from large_object list
                    dbl_link_remove(bd, &oldest_gen->large_objects);
                    // move to scavenged_large_objects
                    dbl_link_onto(bd, &oldest_gen->scavenged_large_objects);
                    oldest_gen->n_scavenged_large_blocks += bd->blocks;
#if defined(DEBUG)
                    found_it = true;
#endif
                    break;
                }
            }

#if defined(DEBUG)
            if (!found_it) {
                // Not in large_objects list, must be in scavenged_large_objects
                for (bdescr *large = oldest_gen->scavenged_large_objects; large; large = large->link) {
                    if (large == bd) {
                        found_it = true;
                        break;
                    }
                }
            }

            ASSERT(found_it);
#endif

            // Mark contents
            p = (StgClosure*)bd->start;
        } else {
            struct nonmoving_segment *seg = nonmoving_get_segment((StgPtr) p);
            nonmoving_block_idx block_idx = nonmoving_get_block_idx((StgPtr) p);
            if (p >= (StgClosure *) nonmoving_segment_get_block(seg, seg->next_free_snap)
                || nonmoving_get_mark_bit(seg, block_idx)) {
                return;
            }
            nonmoving_set_mark_bit(seg, block_idx);
        }
    }

    // A pinned object that is still attached to a capability (because it's not
    // filled yet). No need to trace it pinned objects can't contain poiners.
    else if (bd->flags & BF_PINNED) {
#if defined(DEBUG)
        bool found_it = false;
        for (uint32_t i = 0; i < n_capabilities; ++i) {
            if (capabilities[i]->pinned_object_block == bd) {
                found_it = true;
                break;
            }
        }
        ASSERT(found_it);
#endif
        return;
    }

    else {
        // Here we have an object living outside of the non-moving heap. Since
        // we moved everything to the non-moving heap before starting the major
        // collection, we know that we don't need to trace it: it was allocated
        // after we took our snapshot.
        return;
    }

    /////////////////////////////////////////////////////
    // Trace pointers
    /////////////////////////////////////////////////////

    const StgInfoTable *info = get_itbl(p);
    switch (info->type) {

    case MVAR_CLEAN:
    case MVAR_DIRTY: {
        StgMVar *mvar = (StgMVar *) p;
        PUSH_FIELD(mvar, head);
        PUSH_FIELD(mvar, tail);
        PUSH_FIELD(mvar, value);
        break;
    }

    case TVAR: {
        StgTVar *tvar = ((StgTVar *)p);
        PUSH_FIELD(tvar, current_value);
        PUSH_FIELD(tvar, first_watch_queue_entry);
        break;
    }

    case FUN_2_0:
        mark_queue_push_fun_srt(queue, info);
        PUSH_FIELD(p, payload[1]);
        PUSH_FIELD(p, payload[0]);
        break;

    case THUNK_2_0: {
        StgThunk *thunk = (StgThunk *) p;
        mark_queue_push_thunk_srt(queue, info);
        PUSH_FIELD(thunk, payload[1]);
        PUSH_FIELD(thunk, payload[0]);
        break;
    }

    case CONSTR_2_0:
        PUSH_FIELD(p, payload[1]);
        PUSH_FIELD(p, payload[0]);
        break;

    case THUNK_1_0:
        mark_queue_push_thunk_srt(queue, info);
        PUSH_FIELD((StgThunk *) p, payload[0]);
        break;

    case FUN_1_0:
        mark_queue_push_fun_srt(queue, info);
        PUSH_FIELD(p, payload[0]);
        break;

    case CONSTR_1_0:
        PUSH_FIELD(p, payload[0]);
        break;

    case THUNK_0_1:
        mark_queue_push_thunk_srt(queue, info);
        break;

    case FUN_0_1:
        mark_queue_push_fun_srt(queue, info);
        break;

    case CONSTR_0_1:
    case CONSTR_0_2:
        break;

    case THUNK_0_2:
        mark_queue_push_thunk_srt(queue, info);
        break;

    case FUN_0_2:
        mark_queue_push_fun_srt(queue, info);
        break;

    case THUNK_1_1:
        mark_queue_push_thunk_srt(queue, info);
        PUSH_FIELD((StgThunk *) p, payload[0]);
        break;

    case FUN_1_1:
        mark_queue_push_fun_srt(queue, info);
        PUSH_FIELD(p, payload[0]);
        break;

    case CONSTR_1_1:
        PUSH_FIELD(p, payload[0]);
        break;

    case FUN:
        mark_queue_push_fun_srt(queue, info);
        goto gen_obj;

    case THUNK: {
        mark_queue_push_thunk_srt(queue, info);
        for (StgWord i = 0; i < info->layout.payload.ptrs; i++) {
            StgClosure *field = ((StgThunk *) p)->payload[i];
            mark_queue_push_closure(queue, field, p, i);
        }
        break;
    }

    gen_obj:
    case CONSTR:
    case CONSTR_NOCAF:
    case WEAK:
    case PRIM:
    {
        for (StgWord i = 0; i < info->layout.payload.ptrs; i++) {
            StgClosure *field = ((StgClosure *) p)->payload[i];
            mark_queue_push_closure(queue, field, p, i);
        }
        break;
    }

    case BCO: {
        StgBCO *bco = (StgBCO *)p;
        PUSH_FIELD(bco, instrs);
        PUSH_FIELD(bco, literals);
        PUSH_FIELD(bco, ptrs);
        break;
    }


    case IND:
    case BLACKHOLE:
        PUSH_FIELD((StgInd *) p, indirectee);
        break;

    case MUT_VAR_CLEAN:
    case MUT_VAR_DIRTY:
        PUSH_FIELD((StgMutVar *)p, var);
        break;

    case BLOCKING_QUEUE: {
        StgBlockingQueue *bq = (StgBlockingQueue *)p;
        PUSH_FIELD(bq, bh);
        PUSH_FIELD(bq, owner);
        PUSH_FIELD(bq, queue);
        PUSH_FIELD(bq, link);
        break;
    }

    case THUNK_SELECTOR:
        PUSH_FIELD((StgSelector *) p, selectee);
        // TODO: selector optimization
        break;

    case AP_STACK: {
        StgAP_STACK *ap = (StgAP_STACK *)p;
        PUSH_FIELD(ap, fun);
        mark_stack_(queue, (StgPtr) ap->payload, (StgPtr) ap->payload + ap->size);
        break;
    }

    case PAP: {
        StgPAP *pap = (StgPAP *) p;
        PUSH_FIELD(pap, fun);
        mark_PAP_payload(queue, pap->fun, pap->payload, pap->n_args);
        break;
    }

    case AP: {
        StgAP *ap = (StgAP *) p;
        PUSH_FIELD(ap, fun);
        mark_PAP_payload(queue, ap->fun, ap->payload, ap->n_args);
        break;
    }

    case ARR_WORDS:
        // nothing to follow
        break;

    case MUT_ARR_PTRS_CLEAN:
    case MUT_ARR_PTRS_DIRTY:
    case MUT_ARR_PTRS_FROZEN_CLEAN:
    case MUT_ARR_PTRS_FROZEN_DIRTY:
        // TODO: Check this against Scav.c
        mark_queue_push_array(queue, (StgMutArrPtrs *) p, 0);
        break;

    case SMALL_MUT_ARR_PTRS_CLEAN:
    case SMALL_MUT_ARR_PTRS_DIRTY:
    case SMALL_MUT_ARR_PTRS_FROZEN_CLEAN:
    case SMALL_MUT_ARR_PTRS_FROZEN_DIRTY: {
        StgSmallMutArrPtrs *arr = (StgSmallMutArrPtrs *) p;
        for (StgWord i = 0; i < arr->ptrs; i++) {
            StgClosure *field = arr->payload[i];
            mark_queue_push_closure(queue, field, p, i);
        }
        break;
    }

    case TSO:
        mark_tso(queue, (StgTSO *) p);
        break;

    case STACK: {
        StgStack *stack = (StgStack *) p;
        mark_stack(queue, stack);
        break;
    }

    case MUT_PRIM: {
        for (StgHalfWord p_idx = 0; p_idx < info->layout.payload.ptrs; ++p_idx) {
            mark_queue_push_closure(queue, p->payload[p_idx], p, p_idx);
        }
        break;
    }

    case TREC_CHUNK: {
        StgTRecChunk *tc = ((StgTRecChunk *) p);
        PUSH_FIELD(tc, prev_chunk);
        TRecEntry *end = &tc->entries[tc->next_entry_idx];
        for (TRecEntry *e = &tc->entries[0]; e < end; e++) {
            mark_queue_push_closure_(queue, (StgClosure *) e->tvar);
            mark_queue_push_closure_(queue, (StgClosure *) e->expected_value);
            mark_queue_push_closure_(queue, (StgClosure *) e->new_value);
        }
        break;
    }

    default:
        barf("mark_closure: unimplemented/strange closure type %d @ %p",
             info->type, p);
    }

#   undef PUSH_FIELD
}

/* This is the main mark loop.
 * Invariants:
 *
 *  a. nonmoving_prepare_mark has been called.
 *  b. the nursery has been fully evacuated into the non-moving generation.
 *  c. the mark queue has been seeded with a set of roots.
 *  d. can_yield = false when we are in the midst of a update-remembered set flush.
 */
GNUC_ATTR_HOT void nonmoving_mark(MarkQueue *queue)
{
    while (true) {
        MarkQueueEnt ent = mark_queue_pop(queue);

        switch (ent.type) {
        case MARK_CLOSURE:
            if (!ent.mark_closure.p) continue;
            mark_closure(queue, ent.mark_closure.p);
            break;
        case MARK_ARRAY: {
            const StgMutArrPtrs *arr = ent.mark_array.array;
            if (!arr) continue;
            StgWord start = ent.mark_array.start_index;
            StgWord end = start + MARK_ARRAY_CHUNK_LENGTH;
            if (end < arr->ptrs) {
                mark_queue_push_array(queue, ent.mark_array.array, end);
            } else {
                end = arr->ptrs;
            }
            for (StgWord i = start; i < end; i++) {
                mark_queue_push_closure_(queue, arr->payload[i]);
            }
            break;
        }
        case NULL_MARK_QUEUE_ENTRY:
            // Perhaps the update remembered set has more to mark...
            if (upd_rem_set_block_list) {
                ACQUIRE_LOCK(&upd_rem_set_lock);
                queue->blocks = upd_rem_set_block_list;
                queue->top = (MarkQueueBlock *) queue->blocks->start;
                upd_rem_set_block_list = NULL;
                RELEASE_LOCK(&upd_rem_set_lock);
            } else {
                // Nothing more to do
                return;
            }
        }
    }
}

// A variant of `isAlive` that works for non-moving heap. Used for:
//
// - Collecting weak pointers; checking key of a weak pointer.
// - Resurrecting threads; checking if a thread is dead.
// - Sweeping object lists: large_objects, mut_list, stable_name_table.
//
bool nonmoving_is_alive(HashTable *marked_objects, StgClosure *p)
{
    // Ignore static closures. See comments in `isAlive`.
    if (!HEAP_ALLOCED_GC(p)) {
        return true;
    }

    bdescr *bd = Bdescr((P_)p);
    if (bd->flags & BF_LARGE) {
        return lookupHashTable(marked_objects, (W_)bd);
    } else {
        ASSERT(bd->flags & BF_NONMOVING);
        return nonmoving_get_closure_mark_bit((P_)p);
    }
}

// Non-moving heap variant of `tidyWeakList`
bool nonmoving_mark_weaks(struct MarkQueue_ *queue)
{
    bool did_work = false;

    StgWeak **last_w = &oldest_gen->old_weak_ptr_list;
    StgWeak *next_w;
    for (StgWeak *w = oldest_gen->old_weak_ptr_list; w != NULL; w = next_w) {
        if (w->header.info == &stg_DEAD_WEAK_info) {
            // finalizeWeak# was called on the weak
            next_w = w->link;
            *last_w = next_w;
            continue;
        }

        // Otherwise it's a live weak
        ASSERT(w->header.info == &stg_WEAK_info);

        if (nonmoving_is_alive(queue->marked_objects, w->key)) {
            nonmoving_mark_live_weak(queue, w);
            did_work = true;

            // remove this weak ptr from old_weak_ptr list
            *last_w = w->link;
            next_w = w->link;

            // and put it on the weak ptr list
            w->link = oldest_gen->weak_ptr_list;
            oldest_gen->weak_ptr_list = w;
        } else {
            last_w = &(w->link);
            next_w = w->link;
        }
    }

    return did_work;
}

void nonmoving_mark_dead_weak(struct MarkQueue_ *queue, StgWeak *w)
{
    if (w->cfinalizers != &stg_NO_FINALIZER_closure) {
        mark_queue_push_closure_(queue, w->value);
    }
    mark_queue_push_closure_(queue, w->finalizer);
}

void nonmoving_mark_live_weak(struct MarkQueue_ *queue, StgWeak *w)
{
    // TODO: Omer, why should this be true? The WEAK could be dead even if its key is still alive, no?
    //ASSERT(nonmoving_get_closure_mark_bit((P_)w));
    mark_queue_push_closure_(queue, w->value);
    mark_queue_push_closure_(queue, w->finalizer);
    mark_queue_push_closure_(queue, w->cfinalizers);
}

void nonmoving_mark_dead_weaks(struct MarkQueue_ *queue)
{
    StgWeak *next_w;
    for (StgWeak *w = oldest_gen->old_weak_ptr_list; w; w = next_w) {
        ASSERT(!nonmoving_get_closure_mark_bit((P_)(w->key)));
        nonmoving_mark_dead_weak(queue, w);
        next_w = w ->link;
        w->link = dead_weak_ptr_list;
        dead_weak_ptr_list = w;
    }
}

void nonmoving_mark_threads(struct MarkQueue_ *queue)
{
    StgTSO *next;
    StgTSO **prev = &oldest_gen->old_threads;
    for (StgTSO *t = oldest_gen->old_threads; t != END_TSO_QUEUE; t = next) {

        next = t->global_link;

        if (nonmoving_is_alive(queue->marked_objects, (StgClosure*)t)) {
            // alive
            *prev = next;

            // move this thread onto threads list
            t->global_link = oldest_gen->threads;
            oldest_gen->threads = t;
        } else {
            // not alive (yet): leave this thread on the old_threads list
            prev = &(t->global_link);
        }
    }
}

void nonmoving_resurrect_threads(struct MarkQueue_ *queue)
{
    StgTSO *next;
    for (StgTSO *t = oldest_gen->old_threads; t != END_TSO_QUEUE; t = next) {
        next = t->global_link;

        switch (t->what_next) {
        case ThreadKilled:
        case ThreadComplete:
            continue;
        default:
            mark_queue_push_closure_(queue, (StgClosure*)t);
            t->global_link = resurrected_threads;
            resurrected_threads = t;
        }
    }
}

#ifdef DEBUG

void print_queue_ent(MarkQueueEnt *ent)
{
    if (ent->type == MARK_CLOSURE) {
        debugBelch("Closure: ");
        printClosure(ent->mark_closure.p);
    } else if (ent->type == MARK_ARRAY) {
        debugBelch("Array\n");
    } else {
        debugBelch("End of mark\n");
    }
}

void print_mark_queue(MarkQueue *q)
{
    debugBelch("======== MARK QUEUE ========\n");
    for (bdescr *block = q->blocks; block; block = block->link) {
        MarkQueueBlock *queue = (MarkQueueBlock*)block->start;
        for (uint32_t i = 0; i < queue->head; ++i) {
            print_queue_ent(&queue->entries[i]);
        }
    }
    debugBelch("===== END OF MARK QUEUE ====\n");
}

#endif
