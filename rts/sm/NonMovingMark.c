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
#include "HeapAlloc.h"
#include "Task.h"
#include "HeapUtils.h"
#include "Printer.h"
#include "Weak.h"
#include "MarkWeak.h"
#include "Evac.h"

// How many Array# entries to add to the mark queue at once?
#define MARK_ARRAY_CHUNK_LENGTH 128

static void mark_closure (MarkQueue *queue, MarkQueueEnt *ent);

void mark_queue_add_root(MarkQueue* q, StgClosure** root)
{
    mark_queue_push_closure(q, *root, NULL, NULL);
}

void mark_queue_push (MarkQueue *q, const MarkQueueEnt *ent)
{
    // Are we at the end of the block?
    if (q->top->head == MARK_QUEUE_BLOCK_ENTRIES) {
        // Yes, allocate a fresh block.
        bdescr *bd = allocGroup_lock(1);
        bd->link = q->blocks;
        q->blocks = bd;
        q->top = (MarkQueueBlock *) bd->start;
        q->top->head = 0;
    }

    q->top->entries[q->top->head] = *ent;
    q->top->head++;
}

void mark_queue_push_closure (MarkQueue *q,
                              StgClosure *p,
                              StgClosure *origin_closure,
                              StgClosure **origin_field)
{
    MarkQueueEnt ent = {
        .type = MARK_CLOSURE,
        .mark_closure = {
            .p = p,
            .origin = origin_closure,
            .origin_field = origin_field,
            .origin_value = p
        }
    };
    mark_queue_push(q, &ent);
}

/* Push a closure to the mark queue without origin information */
static void mark_queue_push_closure_ (MarkQueue *q,
                                      StgClosure *p)
{
    mark_queue_push_closure(q, p, NULL, NULL);
}

void mark_queue_push_srt (MarkQueue *q,
                          const StgSRT *srt,
                          uint32_t srt_bitmap)
{
    if (srt_bitmap) {
        MarkQueueEnt ent = {
            .type = MARK_SRT,
            .mark_srt = {
                .srt = srt,
                .srt_bitmap = srt_bitmap
            }
        };
        mark_queue_push(q, &ent);
    }
}

void mark_queue_push_thunk_srt (MarkQueue *q,
                                const StgInfoTable *info)
{
    const StgThunkInfoTable *thunk_info = itbl_to_thunk_itbl(info);
    mark_queue_push_srt(q, GET_SRT(thunk_info), thunk_info->i.srt_bitmap);
}

void mark_queue_push_fun_srt (MarkQueue *q,
                              const StgInfoTable *info)
{
    const StgFunInfoTable *fun_info = itbl_to_fun_itbl(info);
    mark_queue_push_srt(q, GET_FUN_SRT(fun_info), fun_info->i.srt_bitmap);
}


void mark_queue_push_array (MarkQueue *q,
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
    mark_queue_push(q, &ent);
}

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
            freeGroup_lock(old_block); // TODO: hold on to a block to avoid repeated allocation/deallocation?
            goto again;
        }
    }

    q->top->head--;
    MarkQueueEnt ent = q->top->entries[q->top->head];

#if 0 && MARK_PREFETCH_QUEUE_DEPTH > 0
    // TODO
    int old_head = queue->prefetch_head;
    queue->prefetch_head = (queue->prefetch_head + 1) % MARK_PREFETCH_QUEUE_DEPTH;
    queue->prefetch_queue[old_head] = ent;
#endif

    return ent;
}

/* Must hold sm_mutex. */
void init_mark_queue(MarkQueue *queue)
{
    bdescr *bd = allocGroup(1);
    queue->blocks = bd;
    queue->top = (MarkQueueBlock *) bd->start;
    queue->top->head = 0;
    queue->static_objects = allocHashTable();

#if MARK_PREFETCH_QUEUE_DEPTH > 0
    queue->prefetch_head = 0;
    memset(queue->prefetch_queue, 0,
           MARK_PREFETCH_QUEUE_DEPTH * sizeof(MarkQueueEnt));
#endif
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
    freeHashTable(queue->static_objects, NULL);
}

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

static void mark_large_srt_bitmap (MarkQueue *queue, StgLargeSRT *large_srt)
{
    walk_large_srt(do_push_closure, large_srt, queue);
}

static GNUC_ATTR_HOT void mark_srt (MarkQueue *queue, MarkQueueEnt *ent)
{
    uint32_t bitmap = ent->mark_srt.srt_bitmap;
    if (bitmap == (StgHalfWord)(-1)) {
        mark_large_srt_bitmap(queue, (StgLargeSRT *) ent->mark_srt.srt);
        return;
    }

    StgClosure **p = (StgClosure **) ent->mark_srt.srt;
    while (bitmap != 0) {
        if ((bitmap & 1) != 0) {
            // TODO: COMPILING_WINDOWS_DLL hack
            mark_queue_push_closure_(queue, *p);
        }
        p++;
        bitmap = bitmap >> 1;
    }
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
            mark_queue_push_closure(queue, *p, NULL, NULL);
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
mark_stack (MarkQueue *queue, StgPtr sp, StgPtr spBottom)
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
            mark_queue_push_srt(queue, GET_SRT(info), info->i.srt_bitmap);
            continue;

        case RET_BCO: {
            sp++;
            mark_queue_push_closure_(queue, (StgClosure *) sp);
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
mark_closure (MarkQueue *queue, MarkQueueEnt *ent)
{
    ASSERT(ent->type == MARK_CLOSURE);
    StgClosure *p = UNTAG_CLOSURE(ent->mark_closure.p);
    ASSERTM(LOOKS_LIKE_CLOSURE_PTR(p), "invalid closure, info=%p", p->header.info);

#   define PUSH_FIELD(obj, field)                                \
        mark_queue_push_closure(queue,                           \
                                (StgClosure *) (obj)->field,     \
                                p,                               \
                                (StgClosure **) &(obj)->field)

    if (!HEAP_ALLOCED_GC(p)) {
        const StgInfoTable *info = get_itbl(p);
        StgHalfWord type = info->type;

        if (type == CONSTR_0_1 || type == CONSTR_0_2 || type == CONSTR_NOCAF) {
            // no need to put these on the static linked list, they don't need
            // to be marked.
            return;
        }

        if (lookupHashTable(queue->static_objects, (W_)p)) {
            // already marked
            return;
        }

        insertHashTable(queue->static_objects, (W_)p, (P_)1);

        switch (type) {

        case THUNK_STATIC:
            if (info->srt_bitmap != 0) {
                evacuate_static_object(THUNK_STATIC_LINK((StgClosure *)p), p);
                mark_queue_push_thunk_srt(queue, info);
            }
            return;

        case FUN_STATIC:
            if (info->srt_bitmap != 0) {
                evacuate_static_object(FUN_STATIC_LINK((StgClosure *)p), p);
                mark_queue_push_fun_srt(queue, info);
            }
            return;

        case IND_STATIC:
            evacuate_static_object(IND_STATIC_LINK((StgClosure *)p), p);
            StgInd *ind = (StgInd *)p;
            PUSH_FIELD(ind, indirectee);
            return;

        case CONSTR:
        case CONSTR_1_0:
        case CONSTR_2_0:
        case CONSTR_1_1:
            evacuate_static_object(STATIC_LINK(info,(StgClosure *)p), p);
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
        struct nonmoving_segment *seg = nonmoving_get_segment((StgPtr) p);
        nonmoving_block_idx block_idx = nonmoving_get_block_idx((StgPtr) p);
        if (nonmoving_get_mark_bit(seg, block_idx)) {
            return;
        }
        nonmoving_set_mark_bit(seg, block_idx);
    }

    else {
        // This usually means
        // - A large object
        // - A pinned object (which is also a large object)
        // - A bug

        if (lookupHashTable(queue->static_objects, (W_)p)) {
            return;
        }
        insertHashTable(queue->static_objects, (W_)p, (P_)1);

        if (bd->flags & BF_LARGE) {
            // If the object is in large_objects list, move it to
            // scavenged_large_objects list. This happens when the large object
            // is only reachable via some other objects in nonmoving heap.
            bool in_large_objects = false;
            for (bdescr *large = oldest_gen->large_objects; large; large = large->link) {
                if (large == bd) {
                    // remove from large_object list
                    if (bd->u.back) {
                        bd->u.back->link = bd->link;
                    } else { // first object in the list
                        oldest_gen->large_objects = bd->link;
                    }
                    if (bd->link) {
                        bd->link->u.back = bd->u.back;
                    }
                    // move to scavenged_large_objects
                    dbl_link_onto(bd, &oldest_gen->scavenged_large_objects);
                    oldest_gen->n_scavenged_large_blocks += bd->blocks;
                    break;
                }
            }

            p = (StgClosure*)bd->start;
        }
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
        break;

    case THUNK: {
        mark_queue_push_thunk_srt(queue, info);
        StgClosure **end = (StgClosure **) ((StgThunk *)p)->payload + info->layout.payload.ptrs;
        for (StgClosure **field = (StgClosure **) ((StgThunk *)p)->payload; field < end; field++) {
            mark_queue_push_closure(queue, *field, p, field);
        }
        break;
    }

    case CONSTR:
    case CONSTR_NOCAF:
    case WEAK:
    case PRIM:
    {
        StgClosure **end = (StgClosure **) ((StgClosure *)p)->payload + info->layout.payload.ptrs;
        for (StgClosure **field = (StgClosure **) ((StgClosure *)p)->payload; field < end; field++) {
            mark_queue_push_closure(queue, *field, p, field);
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
        mark_stack(queue, (StgPtr) ap->payload, (StgPtr) ap->payload + ap->size);
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
    case MUT_ARR_PTRS_FROZEN:
    case MUT_ARR_PTRS_FROZEN0:
        // TODO: Check this against Scav.c
        mark_queue_push_array(queue, (StgMutArrPtrs *) p, 0);
        break;

    case SMALL_MUT_ARR_PTRS_CLEAN:
    case SMALL_MUT_ARR_PTRS_DIRTY:
    case SMALL_MUT_ARR_PTRS_FROZEN:
    case SMALL_MUT_ARR_PTRS_FROZEN0: {
        StgSmallMutArrPtrs *arr = (StgSmallMutArrPtrs *) p;
        StgClosure **end = arr->payload + arr->ptrs;
        for (StgClosure **i = arr->payload; i < end; i++) {
            mark_queue_push_closure(queue, *i, p, i);
        }
        break;
    }

    case TSO:
        mark_tso(queue, (StgTSO *) p);
        break;

    case STACK: {
        StgStack *stack = (StgStack *) p;
        mark_stack(queue, stack->sp, stack->stack + stack->stack_size);
        break;
    }

    case MUT_PRIM:
        ASSERT(0); // TODO
        break;

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
 *
 */
GNUC_ATTR_HOT void nonmoving_mark(MarkQueue *queue)
{
    while (true) {
        MarkQueueEnt ent = mark_queue_pop(queue);

        switch (ent.type) {
        case MARK_CLOSURE:
            mark_closure(queue, &ent);
            break;
        case MARK_SRT:
            mark_srt(queue, &ent);
            break;
        case MARK_FROM_SEL:
            ASSERT(0); // TODO
            break;
        case MARK_ARRAY: {
            const StgMutArrPtrs *arr = ent.mark_array.array;
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
        case NULL_ENTRY:
            return;
        }
    }
}

static bool nonmoving_is_alive(struct MarkQueue_ *queue, StgClosure *p)
{
    bdescr *bd = Bdescr((P_)p);
    if (bd->flags & BF_NONMOVING) {
        return nonmoving_get_closure_mark_bit((P_)p);
    } else {
        return lookupHashTable(queue->static_objects, (W_)p);
    }
}

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

        if (nonmoving_is_alive(queue, w->key)) {
            // The whole weak (including the value and finalizers) has already
            // been scavenged to the current generation, just mark them.
            // Note that we can't just push the weak itself, because key, value
            // and finalizers are not pointer fields so they won't be marked by
            // mark_closure
            mark_queue_push_closure_(queue, (StgClosure*)w);
            mark_queue_push_closure_(queue, w->value);
            mark_queue_push_closure_(queue, w->finalizer);
            mark_queue_push_closure_(queue, w->cfinalizers);
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

void nonmoving_mark_dead_weaks(struct MarkQueue_ *queue)
{
    StgWeak *next_w;
    for (StgWeak *w = oldest_gen->old_weak_ptr_list; w; w = next_w) {
        if (w->cfinalizers != &stg_NO_FINALIZER_closure) {
            mark_queue_push_closure_(queue, w->value);
        }
        mark_queue_push_closure_(queue, w->finalizer);
        next_w = w ->link;
        w->link = dead_weak_ptr_list;
        dead_weak_ptr_list = w;
    }
}

void nonmoving_mark_threads(struct MarkQueue_ *queue)
{
    StgTSO *next;
    StgTSO **prev = &oldest_gen->old_threads;
    for (StgTSO *t = oldest_gen->old_threads; t != END_TSO_QUEUE; t = t->global_link) {

        next = t->global_link;

        if (nonmoving_is_alive(queue, (StgClosure*)t)) {
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

bool nonmoving_resurrect_threads(struct MarkQueue_ *queue)
{
    bool did_work = false;

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
            did_work = true;
        }
    }

    return did_work;
}

#ifdef DEBUG

void print_queue_ent(MarkQueueEnt *ent)
{
    if (ent->type == MARK_CLOSURE) {
        debugBelch("Closure: ");
        printClosure(ent->mark_closure.p);
    } else if (ent->type == MARK_SRT) {
        debugBelch("SRT: %p\n", (void*)ent->mark_srt.srt);
    } else if (ent->type == MARK_FROM_SEL) {
        debugBelch("Selector\n");
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
