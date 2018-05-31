#include "Rts.h"
#include "RtsUtils.h"
#include "NonMoving.h"
#include "NonMovingScav.h"
#include "Capability.h"
#include "Scav.h"
#include "Evac.h"
#include "GCThread.h" // for GCUtils.h
#include "GCUtils.h"
#include "Printer.h"
#include "MarkWeak.h" // scavengeLiveWeak

void
nonmoving_scavenge_one(StgClosure *q)
{
    ASSERT(LOOKS_LIKE_CLOSURE_PTR(q));
    StgPtr p = (StgPtr)q;
    const StgInfoTable *info = get_itbl(q);

    switch (info->type) {

    case MVAR_CLEAN:
    case MVAR_DIRTY:
    {
        StgMVar *mvar = ((StgMVar *)p);
        evacuate((StgClosure **)&mvar->head);
        evacuate((StgClosure **)&mvar->tail);
        evacuate((StgClosure **)&mvar->value);
        if (gct->failed_to_evac) {
            mvar->header.info = &stg_MVAR_DIRTY_info;
        } else {
            mvar->header.info = &stg_MVAR_CLEAN_info;
        }
        break;
    }

    case TVAR:
    {
        StgTVar *tvar = ((StgTVar *)p);
        evacuate((StgClosure **)&tvar->current_value);
        evacuate((StgClosure **)&tvar->first_watch_queue_entry);
        if (gct->failed_to_evac) {
            tvar->header.info = &stg_TVAR_DIRTY_info;
        } else {
            tvar->header.info = &stg_TVAR_CLEAN_info;
        }
        break;
    }

    case FUN_2_0:
        scavenge_fun_srt(info);
        evacuate(&((StgClosure *)p)->payload[1]);
        evacuate(&((StgClosure *)p)->payload[0]);
        break;

    case THUNK_2_0:
        scavenge_thunk_srt(info);
        evacuate(&((StgThunk *)p)->payload[1]);
        evacuate(&((StgThunk *)p)->payload[0]);
        break;

    case CONSTR_2_0:
        evacuate(&((StgClosure *)p)->payload[1]);
        evacuate(&((StgClosure *)p)->payload[0]);
        break;

    case THUNK_1_0:
        scavenge_thunk_srt(info);
        evacuate(&((StgThunk *)p)->payload[0]);
        break;

    case FUN_1_0:
        scavenge_fun_srt(info);
        /* fallthrough */
    case CONSTR_1_0:
        evacuate(&((StgClosure *)p)->payload[0]);
        break;

    case THUNK_0_1:
        scavenge_thunk_srt(info);
        break;

    case FUN_0_1:
        scavenge_fun_srt(info);
        /* fallthrough */
    case CONSTR_0_1:
        break;

    case THUNK_0_2:
        scavenge_thunk_srt(info);
        break;

    case FUN_0_2:
        scavenge_fun_srt(info);
        /* fallthrough */
    case CONSTR_0_2:
        break;

    case THUNK_1_1:
        scavenge_thunk_srt(info);
        evacuate(&((StgThunk *)p)->payload[0]);
        break;

    case FUN_1_1:
        scavenge_fun_srt(info);
        /* fallthrough */
    case CONSTR_1_1:
        evacuate(&q->payload[0]);
        break;

    case FUN:
        scavenge_fun_srt(info);
        goto gen_obj;

    case THUNK:
    {
        scavenge_thunk_srt(info);
        StgPtr end = (P_)((StgThunk *)p)->payload + info->layout.payload.ptrs;
        for (p = (P_)((StgThunk *)p)->payload; p < end; p++) {
            evacuate((StgClosure **)p);
        }
        break;
    }

    gen_obj:
    case CONSTR:
    case CONSTR_NOCAF:
    case WEAK:
    case PRIM:
    {
        StgPtr end = (P_)((StgClosure *)p)->payload + info->layout.payload.ptrs;
        for (p = (P_)((StgClosure *)p)->payload; p < end; p++) {
            evacuate((StgClosure **)p);
        }
        break;
    }

    case BCO: {
        StgBCO *bco = (StgBCO *)p;
        evacuate((StgClosure **)&bco->instrs);
        evacuate((StgClosure **)&bco->literals);
        evacuate((StgClosure **)&bco->ptrs);
        break;
    }

    case MUT_VAR_CLEAN:
    case MUT_VAR_DIRTY:
        evacuate(&((StgMutVar *)p)->var);
        if (gct->failed_to_evac) {
            ((StgClosure *)q)->header.info = &stg_MUT_VAR_DIRTY_info;
        } else {
            ((StgClosure *)q)->header.info = &stg_MUT_VAR_CLEAN_info;
        }
        break;

    case BLOCKING_QUEUE:
    {
        StgBlockingQueue *bq = (StgBlockingQueue *)p;

        evacuate(&bq->bh);
        evacuate((StgClosure**)&bq->owner);
        evacuate((StgClosure**)&bq->queue);
        evacuate((StgClosure**)&bq->link);

        if (gct->failed_to_evac) {
            bq->header.info = &stg_BLOCKING_QUEUE_DIRTY_info;
        } else {
            bq->header.info = &stg_BLOCKING_QUEUE_CLEAN_info;
        }
        break;
    }

    case THUNK_SELECTOR:
    {
        StgSelector *s = (StgSelector *)p;
        evacuate(&s->selectee);
        break;
    }

    // A chunk of stack saved in a heap object
    case AP_STACK:
    {
        StgAP_STACK *ap = (StgAP_STACK *)p;

        evacuate(&ap->fun);
        scavenge_stack((StgPtr)ap->payload, (StgPtr)ap->payload + ap->size);
        break;
    }

    case PAP:
        p = scavenge_PAP((StgPAP *)p);
        break;

    case AP:
        scavenge_AP((StgAP *)p);
        break;

    case ARR_WORDS:
        // nothing to follow
        break;

    case MUT_ARR_PTRS_CLEAN:
    case MUT_ARR_PTRS_DIRTY:
    {
        // We don't eagerly promote objects pointed to by a mutable
        // array, but if we find the array only points to objects in
        // the same or an older generation, we mark it "clean" and
        // avoid traversing it during minor GCs.
        scavenge_mut_arr_ptrs((StgMutArrPtrs*)p);
        if (gct->failed_to_evac) {
            ((StgClosure *)q)->header.info = &stg_MUT_ARR_PTRS_DIRTY_info;
        } else {
            ((StgClosure *)q)->header.info = &stg_MUT_ARR_PTRS_CLEAN_info;
        }
        gct->failed_to_evac = true; // always put it on the mutable list.
        break;
    }

    case MUT_ARR_PTRS_FROZEN:
    case MUT_ARR_PTRS_FROZEN0:
        // follow everything
    {
        scavenge_mut_arr_ptrs((StgMutArrPtrs*)p);

        // If we're going to put this object on the mutable list, then
        // set its info ptr to MUT_ARR_PTRS_FROZEN0 to indicate that.
        if (gct->failed_to_evac) {
            ((StgClosure *)q)->header.info = &stg_MUT_ARR_PTRS_FROZEN0_info;
        } else {
            ((StgClosure *)q)->header.info = &stg_MUT_ARR_PTRS_FROZEN_info;
        }
        break;
    }

    case SMALL_MUT_ARR_PTRS_CLEAN:
    case SMALL_MUT_ARR_PTRS_DIRTY:
        // follow everything
    {
        // We don't eagerly promote objects pointed to by a mutable
        // array, but if we find the array only points to objects in
        // the same or an older generation, we mark it "clean" and
        // avoid traversing it during minor GCs.
        StgPtr next = p + small_mut_arr_ptrs_sizeW((StgSmallMutArrPtrs*)p);
        for (p = (P_)((StgSmallMutArrPtrs *)p)->payload; p < next; p++) {
            evacuate((StgClosure **)p);
        }
        if (gct->failed_to_evac) {
            ((StgClosure *)q)->header.info = &stg_SMALL_MUT_ARR_PTRS_DIRTY_info;
        } else {
            ((StgClosure *)q)->header.info = &stg_SMALL_MUT_ARR_PTRS_CLEAN_info;
        }
        gct->failed_to_evac = true; // always put it on the mutable list.
        break;
    }

    case SMALL_MUT_ARR_PTRS_FROZEN:
    case SMALL_MUT_ARR_PTRS_FROZEN0:
        // follow everything
    {
        StgPtr next = p + small_mut_arr_ptrs_sizeW((StgSmallMutArrPtrs*)p);
        for (p = (P_)((StgSmallMutArrPtrs *)p)->payload; p < next; p++) {
            evacuate((StgClosure **)p);
        }

        // If we're going to put this object on the mutable list, then
        // set its info ptr to SMALL_MUT_ARR_PTRS_FROZEN0 to indicate that.
        if (gct->failed_to_evac) {
            ((StgClosure *)q)->header.info = &stg_SMALL_MUT_ARR_PTRS_FROZEN0_info;
        } else {
            ((StgClosure *)q)->header.info = &stg_SMALL_MUT_ARR_PTRS_FROZEN_info;
        }
        break;
    }

    case TSO:
    {
        scavengeTSO((StgTSO *)p);
        break;
    }

    case STACK:
    {
        StgStack *stack = (StgStack*)p;

        scavenge_stack(stack->sp, stack->stack + stack->stack_size);
        stack->dirty = gct->failed_to_evac;
        // TODO (osa): There may be something special about stacks that we're
        // missing. All other mut objects are marked by using a different info
        // table except stacks.

        break;
    }

    case MUT_PRIM:
    {
        StgPtr end = (P_)((StgClosure *)p)->payload + info->layout.payload.ptrs;
        for (p = (P_)((StgClosure *)p)->payload; p < end; p++) {
            evacuate((StgClosure **)p);
        }
        gct->failed_to_evac = true; // mutable
        break;
    }

    case TREC_CHUNK:
      {
        StgWord i;
        StgTRecChunk *tc = ((StgTRecChunk *) p);
        TRecEntry *e = &(tc -> entries[0]);
        evacuate((StgClosure **)&tc->prev_chunk);
        for (i = 0; i < tc -> next_entry_idx; i ++, e++ ) {
          evacuate((StgClosure **)&e->tvar);
          evacuate((StgClosure **)&e->expected_value);
          evacuate((StgClosure **)&e->new_value);
        }
        gct->failed_to_evac = true; // mutable
        break;
      }

    case IND:
    case BLACKHOLE:
    case IND_STATIC:
        evacuate(&((StgInd *)p)->indirectee);
        break;

    default:
        barf("nonmoving scavenge: unimplemented/strange closure type %d @ %p",
             info->type, p);
    }

    if (gct->failed_to_evac) {
        // Mutable object or points to a younger object, add to the mut_list
        gct->failed_to_evac = false;
        if (oldest_gen->no > 0) {
            recordMutableGen_GC(q, oldest_gen->no);
        }
    }
}

static void
scavenge_nonmoving_segment(struct nonmoving_segment *seg)
{
    // scavenge objects between scan and free_ptr whose bitmap bits are 0
    bdescr *seg_block = Bdescr((P_)seg);

    ASSERT(seg_block->u.scan >= (P_)nonmoving_segment_get_block(seg, 0));
    ASSERT(seg_block->u.scan <= (P_)nonmoving_segment_get_block(seg, seg->next_free));

    while (seg_block->u.scan < (P_)nonmoving_segment_get_block(seg, seg->next_free)) {
        StgClosure *p = (StgClosure*)seg_block->u.scan;
        nonmoving_block_idx p_idx = nonmoving_get_block_idx((StgPtr)p);
        // bit set = was allocated in the previous GC
        // bit not set = new allocation, so scavenge
        if (!(nonmoving_get_mark_bit(seg, p_idx))) {
            // Set the mark bit to avoid scavenging this object in the next GC.
            // We only need to scavenge it again if it points to a younger
            // generation, but in that case it should be in the mut_list, which
            // is scavenged always.
            nonmoving_set_mark_bit(seg, p_idx);
            nonmoving_scavenge_one(p);
        }

        seg_block->u.scan = (P_)(((uint8_t*)seg_block->u.scan) + nonmoving_segment_block_size(seg));
    }
}

void scavenge_nonmoving_heap()
{
    // Always evacuate to non-moving heap when scavenging non-moving heap
    bool saved_forced_promotion = gct->forced_promotion;
    gct->forced_promotion = true;
    gct->evac_gen_no = oldest_gen->no; // to properly set failed_to_evac

    bool did_something;
loop:
    did_something = false;

    // Scavenge large objects
    gen_workspace *ws = &gct->gens[oldest_gen->no];
    for (bdescr *bd = ws->todo_large_objects; bd; bd = ws->todo_large_objects) {
        ASSERT(bd->flags & BF_NONMOVING);
        ws->todo_large_objects = bd->link;
        dbl_link_onto(bd, &ws->gen->scavenged_large_objects);
        ws->gen->n_scavenged_large_blocks += bd->blocks;
        nonmoving_scavenge_one((StgClosure*)bd->start);
        did_something = true;
    }

    // Scavenge segments
    while (nonmoving_todos) {
        struct nonmoving_segment* todo = nonmoving_todos;
        nonmoving_todos = todo->todo_link;
        todo->todo_link = NULL;
        scavenge_nonmoving_segment(todo);
        did_something = true;
    }

    // Perhaps we evacuated a large object while scavenging segments, so loop
    // again (FIXME ineffcient)
    if (did_something) {
        goto loop;
    }

    gct->forced_promotion = saved_forced_promotion;
}
