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

#define MIN(l,o) ((l) < (o) ? (l) : (o))

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

// How many Array# entries to add to the mark queue at once?
#define MARK_ARRAY_CHUNK_LENGTH 128

typedef struct {
    // index of first unused queue entry
    uint32_t head;

    MarkQueueEnt entries[];
} MarkQueueBlock;

// The length of MarkQueueBlock.entries
#define MARK_QUEUE_BLOCK_ENTRIES ((BLOCK_SIZE - sizeof(MarkQueueBlock)) / sizeof(MarkQueueEnt))

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

static void mark_queue_push (MarkQueue *q,
                             const MarkQueueEnt *ent)
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

static void mark_queue_push_closure (MarkQueue *q,
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

static void mark_queue_push_srt (MarkQueue *q,
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

static void mark_queue_push_thunk_srt (MarkQueue *q,
                                       const StgInfoTable *info)
{
    const StgThunkInfoTable *thunk_info = itbl_to_thunk_itbl(info);
    mark_queue_push_srt(q, GET_SRT(thunk_info), thunk_info->i.srt_bitmap);
}

static void mark_queue_push_fun_srt (MarkQueue *q,
                                     const StgInfoTable *info)
{
    const StgFunInfoTable *fun_info = itbl_to_fun_itbl(info);
    mark_queue_push_srt(q, GET_FUN_SRT(fun_info), fun_info->i.srt_bitmap);
}


static void mark_queue_push_array (MarkQueue *q,
                                   StgMutArrPtrs *array,
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

static bool is_valid_mark_queue_ent(const MarkQueueEnt *ent) {
    return ent->type != NULL_ENTRY;
}

// Returns invalid MarkQueueEnt if queue is empty.
static MarkQueueEnt mark_queue_pop(MarkQueue *queue)
{
    bool again;
    do {
        MarkQueueBlock *top = queue->top;
        again = false;

        // Are we at the beginning of the block?
        if (top->head == 0) {
            // Is this the first block of the queue?
            if (queue->blocks->link == NULL) {
                // Yes, therefore queue is empty...
                MarkQueueEnt none = {NULL_ENTRY, {{0}}};
                return none;
            } else {
                // No, unwind to the previous block and try popping again...
                bdescr *old_block = queue->blocks;
                queue->blocks = old_block->link;
                queue->top = (MarkQueueBlock *) old_block->start;
                freeGroup_lock(old_block); // TODO: hold on to a block to avoid repeated allocation/deallocation?
                again = true;
            }
        }
    } while (again);

    MarkQueueEnt ent = queue->top->entries[queue->top->head];
    queue->top->head--;

#if 0 && MARK_PREFETCH_QUEUE_DEPTH > 0
    // TODO
    int old_head = queue->prefetch_head;
    queue->prefetch_head = (queue->prefetch_head + 1) % MARK_PREFETCH_QUEUE_DEPTH;
    queue->prefetch_queue[old_head] = ent;
#endif

    return ent;
}

void init_mark_queue(MarkQueue *queue) {
    bdescr *bd = allocGroup_lock(1);
    bd->link = NULL;
    queue->blocks = bd;
    queue->top = (MarkQueueBlock *) bd->start;
    queue->top->head = 0;

#if MARK_PREFETCH_QUEUE_DEPTH > 0
    queue->prefetch_head = 0;
    memset(queue->prefetch_queue, 0,
           MARK_PREFETCH_QUEUE_DEPTH * sizeof(MarkQueueEnt));
#endif
}

/* Prepare to enter the mark phase. Must be done in stop-the-world. */
void nonmoving_prepare_mark(void)
{
    // The mark list should be empty since we shouldn't be in a GC.
    ASSERT(nonmoving_heap.mark_list == NULL);

    // Move blocks in the allocators' filled lists into mark_list and clear
    // their bitmaps
    for (int i=0; i < NONMOVING_ALLOCA_CNT; i++)
    {
        struct nonmoving_allocator *alloc = nonmoving_heap.allocators[i];
        struct nonmoving_segment *filled = alloc->filled;
        alloc->filled = NULL;
        if (filled == NULL) continue;

        // Walk down filled list, clearing bitmaps and updating snapshot
        // pointers as we go
        struct nonmoving_segment *seg = filled;
        while (true) {
            nonmoving_clear_bitmap(seg);
            seg->next_free_snap = seg->next_free;
            if (seg->link == NULL) {
                // We've reached the end; link into mark_list.
                seg->link = nonmoving_heap.mark_list;
                nonmoving_heap.mark_list = filled;
                break;
            }
            seg = seg->link;
        }
    }
}

static void mark_static_object(StgClosure **static_link, StgClosure *p)
{
    TODO;
}

static GNUC_ATTR_HOT void mark_closure(MarkQueue *queue,
                                       MarkQueueEnt *ent)
{
    ASSERT(ent->type == MARK_CLOSURE);
    StgClosure *p = ent->mark_closure.p;
    const StgWord tag = GET_CLOSURE_TAG(p);
    p = UNTAG_CLOSURE(p);
    const StgInfoTable *info = get_itbl(p);
    ASSERTM(LOOKS_LIKE_CLOSURE_PTR(p), "invalid closure, info=%p", p->header.info);

    if (!HEAP_ALLOCED_GC(p)) {
        switch (info->type) {
        case THUNK_STATIC:
            if (info->srt_bitmap != 0) {
                // TODO
            }
            return;

        case FUN_STATIC:
            if (info->srt_bitmap != 0) {
                // TODO
            }
            return;

        case IND_STATIC:
            // TODO
            return;

        case CONSTR:
        case CONSTR_1_0:
        case CONSTR_2_0:
        case CONSTR_1_1:
            // TODO
            return;

        case CONSTR_0_1:
        case CONSTR_0_2:
        case CONSTR_NOCAF:
            /* no need to put these on the static linked list, they don't need
             * to be marked.
             */
            return;

        default:
            barf("mark_closure(static): strange closure type %d", (int)(info->type));
        }
    }

    bdescr *bd = Bdescr((StgPtr) p);
    if (! (bd->flags & BF_NONMOVING)) {
        // The object lives outside of the non-moving heap; we needn't mark/trace
        // it since all references that we must trace to maintain our
        // liveness invariant were either promoted into the non-moving heap
        // at the beginning of this collection or are added to the update
        // remembered set.
        return;
    }


    // Mark the object
    struct nonmoving_segment *seg = nonmoving_get_segment((StgPtr) p);
    nonmoving_block_idx block_idx = nonmoving_get_block_idx((StgPtr) p);
    nonmoving_set_mark_bit(seg, block_idx);

    /////////////////////////////////////////////////////
    // Trace pointers
    /////////////////////////////////////////////////////

#   define PUSH_FIELD(obj, field)                                \
        mark_queue_push_closure(queue,                           \
                                (StgClosure *) (obj)->field,   \
                                p,                               \
                                (StgClosure **) &(obj)->field)

    // TODO: Write everything below here
    switch (INFO_PTR_TO_STRUCT(info)->type) {

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

    case CONSTR_0_1:
        // TODO: Factor out Evac's low-value Int/Char coalesce logic
        PUSH_FIELD(p, payload[0]);
        break;

    case THUNK_0_2:
        mark_queue_push_thunk_srt(queue, info);
        break;

    case FUN_0_2:
        mark_queue_push_fun_srt(queue, info);
        break;

    case CONSTR_0_2:
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

    case PAP:
        // TODO
        break;

    case AP:
        // TODO
        break;

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
        // TODO
        break;

    case STACK:
        // TODO
        break;


    case MUT_PRIM:
        // TODO
        break;

    case TREC_CHUNK: {
        StgTRecChunk *tc = ((StgTRecChunk *) p);
        // TODO
        PUSH_FIELD(tc, prev_chunk);
        TRecEntry *end = &tc->entries[tc->next_entry_idx];
        for (TRecEntry *e = &tc->entries[0]; e < end; e++) {
            mark_queue_push_closure(queue, (StgClosure *) e->tvar, NULL, NULL);
            mark_queue_push_closure(queue, (StgClosure *) e->expected_value, NULL, NULL);
            mark_queue_push_closure(queue, (StgClosure *) e->new_value, NULL, NULL);
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
            // TODO
            break;
        case MARK_FROM_SEL:
            // TODO
            break;
        case MARK_ARRAY: {
            StgMutArrPtrs *arr = ent.mark_array.array;
            StgWord start = ent.mark_array.start_index;
            StgWord end = start + MARK_ARRAY_CHUNK_LENGTH;
            if (end < arr->ptrs) {
                mark_queue_push_array(queue, ent.mark_array.array, end);
            } else {
                end = arr->ptrs;
            }
            for (StgWord i = start; i < end; i++) {
                mark_queue_push_closure(queue, arr->payload[i], NULL, NULL);
            }
            break;
        }
        case NULL_ENTRY:
            return;
        }
    }
}
