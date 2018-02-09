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

enum EntryType {
    NULL_ENTRY = 0,
    MARK_CLOSURE,
    MARK_STATIC_INFO,
    MARK_FROM_SEL,
    MARK_ARRAY
};

typedef struct {
    enum EntryType type;
    union {
        struct {
            StgClosure *p;            // the object to be marked
            StgClosure *origin;       // the object where this reference was found
            StgWord origin_field;     // index of the referencing field
            StgClosure *origin_value;
        } mark_closure;
        struct {
            StgClosure *p;
        } mark_static_info;
        struct {
            StgClosure *p;
            StgWord origin_field;    // index of the referencing field
            StgClosure *mark_indir;
        } mark_from_sel;
        struct {
            StgClosure *p;           // may be StgMutArrPtrs or StgSmallMutArrPtrs
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

static void mark_queue_push_array (MarkQueue *q,
                                   StgClosure *array,
                                   StgWord start_index)
{
    MarkQueueEnt ent = {
        .type = MARK_ARRAY,
        .mark_array = {
            .p = array,
            .start_index = start_index
        }
    };
    mark_queue_push(q, &ent);
}
static void mark_queue_push_closure (MarkQueue *q,
                                     StgClosure *p,
                                     StgClosure *origin_closure,
                                     unsigned int origin_field,
                                     StgClosure *origin_value)
{
    MarkQueueEnt ent = {
        .type = MARK_CLOSURE,
        .mark_closure = {
            .p = p,
            .origin = origin_closure,
            .origin_field = origin_field,
            .origin_value = origin_value
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

/* Given a pointer array (i.e. StgMutArrPtrs or StgSmallMutArrPtrs),
 * return a pointer to the payload and the array length (in pointers).
 */
static StgClosure **get_ptr_array_payload(const StgClosure *arr, StgWord len[1])
{
    switch (arr->header.info->type) {
    case MUT_ARR_PTRS_CLEAN:
    case MUT_ARR_PTRS_DIRTY:
    case MUT_ARR_PTRS_FROZEN:
    case MUT_ARR_PTRS_FROZEN0: {
        StgMutArrPtrs *arr2 = (StgMutArrPtrs *) arr;
        *len = arr2->ptrs;
        return arr2->payload;
    }

    case SMALL_MUT_ARR_PTRS_CLEAN:
    case SMALL_MUT_ARR_PTRS_DIRTY:
    case SMALL_MUT_ARR_PTRS_FROZEN:
    case SMALL_MUT_ARR_PTRS_FROZEN0: {
        StgSmallMutArrPtrs *arr2 = (StgSmallMutArrPtrs *) arr;
        *len = arr2->ptrs;
        return arr2->payload;
    }

    default:
        barf("nonmoving_mark: Unexpected non-array in MARK_ARRAY queue entry: 0x%x",
             arr->header.info->type);
    }
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
            // TODO
            break;
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

    // Trace pointers
    // TODO: Write everything below here
}

#define MIN(l,o) ((l) < (o) ? (l) : (o))

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
        case MARK_STATIC_INFO:
            // TODO
            break;
        case MARK_FROM_SEL:
            // TODO
            break;
        case MARK_ARRAY: {
            StgWord len;
            StgClosure** payload = get_ptr_array_payload(ent.mark_array.p, &len);
            const StgWord start = ent.mark_array.start_index;
            StgWord end = start + MARK_ARRAY_CHUNK_LENGTH;
            if (end < len) {
                mark_queue_push_array(queue, ent.mark_array.p, end);
            } else {
                end = len;
            }
            for (StgWord i = start; i < end; i++) {
                mark_queue_push_closure(queue, payload[i], NULL, 0, NULL);
            }
            break;
        }
        case NULL_ENTRY:
            return;
        }
    }
}
