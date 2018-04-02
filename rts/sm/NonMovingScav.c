#include "Rts.h"
#include "RtsUtils.h"
#include "NonMoving.h"
#include "NonMovingScav.h"
#include "Capability.h"
#include "Scav.h"
#include "GCThread.h" // for GCUtils.h
#include "GCUtils.h"

static void
scavenge_nonmoving_segment(struct nonmoving_segment *seg)
{
    // scavenge objects whose bitmap bits are 0

#ifdef DEBUG
    debugBelch("Scavenging segment:\n");
    nonmoving_print_segment(seg);
#endif

    nonmoving_block_idx p_idx = 0;
    // in this context block = closure
    StgClosure *p = (StgClosure*)nonmoving_segment_get_block(seg, 0);

    while (p_idx < seg->next_free) {
        ASSERT(LOOKS_LIKE_CLOSURE_PTR(p));
        // bit set = was allocated in the previous GC
        // bit not set = new allocation, so scavenge
        if (!(nonmoving_get_mark_bit(seg, p_idx))) {
            if (scavenge_one((StgPtr)p)) {
                recordMutableGen_GC((StgClosure*)p, oldest_gen->no);
            }
        }

        p_idx++;
        p = (StgClosure*)(((uint8_t*)p) + nonmoving_segment_block_size(seg));
    }
}

void scavenge_nonmoving_heap(void)
{
    while (nonmoving_todos) {
        struct nonmoving_segment* todo = nonmoving_todos;
        nonmoving_todos = todo->todo_link;
        scavenge_nonmoving_segment(todo);
    }
}
