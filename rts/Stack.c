/* ---------------------------------------------------------------------------
 *
 * (c) The GHC Team, 2015-2015
 *
 * Stack-related functionality
 *
 * --------------------------------------------------------------------------*/

#include "Rts.h"
#include "Stack.h"
#include "sm/Storage.h"

#include <string.h>
#include <stdlib.h>
#include <stdarg.h>

// It is quite cumbersome to traverse the stack manually, as it's in
// fact chunked. This macro abstracts away from that.
#define TRAVERSE_STACK(sp_var, ret_info_var)                                 \
            for (;                                                           \
                 (ret_info_var = get_ret_itbl((StgClosure *)sp_var)) &&      \
                 ret_info_var->i.type != STOP_FRAME                          \
                 ;                                                           \
                 (ret_info_var->i.type == UNDERFLOW_FRAME)                   \
                   ? (sp_var = ((StgUnderflowFrame*)sp_var)->next_chunk->sp) \
                   : (sp_var += stack_frame_sizeW((StgClosure *)sp_var))     \
                )                                                            \

/* -----------------------------------------------------------------------------
   countLimitedStackSize

   Count number of frames on the whole stack.

   @param sp    Pointer to the stack, typically `my_tso->stackobj->sp`
   @param limit Stop search after limit frames and return limit
   -------------------------------------------------------------------------- */
StgWord
countLimitedStackSize (StgPtr sp, const nat limit)
{
    const StgRetInfoTable* ret_info;
    StgWord framecount;
    framecount = 0;
    TRAVERSE_STACK(sp, ret_info) {
        if(framecount >= limit) {
            return framecount;
        }
        framecount++;
    }
    return framecount;
}

/* -----------------------------------------------------------------------------
   getExecutableCode

   Given a closure object, return a pointer to the executable code of
   its info table. In the case of it being some sort of an update frame,
   then try to return the code of the updatee rather than the code of
   the update frame.
   -------------------------------------------------------------------------- */
StgFunPtr getExecutableCode (StgClosure *p);
StgFunPtr
getExecutableCode (StgClosure *p) {
    if (p->header.info == &stg_upd_frame_info) {
        // In this case, it's more intersting to point to the function that
        // the update frame is going to execute
        p = ((StgUpdateFrame*)p)->updatee;
    }
    return GET_ENTRY(p);
}

/* -----------------------------------------------------------------------------
   reifyStack

   Reify a stack.  This function travereses the stack and copies over just the
   info pointers (not the payloads).

   @param cap   Capability into which we allocate memory.
   @param sp    Pointer to the stack, typically `my_tso->stackobj->sp`.
   @param limit Don't reify more than the first limit frames.
   -------------------------------------------------------------------------- */
StgArrWords *
reifyStack (Capability *cap, StgPtr sp, nat limit)
{
    const StgRetInfoTable* ret_info;
    StgWord framecount;
    StgArrWords* reified;
    StgFunPtr *reified_payload;

    framecount = countLimitedStackSize(sp, limit);
    reified = allocArrWords(cap, framecount * sizeof(char *));
    reified_payload = (StgFunPtr*)reified->payload;

    StgPtr p = sp;
    StgWord count = 0;
    TRAVERSE_STACK (p, ret_info) {
        if (count >= framecount) {
            break;
        }
        count++;
        *(reified_payload++) = getExecutableCode((StgClosure*)p);
    }
    return reified;
}
