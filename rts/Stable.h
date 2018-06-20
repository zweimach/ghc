/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team, 1998-2004
 *
 * Stable Pointers: A stable pointer is represented as an index into
 * the stable pointer table.
 *
 * StgStablePtr used to be a synonym for StgWord, but stable pointers
 * are guaranteed to be void* on the C-side, so we have to do some
 * occasional casting. Size is not a matter, because StgWord is always
 * the same size as a void*.
 *
 * ---------------------------------------------------------------------------*/

#pragma once

#include "sm/GC.h" // for evac_fn below

#include "BeginPrivate.h"

extern unsigned int SNT_size;

#define FOR_EACH_STABLE_NAME(p, CODE)                                   \
    do {                                                                \
        snEntry *p;                                                     \
        snEntry *__end_ptr = &stable_name_table[SNT_size];              \
        for (p = stable_name_table + 1; p < __end_ptr; p++) {           \
            /* Internal pointers are free slots.  */                    \
            /* If p->addr == NULL, it's a */                            \
            /* stable name where the object has been GC'd, but the */   \
            /* StableName object (sn_obj) is still alive. */            \
            if ((p->addr < (P_)stable_name_table ||                     \
                 p->addr >= (P_)__end_ptr))                             \
            {                                                           \
                /* NOTE: There is an ambiguity here if p->addr == NULL */ \
                /* it is either the last item in the free list or it */ \
                /* is a stable name whose pointee died. sn_obj == NULL */ \
                /* disambiguates as last free list item. */             \
                do { CODE } while(0);                                   \
            }                                                           \
        }                                                               \
    } while(0)

void    freeStablePtr         ( StgStablePtr sp );

/* Use the "Unsafe" one after manually locking with stableLock/stableUnlock */
void    freeStablePtrUnsafe   ( StgStablePtr sp );

void    freeSnEntry           ( snEntry *sn );

void    initStableTables      ( void );
void    exitStableTables      ( void );
StgWord lookupStableName      ( StgPtr p );

/* Call given function on every stable ptr. markStableTables depends
 * on the function updating its pointers in case the object is
 * moved. */
/* TODO: This also remembers old stable name addresses, which isn't
 * necessary in some contexts markStableTables is called from.
 * Consider splitting it.
 */
void    markStableTables      ( evac_fn evac, void *user );
void    markStablePtrTable    ( evac_fn evac, void *user );

void    threadStableTables    ( evac_fn evac, void *user );
void    gcStableTables        ( void );
void    updateStableTables    ( bool full );

void    stableLock            ( void );
void    stableUnlock          ( void );

#if defined(THREADED_RTS)
// needed by Schedule.c:forkProcess()
extern Mutex stable_mutex;
#endif

#include "EndPrivate.h"
