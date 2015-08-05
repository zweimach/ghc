/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team 2014-2014
 *
 * Prototypes for functions in Stack.c
 * (Functions operating on the STG stack)
 *
 * -------------------------------------------------------------------------*/

#ifndef STACK_H
#define STACK_H

#include "Capability.h"

#include "BeginPrivate.h"

StgWord countLimitedStackSize (StgPtr sp, nat limit);

StgArrWords *reifyStack (Capability* cap, StgPtr sp, nat limit);

#include "EndPrivate.h"

#endif /* STACK_H */
