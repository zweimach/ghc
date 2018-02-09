/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team, 1998-2018
 *
 * Non-moving garbage collector and allocator: Mark phase
 *
 * ---------------------------------------------------------------------------*/

#pragma once

#include "BeginPrivate.h"

struct MarkQueue_;

void init_mark_queue(struct MarkQueue_ *queue);
void nonmoving_prepare_mark(void);
void nonmoving_mark(struct MarkQueue_ *restrict queue);

#include "EndPrivate.h"
