#pragma once

#include "NonMoving.h"

#include "BeginPrivate.h"

void nonmoving_scavenge_one(StgClosure *p);
void scavenge_nonmoving_segment(struct nonmoving_segment *seg);
void scavenge_upd_rem_set(void);

#include "EndPrivate.h"
