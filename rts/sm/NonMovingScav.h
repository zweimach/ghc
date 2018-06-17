#pragma once

#include "BeginPrivate.h"

#include "NonMoving.h"

void nonmoving_scavenge_one(StgClosure *p);
void scavenge_nonmoving_segment(struct nonmoving_segment *seg);

#include "EndPrivate.h"
