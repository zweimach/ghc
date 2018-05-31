#pragma once

#include "BeginPrivate.h"

void nonmoving_scavenge_one(StgClosure *p);
void scavenge_nonmoving_heap(void);

#include "EndPrivate.h"
