/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team, 1998-2018
 *
 * Non-moving garbage collector and allocator: Sweep phase
 *
 * ---------------------------------------------------------------------------*/

#pragma once

#include "NonMoving.h"

GNUC_ATTR_HOT void nonmoving_sweep(void);
