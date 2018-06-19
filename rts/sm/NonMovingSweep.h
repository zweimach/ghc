/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team, 1998-2018
 *
 * Non-moving garbage collector and allocator: Sweep phase
 *
 * ---------------------------------------------------------------------------*/

#pragma once

#include "NonMoving.h"
#include "Hash.h"

GNUC_ATTR_HOT void nonmoving_sweep(void);

// Remove unmarked entries in oldest generation mut_lists
void nonmoving_sweep_mut_lists(HashTable *marked_objects);

// Remove unmarked entries in oldest generation scavenged_large_objects list
void nonmoving_sweep_large_objects(HashTable *marked_objects);

// Remove dead entries in the stable name table
void nonmoving_sweep_stable_name_table(HashTable *marked_objects);
