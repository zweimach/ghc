/* ---------------------------------------------------------------------------
 *
 * (c) The GHC Team, 2014-2015
 *
 * Producing DWARF-based stacktraces with libdw.
 *
 * --------------------------------------------------------------------------*/

#ifndef PRIVATE_LIBDW_H
#define PRIVATE_LIBDW_H

#include "Rts.h"

// Default chunk capacity
#define BACKTRACE_CHUNK_SZ 256

struct BacktraceChunk_ {
    StgWord n_frames;                          // number of frames in this chunk
    struct BacktraceChunk_ *next;              // the chunk following this one
    StgPtr frames[BACKTRACE_CHUNK_SZ]; // the actual stack frames
} __attribute__((packed));

typedef struct BacktraceChunk_ BacktraceChunk;

struct Backtrace_ {
    StgWord n_frames;             // Total number of frames in the backtrace
    BacktraceChunk frames;        // The first chunk of frames
};

typedef struct Backtrace_ Backtrace;

void backtrace_free(Backtrace *bt);

// Various information describing the location of an address
struct Location_ {
    const char *object_file;
    const char *function;

    // lineno and colno are only valid if source_file /= NULL
    const char *source_file;
    StgWord32 lineno;
    StgWord32 colno;
} __attribute__((packed));

typedef struct Location_ Location;

struct LibDwSession_;
typedef struct LibDwSession_ LibDwSession;

/* Begin a libdw session. A session is tied to a particular capability */
LibDwSession *libdw_init(void);
/* Free a session */
void libdw_free(LibDwSession *session);
/* Request a backtrace of the current stack state */
Backtrace *libdw_get_backtrace(LibDwSession *session);
/* Lookup Location information for the given address.
 * Returns 0 if successful, 1 if address could not be found. */
int libdw_lookup_location(LibDwSession *session, Location *loc, StgPtr pc);
/* Pretty-print a backtrace to std*/
void libdw_print_backtrace(LibDwSession *session, FILE *file, Backtrace *bt);

Backtrace *get_stg_backtrace(StgTSO *tso);

#define FOREACH_FRAME(pc, bt)                                         \
    BacktraceChunk *_chunk;                                           \
    unsigned int _frame_idx;                                          \
    for (_chunk = &bt->frames; _chunk != NULL; _chunk = _chunk->next) \
        for (_frame_idx=0;                                            \
             pc = _chunk->frames[_frame_idx], _frame_idx < _chunk->n_frames; \
             _frame_idx++)

/* -------------------------------------------------------------------------
 * Helpers for Haskell interface:
 * ------------------------------------------------------------------------*/

struct LocationBacktrace_ {
    StgWord n_frames;
    Location frames[];
} __attribute__((packed));

typedef struct LocationBacktrace_ LocationBacktrace;

#ifdef USE_LIBDW

// Use the current capability's libdw context (initializing if necessary)
// to collect a backtrace.
LocationBacktrace *libdw_cap_get_backtrace(void);

// Free the current capability's libdw context. This is necessary after
// you have loaded or unloaded a dynamic module.
void libdw_cap_free(void);

#else

INLINE_HEADER LocationBacktrace *libdw_cap_get_backtrace(void) {
    return NULL;
}

INLINE_HEADER void libdw_cap_free(void) { }

#endif

#endif
