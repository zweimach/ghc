/* ---------------------------------------------------------------------------
 *
 * (c) The GHC Team, 2014-2015
 *
 * Producing DWARF-based stacktraces with libdw.
 *
 * --------------------------------------------------------------------------*/

#ifndef RTS_LIBDW_H
#define RTS_LIBDW_H

// Default chunk capacity
#define BACKTRACE_CHUNK_SZ 256

typedef struct BacktraceChunk_ {
    StgWord n_frames;                      // number of frames in this chunk
    struct BacktraceChunk_ *next;          // the chunk following this one
    StgPtr frames[BACKTRACE_CHUNK_SZ];     // the code addresses from the
                                           // frames
} __attribute__((packed)) BacktraceChunk;

typedef struct Backtrace_ {
    StgWord n_frames;             // Total number of frames in the backtrace
    BacktraceChunk frames;        // The first chunk of frames
} Backtrace;

// Various information describing the location of an address
typedef struct Location_ {
    const char *object_file;
    const char *function;

    // lineno and colno are only valid if source_file /= NULL
    const char *source_file;
    StgWord32 lineno;
    StgWord32 colno;
} __attribute__((packed)) Location;

#ifdef USE_LIBDW

void backtrace_free(Backtrace *bt);

/* -------------------------------------------------------------------------
 * Helpers for Haskell interface:
 * ------------------------------------------------------------------------*/

/*
 * Use the current capability's libdw context (initializing if necessary)
 * to collect a backtrace.
 */
Backtrace *libdw_cap_get_backtrace(void);

/*
 * Lookup the location of an address using the current capabiliy's libdw
 * context. Returns 0 if successful.
 */
int libdw_cap_lookup_location(StgPtr pc, Location *loc);

/*
 * Free the current capability's libdw context. This is necessary after
 * you have loaded or unloaded a dynamic module.
 */
void libdw_cap_free(void);

#else

INLINE_HEADER Backtrace *libdw_cap_get_backtrace(void) {
    return NULL;
}

INLINE_HEADER void libdw_cap_free(void) { }

INLINE_HEADER void backtrace_free(Backtrace *bt) { }

#endif /* USE_LIBDW */

#endif /* RTS_LIBDW_H */
