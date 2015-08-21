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

#else

INLINE_HEADER void backtrace_free(Backtrace *bt) { }

#endif /* USE_LIBDW */

#endif /* RTS_LIBDW_H */
