#include <stdio.h>

struct BacktraceFrame_ {
    const char *filename;
    StgWord lineno;
    uintptr_t pc;
    const char *function;
};

typedef struct BacktraceFrame_ BacktraceFrame;

struct BacktraceChunk_ {
    StgWord n_frames;             // number of frames in this chunk
    struct BacktraceChunk_ *next; // the chunk following this one
    BacktraceFrame frames[];      // the actual stack frames
};

typedef struct BacktraceChunk_ BacktraceChunk;

struct Backtrace_ {
    StgWord n_frames;             // Total number of frames in the backtrace
    BacktraceChunk frames;        // The first chunk of frames
};

typedef struct Backtrace_ Backtrace;

void free_backtrace(Backtrace *bt);

void print_backtrace(FILE *file, Backtrace *bt);

struct LibunwindSession_;
typedef struct LibunwindSession_ LibunwindSession;

LibunwindSession *libunwind_init(void);

Backtrace *libunwind_get_backtrace(LibunwindSession *session);
