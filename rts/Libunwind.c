#include <string.h>
#include <libunwind.h>
#include <Libunwind.h>

// Default chunk capacity
#define BACKTRACE_CHUNK_CAP 256

// Allocate a Backtrace
static Backtrace *backtrace_alloc() {
    // We allocate not only the Backtrace object itself but also its first chunk
    int bytes = sizeof(Backtrace) + sizeof(uintptr_t) * BACKTRACE_CHUNK_CAP;
    Backtrace *bt = stgMallocBytes(bytes, "backtrace_alloc");
    bt->n_frames = 0;
    bt->frames.n_frames = 0;
    return bt;
}

static BacktraceChunk *backtrace_alloc_chunk() {
    int bytes = sizeof(BacktraceChunk) + sizeof(uintptr_t) * BACKTRACE_CHUNK_CAP;
    BacktraceChunk *chunk = stgMallocBytes(bytes, "backtrace_alloc_chunk");
    chunk->n_frames = 0;
    chunk->next = NULL;
    return chunk;
}

static int backtrace_push(Backtrace *bt, BacktraceFrame frame) {
    // Find tail chunk
    BacktraceChunk *chunk = &bt->frames;
    while (chunk->next != NULL)
        chunk = chunk->next;

    // Is this chunk full?
    if (chunk->n_frames == BACKTRACE_CHUNK_CAP) {
        chunk->next = backtrace_alloc_chunk();
        if (chunk->next == NULL) {
            sysErrorBelch("failed to allocate backtrace chunk");
            return -1;
        }
        chunk = chunk->next;
    }

    // Push the PC
    chunk->frames[chunk->n_frames] = frame;
    chunk->n_frames++;
    bt->n_frames++;
    return 0;
}

void print_backtrace(FILE *file, Backtrace *bt) {
    BacktraceChunk *chunk = &bt->frames;
    while (chunk != NULL) {
        int i;
        for (i=0; i<chunk->n_frames; i++) {
            BacktraceFrame *frame = &chunk->frames[i];
            fprintf(file, "  %24p    %s (%s:%d)\n",
                    (void*)frame->pc, frame->function,
                    frame->filename, frame->lineno);
        }
        chunk = chunk->next;
    }
}

void free_backtrace(Backtrace *bt) {
    BacktraceChunk *chunk = bt->frames.next;
    stgFree(bt);
    while (chunk != NULL) {
        BacktraceChunk *next = chunk->next;
        stgFree(chunk);
        chunk = next;
    }
}

struct LibunwindSession_ {
    int dummy;
};

LibunwindSession *libunwind_init() {
    LibunwindSession *session = stgCallocBytes(sizeof(LibunwindSession), "libbt_init");
    return session;
}

Backtrace *libunwind_get_backtrace(LibunwindSession *session) {
    Backtrace *bt = backtrace_alloc();
    unw_context_t ctxt;
    int ret = unw_getcontext(&ctxt);
    if (ret != 0) {
        sysErrorBelch("failed to get context");
        return NULL;
    }

    unw_cursor_t cursor;
    ret = unw_init_local(&cursor, &ctxt);
    if (ret == -1) {
        free_backtrace(bt);
        sysErrorBelch("Failed to get stack frames of current process");
        return NULL;
    }

    char name_buf[128];
    do {
        BacktraceFrame frame;
        unw_word_t off;
        ret = unw_get_proc_name(&cursor, name_buf, sizeof(name_buf), &off);
        switch (ret) {
        case 0:
        case UNW_ENOMEM:
            frame.function = strdup(name_buf);
            break;

        default:
            frame.function = NULL;
            sysErrorBelch("Error getting procedure name");
        }

        unw_proc_info_t pip;
        ret = unw_get_proc_info(&cursor, &pip);
        switch (ret) {
        case 0:
            frame.pc = off + pip.start_ip;
            break;
        default:
            frame.pc = 0;
            sysErrorBelch("Error getting procedure info");
        }

        backtrace_push(bt, frame);
        ret = unw_step(&cursor);
    } while (ret > 0);

    if (ret < 0) {
        free_backtrace(bt);
        sysErrorBelch("Error getting stack frame");
        return NULL;
    }
    return bt;
}
