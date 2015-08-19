#include <backtrace.h>
#include <Libbacktrace.h>

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

struct LibBtSession_ {
    struct backtrace_state *state;
    Backtrace *cur_bt;
};

static void session_error_cb(void *data, const char *msg, int errnum) {
    sysErrorBelch("Error collecting backtrace: %s", msg);
}

LibBtSession *libbt_init() {
    LibBtSession *session = stgCallocBytes(sizeof(LibBtSession), "libbt_init");
    session->state = backtrace_create_state(NULL, 1, session_error_cb, NULL);
    return session;
}

static void frame_error_cb(void *data, const char *msg, int errnum) {
    sysErrorBelch("Error collecting backtrace frame: %s", msg);
}

static int frame_cb(void *data, uintptr_t pc,
                    const char *filename, int lineno,
                    const char *function) {
    LibBtSession *session = data;
    BacktraceFrame frame;
    frame.filename = filename;
    frame.lineno = lineno;
    frame.function = function;
    frame.pc = pc;
    backtrace_push(session->cur_bt, frame);
    return 0;
}

Backtrace *libbt_get_backtrace(LibBtSession *session) {
    if (session->cur_bt != NULL) {
        sysErrorBelch("Already collecting backtrace. Uh oh.");
        return NULL;
    }

    Backtrace *bt = backtrace_alloc();
    session->cur_bt = bt;
    int ret = backtrace_full(session->state, 1, frame_cb, frame_error_cb, session);
    if (ret == -1) {
        free_backtrace(bt);
        session->cur_bt = NULL;
        sysErrorBelch("Failed to get stack frames of current process");
        return NULL;
    }

    session->cur_bt = NULL;
    return bt;
}
