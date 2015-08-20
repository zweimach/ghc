#include <elfutils/libdwfl.h>
#include <unistd.h>
#include "Libdw.h"

// Default chunk capacity
#define BACKTRACE_CHUNK_CAP 256

// Allocate a Backtrace
static Backtrace *backtrace_alloc(void) {
    // We allocate not only the Backtrace object itself but also its first chunk
    int bytes = sizeof(Backtrace) + sizeof(uintptr_t) * BACKTRACE_CHUNK_CAP;
    Backtrace *bt = stgMallocBytes(bytes, "backtrace_alloc");
    bt->n_frames = 0;
    bt->frames.n_frames = 0;
    return bt;
}

static BacktraceChunk *backtrace_alloc_chunk(void) {
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

void backtrace_free(Backtrace *bt) {
    BacktraceChunk *chunk = bt->frames.next;
    stgFree(bt);
    while (chunk != NULL) {
        BacktraceChunk *next = chunk->next;
        stgFree(chunk);
        chunk = next;
    }
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

struct LibDwSession_ {
    Dwfl *dwfl;
    Backtrace *cur_bt; // The current backtrace we are collecting (if any)
};

typedef struct LibDwSession_ LibDwSession;

static const Dwfl_Thread_Callbacks thread_cbs;

void libdw_free(LibDwSession *session) {
  // TODO
    dwfl_end(session->dwfl);
}

// Load DWARF information for all present modules
LibDwSession *libdw_init() {
  LibDwSession *session = stgCallocBytes(sizeof(LibDwSession), "libdw_init");
	// Initialize ELF library
	if (elf_version(EV_CURRENT) == EV_NONE) {
      sysErrorBelch("libelf version too old!");
      return NULL;
	}

  // Initialize a libdwfl session
  static char *debuginfo_path;
  static const Dwfl_Callbacks proc_callbacks =
      {
          .find_debuginfo = dwfl_standard_find_debuginfo,
          .debuginfo_path = &debuginfo_path,
          .find_elf = dwfl_linux_proc_find_elf,
      };
  session->dwfl = dwfl_begin (&proc_callbacks);
  if (session->dwfl == NULL) {
      sysErrorBelch("dwfl_begin failed: %s", dwfl_errmsg(-1));
      return NULL;
  }

  // Report the loaded modules
  int ret = dwfl_linux_proc_report(session->dwfl, getpid());
  if (ret < 0) {
      sysErrorBelch("dwfl_linux_proc_report failed: %s", dwfl_errmsg(-1));
      return NULL;
  }
  if (dwfl_report_end (session->dwfl, NULL, NULL) != 0) {
      sysErrorBelch("dwfl_report_end failed: %s", dwfl_errmsg(-1));
      return NULL;
  }

  return session;
}

static void libdw_lookup_addr(LibDwSession *session, BacktraceFrame *frame,
                              uintptr_t pc) {
    frame->pc = pc;

    // Find the module and function name
    Dwfl_Module *mod = dwfl_addrmodule(session->dwfl, pc);
    frame->function = dwfl_module_addrname(mod, pc);

    // Try looking up source location
    Dwfl_Line *line = dwfl_getsrc(session->dwfl, pc);
    Dwarf_Addr addr;
    frame->filename = dwfl_lineinfo(line, &addr, &frame->lineno,
                                    NULL, NULL, NULL);
}

static int frame_cb(Dwfl_Frame *frame, void *arg) {
    LibDwSession *session = arg;
    Dwarf_Addr pc;
    bool is_activation;
    if (! dwfl_frame_pc(frame, &pc, &is_activation)) {
        // failed to find PC
        BacktraceFrame frame = {};
        backtrace_push(session->cur_bt, frame);
    } else {
        if (is_activation)
            pc -= 1; // TODO: is this right?

        BacktraceFrame frame;
        libdw_lookup_addr(session, &frame, pc);
        backtrace_push(session->cur_bt, frame);
    }
    return DWARF_CB_OK;
}

Backtrace *libdw_get_backtrace(LibDwSession *session) {
    pid_t pid = getpid();
    if (session->cur_bt != NULL) {
        sysErrorBelch("Already collecting backtrace. Uh oh.");
        return NULL;
    }

    Backtrace *bt = backtrace_alloc();
    session->cur_bt = bt;

    if (! dwfl_attach_state(session->dwfl, NULL, pid, &thread_cbs, NULL)) {
        sysErrorBelch("Failed to attach");
        return NULL;
    }

    int ret = dwfl_getthread_frames(session->dwfl, pid, frame_cb, session);
    if (ret == -1) {
        backtrace_free(bt);
        session->cur_bt = NULL;
        sysErrorBelch("Failed to get stack frames of current process: %s",
                      dwfl_errmsg(dwfl_errno()));
        return NULL;
    }

    session->cur_bt = NULL;
    return bt;
}

static pid_t next_thread(Dwfl *dwfl, void *arg, void **thread_argp) {
    /* there is only the current thread */
    if (*thread_argp != NULL)
        return 0;

    *thread_argp = arg;
    return dwfl_pid(dwfl);
}

static bool memory_read(Dwfl *dwfl, Dwarf_Addr addr, Dwarf_Word *result,
                     void *dwfl_arg) {
    *result = *(Dwarf_Word *) addr;
    return true;
}

static bool set_initial_registers(Dwfl_Thread *thread, void *arg);

static bool set_initial_registers(Dwfl_Thread *thread, void *arg) {
    Dwarf_Word regs[17];
    __asm__ ("movq %%rax, 0x00(%0)\n\t"
             "movq %%rdx, 0x08(%0)\n\t"
             "movq %%rcx, 0x10(%0)\n\t"
             "movq %%rbx, 0x18(%0)\n\t"
             "movq %%rsi, 0x20(%0)\n\t"
             "movq %%rdi, 0x28(%0)\n\t"
             "movq %%rbp, 0x30(%0)\n\t"
             "movq %%rsp, 0x38(%0)\n\t"
             "movq %%r8,  0x40(%0)\n\t"
             "movq %%r9,  0x48(%0)\n\t"
             "movq %%r10, 0x50(%0)\n\t"
             "movq %%r11, 0x58(%0)\n\t"
             "movq %%r12, 0x60(%0)\n\t"
             "movq %%r13, 0x68(%0)\n\t"
             "movq %%r14, 0x70(%0)\n\t"
             "movq %%r15, 0x78(%0)\n\t"
             "lea 0(%%rip), %%rax\n\t"
             "movq %%rax, 0x80(%0)\n\t" // TODO RIP
             :                            /* no output */
             :"r" (&regs[0])              /* input */
             :"%rax"                      /* clobbered */
        );
    return dwfl_thread_state_registers(thread, 0, 17, regs);
}

static const Dwfl_Thread_Callbacks thread_cbs = {
    .next_thread = next_thread,
    .memory_read = memory_read,
    .set_initial_registers = set_initial_registers,
};
