/* ---------------------------------------------------------------------------
 *
 * (c) The GHC Team, 2014-2015
 *
 * Producing DWARF-based stacktraces with libdw.
 *
 * --------------------------------------------------------------------------*/

#ifdef USE_LIBDW

#include <elfutils/libdwfl.h>
#include <dwarf.h>
#include <unistd.h>

#include "Rts.h"
#include "Libdw.h"
#include "RtsUtils.h"

// Allocate a Backtrace
static Backtrace *backtrace_alloc(void) {
    Backtrace *bt = stgMallocBytes(sizeof(Backtrace), "backtrace_alloc");
    bt->n_frames = 0;
    bt->frames.n_frames = 0;
    bt->frames.next = 0;
    return bt;
}

static BacktraceChunk *backtrace_alloc_chunk(void) {
    BacktraceChunk *chunk = stgMallocBytes(sizeof(BacktraceChunk),
                                           "backtrace_alloc_chunk");
    chunk->n_frames = 0;
    chunk->next = NULL;
    return chunk;
}

static int backtrace_push(Backtrace *bt, StgPtr pc) {
    // Find tail chunk
    BacktraceChunk *chunk = &bt->frames;
    while (chunk->next != NULL)
        chunk = chunk->next;

    // Is this chunk full?
    if (chunk->n_frames == BACKTRACE_CHUNK_SZ) {
        chunk->next = backtrace_alloc_chunk();
        if (chunk->next == NULL) {
            sysErrorBelch("failed to allocate backtrace chunk");
            return -1;
        }
        chunk = chunk->next;
    }

    // Push the PC
    chunk->frames[chunk->n_frames] = pc;
    chunk->n_frames++;
    bt->n_frames++;
    return 0;
}

void backtrace_free(Backtrace *bt) {
    if (bt == NULL)
        return;
    BacktraceChunk *chunk = bt->frames.next;
    stgFree(bt);
    while (chunk != NULL) {
        BacktraceChunk *next = chunk->next;
        stgFree(chunk);
        chunk = next;
    }
}

struct LibDwSession_ {
    Dwfl *dwfl;
    Backtrace *cur_bt; // The current backtrace we are collecting (if any)
};

typedef struct LibDwSession_ LibDwSession;

static const Dwfl_Thread_Callbacks thread_cbs;

void libdw_free(LibDwSession *session) {
    dwfl_end(session->dwfl);
    stgFree(session);
}

// Load DWARF information for all present modules
LibDwSession *libdw_init() {
  LibDwSession *session = stgCallocBytes(1, sizeof(LibDwSession), "libdw_init");
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

  pid_t pid = getpid();
  if (! dwfl_attach_state(session->dwfl, NULL, pid, &thread_cbs, NULL)) {
      sysErrorBelch("Failed to attach");
      return NULL;
  }

  return session;
}

int libdw_lookup_location(LibDwSession *session, Location *frame,
                           StgPtr pc) {
    // Find the module containing PC
    Dwfl_Module *mod = dwfl_addrmodule(session->dwfl, (Dwarf_Addr) pc);
    if (mod == NULL)
        return 1;
    dwfl_module_info(mod, NULL, NULL, NULL, NULL, NULL,
                     &frame->object_file, NULL);

    // Find function name
    frame->function = dwfl_module_addrname(mod, (Dwarf_Addr) pc);

    // Try looking up source location
    Dwfl_Line *line = dwfl_module_getsrc(mod, (Dwarf_Addr) pc);
    if (line != NULL) {
        Dwarf_Addr addr;
        int lineno, colno;
        /* libdwfl owns the source_file buffer, don't free it */
        frame->source_file = dwfl_lineinfo(line, &addr, &lineno,
                                           &colno, NULL, NULL);
        frame->lineno = lineno;
        frame->colno = colno;
    }

    if (line == NULL || frame->source_file == NULL) {
        frame->source_file = NULL;
        frame->lineno = 0;
        frame->colno = 0;
    }
    return 0;
}

void libdw_print_backtrace(LibDwSession *session, FILE *file, Backtrace *bt) {
    if (bt == NULL) {
        fprintf(file, "Warning: tried to print failed backtrace\n");
        return;
    }

    StgPtr pc;
    FOREACH_FRAME(pc, bt) {
        Location loc;
        libdw_lookup_location(session, &loc, pc);
        fprintf(file, "  %24p    %s ",
                (void*) pc, loc.function);
        if (loc.source_file)
            fprintf(file, "(%s:%d.%d)\n",
                    loc.source_file, loc.lineno, loc.colno);
        else
            fprintf(file, "(%s)\n", loc.object_file);
    }
}

static int frame_cb(Dwfl_Frame *frame, void *arg) {
    LibDwSession *session = arg;
    Dwarf_Addr pc;
    bool is_activation;
    if (! dwfl_frame_pc(frame, &pc, &is_activation)) {
        // failed to find PC
        backtrace_push(session->cur_bt, 0x0);
    } else {
        if (is_activation)
            pc -= 1; // TODO: is this right?
        backtrace_push(session->cur_bt, (StgPtr) pc);
    }

    if ((void *) pc == &stg_stop_thread_info)
        return DWARF_CB_ABORT;
    else
        return DWARF_CB_OK;
}

Backtrace *libdw_get_backtrace(LibDwSession *session) {
    if (session->cur_bt != NULL) {
        sysErrorBelch("Already collecting backtrace. Uh oh.");
        return NULL;
    }

    Backtrace *bt = backtrace_alloc();
    session->cur_bt = bt;

    int pid = getpid();
    int ret = dwfl_getthread_frames(session->dwfl, pid, frame_cb, session);
    if (ret == -1)
        sysErrorBelch("Failed to get stack frames of current process: %s",
                      dwfl_errmsg(dwfl_errno()));

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

static bool memory_read(Dwfl *dwfl STG_UNUSED, Dwarf_Addr addr,
                        Dwarf_Word *result, void *arg STG_UNUSED) {
    *result = *(Dwarf_Word *) addr;
    return true;
}

static bool set_initial_registers(Dwfl_Thread *thread, void *arg);

static bool set_initial_registers(Dwfl_Thread *thread,
                                  void *arg STG_UNUSED) {
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
             "movq %%rax, 0x80(%0)\n\t"
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

Backtrace *get_stg_backtrace(StgTSO *tso) {
    StgPtr sp = tso->stackobj->sp;
    Backtrace *bt = backtrace_alloc();

    while (1) {
        StgRetInfoTable *info = get_ret_itbl((StgClosure *)sp);
        StgPtr next = sp + stack_frame_sizeW((StgClosure *)sp);

        switch (info->i.type) {
        case STOP_FRAME:
            return bt;
        default:
            backtrace_push(bt, (StgPtr) info->i.code);
            break;
        }

        sp = next;
    }
    return bt;
}

#endif /* USE_LIBDW */
