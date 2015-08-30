/* ---------------------------------------------------------------------------
 *
 * (c) The GHC Team, 2014-2015
 *
 * A simple statistical profiler
 *
 * --------------------------------------------------------------------------*/

#include <elfutils/libdwfl.h>
#include <string.h>
#include <unistd.h>

#include <Rts.h>
#include "Task.h"
#include "Trace.h"
#include "eventlog/EventLog.h"
#include "StatProfile.h"

#ifdef STAT_PROFILE

/*
 * Find the .debug_ghc sections in the loaded modules and post them to the event
 * log
 */
static int module_cb (Dwfl_Module *mod, void **userdata STG_UNUSED,
                      const char *mainfile STG_UNUSED,
                      Dwarf_Addr start STG_UNUSED,
                      void *arg STG_UNUSED)
{
  GElf_Addr bias;
  Elf *elf = dwfl_module_getelf(mod, &bias);
  Elf_Scn *section = elf_getscn(elf, 0);
  size_t strtab_sect;
  if (elf_getshdrstrndx (elf, &strtab_sect) < 0) {
      errorBelch("cannot get section header string table index");
      return DWARF_CB_ABORT;
  }

  while (section != NULL) {
	  GElf_Shdr sect_hdr;
    if (gelf_getshdr(section, &sect_hdr) == NULL) {
      errorBelch("StatProfile: Failed to get section header.");
      goto next_section;
    }

    const char *sect_name = elf_strptr(elf, strtab_sect, sect_hdr.sh_name);
    if (strcmp(".debug_ghc", sect_name) != 0)
      goto next_section;

    // sanity check
    if (sect_hdr.sh_type != SHT_PROGBITS) {
      errorBelch("StatProfile: Found .debug_ghc section of wrong type");
      goto next_section;
    }

	  Elf_Data *data = elf_getdata(section, NULL);
	  if (data == NULL) {
      errorBelch("StatProfile: Failed to get data from .debug_ghc section");
      goto next_section;
    }

    traceGhcDebug(mainfile, data->d_buf, data->d_size);
  next_section:
    section = elf_nextscn(elf, section);
  }
  return DWARF_CB_OK;
}

static int find_debug_ghc(void) {
  // Initialize a libdwfl session
  static char *debuginfo_path;
  static const Dwfl_Callbacks proc_callbacks =
      {
          .find_debuginfo = dwfl_standard_find_debuginfo,
          .debuginfo_path = &debuginfo_path,
          .find_elf = dwfl_linux_proc_find_elf,
      };
  Dwfl *dwfl = dwfl_begin (&proc_callbacks);
  if (dwfl == NULL) {
      errorBelch("dwfl_begin failed: %s", dwfl_errmsg(-1));
      return 1;
  }

  // Report the loaded modules
  int ret = dwfl_linux_proc_report(dwfl, getpid());
  if (ret < 0) {
      errorBelch("dwfl_linux_proc_report failed: %s", dwfl_errmsg(-1));
      return 1;
  }
  if (dwfl_report_end (dwfl, NULL, NULL) != 0) {
      errorBelch("dwfl_report_end failed: %s", dwfl_errmsg(-1));
      return 1;
  }

  dwfl_getmodules(dwfl, module_cb, NULL, 0);
  dwfl_end(dwfl);
  return 0;
}

void statprof_init(void) {
  // find and post .debug_ghc sections
  if (find_debug_ghc()) {
    errorBelch("Tried to initialize static profiler on executable without valid .debug_ghc information.");
    return;
  }
}

#endif
