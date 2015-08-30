/* ---------------------------------------------------------------------------
 *
 * (c) The GHC Team, 2014-2015
 *
 * A simple statistical profiler
 *
 * --------------------------------------------------------------------------*/

#include <Rts.h>
#include "Libdw.h"

int module_cb (Dwfl_Module *mod, void **userdata,
               const char *mainfile, Dwarf_Addr start, void *arg) {

  Elf *elf = dwfl_module_getelf(mod, NULL);
  Elf_Scn *section = elf_getscn(elf, 0);
  while (section != NULL) {

	  GElf_Shdr sect_hdr;
    if (gelf_getshdr(elf_getscn (ebl->elf, shdr->sh_info), &sect_hdr) == NULL) {
      Warn("StatProfile: Failed to get section header.");
      continue;
    }

    if (strcmp(".debug_ghc", sect_hdr->sh_name) != 0)
      continue;
    if (sect_hdr->sh_type != SHT_PROGBITS) {
      Warn("StatProfile: Found .debug_ghc section of wrong type")
      continue;
    }

	  Elf_Data *data = elf_getdata (scn, NULL);
	  if (data == NULL) {
      Warn("StatProfile: Failed to get data from .debug_ghc section");
	    continue;
    }

    postStatProfInitEvent(data->d_buf, data->d_size);
    section = elf_nextscn(elf, section);
  }
  return DWARF_CB_OK;
}

static int find_debug_ghc(StgPtr *buf, StgWord64 *len) {
  LibDwSession *sess = libdw_init();
  if (sess == NULL) {
    Warn("find_debug_ghc: Failed to initialize libdw session");
    return 1;
  }
  Dwfl *dwfl = sess->dwfl;
  dwfl_getmodules(dwfl, module_cb, NULL, 0);
  dwfl_end(sess);
  return 0;
}

void statprof_init(void) {
  // find .debug_ghc section
  StgPtr buf = NULL;
  StgWord64 len = 0;
  find_debug_ghc(&buf, len);
  if (buf == NULL) {
    Warn("Tried to initialize static profiler on executable without valid .debug_ghc information.");
    return;
  }
}

void statprof_sample(enum sample_reason reason) {
    Task *task = myTask();
    Capability *cap = task->cap;
    StgTSO *tso = task->cap->r.rCurrentTSO;
    postStatProfSampleEvent(cap->no, tso->id, reason);
}
