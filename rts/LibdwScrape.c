/* ---------------------------------------------------------------------------
 *
 * (c) The GHC Team, 2014-2015
 *
 * Scape DWARF and .debug_ghc information out of loaded modules and place in
 * event log
 *
 * --------------------------------------------------------------------------*/

#include <elfutils/libdwfl.h>

#include "Rts.h"
#include "Trace.h"

#if 0
static int subprogram_cb(Dwarf_Die *die, void *cbdata)
{
    Dwarf_Addr basep, startp, endp;
    ptrdiff_t offset = 0;
    traceProc(dwarf_diename(die));
    while (true) {
        dwarf_getfuncs(cu_die)
            int offset = dwarf_ranges(die, offset, &basep, &startp, &endp);
        if (offset <= 0)
            break;
        traceProcRange(startp, endp);
    }
    return DWARF_CB_OK;
}

/* We have two sources of debug information which we want to collect
 * and emit to the event log,
 *
 *   1. event log records from .debug_ghc
 *   2. DWARF DIE information
 *
 * To do this reasonably efficiently we first iterate over all of the
 * modules, building up an index of their DWARF subprogram DIEs. We
 * then iterate over the .debug_ghc records, emitting them to the event log
 * along with any associated DIE information.
 */

static void index_dwarf_procs_cb(Dwarf_Die *die, void *cbdata)
{
    HashTable *table = (HashTable *) cbdata;
    insertStrHashTable(table, dwarf_diename(die), die);
    return DWARF_CB_OK;
}

// Build a hash table mapping procedure names to corresponding Dwarf_Dies
// for all subprograms in the given module.
static HashTable *index_dwarf_procs(Dwarf_Module *mod)
{
    HashTable *table = allocStrHashTable();
    Dwarf_Die *cu_die = NULL;
    while (true) {
        cu_die = dwfl_module_nextcu(mod, cu_die, &bias);
        if (cu_die == NULL)
            break;
        int res = dwarf_getfuncs(cu_die, subprogram_cb, table, 0);
    }
    return table;
}

/* Find the Elf_Data of the .debug_ghc section of the given module */
static Elf_Data find_debug_ghc(Dwfl_Module *mod) {
    GElf_Addr bias;
    Elf *elf = dwfl_module_getelf(mod, &bias);

    Elf_Scn *section = elf_getscn(elf, 0);
    size_t strtab_sect;
    if (elf_getshdrstrndx (elf, &strtab_sect) < 0) {
        errorBelch("find_debug_ghc: cannot get section header string table index");
        return DWARF_CB_ABORT;
    }

    while (section != NULL) {
        GElf_Shdr sect_hdr;
        if (gelf_getshdr(section, &sect_hdr) == NULL) {
            errorBelch("find_debug_ghc: Failed to get section header.");
            goto next_section;
        }

        const char *sect_name = elf_strptr(elf, strtab_sect, sect_hdr.sh_name);
        if (strcmp(".debug_ghc", sect_name) != 0)
            goto next_section;

        // sanity check
        if (sect_hdr.sh_type != SHT_PROGBITS) {
            errorBelch("find_debug_ghc: Found .debug_ghc section of wrong type");
            goto next_section;
        }

        Elf_Data *data = elf_getdata(section, NULL);
        if (data == NULL) {
            errorBelch("find_debug_ghc: Failed to get data from .debug_ghc section");
            goto next_section;
        }

        return data;
    next_section:
        section = elf_nextscn(elf, section);
    }
    return NULL;
}

static int module_cb(Dwfl_Module *mod, void **user_data, const char *name,
                     Dwarf_Addr start, void *cbdata)
{
    HashTable table = index_dwarf_procs(mod);

    Dwarf_Addr bias;
    Elf_Data *debug_ghc = find_debug_ghc(mod);
    StgWord8 *dbg = debug_ghc->d_buf;
    size_t remaining = debug_ghc->d_size;

    while (remaining > 0) {
        EventTypeNum num = (EventTypeNum) (*(StgWord8 *) dbg);
        dbg++;
        StgWord32 size = ntohl(*(StgWord32 *)dbg);
        dbg += sizeof(StgWord32);

        // Sanity check
        switch (num) {
        case EVENT_DEBUG_MODULE:
        case EVENT_DEBUG_BLOCK:
        case EVENT_DEBUG_SOURCE:
        case EVENT_DEBUG_CORE:
            break;
        default:
            continue;
        }

        Dwarf_Die *proc_die = removeHashTable(table, )

        traceModule(dwarf_diename(cu_die));
    }
    freeHashTable(table, NULL);
    return DWARF_CB_OK;
}

int libdw_scrape()
{
    Dwfl *dwfl = dwfl_begin (&proc_callbacks);
    if (session->dwfl == NULL) {
        sysErrorBelch("dwfl_begin failed: %s", dwfl_errmsg(dwfl_errno()));
        return 1;
    }

    // Report the loaded modules
    int ret = dwfl_linux_proc_report(session->dwfl, getpid());
    if (ret < 0) {
        sysErrorBelch("dwfl_linux_proc_report failed: %s",
                      dwfl_errmsg(dwfl_errno()));
        return 1;
    }
    if (dwfl_report_end (session->dwfl, NULL, NULL) != 0) {
        sysErrorBelch("dwfl_report_end failed: %s", dwfl_errmsg(dwfl_errno()));
        return 1;
    }

    if (dwfl_getmodules(dwfl, module_cb, 0) != 0) {
        sysErrorBelch("dwfl_getmodules failed: %s", dwfl_errmsg(dwfl_errno()));
    }

    dwfl_end(dwfl);
    return 0;
}
#endif

int libdw_scrape() { return 0; }
