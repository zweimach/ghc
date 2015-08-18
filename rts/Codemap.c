/* ---------------------------------------------------------------------------
 *
 * (c) The GHC Team, 2015-2015
 *
 * Codemap, map from instruction pointers to function names
 *
 * --------------------------------------------------------------------------*/

#ifdef USE_ELF

#include "Rts.h"
#include "RtsUtils.h"

#include "Hash.h"
#include "Trace.h"
#include "Codemap.h"

#include "gelf.h"

#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <stdio.h>
#include <fcntl.h>
#include <string.h>

// Global compilation unit list
CodemapUnit *codemap_units;
/* if codemap_ref > 0, then codemap data is loaded (not iff). */
int codemap_ref;

#ifdef THREADED_RTS
// Lock (when multiple threads write to the globals using codemap_load())
Mutex codemap_mutex;
#endif

// Internal helpers
static void codemap_load_symbols(char *module_path, Elf *elf);

static void codemap_load_file(char *module_path);
static void codemap_init_lookup(void);
static void codemap_load(void);
static void codemap_unload(void);
static int compare_low_pc(const void *a, const void *b);

// These functions must only be called after the codemap data is loaded. See
// Codemap header file includes/rts/Codemap.h.
static CodemapUnit *codemap_get_unit(char *name);
static CodemapProc *codemap_lookup_proc(void *ip, CodemapUnit **punit);

static CodemapUnit *codemap_new_unit(char *name);
static CodemapProc *codemap_new_proc(CodemapUnit *unit, char *name, void
        *low_pc, void *high_pc);

void initCodemap() {
    codemap_units = NULL;
    codemap_ref = 0;
#ifdef THREADED_RTS
    initMutex(&codemap_mutex);
#endif
}

int codemap_is_loaded() {
    return codemap_units != NULL;
}

void codemap_load()
{
    if (codemap_is_loaded()) {
        errorBelch("Codemap is already loaded!");
        return;
    }

    // Initialize ELF library
    if (elf_version(EV_CURRENT) == EV_NONE) {
        errorBelch("libelf version too old!");
        return;
    }

    codemap_load_file(prog_argv[0]);
    codemap_init_lookup();
}

void codemap_load_file(char *module_path)
{

    // Open the module
    int fd = open(module_path, O_RDONLY);
    if (fd < 0) {
        sysErrorBelch("Could not open %s for reading debug data", module_path);
        return;
    }

    // Open using libelf (no archives, don't need elf_next)
    Elf *elf = elf_begin(fd, ELF_C_READ, 0);
    if(!elf) {
        errorBelch("Could not open ELF file: %s", elf_errmsg(-1));
        close(fd);
        return;
    }

    // Not actually an ELF file? That's okay, we are attempting this
    // for pretty much all memory-mapped files, so we can expect to
    // come across a few non-object files.
    if (elf_kind(elf) != ELF_K_ELF) {
        elf_end(elf);
        close(fd);
        return;
    }

    // Load symbols
    codemap_load_symbols(module_path, elf);

    elf_end(elf);
    close(fd);
}

void codemap_load_symbols(char *module_path, Elf *elf)
{
    // Locate symbol table section
    Elf_Scn *scn = 0; GElf_Shdr hdr;
    GElf_Shdr sym_shdr;
    GElf_Half sym_shndx = ~0;

    while ((scn = elf_nextscn(elf, scn))) {
        if (!gelf_getshdr(scn, &hdr))
            return;
        if (hdr.sh_type != SHT_SYMTAB && hdr.sh_type != SHT_DYNSYM)
            continue;
        // Get data
        Elf_Data *data = elf_getdata(scn, 0);
        if (!data)
            return;

        // Find or create the catch-all unit for symtab entries
        char symtab_unit_name[1024];
        snprintf (symtab_unit_name, 1024, "SYMTAB: %s", module_path);

        CodemapUnit *unit = codemap_get_unit(symtab_unit_name);
        if (!unit) unit = codemap_new_unit(symtab_unit_name);

        // Iterate over symbols
        nat ndx;
        for (ndx = 1; ndx < hdr.sh_size / hdr.sh_entsize; ndx++) {

            // Get symbol data
            GElf_Sym sym;
            if (gelf_getsym(data, ndx, &sym) != &sym) {
                errorBelch("CODEMAP: Could not read symbol %d: %s\n", ndx,
                        elf_errmsg(-1));
                continue;
            }

            // Look up string
            char *name = elf_strptr(elf, hdr.sh_link, sym.st_name);
            if (!name) {
                errorBelch("CODEMAP: Could not lookup name for symbol no %d: "
                        "%s\n", ndx, elf_errmsg(-1));
                continue;
            }

            // Load associated section header. Use cached one where
            // applicable.
            if (sym.st_shndx != sym_shndx) {
                if (sym.st_shndx == SHN_ABS) {
                    memset(&sym_shdr, 0, sizeof(sym_shdr));
                } else if(sym.st_shndx == SHN_UNDEF) {
                    continue;
                } else {

                    Elf_Scn *sym_scn = elf_getscn(elf, sym.st_shndx);
                    if (gelf_getshdr(sym_scn, &sym_shdr) != &sym_shdr) {
                        memset(&sym_shdr, 0, sizeof(sym_shdr));
                    }
                }
                sym_shndx = sym.st_shndx;
            }

            // Type?
            switch (GELF_ST_TYPE(sym.st_info)) {

                // Haskell symbols can appear in the symbol table flagged as
                // just about anything.
                case STT_NOTYPE:
                case STT_FUNC:
                case STT_OBJECT:

                    // Only look at symbols from executable sections
                    if (!(sym_shdr.sh_flags & SHF_EXECINSTR) ||
                            !(sym_shdr.sh_flags & SHF_ALLOC))
                        continue;

                    // Need a compilation unit to add name to. Ignore
                    // unaccounted-for names.
                    if (!unit)
                        break;

                    // Add procedure
                    codemap_new_proc(unit, name,
                            (void*) sym.st_value,
                            (void*) (sym.st_value+sym.st_size)
                            );

                    break;
            }
        }

    }
}

CodemapUnit *codemap_get_unit(char *name)
{
    CodemapUnit *unit;
    for (unit = codemap_units; unit; unit = unit->next)
        if (!strcmp(name, unit->name))
            return unit;
    return 0;
}

CodemapUnit *codemap_new_unit(char *name)
{
    CodemapUnit *unit = (CodemapUnit *)stgMallocBytes(sizeof(CodemapUnit),
            "codemap_new_unit");
    unit->name = strdup(name);
    unit->low_pc = NULL;
    unit->high_pc = NULL;
    unit->procs = NULL;
    unit->proc_count = 0;
    unit->procs_by_pc = NULL;
    unit->next = codemap_units;
    codemap_units = unit;
    return unit;
}

CodemapProc *codemap_new_proc(CodemapUnit *unit, char *name,
        void *low_pc, void *high_pc
        )
{
    // Security
    if (high_pc <= low_pc)
        return NULL;

    CodemapProc *proc = (CodemapProc *)stgMallocBytes(sizeof(CodemapProc),
            "codemap_new_proc");
    proc->name = strdup(name);
    proc->low_pc = low_pc;
    proc->high_pc = high_pc;

    proc->next = unit->procs;
    unit->procs = proc;

    // Update unit data
    if (!unit->low_pc || low_pc < unit->low_pc)
        unit->low_pc = low_pc;
    if (!unit->high_pc || high_pc > unit->high_pc)
        unit->high_pc = high_pc;
    unit->proc_count++;

    return proc;
}

void codemap_unload()
{
    if (!codemap_is_loaded()) {
        errorBelch("Codemap is not even loaded!");
    }
    CodemapUnit *unit;
    while ((unit = codemap_units)) {
        codemap_units = unit->next;
        free(unit->procs_by_pc);

        CodemapProc *proc;
        while ((proc = unit->procs)) {
            unit->procs = proc->next;
            free(proc->name);
            free(proc);
        }

        free(unit->name);
        free(unit);
    }
}

// Builds up associations between debug and CODEMAP data.

int compare_low_pc(const void *a, const void *b) {
    CodemapProc *proca = *(CodemapProc **)a;
    CodemapProc *procb = *(CodemapProc **)b;
    if (proca->low_pc < procb->low_pc) return -1;
    if (proca->low_pc == procb->low_pc) {
        return 0;
    }
    return 1;
}

// For debbuging purposes
void codemap_dump_tables(CodemapUnit *unit);
void codemap_dump_tables(CodemapUnit *unit)
{
    StgWord i;
    printf(" Unit %s (%lu procs) %p-%p:\n",
            unit->name, unit->proc_count,
            unit->low_pc, unit->high_pc);
    for (i = 0; i < unit->proc_count; i++) {
        printf("%p-%p: %s\n",
                unit->procs_by_pc[i]->low_pc, unit->procs_by_pc[i]->high_pc,
                unit->procs_by_pc[i]->name);
    }
}

void codemap_init_lookup(void)
{
    // Build procedure tables for every unit
    CodemapUnit *unit;
    for (unit = codemap_units; unit; unit = unit->next) {

        // Just in case we run this twice for some reason
        free(unit->procs_by_pc); unit->procs_by_pc = NULL;

        // Allocate tables
        StgWord pcTableSize = unit->proc_count * sizeof(CodemapProc *);
        unit->procs_by_pc = (CodemapProc **)stgMallocBytes(pcTableSize,
                "codemap_init_pc_table");

        // Populate
        StgWord i = 0;
        CodemapProc *proc;
        for (proc = unit->procs; proc; proc = proc->next) {
            unit->procs_by_pc[i++] = proc;
        }

        // Sort PC table by low_pc
        qsort(unit->procs_by_pc, unit->proc_count, sizeof(CodemapProc *),
                compare_low_pc);

    }
}

// Helper for codemap_lookup_ip
CodemapProc *codemap_lookup_proc(void *ip, CodemapUnit **punit)
{
    CodemapUnit *unit;
    for (unit = codemap_units; unit; unit = unit->next) {

        // Pointer in unit range?
        if (ip < unit->low_pc || ip >= unit->high_pc)
            continue;
        if (!unit->proc_count || !unit->procs_by_pc)
            continue;

        // Find first entry with low_pc < ip in table (using binary search)
        StgWord low = 0, high = unit->proc_count;
        while (low < high) {
            int mid = (low + high) / 2;
            if (unit->procs_by_pc[mid]->low_pc <= ip)
                low = mid + 1;
            else
                high = mid;
        }

        // Find an entry covering it
        while (low > 0) {
            CodemapProc *proc = unit->procs_by_pc[low-1];

            // Security
            if (ip < proc->low_pc) {
                debugBelch("CODEMAP lookup: PC table corruption!");
                break;
            }

            // In bounds? Then we have found it
            if (ip <= proc->high_pc) {
                if (punit)
                    *punit = unit;
                return proc;
            }

            // Otherwise backtrack
            low--;
        }

    }

    return NULL;
}

void codemap_lookup_ip(void *ip, CodemapProc **p_proc, CodemapUnit **p_unit)
{
    *p_proc = codemap_lookup_proc(ip, p_unit);
    if(*p_proc == NULL) {
        *p_unit = NULL; // To signal failure
    }
}

void codemap_inc_ref(void) {
    ACQUIRE_LOCK(&codemap_mutex);
    codemap_ref++;
    if (!codemap_is_loaded()) {
        // If isn't initialized
        codemap_load();
    }
    RELEASE_LOCK(&codemap_mutex);
}

void codemap_dec_ref(void) {
    ACQUIRE_LOCK(&codemap_mutex);
    codemap_ref--;
    RELEASE_LOCK(&codemap_mutex);
}

StgBool codemap_try_unload(void) {
    StgBool will_unload;
    ACQUIRE_LOCK(&codemap_mutex);
    will_unload = codemap_ref == 0 && codemap_is_loaded();
    if (will_unload) {
        codemap_unload();
    }
    RELEASE_LOCK(&codemap_mutex);
    return will_unload;
}

#else /* USE_ELF */

#include "Rts.h"

void codemap_lookup_ip(void *ip STG_UNUSED,
                CodemapProc **p_proc,
                CodemapUnit **p_unit)
{
    *p_proc = NULL; // Signal failure
    *p_unit = NULL; // Signal failure
}

void codemap_inc_ref(void) {
}

void codemap_dec_ref(void) {
}

StgBool codemap_try_unload(void) {
    return 0;
}

StgBool codemap_is_loaded(void) {
    return 0;
}

#endif /* USE_ELF */
