/* ----------------------------------------------------------------------------
 *
 * (c) The GHC Team, 2015-2015
 *
 * Codemap
 *
 * This module tries to give a mapping between code instruction pointer within
 * the running binary (argv[0]) to a descriptive source file location info.
 *
 * Essentially, this is like using a debugger like gdb but reimplemented in the
 * rts.
 *
 * Do not #include this file directly: #include "Rts.h" instead.
 *
 * To understand the structure of the RTS headers, see the wiki:
 *   http://ghc.haskell.org/trac/ghc/wiki/Commentary/SourceTree/Includes
 *
 * -------------------------------------------------------------------------- */

#ifndef PUBLIC_CODEMAP_H
#define PUBLIC_CODEMAP_H

typedef struct CodemapUnit_ CodemapUnit;
typedef struct CodemapProc_ CodemapProc;

/* This represents a compilation unit.  A compilation unit knows what
 * procedures are within it.
 *
 * The current elf only implementation of Codemap only uses the section header
 * SYMTAB and DYNSYM and they both will be considered the same compilation
 * unit.  When Codemap can read and understand DWARF, there will be one
 * compilation unit per Haskell module.
 */
struct CodemapUnit_ {
    char *name;
    void *low_pc, *high_pc;
    CodemapProc *procs;
    StgWord proc_count;

    CodemapProc **procs_by_pc; // sorted by low_pc

    CodemapUnit *next;
};

/* All known debug data and the code-location range for a procedure.
 *
 * A procedure is any compiled jumpto-able entry point. Typically seen in .o
 * files. These includes:
 *
 *  *) Info tables for Haskell-written functions
 *  *) Rts functions in C--
 *
 */
struct CodemapProc_ {
    char *name;
    void *low_pc;
    void *high_pc;
    struct CodemapProc_ *next;
};

void codemap_inc_ref(void); // Will load codemap, if it isn't already.
void codemap_dec_ref(void); // Let rts know your thread is done using codemap.
                            // So it's safe to unload codemap.
StgBool codemap_try_unload(void); // Returns true iff it actually did unload
StgBool codemap_is_loaded(void); // Check if codemap is loaded.

/* Look-up the procedure associated with a given address.  Storing the result
 * in p_proc and p_unit. If no matching procedure is found. It'll set both
 * *p_proc and *p_unit to NULL.
 *
 * Before using codemap_lookup_ip, you must load the debug data. See
 * codemap_inc_ref()
 */
void codemap_lookup_ip(void *ip,
        CodemapProc **p_proc, /* out */
        CodemapUnit **p_unit /* out */
        );

#endif // PUBLIC_CODEMAP_H
