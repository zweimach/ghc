# Debugging compiled programs

Since the 8.0 release GHC can emit a variety of debug information to help
debugging tools understand the code that GHC produces. For this, GHC uses both
the standard the [DWARF v4][dwarf] debugging format, as well as its own custom
encoding.


## DWARF debugging information

When invoked with the `-g` flag GHC will produce everything necessary to get
stack-traces with line numbers from a debugging tool supporting DWARF (e.g.
`gdb`).

### What is produced

In particular GHC produces the following DWARF information,

 * line number information necessary to map instruction addresses to line
   numbers in the source program (the `.debug_line` section)
 * call frame information necessary for stack unwinding to produce a call stack
   trace (the `.debug_frames` section)
 * address range information necessary for efficient lookup in debug information
   (the `.debug_arange` section)

### Limitations

Unfortunately DWARF isn't expressive enough to fully describe the code that GHC
produces. This is most apparent in the case of line information, where GHC is
forced to choose some between a variety of possible originating source
locations. This limits the usefulness of DWARF information with traditional
statistical profiling tools. For profiling it is recommended that one use the
extended debugging information. See the *Profiling* section below.

## Extended debugging information

To overcome the limitations of DWARF, GHC can also produce debugging information
in its own debugging information format (known as "extended debug information").
This can include the Core representation of the program, as well as more
descriptive line information, allowing for more accurate profiling.


## Requesting a stack trace from Haskell code

GHC's runtime system has built-in support for collecting stack trace information
from a running Haskell program. This currently requires that the `libdw` library
from the `elfutils` package is available.

Stack trace functionality is exposed to for use by Haskell programs in the
`GHC.ExecutionStack` module. See the Haddock documentation in this module for
details regarding usage.

## Requesting a stack trace with Posix signal

GHC's runtime system will produce a stack trace on `stderr` when a `SIGUSR2`
signal is received.

## Further Reading

For more information about the debug information produced by GHC see Peter
Wortmann PhD thesis,
[*Profiling Optimized Haskell: Causal Analysis and Implementation*][scpmw-thesis].

[scpmw-thesis]: http://etheses.whiterose.ac.uk/8321/
[dwarf]: http://dwarfstd.org/
