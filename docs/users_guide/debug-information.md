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
 * debug information entity (DIE) information (the `.debug_info` section)

As GHC's compilation products don't map perfectly onto DWARF constructs, some 

GHC may produce the following DIEs,

#### `DW_TAG_compile_unit`

hi

#### `DW_TAG_subprogram`

#### `DW_TAG_lexical_block`

### Limitations

Unfortunately DWARF isn't expressive enough to fully describe the code that GHC
produces. This is most apparent in the case of line information, where GHC is
forced to choose some between a variety of possible originating source
locations. This limits the usefulness of DWARF information with traditional
statistical profiling tools. For profiling it is recommended that one use the
extended debugging information. See the *Profiling* section below.

### DWARF extensions

In addition to the usual DIEs specified by the DWARF specification, GHC produces
a variety of others using the vendor-extensibility regions of the tag and
attribute space.

#### `DW_TAG_ghc_core_note`

DIEs of this type (tag 0x5b000 )are found as children of `DW_TAG_lexical_block`
DIEs. They carry a single string attribute, `DW_AT_core`. This attribute
provides a string representation of the simplified Core which gave rise to the
block (e.g. as would have been produced by `-ddump-simpl`).

 * `DW_AT_ghc_core` (0x2b00) - string : A textual representation of the Core
   AST which gave rise to the block.

#### `DW_TAG_ghc_src_note`

`DW_TAG_ghc_src_note` DIEs (tag 0x5b01) are found as children of
`DW_TAG_lexical_block` DIEs. They describe source spans which gave rise to the
block; formally these spans are causally responsible for produced code:
changes to code in the given span may change the code within the block; conversely
changes outside the span are guaranteed not to affect the code in the block.

Spans are described with the following attributes,

 * `DW_AT_ghc_span_file` (0x2b10) - string : the name of the source file
 * `DW_AT_ghc_span_start_line` (0x2b11) - integer : the line number of the beginning of the span
 * `DW_AT_ghc_span_start_col` (0x2b11) - integer : the column number of the beginning of the span
 * `DW_AT_ghc_span_end_line` (0x2b11) - integer : the line number of the end of the span
 * `DW_AT_ghc_span_end_col` (0x2b11) - integer : the column number of the end of the span

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
