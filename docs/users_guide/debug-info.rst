Debugging compiled programs
===========================

Since the 8.0 release GHC can emit a debugging information to help debugging
tools understand the code that GHC produces. This debugging information is
useable by most UNIX debugging tools.

Tutorial
--------

Let's consider a simple example,

.. code-block:: hs
   :linenos:

    -- fib.hs
    fib :: Int -> Int
    fib 0 = 0
    fib 1 = 1
    fib n = fib (n-1) + fib (n-2)

    main :: IO ()
    main = print $ fib 50

Let's first see how execution flows through this program. We start by telling
GHC that we want debug information,

.. code-block:: sh

    $ ghc -g -rtsopts fib.hs

Here we used the ``-g`` option to inform GHC that it should add debugging
information in the produced binary. There are three levels of debugging
output: ``-g0`` (no debugging information, the default), ``-g1`` (sufficient for
basic backtraces), ``-g2`` (or just ``-g`` for short; emitting everything GHC knows).
Note that this debugging information does not affect the optimizations performed
by GHC.

.. tip::
   Under Mac OS X debug information is kept apart from the executable. After
   compiling the executable you'll need to use the ``dsymutil`` utility to
   extract the debugging information and place them in the debug archive,

   .. code-block:: sh

      $ dsymutil fib

   This should produce a file named ``fib.dSYM``.

Now let's have a look at the flow of control. For this we can just start our
program under ``gdb`` (or an equivalent debugger) as we would any other native
executable,

.. code-block:: none

    $ gdb --args ./Fib +RTS -V0
    Reading symbols from Fib...done.
    (gdb) run
    Starting program: /opt/exp/ghc/ghc-dwarf/Fib
    [Thread debugging using libthread_db enabled]
    Using host libthread_db library "/lib/x86_64-linux-gnu/libthread_db.so.1".
    ^C
    Program received signal SIGINT, Interrupt.
    0x000000000064fc7c in cfy4_info () at libraries/integer-gmp/src/GHC/Integer/Type.hs:424
    424     minusInteger x y = inline plusInteger x (inline negateInteger y)
    (gdb)

Here we have used the runtime system's ``-V0`` option to disable the RTS's
periodic timer which may interfere with our debugging session. Upon breaking
into the program ``gdb`` shows us a location in our source program corresponding
to the current point of execution.

Moreover, we can ask ``gdb`` to tell us the flow of execution that lead us to
this point in the program,

.. code-block:: none

   (gdb) bt
   #0  0x000000000064fc7c in cfy4_info () at libraries/integer-gmp/src/GHC/Integer/Type.hs:424
   #1  0x00000000006eb0c0 in ?? ()
   #2  0x000000000064301c in cbuV_info () at libraries/integer-gmp/src/GHC/Integer/Type.hs:323
   #3  0x000000000064311b in integerzmgmp_GHCziIntegerziType_eqInteger_info () at libraries/integer-gmp/src/GHC/Integer/Type.hs:312
   #4  0x0000000000406eca in roz_info () at Fib.hs:2
   #5  0x00000000006eb0c0 in ?? ()
   #6  0x000000000064f075 in cfru_info () at libraries/integer-gmp/src/GHC/Integer/Type.hs:412
   #7  0x00000000006eb0c0 in ?? ()
   #8  0x000000000064f075 in cfru_info () at libraries/integer-gmp/src/GHC/Integer/Type.hs:412
   #9  0x00000000006eb0c0 in ?? ()
   #10 0x000000000064eefe in integerzmgmp_GHCziIntegerziType_plusInteger_info () at libraries/integer-gmp/src/GHC/Integer/Type.hs:393
   ...
   #64 0x0000000000643ac8 in integerzmgmp_GHCziIntegerziType_ltIntegerzh_info () at libraries/integer-gmp/src/GHC/Integer/Type.hs:343
   #65 0x00000000004effcc in base_GHCziShow_zdwintegerToString_info () at libraries/base/GHC/Show.hs:443
   #66 0x00000000004f0795 in base_GHCziShow_zdfShowIntegerzuzdcshow_info () at libraries/base/GHC/Show.hs:145
   #67 0x000000000048892b in cdGW_info () at libraries/base/GHC/IO/Handle/Text.hs:595
   #68 0x0000000000419cb2 in base_GHCziBase_thenIO1_info () at libraries/base/GHC/Base.hs:1072


.. hint::

    Here we notice the first bit of the stack trace has many unidentified stack
    frames at address ``0x006eb0c0``. If we ask ``gdb`` about this location, we
    find that these frames are actually STG update closures,

    .. code-block:: none

        (gdb) print/a 0x006eb0c0
        $1 = 0x6eb0c0 <stg_upd_frame_info>

    The reason ``gdb`` doesn't show this symbol name in the backtrace output is an
    infidelity in its interpretation of debug information, which assumes an
    invariant preserved in C but not Haskell programs. Unfortunately it is
    necessary to work around this manually until this behivior is fixed
    upstream.

.. note::

    Because of the aggressive optimization that GHC performs to the programs it
    compiles it is quite difficult to pin-point exactly which point in the source
    program a given machine instruction should be attributed to. In fact,
    internally GHC associates each instruction with a **set** of source
    locations. When emitting the standard debug information used by ``gdb`` and
    other language-agnostic debugging tools, GHC is forced to heuristically
    choose one location from among this set.

    For this reason we should be cautious when interpretting the source locations
    provided by GDB. While these locations will usually be in some sense
    "correct", they aren't always useful. This is why profiling tools targetting
    Haskell should supplement the standard source location information with
    GHC-specific annotations (emitted with ``-g2``) when assigning costs.

Indeed, we can even set breakpoints,

.. code-block:: none

    (gdb) break fib.hs:4
    Breakpoint 1 at 0x406c60: fib.hs:4. (5 locations)
    (gdb) run
    Starting program: /opt/exp/ghc/ghc-dwarf/Fib

    Breakpoint 1, c1RV_info () at Fib.hs:4
    4        fib n = fib (n-1) + fib (n-2)
    (gdb) bt
    #0  c1RV_info () at Fib.hs:4
    #1  0x00000000006eb0c0 in ?? ()
    #2  0x0000000000643ac8 in integerzmgmp_GHCziIntegerziType_ltIntegerzh_info () at libraries/integer-gmp/src/GHC/Integer/Type.hs:343
    #3  0x00000000004effcc in base_GHCziShow_zdwintegerToString_info () at libraries/base/GHC/Show.hs:443
    #4  0x00000000004f0795 in base_GHCziShow_zdfShowIntegerzuzdcshow_info () at libraries/base/GHC/Show.hs:145
    #5  0x000000000048892b in cdGW_info () at libraries/base/GHC/IO/Handle/Text.hs:595
    #6  0x0000000000419cb2 in base_GHCziBase_thenIO1_info () at libraries/base/GHC/Base.hs:1072
    #7  0x00000000006ebcb0 in ?? () at rts/Exception.cmm:332
    #8  0x00000000006e7320 in ?? ()
    (gdb)


Due to the nature of GHC's heap


Requesting a stack trace from Haskell code
------------------------------------------

GHC's runtime system has built-in support for collecting stack trace information
from a running Haskell program. This currently requires that the ``libdw``
library from the ``elfutils`` package is available. Of course, the backtrace
will be of little use unless debug information is available in the executable
and its dependent libraries.

Stack trace functionality is exposed for use by Haskell programs in the
:base-ref:`GHC.ExecutionStack <GHC-ExecutionStack.html>` module. See the Haddock
documentation in this module for details regarding usage.

Requesting a stack trace with ``SIGUSR2``
-----------------------------------------

On POSIX-compatible platforms GHC's runtime system (when built with ``libdw``
support) will produce a stack trace on ``stderr`` when a ``SIGUSR2`` signal is
received. For instance (using the same ``fib.hs`` as above),

.. code-block:: sh

    $ ./fib  &  killall -SIGUSR2 fib
    0x7f3176b15dd8    dwfl_thread_getframes (/usr/lib/x86_64-linux-gnu/libdw-0.163.so)
    0x7f3176b1582f    (null) (/usr/lib/x86_64-linux-gnu/libdw-0.163.so)
    0x7f3176b15b57    dwfl_getthreads (/usr/lib/x86_64-linux-gnu/libdw-0.163.so)
    0x7f3176b16150    dwfl_getthread_frames (/usr/lib/x86_64-linux-gnu/libdw-0.163.so)
          0x6dc857    libdwGetBacktrace (rts/Libdw.c:248.0)
          0x6e6126    backtrace_handler (rts/posix/Signals.c:541.0)
    0x7f317677017f    (null) (/lib/x86_64-linux-gnu/libc-2.19.so)
          0x642e1c    integerzmgmp_GHCziIntegerziType_eqIntegerzh_info (libraries/integer-gmp/src/GHC/Integer/Type.hs:320.1)
          0x643023    integerzmgmp_GHCziIntegerziType_eqInteger_info (libraries/integer-gmp/src/GHC/Integer/Type.hs:312.1)
          0x406eca    roz_info (/opt/exp/ghc/ghc-dwarf//Fib.hs:2.1)
          0x6eafc0    stg_upd_frame_info (rts/Updates.cmm:31.1)
          0x64ee06    integerzmgmp_GHCziIntegerziType_plusInteger_info (libraries/integer-gmp/src/GHC/Integer/Type.hs:393.1)
          0x6eafc0    stg_upd_frame_info (rts/Updates.cmm:31.1)
    ...
          0x6439d0    integerzmgmp_GHCziIntegerziType_ltIntegerzh_info (libraries/integer-gmp/src/GHC/Integer/Type.hs:343.1)
          0x4efed4    base_GHCziShow_zdwintegerToString_info (libraries/base/GHC/Show.hs:442.1)
          0x4f069d    base_GHCziShow_zdfShowIntegerzuzdcshow_info (libraries/base/GHC/Show.hs:145.5)
          0x488833    base_GHCziIOziHandleziText_zdwa8_info (libraries/base/GHC/IO/Handle/Text.hs:582.1)
          0x6ebbb0    stg_catch_frame_info (rts/Exception.cmm:370.1)
          0x6e7220    stg_stop_thread_info (rts/StgStartup.cmm:42.1)


Statistical profiling
---------------------

GHC's runtime system has a statistical profiler which can cheaply collect
samples based on a variety of events including heap allocations and blackhole
blocking. The profiler generates events in the program's event log; these
include information describing the program as well as the sample data.


Implementor's notes: DWARF annotations
--------------------------------------

.. note::
   Most users don't need to worry about the details described in this section.
   This discussion is primarily targeted at tooling authors who need to
   interpret the GHC-specific DWARF annotations contained in compiled binaries.

When invoked with the ``-g`` flag GHC will produce standard `DWARF v4
<http://dwarfstd.org/>`__ debugging information. This format is used by nearly
all POSIX-compliant targets and can be used by debugging and performance tools
(e.g. ``gdb``, ``lldb``, and ``perf``) to understand the structure of
GHC-compiled programs.

In particular GHC produces the following DWARF sections,

``.debug_info``
  Debug information entities (DIEs) describing all of the basic blocks in the
  compiled program.

``.debug_line``
  Line number information necessary to map instruction addresses to line numbers
  in the source program.

  Note that the line information in this section is not nearly as rich as the
  information provided in ``.debug_info``. Whereas ``.debug_line`` requires that
  each instruction is assigned exactly one source location, the DIEs in
  ``.debug_info`` can be used to identify all relevant sources locations.

``.debug_frames``
  Call frame information (CFI) necessary for stack unwinding to produce a call
  stack trace.

``.debug_arange``
  Address range information necessary for efficient lookup in debug information.


Debugging information entities
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

GHC may produce the following standard DIEs in the ``.debug_info`` section,

``DW_TAG_compile_unit``
  Represents a compilation unit (e.g. a Haskell module).

``DW_TAG_subprogram``
  Represents a C-- top-level basic block.

``DW_TAG_lexical_block``
  Represents a C-- basic block. Note that this is a slight departure from the
  intended meaning of this DIE type as it does not necessarily reflect
  lexical scope in the source program.

As GHC's compilation products don't map perfectly onto DWARF constructs,
GHC takes advantage of the extensibility of the DWARF standard to provide
additional information.

Unfortunately DWARF isn't expressive enough to fully describe the code
that GHC produces. This is most apparent in the case of line
information, where GHC is forced to choose some between a variety of
possible originating source locations. This limits the usefulness of
DWARF information with traditional statistical profiling tools. For
profiling it is recommended that one use the extended debugging
information. See the *Profiling* section below.

In addition to the usual DIEs specified by the DWARF specification, GHC
produces a variety of others using the vendor-extensibility regions of
the tag and attribute space.

``DW_TAG_ghc_core_note``
^^^^^^^^^^^^^^^^^^^^^^^^

DIEs of this type (tag 0x5b000) are found as children of
``DW_TAG_lexical_block`` DIEs. They carry a single string attribute,
``DW_AT_core``. This attribute provides a string representation of the
simplified Core which gave rise to the block (e.g. as would have been produced
by ``-ddump-simpl``).

``DW_AT_ghc_core`` (0x2b00, string)
  A textual representation of the Core AST which gave rise to the block.

``DW_TAG_ghc_src_note``
^^^^^^^^^^^^^^^^^^^^^^^

``DW_TAG_ghc_src_note`` DIEs (tag 0x5b01) are found as children of
``DW_TAG_lexical_block`` DIEs. They describe source spans which gave rise to the
block; formally these spans are causally responsible for produced code: changes
to code in the given span may change the code within the block; conversely
changes outside the span are guaranteed not to affect the code in the block.

Spans are described with the following attributes,

``DW_AT_ghc_span_file`` (0x2b10, string)
  the name of the source file

``DW_AT_ghc_span_start_line`` (0x2b11, integer)
  the line number of the beginning of the span

``DW_AT_ghc_span_start_col`` (0x2b11, integer)
  the column number of the beginning of the span

``DW_AT_ghc_span_end_line`` (0x2b11, integer)
  the line number of the end of the span

``DW_AT_ghc_span_end_col`` (0x2b11, integer)
  the column number of the end of the span

Implementor's notes : Statistical profiler events
-------------------------------------------------

.. note::
   Most users don't need to worry about the details described in this section.
   This discussion is primarily targeted at tooling authors who need to
   interpret event-log records produced by the GHC runtime's statistical
   profiler.

Program metadata
~~~~~~~~~~~~~~~~

At program startup the runtime system examines the program (specifically
the DWARF annotations described in the previous section) and emits
events describing the program being run, namely the procedures of the
program, their address ranges, and source location information. These
entities represent a tree which is encoded in suffix order by events,

``EVENT_PROC``
  This variable-length event encodes a procedure (i.e. a C--
  block). The body of the event is the name of the procedure.

``EVENT_SOURCE_NOTE``
  This variable-length event encodes a source note identifying the regions of
  source code responsible for the parent procedure (see the previous section).
  The body consists of,

  * a null-terminated source file name
  * 32-bit unsigned start line number
  * 32-bit unsigned start column number
  * 32-bit unsigned end line number
  * 32-bit unsigned end column number

``EVENT_PROC_RANGE``
  This fixed-length event describes an address range covered by the parent
  procedure. The body consists of 64-bit start and end addresses.

``EVENT_PROC_END``
  This length-0 event denotes the closing of a node in the block tree


Profile sample streams
~~~~~~~~~~~~~~~~~~~~~~

Profiles collected by the statistical profiler consist of a set of samples of some
measurable (e.g. an instruction pointer value or call stack) triggered on some
recurring event (e.g. heap allocation, after a given number of CPU cycles, or
after some duration of time). At any given moment multiple sample streams may
active; samples associated with each stream may be distinguished by the stream's
unique sample stream id.

The beginning of a sample stream is marked with an ``EVENT_SAMPLE_STREAM_BEGIN``
event in the event log. This event identifies the beginning of a sample stream,
along with some metadata describing what event samples in the stream are
triggered by, what is being sampled, and how the samples are encoded. The event
encodes the following fields,

-  8-bit sample stream id
-  16-bit sample type: what was being sampled?

   * ``SAMPLE_TYPE_INSTR_PTR``: Samples are instruction pointer addresses. See
     :ref:`instr-ptr-sample-encoding` for a description of the encoding scheme
     for samples of this type.

   * ``SAMPLE_TYPE_STACK_TRACE``:

-  16-bit trigger type: what triggers sample collection?

   * ``SAMPLE_TRIG_TIME``: Sampling triggered by a periodic timer.

   * ``SAMPLE_TRIG_HEAP_ALLOC``: Sampling triggered on heap checks. Samples

   * ``SAMPLE_TRIG_BLACKHOLE``: Sampling triggered on black hole blocking events

   * ``SAMPLE_TRIG_PERF_EVENT``: Sampling triggered on Linux ``perf_event`` counter

-  16-bit trigger details length: How long is the trigger details field?

-  Trigger details: Structure determined by trigger type.

The end of a sample stream is marked with an ``EVENT_SAMPLE_STREAW_END`` event,
which encodes the following fields,

-  8-bit sample stream id


Profile samples
~~~~~~~~~~~~~~~

Profile samples are encoded by variable-length ``EVENT_STAT_PROF_SAMPLES``
events.

-  16-bit capability number of the capability from which the samples
   originated

-  8-bit sample stream id

-  encoded sample data


_instr-ptr-sample-encoding::

Instruction pointer sample encoding
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

``SAMPLE_TYPE_INSTR_PTR`` samples are encoded in a compressed form,
exploiting the fact that we expect "hot-spots" of many closely-spaced samples
to dominate comprise the majority of the output. Each sample is encoded as an a
one-byte header followed by a compressed address and positive weight (allowing
us to compress samples at the same address into a single sample record).

The header consists of two four-bit fields,

-  bits 7..4: the sample encoding type; one of,

   *  0x00: 8-bit offset to previous address
   *  0x10: negative 8-bit offset to previous address
   *  0x40: 32-bit offset to previous address
   *  0x50: negative 32-bit offset to previous address
   *  0xf0: direct encoding

-  bits 3..0: the number of bytes used to encode the weight. If zero
   bytes are used the weight is taken to be 1.

Following the header is the encoded sample address (either one, four, or
word-size bytes, depending upon the sample encoding type) and the
weight. The "previous address" is taken to be zero at the beginning of
the encoding process.

For instance, we might represent the sequence of samples ::

    0xdeadbeef
    0xdeadbeef
    0xcafebead
    0xcafebeaf
    0xcafebeae
    0xcafebeae

as four encoded sample records,

-  ``0x41 0xdeadbeef 0x2`` (``addr=last + 0xdeadbeef, weight=2``)
-  ``0x50 0x13af0042`` (``addr=last - 0x13af0042, weight=1``)
-  ``0x00 0x2`` (``addr=last + 0x2, weight=1``)
-  ``0x11 0x1`` (``addr=last - 0x1, weight=2``)


Further Reading
---------------

For more information about the debug information produced by GHC see
Peter Wortmann's PhD thesis, `*Profiling Optimized Haskell: Causal
Analysis and Implementation* <http://etheses.whiterose.ac.uk/8321/>`__.
