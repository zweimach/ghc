Eventlog encodings
==================

This section documents the encodings of the events emitted to GHC's
:ref:`event log <rts-eventlog>`. These events can include information about the
thread scheduling events, garbage collection statistics, profiling information,
user-defined tracing events.

This section is intended for implementors of tooling which consume these events.


Event log format
----------------

The log format is designed to be extensible: old tools should be
able to parse (but not necessarily understand all of) new versions
of the format, and new tools will be able to understand old log
files.

- The format is endian-independent: all values are represented in 
  big-endian order.

- The format is extensible:

  - The header describes each event type and its length.  Tools
    that don't recognise a particular event type can skip those events.

  - There is room for extra information in the event type
    specification, which can be ignored by older tools.

  - Events can have extra information added, but existing fields
    cannot be changed.  Tools should ignore extra fields at the
    end of the event record.

The event-log stream begins with a header describing the event types present in
the file. The header is followed by the event records themselves, each of which
consist of a 64-bit timestamp

.. code-block:: none

    log : EVENT_HEADER_BEGIN
          EventType*
          EVENT_HEADER_END
          EVENT_DATA_BEGIN
          Event*
          EVENT_DATA_END

    EventType :
          EVENT_ET_BEGIN
          Word16         -- unique identifier for this event
          Int16          -- >=0  size of the event in bytes (minus the header)
                         -- -1   variable size
          Word32         -- length of the next field in bytes
          Word8*         -- string describing the event
          Word32         -- length of the next field in bytes
          Word8*         -- extra info (for future extensions)
          EVENT_ET_END

    Event : 
          Word16         -- event_type
          Word64         -- time (nanosecs)
          [Word16]       -- length of the rest (for variable-sized events only)
          ... extra event-specific info ...

There are two classes of event types:

 - *Fixed size*: All event records of a fixed-sized type are of the same
   length, given in the header event-log header.

 - *Variable size*: Each event record includes a length field.

Runtime system diagnostics
--------------------------

 * ``ThreadId ~ Word32``
 * ``CapNo ~ Word16``
 * ``CapSetId ~ Word32``

Capability sets
^^^^^^^^^^^^^^^



Environment information
^^^^^^^^^^^^^^^^^^^^^^^

These events are typically produced during program startup and describe the
environment which the program is being run in.

.. event-type:: RTS_IDENTIFIER

   :tag: 29
   :length: variable
   :field CapSetId: Capability set
   :field String: Runtime system name and version.

   Describes the name and version of the runtime system responsible for the
   indicated capability set.

.. event-type:: PROGRAM_ARGS

   :tag: 30
   :length: variable
   :field CapSetId: Capability set
   :field [String]: The command-line arguments passed to the program

   Describes the command-line used to start the program.

.. event-type:: PROGRAM_ENV

   :tag: 31
   :length: variable
   :field CapSetId: Capability set
   :field [String]: The environment variable name/value pairs. (TODO: encoding?)

   Describes the environment variables present in the program's environment.

Thread and scheduling events
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. event-type:: CREATE_THREAD

   :tag: 0
   :length: fixed
   :field ThreadId: thread id

   Marks the creation of a Haskell thread.


.. event-type:: RUN_THREAD

   :tag: 1
   :length: fixed
   :field ThreadId: thread id

   The indicated thread has started running.


.. event-type:: STOP_THREAD

   :tag: 2
   :length: fixed
   :field ThreadId: thread id
   :field Word16: status

      * 1: HeapOverflow
      * 2: StackOverflow
      * 3: ThreadYielding
      * 4: ThreadBlocked
      * 5: ThreadFinished
      * 6: ForeignCall
      * 7: BlockedOnMVar
      * 8: BlockedOnBlackHole
      * 9: BlockedOnRead
      * 10: BlockedOnWrite
      * 11: BlockedOnDelay
      * 12: BlockedOnSTM
      * 13: BlockedOnDoProc
      * 16: BlockedOnMsgThrowTo

   :field ThreadId: thread id of thread being blocked on (only for some status
                    values)

   The indicated thread has stopped running for the reason given by ``status``.


.. event-type:: THREAD_RUNNABLE

   :tag: 3
   :length: fixed
   :field ThreadId: thread id

   The indicated thread is has been marked as ready to run.


.. event-type:: MIGRATE_THREAD

   :tag: 4
   :length: fixed
   :field ThreadId: thread id
   :field CapNo: capability

   The indicated thread has been migrated to a new capability.


.. event-type:: THREAD_WAKEUP

   :tag: 8
   :length: fixed
   :field ThreadId: thread id
   :field CapNo: other capability

   The indicated thread has been been woken up on another capability.

.. event-type:: THREAD_LABEL

   :tag: 44
   :length: fixed
   :field ThreadId: thread id
   :field String: label

   The indicated thread has been given a label (e.g. with
   :base-ref:`Control.Concurrent.setThreadLabel`).


Garbage collector events
^^^^^^^^^^^^^^^^^^^^^^^^

.. event-type:: GC_START

   :tag: 9
   :length: fixed

   A garbage collection pass has been started.

.. event-type:: GC_END

   :tag: 10
   :length: fixed

   A garbage collection pass has been finished.

.. event-type:: REQUEST_SEQ_GC

   :tag: 11
   :length: fixed

   A sequential garbage collection has been requested by a capability.

.. event-type:: REQUEST_PAR_GC

   :tag: 12
   :length: fixed

   A parallel garbage collection has been requested by a capability.

.. event-type:: GC_IDLE

   :tag: 20
   :length: fixed

   An idle-time garbage collection has been started.

.. event-type:: GC_WORK

   :tag: 21
   :length: fixed

   TODO

.. event-type:: GC_DONE

   :tag: 22
   :length: fixed

   TODO

.. event-type:: GC_STATS_GHC

   :tag: 53
   :length: fixed
   :field CapSetId: heap capability set
   :field Word16: generation of collection
   :field Word64: bytes copied
   :field Word64: bytes of slop found
   :field Word64: TODO
   :field Word64: number of parallel garbage collection threads
   :field Word64: maximum number of bytes copied by any single collector thread
   :field Word64: total bytes copied by all collector threads
   
   Report various information about the heap configuration. Typically produced
   during RTS initialization..

.. event-type:: GC_GLOBAL_SYNC

   :tag: 54
   :length: fixed

   TODO

Heap events and statistics
^^^^^^^^^^^^^^^^^^^^^^^^^^

.. event-type:: HEAP_ALLOCATED

   :tag: 49
   :length: fixed
   :field CapSetId: heap capability set
   :field Word64: allocated bytes

   A new chunk of heap has been allocated by the indicated capability set.

.. event-type:: HEAP_SIZE

   :tag: 50
   :length: fixed
   :field CapSetId: heap capability set
   :field Word64: heap size in bytes
   
   Report the heap size.

.. event-type:: HEAP_LIVE

   :tag: 51
   :length: fixed
   :field CapSetId: heap capability set
   :field Word64: heap size in bytes
   
   Report the live heap size.

.. event-type:: HEAP_INFO_GHC

   :tag: 52
   :length: fixed
   :field CapSetId: heap capability set
   :field Word16: number of garbage collection generations
   :field Word64: maximum heap size
   :field Word64: allocation area size
   :field Word64: MBlock size
   :field Word64: Block size
   
   Report various information about the heap configuration. Typically produced
   during RTS initialization..

Spark events
^^^^^^^^^^^^

.. event-type:: CREATE_SPARK_THREAD
   :tag: 15
   :length: fixed

   A thread has been created to perform spark evaluation.

.. event-type:: SPARK_COUNTERS
   :tag: 34
   :length: fixed

   A periodic reporting of various statistics of spark evaluation.

.. event-type:: SPARK_CREATE
   :tag: 35
   :length: fixed

   A spark has been added to the spark pool.

.. event-type:: SPARK_DUD
   :tag: 36
   :length: fixed

   TODO

.. event-type:: SPARK_OVERFLOW
   :tag: 37
   :length: fixed

   TODO

.. event-type:: SPARK_RUN
   :tag: 38
   :length: fixed

   Evaluation has started on a spark.

.. event-type:: SPARK_STEAL
   :tag: 39
   :length: fixed
   :field Word16: capability from which the spark was stolen

   A spark has been stolen from another capability for evaluation.

.. event-type:: SPARK_FIZZLE
   :tag: 40
   :length: fixed

   TODO

.. event-type:: SPARK_GC
   :tag: 41
   :length: fixed

   An unevaluated spark has been garbage collected.

Capability events
^^^^^^^^^^^^^^^^^

.. event-type:: CAP_CREATE
   :tag: 45
   :length: fixed
   :field CapNo: the capability number

   A capability has been started.

.. event-type:: CAP_DELETE
   :tag: 46
   :length: fixed

   A capability has been deleted.

.. event-type:: CAP_DISABLE
   :tag: 47
   :length: fixed

   A capability has been disabled.

.. event-type:: CAP_ENABLE
   :tag: 48
   :length: fixed

   A capability has been enabled.

Task events
^^^^^^^^^^^

TODO: What are tasks?

.. event-type:: TASK_CREATE

   :tag: 55
   :length: fixed
   :field TaskId: task id
   :field CapNo: TODO
   :field ThreadId: TODO

   Marks the creation of a task.

.. event-type:: TASK_MIGRATE

   :tag: 56
   :length: fixed
   :field TaskId: task id
   :field CapNo: old capability
   :field CapNo: new capability

   TODO 

Tracing events
^^^^^^^^^^^^^^

.. event-type:: LOG_MSG
   :tag: 16
   :length: variable
   :field String: The message

   A log message from the runtime system.

.. event-type:: BLOCK_MARKER

   :tag: 18
   :length: variable
   :field Word32: size
   :field Word64: end time in nanoseconds
   :field String: marker name

   TODO 

.. event-type:: USER_MSG

   :tag: 19
   :length: variable
   :field String: message

   A user log message (from, e.g., :base-ref:`Control.Concurrent.traceEvent`).

.. event-type:: USER_MARKER

   :tag: 58
   :length: variable
   :field String: marker name

   TODO 


.. _heap-profiler-events:

Heap profiler event log output
------------------------------

The heap profiler can produce output to GHC's event log, allowing samples to
be correlated with other event log events over the program's lifecycle.

This section defines the layout of these events. The ``String`` type below is
defined to be a UTF-8 encoded NUL-terminated string.

Metadata event types
~~~~~~~~~~~~~~~~~~~~

Beginning of sample stream
^^^^^^^^^^^^^^^^^^^^^^^^^^

A single fixed-width event emitted during program start-up describing the samples that follow.

 * ``EVENT_HEAP_PROF_BEGIN``
   * ``Word8``: Profile ID
   * ``Word64``: Sampling period in nanoseconds
   * ``Word32``: Sample break-down type. One of,

      * ``SAMPLE_TYPE_COST_CENTER`` (output from ``-hc``)
      * ``SAMPLE_TYPE_CLOSURE_DESCR`` (output from ``-hd``)
      * ``SAMPLE_TYPE_RETAINER`` (output from ``-hr``)
      * ``SAMPLE_TYPE_MODULE`` (output from ``-hm``)
      * ``SAMPLE_TYPE_TYPE_DESCR`` (output from ``-hy``)
      * ``SAMPLE_TYPE_BIOGRAPHY`` (output from ``-hb``)

   * ``String``: Module filter
   * ``String``: Closure description filter
   * ``String``: Type description filter
   * ``String``: Cost centre filter
   * ``String``: Cost centre stack filter
   * ``String``: Retainer filter
   * ``String``: Biography filter

Cost centre definitions
^^^^^^^^^^^^^^^^^^^^^^^

A variable-length packet produced once for each cost centre,

 * ``EVENT_HEAP_PROF_COST_CENTRE``
   * ``Word32``: cost centre number
   * ``String``: label
   * ``String``: module
   * ``String``: source location
   * ``Word8``: flags

     * bit 0: is the cost-centre a CAF?


Sample event types
~~~~~~~~~~~~~~~~~~

A sample (consisting of a list of break-down classes, e.g. cost centres, and
heap residency sizes), is to be encoded in the body of one or more events.

We mark the beginning of a new sample with an ``EVENT_HEAP_PROF_SAMPLE_BEGIN``
event,

 * ``EVENT_HEAP_PROF_SAMPLE_BEGIN``
   * ``Word64``: sample number

A heap residency census will follow. Since events may only be up to 2^16^ bytes
in length a single sample may need to be split among multiple
``EVENT_HEAP_PROF_SAMPLE`` events. The precise format of the census entries is
determined by the break-down type.


Cost-centre break-down
^^^^^^^^^^^^^^^^^^^^^^

A variable-length packet encoding a heap profile sample broken down by,
 * cost-centre (``-hc``)

 * ``EVENT_HEAP_PROF_SAMPLE_COST_CENTRE``
   * ``Word8``: Profile ID
   * ``Word64``: heap residency in bytes
   * ``Word8``: stack depth
   * ``Word32[]``: cost centre stack starting with inner-most (cost centre numbers)


String break-down
^^^^^^^^^^^^^^^^^

A variable-length event encoding a heap sample broken down by,
 * type description (``-hy``)
 * closure description (``-hd``)
 * module (``-hm``)

 * ``EVENT_HEAP_PROF_SAMPLE_STRING``
   * ``Word8``: Profile ID
   * ``Word64``: heap residency in bytes
   * ``String``: type or closure description, or module name
