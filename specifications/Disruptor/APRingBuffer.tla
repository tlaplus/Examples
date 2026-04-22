----------------------------- MODULE APRingBuffer ----------------------------
(* Apalache type annotations for RingBuffer.tla, applied via INSTANCE so the
   original spec remains free of tool-specific idiosyncrasies. RingBuffer is
   also exercised indirectly via APDisruptor_SPMC and APDisruptor_MPMC; this
   wrapper checks the helper module on its own. *)

EXTENDS Integers, FiniteSets

CONSTANTS
  \* @type: Int;
  Size,
  \* @type: Set(THREAD);
  Readers,
  \* @type: Set(THREAD);
  Writers,
  \* @type: Set(Int);
  Values,
  \* @type: Int;
  NULL

VARIABLE
  \* @type: { slots: Int -> Int, readers: Int -> Set(THREAD), writers: Int -> Set(THREAD) };
  ringbuffer

INSTANCE RingBuffer

\* The original `RingBuffer` is a helper module that only defines `Init`
\* plus the parameterised actions `Write`, `EndWrite`, `BeginRead`,
\* `EndRead`; it intentionally does not define a `Next`. The concrete
\* protocol (e.g. `Disruptor_SPMC`) is responsible for ensuring that
\* `NoDataRaces` is preserved. There is therefore no `.cfg` for this
\* wrapper -- run `apalache-mc typecheck APRingBuffer.tla` only.

==============================================================================
