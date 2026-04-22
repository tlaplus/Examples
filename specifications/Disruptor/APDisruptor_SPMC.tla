--------------------------- MODULE APDisruptor_SPMC ---------------------------
(* Apalache type annotations for Disruptor_SPMC.tla, applied via INSTANCE so
   the original spec remains free of tool-specific idiosyncrasies. *)

EXTENDS Integers, FiniteSets, Sequences

CONSTANTS
  \* @type: Int;
  MaxPublished,
  \* @type: Set(THREAD);
  Writers,
  \* @type: Set(THREAD);
  Readers,
  \* @type: Int;
  Size,
  \* @type: Int;
  NULL

VARIABLES
  \* @type: { slots: Int -> Int, readers: Int -> Set(THREAD), writers: Int -> Set(THREAD) };
  ringbuffer,
  \* @type: Int;
  published,
  \* @type: THREAD -> Int;
  read,
  \* @type: THREAD -> Str;
  pc,
  \* @type: THREAD -> Seq(Int);
  consumed

\* The polymorphic helper `Range(f) == { f[x] : x \in DOMAIN(f) }` is shadowed
\* here with a typed monomorphic version because its only use in this module
\* is on `read`, a function from THREAD to Int.
\*
\* Brittle: this trick relies on SANY tolerating a duplicate definition only
\* when the body is identical to the one in `Disruptor_SPMC`. Any change to
\* the body below turns the warning into a hard "Multiple declarations"
\* error.
\* @type: (THREAD -> Int) => Set(Int);
Range(f) == { f[x] : x \in DOMAIN(f) }

INSTANCE Disruptor_SPMC

\* Concrete values for the constants used by APDisruptor_SPMC.cfg.
WritersVal == { "w_OF_THREAD" }
ReadersVal == { "r1_OF_THREAD", "r2_OF_THREAD" }

==============================================================================
