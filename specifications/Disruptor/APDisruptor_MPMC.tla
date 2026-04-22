--------------------------- MODULE APDisruptor_MPMC ---------------------------
(* Apalache type annotations for Disruptor_MPMC.tla, applied via INSTANCE so
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
  next_sequence,
  \* @type: THREAD -> Int;
  claimed_sequence,
  \* @type: Int -> Bool;
  published,
  \* @type: THREAD -> Int;
  read,
  \* @type: THREAD -> Str;
  pc,
  \* @type: THREAD -> Seq(Int);
  consumed

\* The polymorphic helper `Range(f) == { f[x] : x \in DOMAIN(f) }` is shadowed
\* here with a typed monomorphic version because its only uses in this module
\* are on `read` and `claimed_sequence`, both of type THREAD -> Int.
\*
\* Brittle: this trick relies on SANY tolerating a duplicate definition only
\* when the body is identical to the one in `Disruptor_MPMC`. Any change to
\* the body below turns the warning into a hard "Multiple declarations"
\* error.
\* @type: (THREAD -> Int) => Set(Int);
Range(f) == { f[x] : x \in DOMAIN(f) }

INSTANCE Disruptor_MPMC

\* Concrete values for the constants used by APDisruptor_MPMC.cfg.
WritersVal == { "w1_OF_THREAD", "w2_OF_THREAD" }
ReadersVal == { "r1_OF_THREAD", "r2_OF_THREAD" }

==============================================================================
