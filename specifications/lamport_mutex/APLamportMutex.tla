--------------------------- MODULE APLamportMutex ---------------------------
(* Apalache type annotations for LamportMutex.tla, applied via INSTANCE so
   the original spec remains free of tool-specific idiosyncrasies. *)

EXTENDS Naturals, Sequences

CONSTANT
  \* @type: Int;
  N,
  \* @type: Int;
  maxClock

VARIABLES
  \* @type: Int -> Int;
  clock,
  \* @type: Int -> (Int -> Int);
  req,
  \* @type: Int -> Set(Int);
  ack,
  \* @type: Int -> (Int -> Seq({ type: Str, clock: Int }));
  network,
  \* @type: Set(Int);
  crit

INSTANCE LamportMutex

==============================================================================
