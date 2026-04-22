------------------------- MODULE APcf1s_folklore -------------------------
(* Apalache type annotations for cf1s_folklore.tla, applied via INSTANCE so
   the original spec remains free of tool-specific idiosyncrasies. *)

EXTENDS Naturals, FiniteSets

CONSTANTS
  \* @type: Int;
  N,
  \* @type: Int;
  T,
  \* @type: Int;
  F

VARIABLES
  \* @type: Int;
  nSnt0,
  \* @type: Int;
  nSnt1,
  \* @type: Int;
  nSnt0F,
  \* @type: Int;
  nSnt1F,
  \* @type: Int;
  nFaulty,
  \* @type: Int -> Str;
  pc,
  \* @type: Int -> Int;
  nRcvd0,
  \* @type: Int -> Int;
  nRcvd1

INSTANCE cf1s_folklore

==========================================================================
