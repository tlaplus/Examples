--------------------------- MODULE APChangRoberts ---------------------------
(* Apalache type annotations for ChangRoberts.tla, applied via INSTANCE so
   the original spec remains free of tool-specific idiosyncrasies. *)

EXTENDS Naturals, Sequences

CONSTANTS
  \* @type: Int;
  N,
  \* @type: Seq(Int);
  Id

VARIABLES
  \* @type: Int -> Set(Int);
  msgs,
  \* @type: Int -> Str;
  pc,
  \* @type: Int -> Bool;
  initiator,
  \* @type: Int -> Str;
  state

INSTANCE ChangRoberts

\* Concrete values for the constants. APChangRoberts.cfg substitutes them
\* via `N <- NVal` and `Id <- IdVal`.
NVal == 3
\* @type: Seq(Int);
IdVal == <<3, 1, 2>>

==============================================================================
