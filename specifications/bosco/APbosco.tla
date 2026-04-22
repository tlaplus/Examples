------------------------------- MODULE APbosco -------------------------------
(* Apalache type annotations for bosco.tla, applied via INSTANCE so the
   original spec remains free of tool-specific idiosyncrasies. *)

EXTENDS Naturals, FiniteSets

CONSTANTS
  \* @type: Int;
  N,
  \* @type: Int;
  T,
  \* @type: Int;
  F

VARIABLES
  \* @type: Int -> Str;
  pc,
  \* @type: Int -> Set(<<Int, Str>>);
  rcvd,
  \* @type: Set(<<Int, Str>>);
  sent

INSTANCE bosco

================================================================================
