------------------------------ MODULE APbcastFolklore ------------------------------
(* Apalache type annotations for bcastFolklore.tla, applied via INSTANCE
   so the original spec remains free of tool-specific idiosyncrasies. *)

EXTENDS Naturals

CONSTANTS
  \* @type: Int;
  N,
  \* @type: Int;
  T,
  \* @type: Int;
  F

VARIABLES
  \* @type: Set(Int);
  Corr,
  \* @type: Int;
  nCrashed,
  \* @type: Int -> Str;
  pc,
  \* @type: Int -> Set(<<Int, Str>>);
  rcvd,
  \* @type: Set(<<Int, Str>>);
  sent

INSTANCE bcastFolklore

=============================================================================
