------------------------------ MODULE APEWD840 ------------------------------
(* Apalache type annotations for EWD840.tla, applied via INSTANCE so the
   original spec remains free of tool-specific idiosyncrasies. *)

EXTENDS Naturals

CONSTANT
  \* @type: Int;
  N

VARIABLES
  \* @type: Int -> Bool;
  active,
  \* @type: Int -> Str;
  color,
  \* @type: Int;
  tpos,
  \* @type: Str;
  tcolor

INSTANCE EWD840

==============================================================================
