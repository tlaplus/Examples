--------------------------- MODULE APnbacg_guer01 ---------------------------
(* Apalache type annotations for nbacg_guer01.tla, applied via INSTANCE so
   the original spec remains free of tool-specific idiosyncrasies. *)

EXTENDS Naturals, FiniteSets

CONSTANTS
  \* @type: Int;
  N

VARIABLES
  \* @type: Int;
  nSntNo,
  \* @type: Int;
  nSntYes,
  \* @type: Int;
  nSntNoF,
  \* @type: Int;
  nSntYesF,
  \* @type: Int -> Int;
  nRcvdYes,
  \* @type: Int -> Int;
  nRcvdNo,
  \* @type: Int -> Bool;
  someFail,
  \* @type: Int -> Str;
  pc

INSTANCE nbacg_guer01

==========================================================================
