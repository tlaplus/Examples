----------------------------- MODULE APclean -----------------------------
(* Apalache type annotations for clean.tla, applied via INSTANCE so the
   original spec remains free of tool-specific idiosyncrasies. *)

EXTENDS Naturals

CONSTANTS
  \* @type: Int;
  DNA,
  \* @type: Int;
  PRIMER

VARIABLES
  \* @type: Str;
  tee,
  \* @type: Int;
  primer,
  \* @type: Int;
  dna,
  \* @type: Int;
  template,
  \* @type: Int;
  hybrid

INSTANCE clean

==========================================================================
