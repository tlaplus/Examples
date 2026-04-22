----------------------------- MODULE APstages -----------------------------
(* Apalache type annotations for stages.tla, applied via INSTANCE so the
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
  hybrid,
  \* @type: Str;
  stage,
  \* @type: Int;
  cycle

INSTANCE stages

==========================================================================
