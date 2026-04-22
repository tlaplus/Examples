------------------------------ MODULE APMajority ------------------------------
(* Apalache type annotations for Majority.tla, applied via INSTANCE so the
   original spec remains free of tool-specific idiosyncrasies. *)

EXTENDS Integers, Sequences, FiniteSets

CONSTANT
  \* @type: Set(VAL);
  Value

VARIABLES
  \* @type: Seq(VAL);
  seq,
  \* @type: Int;
  i,
  \* @type: VAL;
  cand,
  \* @type: Int;
  cnt

INSTANCE Majority

\* Concrete values for the constants used by APMajority.cfg.
ValueVal == { "a_OF_VAL", "b_OF_VAL" }

==============================================================================
