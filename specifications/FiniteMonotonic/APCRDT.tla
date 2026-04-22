------------------------------- MODULE APCRDT -------------------------------
(* Apalache type annotations for CRDT.tla, applied via INSTANCE so the
   original spec remains free of tool-specific idiosyncrasies. *)

EXTENDS Naturals, FiniteSets

CONSTANT
  \* @type: Set(NODE);
  Node

VARIABLE
  \* @type: NODE -> NODE -> Int;
  counter

INSTANCE CRDT

\* Concrete values for the constants used by APCRDT.cfg.
NodeVal == { "n1_OF_NODE", "n2_OF_NODE", "n3_OF_NODE" }

==============================================================================
