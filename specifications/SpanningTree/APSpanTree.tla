------------------------------ MODULE APSpanTree ------------------------------
(* Apalache type annotations for SpanTree.tla, applied via INSTANCE so the
   original spec remains free of tool-specific idiosyncrasies. *)

EXTENDS Integers, FiniteSets

CONSTANTS
  \* @type: Set(NODE);
  Nodes,
  \* @type: Set(Set(NODE));
  Edges,
  \* @type: NODE;
  Root,
  \* @type: Int;
  MaxCardinality

VARIABLES
  \* @type: NODE -> NODE;
  mom,
  \* @type: NODE -> Int;
  dist

INSTANCE SpanTree

\* Concrete values for the constants used by APSpanTree.cfg.
NodesVal == { "n1_OF_NODE", "n2_OF_NODE", "n3_OF_NODE" }
\* @type: Set(Set(NODE));
EdgesVal == { {"n1_OF_NODE", "n2_OF_NODE"}, {"n2_OF_NODE", "n3_OF_NODE"} }
RootVal == "n1_OF_NODE"

==============================================================================
