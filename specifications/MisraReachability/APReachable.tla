----------------------------- MODULE APReachable -----------------------------
(* Apalache type annotations for Reachable.tla, applied via INSTANCE so the
   original spec remains free of tool-specific idiosyncrasies. *)

EXTENDS Integers, FiniteSets

CONSTANT
  \* @type: Set(NODE);
  Nodes,
  \* @type: NODE -> Set(NODE);
  Succ,
  \* @type: NODE;
  Root

VARIABLES
  \* @type: Set(NODE);
  marked,
  \* @type: Set(NODE);
  vroot,
  \* @type: Str;
  pc

INSTANCE Reachable WITH Nodes <- Nodes, Succ <- Succ, Root <- Root

\* Concrete values for the constants used by APReachable.cfg.
NodesVal == { "n1_OF_NODE", "n2_OF_NODE", "n3_OF_NODE" }
\* @type: NODE -> Set(NODE);
SuccVal == [ n \in NodesVal |-> NodesVal \ {n} ]
RootVal == "n1_OF_NODE"

==============================================================================
