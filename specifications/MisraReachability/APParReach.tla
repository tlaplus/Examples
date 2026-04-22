----------------------------- MODULE APParReach -----------------------------
(* Apalache type annotations for ParReach.tla, applied via INSTANCE so the
   original spec remains free of tool-specific idiosyncrasies. *)

EXTENDS Integers, FiniteSets

CONSTANT
  \* @type: Set(NODE);
  Nodes,
  \* @type: NODE -> Set(NODE);
  Succ,
  \* @type: NODE;
  Root,
  \* @type: Set(PROC);
  Procs

VARIABLES
  \* @type: Set(NODE);
  marked,
  \* @type: Set(NODE);
  vroot,
  \* @type: PROC -> Str;
  pc,
  \* @type: PROC -> NODE;
  u,
  \* @type: PROC -> Set(NODE);
  toVroot

INSTANCE ParReach
  WITH Nodes <- Nodes, Succ <- Succ, Root <- Root, Procs <- Procs

\* Concrete values for the constants used by APParReach.cfg.
NodesVal == { "n1_OF_NODE", "n2_OF_NODE", "n3_OF_NODE" }
\* @type: NODE -> Set(NODE);
SuccVal == [ n \in NodesVal |-> NodesVal \ {n} ]
RootVal == "n1_OF_NODE"
ProcsVal == { "p1_OF_PROC", "p2_OF_PROC" }

==============================================================================
