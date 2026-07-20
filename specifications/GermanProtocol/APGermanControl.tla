--------------------------- MODULE APGermanControl ---------------------------
(* Apalache type annotations for GermanControl.tla, applied via INSTANCE so
   the original spec remains free of tool-specific idiosyncrasies.

   Nodes are modelled as an uninterpreted Apalache type (NODE); the NoNode
   sentinel shares that type so that `curPtr \in NODE \cup {NoNode}` is well
   typed.

   Run bounded model checking for executions of at most 20 Next steps with:
     apalache-mc check --config=APGermanControl.cfg --length=20 APGermanControl.tla
   This completes in about 4 minutes on a 2021 M1 MacBook.
*)

CONSTANTS
  \* @type: Set(NODE);
  NODE,
  \* @type: NODE;
  NoNode

VARIABLES
  \* @type: NODE -> Str;
  cache,
  \* @type: NODE -> Str;
  chan1,
  \* @type: NODE -> Str;
  chan2,
  \* @type: NODE -> Str;
  chan3,
  \* @type: Set(NODE);
  invSet,
  \* @type: Set(NODE);
  shrSet,
  \* @type: Bool;
  exGntd,
  \* @type: Str;
  curCmd,
  \* @type: NODE;
  curPtr

INSTANCE GermanControl

\* Concrete values for the constants used by APGermanControl.cfg.
NodeVal   == { "n1_OF_NODE", "n2_OF_NODE" }
NoNodeVal == "noNode_OF_NODE"

==============================================================================
