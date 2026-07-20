------------------------ MODULE APGermanCMPWithMutex ------------------------
(* Apalache type annotations for GermanCMPWithMutex.tla, applied via INSTANCE so the
   original spec remains free of tool-specific idiosyncrasies.

   Nodes are modelled as an uninterpreted Apalache type (NODE); the abstract
   environment node Other and the NoNode sentinel share that type so that
   `curPtr \in NODE \cup {Other, NoNode}` is well typed.

   Run bounded model checking for executions of at most 20 Next steps with:
     apalache-mc check --config=APGermanCMPWithMutex.cfg --length=20 APGermanCMPWithMutex.tla
   This completes in about 20 minutes on a 2021 M1 MacBook.
*)

CONSTANTS
  \* @type: Set(NODE);
  NODE,
  \* @type: NODE;
  Other,
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

INSTANCE GermanCMPWithMutex

\* Concrete values for the constants used by APGermanCMPWithMutex.cfg.
NodeVal   == { "n1_OF_NODE", "n2_OF_NODE" }
OtherVal  == "other_OF_NODE"
NoNodeVal == "noNode_OF_NODE"

==============================================================================
