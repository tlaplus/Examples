----------------------------- MODULE APGerman -----------------------------
(* Apalache type annotations for German.tla, applied via INSTANCE so the
   original spec remains free of tool-specific idiosyncrasies.

   Nodes are modelled as an uninterpreted Apalache type (NODE); the abstract
   environment node Other and the NoNode sentinel share that type so that
   `curPtr \in NODE \cup {Other, NoNode}` is well typed. *)

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
  \* @type: NODE -> Bool;
  invSet,
  \* @type: NODE -> Bool;
  shrSet,
  \* @type: Bool;
  exGntd,
  \* @type: Str;
  curCmd,
  \* @type: NODE;
  curPtr

INSTANCE German

\* Concrete values for the constants used by APGerman.cfg.
NodeVal   == { "n1_OF_NODE", "n2_OF_NODE" }
OtherVal  == "other_OF_NODE"
NoNodeVal == "noNode_OF_NODE"

==============================================================================
