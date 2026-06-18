------------------------- MODULE APGermanCoherence -------------------------
(* Apalache type annotations for GermanCoherence.tla, applied via INSTANCE so
   the original spec remains free of tool-specific idiosyncrasies.

   Nodes are modelled as an uninterpreted Apalache type (NODE); the NoNode
   sentinel shares that type so that `curPtr \in NODE \cup {NoNode}` is well
   typed. *)

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

INSTANCE GermanCoherence

\* Concrete values for the constants used by APGermanCoherence.cfg.
NodeVal   == { "n1_OF_NODE", "n2_OF_NODE" }
NoNodeVal == "noNode_OF_NODE"

==============================================================================
