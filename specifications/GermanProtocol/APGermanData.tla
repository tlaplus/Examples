----------------------------- MODULE APGermanData -----------------------------
(* Apalache type annotations for GermanData.tla, applied via INSTANCE so
   the original spec remains free of tool-specific idiosyncrasies.

   Nodes and data values are modelled as uninterpreted Apalache types (NODE,
   DATA).  The NoNode / NoData sentinels share those types so that the union
   sets in TypeOK are well typed.  Only the safety invariants are checked;
   Apalache does not verify the liveness properties (FairSpec) of the spec.

   Run bounded model checking for executions of at most 10 Next steps with:
     apalache-mc check --config=APGermanData.cfg --length=10 APGermanData.tla
   This completes in about 20 seconds on a 2021 M1 MacBook; length 20 takes
   over 1.5 hours.
*)

CONSTANTS
  \* @type: Set(NODE);
  NODE,
  \* @type: Set(DATA);
  DATA,
  \* @type: DATA;
  NoData,
  \* @type: NODE;
  NoNode

VARIABLES
  \* @type: NODE -> { state: Str, data: DATA };
  cache,
  \* @type: NODE -> { cmd: Str, data: DATA };
  chan1,
  \* @type: NODE -> { cmd: Str, data: DATA };
  chan2,
  \* @type: NODE -> { cmd: Str, data: DATA };
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
  curPtr,
  \* @type: DATA;
  memData,
  \* @type: DATA;
  auxData

INSTANCE GermanData

\* Concrete values for the constants used by APGermanData.cfg.
NodeVal   == { "n1_OF_NODE", "n2_OF_NODE" }
DataVal   == { "d1_OF_DATA", "d2_OF_DATA" }
NoDataVal == "noData_OF_DATA"
NoNodeVal == "noNode_OF_NODE"

==============================================================================
