------------------------------- MODULE APtcp ----------------------------------
(* Apalache type annotations for tcp.tla, applied via INSTANCE so the
   original spec remains free of tool-specific idiosyncrasies. *)

EXTENDS Integers, Sequences, SequencesExt, FiniteSets

CONSTANT
  \* @type: Set(PEER);
  Peers

VARIABLE
  \* @type: PEER -> Bool;
  tcb,
  \* @type: PEER -> Str;
  connstate,
  \* @type: PEER -> Seq(Str);
  network

INSTANCE tcp

\* Concrete values for the constants used by APtcp.cfg.
PeersVal == { "p1_OF_PEER", "p2_OF_PEER" }

==============================================================================
