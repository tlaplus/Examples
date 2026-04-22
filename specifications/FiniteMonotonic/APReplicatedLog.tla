--------------------------- MODULE APReplicatedLog ---------------------------
(* Apalache type annotations for ReplicatedLog.tla, applied via INSTANCE so
   the original spec remains free of tool-specific idiosyncrasies. *)

EXTENDS Naturals, Sequences

CONSTANTS
  \* @type: Set(NODE);
  Node,
  \* @type: Set(TX);
  Transaction

VARIABLES
  \* @type: Seq(TX);
  log,
  \* @type: NODE -> Int;
  executed

INSTANCE ReplicatedLog

\* Concrete values for the constants used by APReplicatedLog.cfg.
NodeVal == { "n1_OF_NODE", "n2_OF_NODE" }
TransactionVal == { "t1_OF_TX", "t2_OF_TX" }

==============================================================================
