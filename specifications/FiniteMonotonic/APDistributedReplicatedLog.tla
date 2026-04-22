--------------------- MODULE APDistributedReplicatedLog ---------------------
(* Apalache type annotations for DistributedReplicatedLog.tla, applied via
   INSTANCE so the original spec remains free of tool-specific
   idiosyncrasies. *)

EXTENDS Sequences, SequencesExt, Integers, FiniteSets, FiniteSetsExt

CONSTANT
  \* @type: Int;
  Lag,
  \* @type: Set(SERVER);
  Servers,
  \* @type: Set(VAL);
  Values

VARIABLE
  \* @type: SERVER -> Seq(VAL);
  cLogs

\* @type: <<SERVER -> Seq(VAL)>>;
vars == <<cLogs>>

INSTANCE DistributedReplicatedLog

\* Concrete values for the constants used by APDistributedReplicatedLog.cfg.
ServersVal == { "s1_OF_SERVER", "s2_OF_SERVER" }
ValuesVal == { "v1_OF_VAL", "v2_OF_VAL" }

==============================================================================
