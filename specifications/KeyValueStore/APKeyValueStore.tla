--------------------------- MODULE APKeyValueStore ---------------------------
(* Apalache type annotations for KeyValueStore.tla, applied via INSTANCE so
   the original spec remains free of tool-specific idiosyncrasies. *)

CONSTANTS
  \* @type: Set(KEY);
  Key,
  \* @type: Set(VAL);
  Val,
  \* @type: Set(TX);
  TxId

VARIABLES
  \* @type: KEY -> VAL;
  store,
  \* @type: Set(TX);
  tx,
  \* @type: TX -> KEY -> VAL;
  snapshotStore,
  \* @type: TX -> Set(KEY);
  written,
  \* @type: TX -> Set(KEY);
  missed

INSTANCE KeyValueStore

\* Concrete values for the constants used by APKeyValueStore.cfg.
KeyVal == { "k1_OF_KEY", "k2_OF_KEY" }
ValVal == { "v1_OF_VAL", "v2_OF_VAL" }
TxIdVal == { "t1_OF_TX", "t2_OF_TX" }

==============================================================================
