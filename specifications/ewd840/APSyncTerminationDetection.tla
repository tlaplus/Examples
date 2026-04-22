--------------------- MODULE APSyncTerminationDetection ---------------------
(* Apalache type annotations for SyncTerminationDetection.tla, applied via
   INSTANCE so the original spec remains free of tool-specific
   idiosyncrasies. *)

EXTENDS Naturals

CONSTANT
  \* @type: Int;
  N

VARIABLES
  \* @type: Int -> Bool;
  active,
  \* @type: Bool;
  terminationDetected

INSTANCE SyncTerminationDetection

==============================================================================
