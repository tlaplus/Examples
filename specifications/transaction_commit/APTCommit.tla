------------------------------ MODULE APTCommit ------------------------------
(* Apalache type annotations for TCommit.tla, applied via INSTANCE so the
   original spec remains free of tool-specific idiosyncrasies. *)

CONSTANT
  \* @type: Set(RM);
  RM

VARIABLE
  \* @type: RM -> Str;
  rmState

INSTANCE TCommit

\* Concrete values for the constants used by APTCommit.cfg.
RMVal == { "r1_OF_RM", "r2_OF_RM", "r3_OF_RM" }

==============================================================================
