----------------------------- MODULE APPrisoners -----------------------------
(* Apalache type annotations for Prisoners.tla, applied via INSTANCE so the
   original spec remains free of tool-specific idiosyncrasies. *)

EXTENDS Naturals, FiniteSets

CONSTANTS
  \* @type: Set(PRISONER);
  Prisoner,
  \* @type: PRISONER;
  Counter

VARIABLES
  \* @type: Bool;
  switchAUp,
  \* @type: Bool;
  switchBUp,
  \* @type: PRISONER -> Int;
  timesSwitched,
  \* @type: Int;
  count

INSTANCE Prisoners

\* Concrete values for the constants used by APPrisoners.cfg.
PrisonerVal == { "p1_OF_PRISONER", "p2_OF_PRISONER", "p3_OF_PRISONER" }
CounterVal == "p1_OF_PRISONER"

==============================================================================
