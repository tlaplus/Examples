---- MODULE APPrisoner ----
(* Apalache type annotations for Prisoner.tla, applied via INSTANCE so the
   original spec remains free of tool-specific idiosyncrasies. *)

EXTENDS FiniteSets, Naturals

CONSTANTS
  \* @type: Set(PRISONER);
  Prisoner,
  \* @type: Bool;
  Light_Unknown

VARIABLES
  \* @type: Int;
  count,
  \* @type: Bool;
  announced,
  \* @type: PRISONER -> Int;
  signalled,
  \* @type: Str;
  light,
  \* @type: Set(PRISONER);
  has_visited

INSTANCE Prisoner

\* Concrete values for the constants used by APPrisoner.cfg.
PrisonerVal == { "Alice_OF_PRISONER", "Bob_OF_PRISONER", "Eve_OF_PRISONER" }

====
