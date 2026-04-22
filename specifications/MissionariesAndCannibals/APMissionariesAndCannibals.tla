--------------- MODULE APMissionariesAndCannibals ---------------
(* Apalache type annotations for MissionariesAndCannibals.tla, applied via
   INSTANCE so the original spec remains free of tool-specific
   idiosyncrasies. *)

EXTENDS Integers, FiniteSets

CONSTANTS
  \* @type: Set(PERSON);
  Missionaries,
  \* @type: Set(PERSON);
  Cannibals

VARIABLES
  \* @type: Str;
  bank_of_boat,
  \* @type: Str -> Set(PERSON);
  who_is_on_bank

INSTANCE MissionariesAndCannibals

\* Concrete values for the constants used by APMissionariesAndCannibals.cfg.
MissionariesVal == { "m1_OF_PERSON", "m2_OF_PERSON", "m3_OF_PERSON" }
CannibalsVal == { "c1_OF_PERSON", "c2_OF_PERSON", "c3_OF_PERSON" }

==============================================================================
