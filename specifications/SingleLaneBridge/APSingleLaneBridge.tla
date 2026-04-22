------------------------- MODULE APSingleLaneBridge -------------------------
(* Apalache type annotations for SingleLaneBridge.tla, applied via INSTANCE
   so the original spec remains free of tool-specific idiosyncrasies. *)

EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
  \* @type: Set(CAR);
  CarsRight,
  \* @type: Set(CAR);
  CarsLeft,
  \* @type: Set(Int);
  Bridge,
  \* @type: Set(Int);
  Positions

VARIABLES
  \* @type: CAR -> Int;
  Location,
  \* @type: Seq(CAR);
  WaitingBeforeBridge

INSTANCE SingleLaneBridge

\* Concrete values for the constants used by APSingleLaneBridge.cfg.
CarsRightVal == { "r1_OF_CAR", "r2_OF_CAR" }
CarsLeftVal == { "l1_OF_CAR", "l2_OF_CAR" }
PositionsVal == 1..6
BridgeVal == 3..4


==============================================================================
