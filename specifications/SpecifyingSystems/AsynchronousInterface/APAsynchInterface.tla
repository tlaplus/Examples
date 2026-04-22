------------------ MODULE APAsynchInterface ---------------------
(* Apalache type annotations for AsynchInterface.tla, applied via INSTANCE
   so the original spec remains free of tool-specific idiosyncrasies. *)

EXTENDS Naturals

CONSTANT
  \* @type: Set(DATUM);
  Data

VARIABLES
  \* @type: DATUM;
  val,
  \* @type: Int;
  rdy,
  \* @type: Int;
  ack

INSTANCE AsynchInterface

\* Concrete values for the constants used by APAsynchInterface.cfg.
DataVal == { "d1_OF_DATUM", "d2_OF_DATUM" }

================================================================
