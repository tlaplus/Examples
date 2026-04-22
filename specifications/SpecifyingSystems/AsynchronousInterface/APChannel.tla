---------------------- MODULE APChannel ----------------------
(* Apalache type annotations for Channel.tla, applied via INSTANCE so the
   original spec remains free of tool-specific idiosyncrasies. *)

EXTENDS Naturals

CONSTANT
  \* @type: Set(DATUM);
  Data

VARIABLE
  \* @type: { val: DATUM, rdy: Int, ack: Int };
  chan

INSTANCE Channel

\* Concrete values for the constants used by APChannel.cfg.
DataVal == { "d1_OF_DATUM", "d2_OF_DATUM" }

================================================================
