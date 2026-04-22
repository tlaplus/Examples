---------------------- MODULE APChannel ----------------------
(* Apalache type annotations for FIFO/Channel.tla, applied via INSTANCE so
   the original spec remains free of tool-specific idiosyncrasies. The
   Channel module is duplicated verbatim across the AsynchronousInterface,
   Composing, and FIFO chapter directories of the Specifying Systems
   repository; each chapter's wrapper instantiates the local copy. *)

EXTENDS Naturals

CONSTANT
  \* @type: Set(DATUM);
  Data

VARIABLE
  \* @type: { val: DATUM, rdy: Int, ack: Int };
  chan

INSTANCE Channel

\* Concrete value for the constant used by APChannel.cfg.
DataVal == { "d1_OF_DATUM", "d2_OF_DATUM" }

================================================================
