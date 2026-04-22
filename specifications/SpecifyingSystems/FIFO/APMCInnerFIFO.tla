--------------------------- MODULE APMCInnerFIFO ----------------------------
(* Apalache type annotations for MCInnerFIFO.tla, applied via INSTANCE so
   the original spec remains free of tool-specific idiosyncrasies.
   MCInnerFIFO is a TLC-style model wrapper around InnerFIFOInstanced that
   adds the bounded-queue constraint `qConstraint == Len(q) <= qLen`. *)

EXTENDS Naturals, Sequences

CONSTANTS
  \* @type: Set(MSG);
  Message,
  \* @type: Int;
  qLen

VARIABLES
  \* @type: { val: MSG, rdy: Int, ack: Int };
  in,
  \* @type: { val: MSG, rdy: Int, ack: Int };
  out,
  \* @type: Seq(MSG);
  q

INSTANCE MCInnerFIFO

\* Concrete value for the constant used by APMCInnerFIFO.cfg.
MessageVal == { "m1_OF_MSG", "m2_OF_MSG", "m3_OF_MSG" }

\* The original `TypeInvariant` references `Seq(Message)` which Apalache
\* cannot enumerate; replace it with the channel-only checks plus a
\* bounded-length check that mirrors `qConstraint`.
ChannelTypeInvariants ==
  /\ InChan_TypeInvariant
  /\ OutChan_TypeInvariant
  /\ Len(q) <= qLen

==============================================================================
