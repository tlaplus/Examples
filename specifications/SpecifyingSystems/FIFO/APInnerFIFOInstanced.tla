------------------------ MODULE APInnerFIFOInstanced --------------------------
(* Apalache type annotations for InnerFIFOInstanced.tla, applied via
   INSTANCE so the original spec remains free of tool-specific
   idiosyncrasies. InnerFIFOInstanced is a hand-expanded variant of
   InnerFIFO that does not use the INSTANCE statement (because older
   versions of TLC did not support it). *)

EXTENDS Naturals, Sequences

CONSTANT
  \* @type: Set(MSG);
  Message

VARIABLES
  \* @type: { val: MSG, rdy: Int, ack: Int };
  in,
  \* @type: { val: MSG, rdy: Int, ack: Int };
  out,
  \* @type: Seq(MSG);
  q

INSTANCE InnerFIFOInstanced

\* Concrete value for the constant used by APInnerFIFOInstanced.cfg.
MessageVal == { "m1_OF_MSG", "m2_OF_MSG" }

\* The original `TypeInvariant` includes `q \in Seq(Message)` (an unbounded
\* set Apalache cannot enumerate); replace it with the channel-only checks.
ChannelTypeInvariants ==
  /\ InChan_TypeInvariant
  /\ OutChan_TypeInvariant

==============================================================================
