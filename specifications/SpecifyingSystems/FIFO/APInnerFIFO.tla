---------------------------- MODULE APInnerFIFO -------------------------------
(* Apalache type annotations for InnerFIFO.tla, applied via INSTANCE so the
   original spec remains free of tool-specific idiosyncrasies. *)

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

INSTANCE InnerFIFO

\* Concrete values for the constants used by APInnerFIFO.cfg.
MessageVal == { "m1_OF_MSG", "m2_OF_MSG" }

\* Channel-level invariant that excludes `q \in Seq(Message)` (an unbounded
\* set Apalache cannot enumerate) but keeps the channel record checks.
ChannelTypeInvariants ==
  /\ InChan!TypeInvariant
  /\ OutChan!TypeInvariant

==============================================================================
