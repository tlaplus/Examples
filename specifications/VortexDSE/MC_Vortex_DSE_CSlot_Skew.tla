---- MODULE MC_Vortex_DSE_CSlot_Skew ----
(***************************************************************************)
(* TLC harness for Vortex_DSE_CSlot_Skew.                                  *)
(*                                                                          *)
(* MaxSkew is a protocol parameter and stays in the specification: it is    *)
(* the assumption the protocol relies on. MaxSlot is only a horizon for     *)
(* model checking, so it lives here and bounds the actions directly.        *)
(***************************************************************************)
EXTENDS Vortex_DSE_CSlot_Skew

CONSTANT MaxSlot

Slots == 0..MaxSlot

MCTick(n) ==
    /\ node_slot[n] < MaxSlot
    /\ SkewedTick(n)

MCNext ==
    \/ \E id \in MsgIDs, n \in Nodes : Submit(id, n)
    \/ \E n \in Nodes, m \in network : Process(n, m)
    \/ \E n \in Nodes : Crash(n)
    \/ \E n \in Nodes : Rejoin(n)
    \/ \E id \in MsgIDs, k \in Slots : ByzantineInject(id, k)
    \/ \E n \in Nodes : MCTick(n)

MCSpec == Init /\ [][MCNext]_vars

MCTypeInvariant ==
    /\ TypeInvariant
    /\ node_slot \in [Nodes -> Slots]
    /\ \A m \in network : m.cslot \in Slots

====
