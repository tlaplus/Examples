---- MODULE MC_Vortex_DSE_CSlot_TTL ----
(***************************************************************************)
(* TLC harness for Vortex_DSE_CSlot_TTL.                                   *)
(*                                                                          *)
(* As in MC_Vortex_DSE_CSlot, the slot horizon is a model-checking concern  *)
(* and is imposed inside the actions rather than as a CONSTRAINT, so that   *)
(* no successor state is discarded while temporal properties are checked.   *)
(***************************************************************************)
EXTENDS Vortex_DSE_CSlot_TTL

CONSTANT MaxSlot

Slots == 0..MaxSlot

MCTick ==
    /\ current_slot < MaxSlot
    /\ Tick

MCNext ==
    \/ \E id \in MsgIDs, k \in Slots : Send(id, k)
    \/ \E n \in Nodes, m \in network : Process(n, m)
    \/ \E n \in Nodes : Crash(n)
    \/ \E n \in Nodes : Rejoin(n)
    \/ MCTick

MCSpec == Init /\ [][MCNext]_vars

MCFairness ==
    /\ WF_vars(MCTick)
    /\ \A n \in Nodes : WF_vars(Rejoin(n))

MCLiveSpec == Init /\ [][MCNext]_vars /\ MCFairness

MCTickProgress == <>[](current_slot = MaxSlot)

MCTypeInvariant ==
    /\ TypeInvariant
    /\ current_slot \in Slots
    /\ \A m \in network : m.cslot \in Slots

====
