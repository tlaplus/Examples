---- MODULE MC_Vortex_DSE_CSlot ----
(***************************************************************************)
(* TLC harness for Vortex_DSE_CSlot.                                       *)
(*                                                                          *)
(* The specification itself has no slot horizon: Tick is unbounded and      *)
(* DuplicateInject may forge any slot in Nat. The horizon is a             *)
(* model-checking concern and lives here.                                   *)
(*                                                                          *)
(* It is imposed inside the actions rather than as a CONSTRAINT, so the    *)
(* state graph is genuinely finite rather than merely truncated. That      *)
(* matters for the liveness model: under a state constraint TLC discards   *)
(* successor states, which can mask or invent violations of temporal       *)
(* properties.                                                              *)
(***************************************************************************)
EXTENDS Vortex_DSE_CSlot

CONSTANT MaxSlot

Slots == 0..MaxSlot

\* The ticker stops at the horizon.
MCTick ==
    /\ current_slot < MaxSlot
    /\ Tick

MCNext ==
    \/ \E id \in MsgIDs : Submit(id)
    \/ \E n \in Nodes, m \in network : Process(n, m)
    \/ \E n \in Nodes : Crash(n)
    \/ \E n \in Nodes : Rejoin(n)
    \/ \E id \in MsgIDs, k \in Slots : DuplicateInject(id, k)
    \/ MCTick

MCSpec == Init /\ [][MCNext]_vars

MCFairness ==
    /\ WF_vars(MCTick)
    /\ \A n \in Nodes : WF_vars(Rejoin(n))
    /\ \A n \in Nodes : SF_vars(\E m \in network : Process(n, m))

MCLiveSpec == Init /\ [][MCNext]_vars /\ MCFairness

\* Bounded counterpart of TickProgress, strengthened as suggested: once the
\* ticker reaches the horizon MCTick is permanently disabled, so the slot
\* counter stays there rather than merely visiting it.
MCTickProgress == <>[](current_slot = MaxSlot)

\* Everything reachable in this model lies within the horizon.
MCTypeInvariant ==
    /\ TypeInvariant
    /\ current_slot \in Slots
    /\ \A m \in network : m.cslot \in Slots

====
