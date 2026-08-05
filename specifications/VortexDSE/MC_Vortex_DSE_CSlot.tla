---- MODULE MC_Vortex_DSE_CSlot ----
(***************************************************************************)
(* TLC harness for Vortex_DSE_CSlot.                                       *)
(*                                                                          *)
(* The specification has no slot horizon: Tick is unbounded and the        *)
(* adversary may forge any slot in Nat. The horizon is a model-checking    *)
(* concern and lives here.                                                  *)
(*                                                                          *)
(* It is imposed inside MCTick rather than as a state CONSTRAINT. A         *)
(* constraint was tried first, as the review guidelines prefer, but TLC     *)
(* evaluates invariants on the state that crosses the boundary before the   *)
(* constraint discards it: with MaxSlot = 2 a Tick produces current_slot =  *)
(* 3, and any invariant mentioning the horizon fails there. Bounding the    *)
(* ticker instead keeps the reachable graph inside the horizon.             *)
(*                                                                          *)
(* It also avoids a second problem in the liveness model, where discarding  *)
(* successor states can mask or invent violations of temporal properties.   *)
(*                                                                          *)
(* MCNext restricts the forged slot as well, because TLC cannot enumerate   *)
(* Nat.                                                                     *)
(***************************************************************************)
EXTENDS Vortex_DSE_CSlot

CONSTANT MaxSlot

ASSUME MaxSlotAssumption == MaxSlot \in Nat

Slots == 0..MaxSlot

MCMsgRecord == [id: MsgIDs, cslot: Slots]

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

\* Type correctness within the horizon. TLC cannot evaluate the
\* specification's own TypeInvariant, whose MsgRecord ranges over Nat.
MCTypeInvariant ==
    /\ current_slot \in Slots
    /\ network      \subseteq MCMsgRecord
    /\ processed    \in [Nodes -> SUBSET MsgIDs]
    /\ persisted    \in [Nodes -> SUBSET MsgIDs]
    /\ node_state   \in [Nodes -> {Up, Down}]

-------------------------------------------------------------------------------
(*                            LIVENESS HARNESS                              *)

\* Strong fairness on Process is necessary, not decorative: with weak
\* fairness the liveness model reports a temporal-property violation,
\* because a crash intermittently disables Process.
MCFairness ==
    /\ WF_vars(MCTick)
    /\ \A n \in Nodes : WF_vars(Rejoin(n))
    /\ \A n \in Nodes : SF_vars(\E m \in network : Process(n, m))

MCLiveSpec == Init /\ [][MCNext]_vars /\ MCFairness

\* Bounded counterpart of TickProgress, strengthened as suggested: once the
\* ticker reaches the horizon MCTick is permanently disabled, so the slot
\* counter stays there rather than merely visiting it.
MCTickProgress == <>[](current_slot = MaxSlot)

====
