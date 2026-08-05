---------------- MODULE MC_Vortex_DSE_CSlot_AE ----------------
(***************************************************************************)
(* Harness for Vortex_DSE_CSlot_AE, used by both TLC and Apalache.         *)
(*                                                                          *)
(* The specification has no slot horizon; NextCslot advances without bound  *)
(* and DuplicateInject may forge any slot in Nat. The horizon is a          *)
(* model-checking concern and is imposed here inside the actions, not as a  *)
(* CONSTRAINT, so no successor state is discarded while temporal properties *)
(* are checked.                                                             *)
(*                                                                          *)
(* Invariants are deliberately left separate rather than bundled into one   *)
(* conjunction, so that a checker reports which one was violated.           *)
(***************************************************************************)
EXTENDS Vortex_DSE_CSlot_AE

CONSTANT MaxSlot

Slots == 0..MaxSlot

MCNextCslot ==
    /\ current_slot < MaxSlot
    /\ NextCslot

MCNext ==
    \/ \E id \in MsgIDs : Submit(id)
    \/ \E n \in Nodes, m \in network : Process(n, m)
    \/ \E n \in Nodes : Freeze(n)
    \/ Reconcile
    \/ \E id \in MsgIDs, k \in Slots : DuplicateInject(id, k)
    \/ MCNextCslot

MCSpec == Init /\ [][MCNext]_vars

MCFairness ==
    /\ SF_vars(Reconcile)
    /\ SF_vars(MCNextCslot)
    /\ \A n \in Nodes : WF_vars(Freeze(n))

MCLiveSpec == Init /\ [][MCNext]_vars /\ MCFairness

MCTypeInvariant ==
    /\ TypeInvariant
    /\ current_slot \in Slots
    /\ \A m \in network : m.cslot \in Slots

\* Apalache entry point: constants fixed symbolically.
ConstInit ==
    /\ Nodes   = {"n1", "n2"}
    /\ MsgIDs  = {"a", "b"}
    /\ MaxSlot = 1

===============================================================
