-------------------- MODULE Vortex_DSE_CSlot_AE_Proofs --------------------
(***************************************************************************)
(* TLAPS target: Vortex_DSE_CSlot_AE (per-slot Merkle agreement layer).     *)
(*                                                                          *)
(* Public bundle today: TLC + Apalache (bounded). This module is the       *)
(* deductive upgrade — see TLAPS_NEXT.md for scope and theorem order.       *)
(*                                                                          *)
(* Scaffold status: TypeInvariant proof structure started; remaining        *)
(* obligations require TLAPS on a developer machine (tlapm not in CI here). *)
(***************************************************************************)

EXTENDS Vortex_DSE_CSlot_AE, TLAPS

ASSUME MaxSlotType == MaxSlot \in Nat

-------------------------------------------------------------------------------
(*                  PART A — TYPE INVARIANT                                 *)

LEMMA InitType == Init => TypeInvariant
  BY MaxSlotType DEF Init, TypeInvariant, MsgRecord

LEMMA NextType == TypeInvariant /\ [Next]_vars => TypeInvariant'
  <1> USE MaxSlotType DEF TypeInvariant, MsgRecord, vars
  <1> SUFFICES ASSUME TypeInvariant, [Next]_vars
               PROVE  TypeInvariant'
      OBVIOUS
  <1>1. CASE \E id \in MsgIDs : Submit(id)
        BY <1>1 DEF Submit
  <1>2. CASE \E n \in Nodes, m \in network : Process(n, m)
        BY <1>2 DEF Process
  <1>3. CASE \E n \in Nodes : Freeze(n)
        BY <1>3 DEF Freeze
  <1>4. CASE Reconcile
        BY <1>4 DEF Reconcile
  <1>5. CASE \E id \in MsgIDs, k \in 0..MaxSlot : DuplicateInject(id, k)
        BY <1>5 DEF DuplicateInject
  <1>6. CASE NextCslot
        BY <1>6 DEF NextCslot
  <1>7. CASE UNCHANGED vars
        BY <1>7
  <1>8. QED
        BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7 DEF Next

THEOREM TypeCorrect == Spec => []TypeInvariant
  <1>1. Init => TypeInvariant
        BY InitType
  <1>2. TypeInvariant /\ [Next]_vars => TypeInvariant'
        BY NextType
  <1>3. QED
        BY <1>1, <1>2, PTL DEF Spec

-------------------------------------------------------------------------------
(*                  PART B — MERKLE AGREEMENT (headline)                  *)
(* OPEN: MerkleAgreement is not inductive alone; expect strengthening with  *)
(* CommittedSupersetsProcessed and/or phase synchronization lemmas.        *)

\* THEOREM MerkleAgreementAlways == Spec => []MerkleAgreement

=============================================================================
