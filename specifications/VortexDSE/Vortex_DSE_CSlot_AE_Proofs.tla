-------------------- MODULE Vortex_DSE_CSlot_AE_Proofs --------------------
(***************************************************************************)
(* TLAPS target: Vortex_DSE_CSlot_AE (per-slot Merkle agreement layer).     *)
(*                                                                          *)
(* Deductive counterpart to the TLC models in this directory.              *)
(***************************************************************************)

EXTENDS Vortex_DSE_CSlot_AE, TLAPS


-------------------------------------------------------------------------------
(*                  PART A — TYPE INVARIANT                                 *)

LEMMA InitType == Init => TypeInvariant
  BY DEF Init, TypeInvariant, MsgRecord

LEMMA NextType == TypeInvariant /\ [Next]_vars => TypeInvariant'
  BY DEF TypeInvariant, MsgRecord, vars, Next,
         Send, Process, Freeze, Reconcile, NextCslot

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
