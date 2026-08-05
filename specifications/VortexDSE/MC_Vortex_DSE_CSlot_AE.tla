---------------- MODULE MC_Vortex_DSE_CSlot_AE ----------------
(* Apalache harness for Vortex_DSE_CSlot_AE.                                *)
(* Fixes constants and bundles the safety invariants for a single          *)
(* symbolic (SMT-backed) check via Apalache.                               *)

EXTENDS Vortex_DSE_CSlot_AE

ConstInit ==
    /\ Nodes   = {"n1", "n2"}
    /\ MsgIDs  = {"a", "b"}
    /\ MaxSlot = 1

\* Conjunction of every safety invariant in the module.
AllInv ==
    /\ TypeInvariant
    /\ MerkleAgreement
    /\ CommittedSupersetsProcessed
    /\ NoPhantomInCommitted
    /\ NoReorderAcrossCslot
    /\ PhaseProgressionValid

===============================================================
