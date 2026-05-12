--------------------------- MODULE TCommit_proof ---------------------------
(***************************************************************************)
(* TLAPS proof of                                                          *)
(*   THEOREM TCSpec => [](TCTypeOK /\ TCConsistent)                        *)
(* stated in TCommit.tla.                                                  *)
(***************************************************************************)
EXTENDS TCommit, TLAPS

Inv == TCTypeOK /\ TCConsistent

THEOREM TCorrect == TCSpec => []Inv
<1>1. TCInit => Inv
  BY DEF TCInit, Inv, TCTypeOK, TCConsistent
<1>2. Inv /\ [TCNext]_rmState => Inv'
  <2> SUFFICES ASSUME Inv,
                      [TCNext]_rmState
               PROVE  Inv'
    OBVIOUS
  <2>. USE DEF Inv, TCTypeOK, TCConsistent
  <2>1. ASSUME NEW rm \in RM, Prepare(rm)
        PROVE  Inv'
    BY <2>1 DEF Prepare
  <2>2. ASSUME NEW rm \in RM, Decide(rm)
        PROVE  Inv'
    BY <2>2 DEF Decide, canCommit, notCommitted
  <2>3. CASE UNCHANGED rmState
    BY <2>3
  <2>. QED  BY <2>1, <2>2, <2>3 DEF TCNext
<1>. QED  BY <1>1, <1>2, PTL DEF TCSpec, Inv

============================================================================
