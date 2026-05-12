--------------------------- MODULE stages_proof -------------------------------
(***************************************************************************)
(* TLAPS proof of the type-correctness invariant of stages.tla.            *)
(*                                                                         *)
(*   Spec => []TypeOK                                                      *)
(***************************************************************************)
EXTENDS stages, TLAPS

ASSUME ConstantsAreNat == DNA \in Nat /\ PRIMER \in Nat

LEMMA NatMinNat ==
  ASSUME NEW i \in Nat, NEW j \in Nat
  PROVE  natMin(i, j) \in Nat
  BY DEF natMin

THEOREM TypeCorrect == Spec => []TypeOK
<1>1. Init => TypeOK
  BY ConstantsAreNat DEF Init, TypeOK
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  <2>. SUFFICES ASSUME TypeOK, [Next]_vars  PROVE TypeOK'
    OBVIOUS
  <2>. USE DEF TypeOK
  <2>1. CASE heat
    BY <2>1 DEF heat
  <2>2. CASE cool
    BY <2>2 DEF cool
  <2>3. CASE anneal
    <3>. PICK k \in 1..natMin(primer, template) :
            /\ primer' = primer - k
            /\ template' = template - k
            /\ hybrid' = hybrid + k
      BY <2>3 DEF anneal
    <3>1. natMin(primer, template) <= primer
          /\ natMin(primer, template) <= template
      BY DEF natMin
    <3>1a. natMin(primer, template) \in Nat
      BY NatMinNat
    <3>1b. k <= natMin(primer, template)
      BY <3>1a
    <3>2. k \in Nat
      BY <3>1a, <3>1b
    <3>3. k <= primer /\ k <= template
      BY <3>1, <3>1a, <3>1b, <3>2
    <3>4. primer' \in Nat /\ template' \in Nat /\ hybrid' \in Nat
      BY <3>2, <3>3
    <3>. QED  BY <2>3, <3>4 DEF anneal
  <2>4. CASE extend
    BY <2>4 DEF extend
  <2>5. CASE UNCHANGED vars
    BY <2>5 DEF vars
  <2>. QED  BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
<1>. QED  BY <1>1, <1>2, PTL DEF Spec
============================================================================
