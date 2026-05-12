--------------------------- MODULE clean_proof --------------------------------
(***************************************************************************)
(* TLAPS proof of the safety invariants of clean.tla:                      *)
(*                                                                         *)
(*   Spec => []TypeOK                                                      *)
(*   Spec => []primerPositive                                              *)
(*   Spec => []preservationInvariant                                       *)
(***************************************************************************)
EXTENDS clean, TLAPS

(***************************************************************************)
(* The CONSTANTS DNA, PRIMER are unconstrained in the spec; for the        *)
(* arithmetic preservation argument we need them in Nat.  Restate as a     *)
(* named ASSUME in the proof file.                                         *)
(***************************************************************************)
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
    <3>1b. k \in 1..natMin(primer, template) /\ k <= natMin(primer, template)
      BY <3>1a
    <3>2. k \in Nat
      BY <3>1a, <3>1b
    <3>3. k <= primer /\ k <= template
      BY <3>1, <3>1a, <3>1b, <3>2
    <3>4. primer' \in Nat /\ template' \in Nat
      BY <3>2, <3>3
    <3>5. hybrid' \in Nat
      BY <3>2
    <3>. QED  BY <2>3, <3>4, <3>5 DEF anneal
  <2>4. CASE extend
    BY <2>4 DEF extend
  <2>5. CASE UNCHANGED vars
    BY <2>5 DEF vars
  <2>. QED  BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
<1>. QED  BY <1>1, <1>2, PTL DEF Spec

THEOREM PrimerPositive == Spec => []primerPositive
<1>1. TypeOK => primerPositive
  BY DEF TypeOK, primerPositive
<1>. QED  BY <1>1, TypeCorrect, PTL

THEOREM Preservation == Spec => []preservationInvariant
<1>. DEFINE Inv == TypeOK /\ preservationInvariant
<1>1. Init => Inv
  BY ConstantsAreNat DEF Init, TypeOK, preservationInvariant
<1>2. Inv /\ [Next]_vars => Inv'
  <2>. SUFFICES ASSUME Inv, [Next]_vars  PROVE Inv'
    OBVIOUS
  <2>. USE DEF TypeOK, preservationInvariant
  <2>typok. TypeOK'
    \* Re-derive type-correctness step inline.
    <3>1. CASE heat
      BY <3>1 DEF heat
    <3>2. CASE cool
      BY <3>2 DEF cool
    <3>3. CASE anneal
      <4>. PICK k \in 1..natMin(primer, template) :
              /\ primer' = primer - k
              /\ template' = template - k
              /\ hybrid' = hybrid + k
        BY <3>3 DEF anneal
      <4>1. natMin(primer, template) <= primer
            /\ natMin(primer, template) <= template
        BY DEF natMin
      <4>1a. natMin(primer, template) \in Nat
        BY NatMinNat
      <4>1b. k <= natMin(primer, template)
        BY <4>1a
      <4>2. k \in Nat
        BY <4>1a, <4>1b
      <4>3. k <= primer /\ k <= template
        BY <4>1, <4>1a, <4>1b, <4>2
      <4>. primer' \in Nat /\ template' \in Nat /\ hybrid' \in Nat
        BY <4>2, <4>3
      <4>. QED  BY <3>3 DEF anneal
    <3>4. CASE extend
      BY <3>4 DEF extend
    <3>5. CASE UNCHANGED vars
      BY <3>5 DEF vars
    <3>. QED  BY <3>1, <3>2, <3>3, <3>4, <3>5 DEF Next
  <2>pres. preservationInvariant'
    <3>1. CASE heat
      \* primer' = primer + hybrid; dna' = 0;
      \* template' = template + hybrid + 2*dna; hybrid' = 0
      \* template' + primer' + 2*(dna' + hybrid') =
      \*   (template + hybrid + 2*dna) + (primer + hybrid) + 2*(0 + 0)
      \* = template + primer + 2*hybrid + 2*dna
      \* = template + primer + 2*(dna + hybrid)
      BY <3>1 DEF heat
    <3>2. CASE cool
      BY <3>2 DEF cool
    <3>3. CASE anneal
      <4>. PICK k \in 1..natMin(primer, template) :
              /\ primer' = primer - k
              /\ template' = template - k
              /\ hybrid' = hybrid + k
              /\ dna' = dna
        BY <3>3 DEF anneal
      <4>1. natMin(primer, template) <= primer
            /\ natMin(primer, template) <= template
        BY DEF natMin
      <4>1a. natMin(primer, template) \in Nat
        BY NatMinNat
      <4>1b. k <= natMin(primer, template)
        BY <4>1a
      <4>2. k \in Nat
        BY <4>1a, <4>1b
      <4>3. k <= primer /\ k <= template
        BY <4>1, <4>1a, <4>1b, <4>2
      <4>. QED  BY <4>2, <4>3
    <3>4. CASE extend
      \* primer' = primer; template' = template; dna' = dna + hybrid;
      \* hybrid' = 0
      \* template + primer + 2*(dna + hybrid + 0) = original
      BY <3>4 DEF extend
    <3>5. CASE UNCHANGED vars
      BY <3>5 DEF vars
    <3>. QED  BY <3>1, <3>2, <3>3, <3>4, <3>5 DEF Next
  <2>. QED  BY <2>typok, <2>pres
<1>3. Inv => preservationInvariant
  OBVIOUS
<1>. QED  BY <1>1, <1>2, <1>3, PTL DEF Spec
============================================================================
