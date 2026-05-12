--------------------------- MODULE DieHard_proof ------------------------------
(***************************************************************************)
(* TLAPS proof of  Spec => []TypeOK.                                       *)
(* (NotSolved is meant to be violated -- it's the puzzle's "find a         *)
(*  solution" search invariant -- so we don't try to prove it.)            *)
(***************************************************************************)
EXTENDS DieHard, TLAPS

LEMMA MinNat ==
  ASSUME NEW m \in Nat, NEW n \in Nat
  PROVE  Min(m, n) \in Nat /\ Min(m, n) <= m /\ Min(m, n) <= n
  BY DEF Min

THEOREM TypeCorrect == Spec => []TypeOK
<1>1. Init => TypeOK
  BY DEF Init, TypeOK
<1>2. TypeOK /\ [Next]_<<big, small>> => TypeOK'
  <2>. SUFFICES ASSUME TypeOK, [Next]_<<big, small>>  PROVE TypeOK'
    OBVIOUS
  <2>. USE DEF TypeOK
  <2>1. CASE FillSmallJug
    BY <2>1 DEF FillSmallJug
  <2>2. CASE FillBigJug
    BY <2>2 DEF FillBigJug
  <2>3. CASE EmptySmallJug
    BY <2>3 DEF EmptySmallJug
  <2>4. CASE EmptyBigJug
    BY <2>4 DEF EmptyBigJug
  <2>5. CASE SmallToBig
    <3>1. big \in Nat /\ small \in Nat /\ big + small \in Nat
      OBVIOUS
    <3>2. big' = Min(big + small, 5) /\ small' = small - (big' - big)
      BY <2>5 DEF SmallToBig
    <3>3. big' \in 0..5
      <4>. Min(big + small, 5) \in Nat /\ Min(big + small, 5) <= 5
        BY <3>1, MinNat
      <4>. QED  BY <3>2
    <3>4. small' \in 0..3
      <4>1. big' \in Nat /\ big' >= big
        <5>1. big + small >= big
          BY <3>1
        <5>. Min(big + small, 5) >= big
          BY <5>1, <3>1 DEF Min
        <5>. QED  BY <3>2, <3>3
      <4>2. big' <= big + small
        <5>. Min(big + small, 5) <= big + small
          BY <3>1, MinNat
        <5>. QED  BY <3>2
      <4>3. small - (big' - big) \in 0..small
        BY <4>1, <4>2, <3>1, <3>3
      <4>. QED  BY <3>2, <4>3
    <3>. QED  BY <3>3, <3>4
  <2>6. CASE BigToSmall
    <3>1. big \in Nat /\ small \in Nat /\ big + small \in Nat
      OBVIOUS
    <3>2. small' = Min(big + small, 3) /\ big' = big - (small' - small)
      BY <2>6 DEF BigToSmall
    <3>3. small' \in 0..3
      <4>. Min(big + small, 3) \in Nat /\ Min(big + small, 3) <= 3
        BY <3>1, MinNat
      <4>. QED  BY <3>2
    <3>4. big' \in 0..5
      <4>1. small' \in Nat /\ small' >= small
        <5>1. big + small >= small
          BY <3>1
        <5>. Min(big + small, 3) >= small
          BY <5>1, <3>1 DEF Min
        <5>. QED  BY <3>2, <3>3
      <4>2. small' <= big + small
        <5>. Min(big + small, 3) <= big + small
          BY <3>1, MinNat
        <5>. QED  BY <3>2
      <4>3. big - (small' - small) \in 0..big
        BY <4>1, <4>2, <3>1, <3>3
      <4>. QED  BY <3>2, <4>3
    <3>. QED  BY <3>3, <3>4
  <2>7. CASE UNCHANGED <<big, small>>
    BY <2>7
  <2>. QED  BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF Next
<1>. QED  BY <1>1, <1>2, PTL DEF Spec
============================================================================
