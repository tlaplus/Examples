--------------------------- MODULE CoffeeCan_proof ----------------------------
(***************************************************************************)
(* TLAPS proof of  Spec => []TypeInvariant.                                *)
(*                                                                         *)
(* Strengthening: BeanCount \in 0..MaxBeanCount.  Each action decreases    *)
(* the total bean count by exactly 1, so the bound is preserved.           *)
(* Without the bound, PickSameColorWhite could push can.black past         *)
(* MaxBeanCount.                                                            *)
(***************************************************************************)
EXTENDS CoffeeCan, TLAPS

BeanBound == BeanCount \in 0 .. MaxBeanCount

Inv == TypeInvariant /\ BeanBound

THEOREM TypeCorrect == Spec => []TypeInvariant
<1>1. Init => Inv
  BY DEF Init, Inv, TypeInvariant, BeanBound, BeanCount, Can
<1>2. Inv /\ [Next]_can => Inv'
  <2>. SUFFICES ASSUME Inv, [Next]_can  PROVE Inv'
    OBVIOUS
  <2>. USE DEF Inv, TypeInvariant, BeanBound, BeanCount, Can
  <2>1. CASE PickSameColorBlack
    <3>. USE <2>1 DEF PickSameColorBlack
    <3>1. /\ can.black >= 2 /\ can \in Can
          /\ BeanCount > 1
          /\ can.black \in 0..MaxBeanCount
          /\ can.white \in 0..MaxBeanCount
          /\ BeanCount \in 0..MaxBeanCount
      BY DEF Can
    <3>2. can' = [can EXCEPT !.black = @ - 1]
      OBVIOUS
    <3>3. can'.black = can.black - 1 /\ can'.white = can.white
      BY <3>2, <3>1
    <3>4. can'.black \in 0..MaxBeanCount /\ can'.white \in 0..MaxBeanCount
      BY <3>1, <3>3, MaxBeanFact
    <3>5. can' \in Can
      BY <3>4 DEF Can
    <3>6. BeanCount' = can'.black + can'.white
      BY DEF BeanCount
    <3>7. BeanCount' = BeanCount - 1
      BY <3>3, <3>6, <3>1 DEF BeanCount
    <3>8. BeanCount' \in 0..MaxBeanCount
      BY <3>1, <3>7, MaxBeanFact
    <3>. QED  BY <3>5, <3>8
  <2>2. CASE PickSameColorWhite
    <3>. USE <2>2 DEF PickSameColorWhite
    <3>1. /\ can.white >= 2 /\ BeanCount > 1 /\ can \in Can
          /\ can.black \in 0..MaxBeanCount
          /\ can.white \in 0..MaxBeanCount
          /\ BeanCount \in 0..MaxBeanCount
      BY DEF Can
    <3>2. can' = [can EXCEPT !.black = @ + 1, !.white = @ - 2]
      OBVIOUS
    <3>3. can'.black = can.black + 1 /\ can'.white = can.white - 2
      BY <3>2, <3>1
    <3>4. BeanCount' = BeanCount - 1
      BY <3>3, <3>1 DEF BeanCount
    <3>5. BeanCount' \in 0..MaxBeanCount
      BY <3>1, <3>4, MaxBeanFact
    <3>6. can'.white \in 0..MaxBeanCount
      BY <3>1, <3>3, MaxBeanFact
    <3>7. can'.black \in 0..MaxBeanCount
      <4>1. can'.black = can.black + 1
        BY <3>3
      <4>2. can.black + can.white = BeanCount
        BY DEF BeanCount
      <4>3. can.white >= 2
        BY <3>1
      <4>4. can.black + 1 <= can.black + can.white - 1
        BY <3>1, <4>3
      <4>5. can.black + 1 <= BeanCount - 1
        BY <4>2, <4>4, <3>1
      <4>6. BeanCount - 1 <= MaxBeanCount
        BY <3>1, MaxBeanFact
      <4>7. can.black + 1 <= MaxBeanCount
        BY <4>5, <4>6, <3>1, MaxBeanFact
      <4>8. can.black + 1 \in Nat
        BY <3>1
      <4>. QED  BY <4>1, <4>7, <4>8, MaxBeanFact
    <3>8. can' \in Can
      BY <3>6, <3>7 DEF Can
    <3>. QED  BY <3>5, <3>8
  <2>3. CASE PickDifferentColor
    <3>. USE <2>3 DEF PickDifferentColor
    <3>1. /\ can.black >= 1 /\ can.white >= 1 /\ can \in Can
          /\ BeanCount > 1
          /\ can.black \in 0..MaxBeanCount
          /\ can.white \in 0..MaxBeanCount
          /\ BeanCount \in 0..MaxBeanCount
      BY DEF Can
    <3>2. can' = [can EXCEPT !.black = @ - 1]
      OBVIOUS
    <3>3. can'.black = can.black - 1 /\ can'.white = can.white
      BY <3>2, <3>1
    <3>4. can'.black \in 0..MaxBeanCount
      BY <3>1, <3>3, MaxBeanFact
    <3>5. can'.white \in 0..MaxBeanCount
      BY <3>1, <3>3, MaxBeanFact
    <3>6. can' \in Can
      BY <3>4, <3>5 DEF Can
    <3>7. BeanCount' = BeanCount - 1
      BY <3>3, <3>1 DEF BeanCount
    <3>8. BeanCount' \in 0..MaxBeanCount
      BY <3>1, <3>7, MaxBeanFact
    <3>. QED  BY <3>6, <3>8
  <2>4. CASE Termination
    BY <2>4 DEF Termination
  <2>5. CASE UNCHANGED can
    BY <2>5
  <2>. QED  BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
<1>3. Inv => TypeInvariant
  BY DEF Inv
<1>. QED  BY <1>1, <1>2, <1>3, PTL DEF Spec
============================================================================
