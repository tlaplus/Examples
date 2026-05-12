--------------------- MODULE CigaretteSmokers_proof ---------------------------
(***************************************************************************)
(* TLAPS proofs of                                                         *)
(*                                                                         *)
(*   Spec => []TypeOK                                                      *)
(*   Spec => []AtMostOne                                                   *)
(*                                                                         *)
(* AtMostOne (at most one smoker is smoking) is inductive together with    *)
(* TypeOK once we know `Ingredients` is finite.                            *)
(***************************************************************************)
EXTENDS CigaretteSmokers, FiniteSets, FiniteSetTheorems, TLAPS

(***************************************************************************)
(* Ingredients is implicitly finite: the spec uses Cardinality on it.      *)
(***************************************************************************)
ASSUME IngredientsFinite == IsFiniteSet(Ingredients)

(***************************************************************************)
(* Type correctness.  The dealer disjunct dealer \in Offers \/ dealer = {} *)
(* is preserved trivially since both actions either set dealer to {} or    *)
(* nondeterministically choose dealer' \in Offers.                         *)
(***************************************************************************)
THEOREM TypeCorrect == Spec => []TypeOK
<1>1. Init => TypeOK
  BY DEF Init, TypeOK
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  <2>. SUFFICES ASSUME TypeOK, [Next]_vars  PROVE TypeOK'
    OBVIOUS
  <2>. USE DEF TypeOK
  <2>1. CASE startSmoking
    <3>. USE <2>1 DEF startSmoking
    <3>1. smokers' \in [Ingredients -> [smoking : BOOLEAN]]
      OBVIOUS
    <3>2. dealer' = {}
      OBVIOUS
    <3>. QED  BY <3>1, <3>2
  <2>2. CASE stopSmoking
    <3>. USE <2>2 DEF stopSmoking
    <3>1. smokers' \in [Ingredients -> [smoking : BOOLEAN]]
      <4>. DEFINE r == ChooseOne(Ingredients, LAMBDA x : smokers[x].smoking)
      <4>1. smokers' = [smokers EXCEPT ![r].smoking = FALSE]
        BY DEF stopSmoking
      <4>. QED  BY <4>1
    <3>2. dealer' \in Offers \/ dealer' = {}
      OBVIOUS
    <3>. QED  BY <3>1, <3>2
  <2>3. CASE UNCHANGED vars
    BY <2>3 DEF vars
  <2>. QED  BY <2>1, <2>2, <2>3 DEF Next
<1>. QED  BY <1>1, <1>2, PTL DEF Spec

(***************************************************************************)
(* AtMostOne: at most one smoker is smoking.                               *)
(* Combined invariant with TypeOK (TypeOK is needed to type-check the     *)
(* set comprehension).                                                     *)
(***************************************************************************)
SmokingSet == {r \in Ingredients : smokers[r].smoking}

LEMMA SmokingSetFinite ==
  ASSUME TypeOK
  PROVE  /\ IsFiniteSet(SmokingSet)
         /\ Cardinality(SmokingSet) \in Nat
  <1>1. SmokingSet \subseteq Ingredients
    BY DEF SmokingSet
  <1>2. IsFiniteSet(SmokingSet)
    BY <1>1, IngredientsFinite, FS_Subset
  <1>3. Cardinality(SmokingSet) \in Nat
    BY <1>2, FS_CardinalityType
  <1>. QED  BY <1>2, <1>3

LEMMA AtMostOneViaSmokingSet == AtMostOne <=> Cardinality(SmokingSet) <= 1
  BY DEF AtMostOne, SmokingSet

(***************************************************************************)
(* The spec's unnamed ASSUME extracted as a fact for use in proofs.        *)
(***************************************************************************)
LEMMA OffersFact ==
  /\ Offers \subseteq SUBSET Ingredients
  /\ \A n \in Offers : Cardinality(n) = Cardinality(Ingredients) - 1
  BY OffersAssumption

(***************************************************************************)
(* Cardinality(Ingredients) >= 1 follows from the existence of any         *)
(* dealer \in Offers (Offers is non-empty by Init's `dealer \in Offers`,  *)
(* but more directly: any d \in Offers has |d| = |Ingredients| - 1 \in Nat *)
(* which implies |Ingredients| >= 1.  We don't actually need this for the  *)
(* proof of AtMostOne, just for OffersFact reasoning).                     *)
(***************************************************************************)

LEMMA UniqueComplement2 ==
  ASSUME TypeOK, dealer \in Offers
  PROVE  Cardinality({r \in Ingredients : {r} \cup dealer = Ingredients}) = 1
  <1>. USE DEF TypeOK
  <1>1. dealer \in SUBSET Ingredients
    BY OffersFact
  <1>2. Cardinality(dealer) = Cardinality(Ingredients) - 1
    BY OffersFact
  <1>3. IsFiniteSet(dealer)
    BY <1>1, IngredientsFinite, FS_Subset
  <1>4. Cardinality(dealer) \in Nat
    BY <1>3, FS_CardinalityType
  <1>5. Cardinality(Ingredients) \in Nat
    BY IngredientsFinite, FS_CardinalityType
  <1>6. Cardinality(Ingredients) > Cardinality(dealer)
    BY <1>2, <1>4, <1>5
  <1>7. dealer # Ingredients
    BY <1>3, IngredientsFinite, <1>6, FS_Subset, <1>1
  <1>. DEFINE missing == Ingredients \ dealer
  <1>9. IsFiniteSet(missing)
    BY IngredientsFinite, FS_Difference
  <1>10. Cardinality(missing) = Cardinality(Ingredients) - Cardinality(dealer)
    <2>1. Ingredients \cap dealer = dealer
      BY <1>1
    <2>2. Cardinality(missing) =
            Cardinality(Ingredients) - Cardinality(Ingredients \cap dealer)
      BY IngredientsFinite, FS_Difference
    <2>. QED  BY <2>1, <2>2
  <1>11. Cardinality(missing) = 1
    BY <1>2, <1>4, <1>5, <1>10
  <1>12. PICK m : missing = {m}
    BY <1>9, <1>11, FS_Singleton
  <1>13. m \in Ingredients /\ m \notin dealer
    <2>1. m \in missing  BY <1>12
    <2>. QED  BY <2>1
  <1>14. \A r \in Ingredients : ({r} \cup dealer = Ingredients) => r = m
    <2>. SUFFICES ASSUME NEW r \in Ingredients,
                         {r} \cup dealer = Ingredients
                  PROVE  r = m
      OBVIOUS
    <2>1. m \in {r} \cup dealer
      BY <1>13
    <2>. QED  BY <2>1, <1>13
  <1>15. \A r \in Ingredients : (r = m) => ({r} \cup dealer = Ingredients)
    <2>. SUFFICES {m} \cup dealer = Ingredients
      OBVIOUS
    <2>1. {m} \cup dealer \subseteq Ingredients
      BY <1>1, <1>13
    <2>2. Ingredients \subseteq {m} \cup dealer
      <3>. SUFFICES ASSUME NEW i \in Ingredients
                    PROVE  i \in {m} \cup dealer
        OBVIOUS
      <3>1. CASE i \in dealer  BY <3>1
      <3>2. CASE i \notin dealer
        <4>. i \in missing  BY <3>2
        <4>. i = m  BY <1>12
        <4>. QED  OBVIOUS
      <3>. QED  BY <3>1, <3>2
    <2>. QED  BY <2>1, <2>2
  <1>16. {r \in Ingredients : {r} \cup dealer = Ingredients} = {m}
    <2>1. \A r \in Ingredients :
            (r \in {r2 \in Ingredients : {r2} \cup dealer = Ingredients})
              <=> r = m
      BY <1>14, <1>15
    <2>2. {r \in Ingredients : {r} \cup dealer = Ingredients} \subseteq {m}
      BY <2>1
    <2>3. {m} \subseteq {r \in Ingredients : {r} \cup dealer = Ingredients}
      BY <2>1, <1>13
    <2>. QED  BY <2>2, <2>3
  <1>17. Cardinality({m}) = 1
    BY FS_Singleton
  <1>. QED  BY <1>16, <1>17

(***************************************************************************)
(* The smoking set after `startSmoking` equals the set of ingredients     *)
(* that complete the dealer.                                               *)
(***************************************************************************)
LEMMA StartSmokingSmokingSet ==
  ASSUME TypeOK, startSmoking
  PROVE  /\ smokers' \in [Ingredients -> [smoking : BOOLEAN]]
         /\ {r \in Ingredients : smokers'[r].smoking}
              = {r \in Ingredients : {r} \cup dealer = Ingredients}
  <1>. USE DEF TypeOK, startSmoking
  <1>1. smokers' = [r \in Ingredients |->
                     [smoking |-> {r} \cup dealer = Ingredients]]
    OBVIOUS
  <1>2. smokers' \in [Ingredients -> [smoking : BOOLEAN]]
    BY <1>1
  <1>3. \A r \in Ingredients :
          smokers'[r].smoking = ({r} \cup dealer = Ingredients)
    BY <1>1
  <1>. QED  BY <1>2, <1>3

(***************************************************************************)
(* The smoking set after `stopSmoking` is a subset of the previous one.   *)
(***************************************************************************)
LEMMA StopSmokingSmokingSet ==
  ASSUME TypeOK, stopSmoking
  PROVE  /\ smokers' \in [Ingredients -> [smoking : BOOLEAN]]
         /\ {r \in Ingredients : smokers'[r].smoking}
              \subseteq {r \in Ingredients : smokers[r].smoking}
  <1>. USE DEF TypeOK, stopSmoking
  <1>. DEFINE r0 == ChooseOne(Ingredients, LAMBDA x : smokers[x].smoking)
  <1>1. smokers' = [smokers EXCEPT ![r0].smoking = FALSE]
    OBVIOUS
  <1>2. smokers' \in [Ingredients -> [smoking : BOOLEAN]]
    BY <1>1
  <1>3. \A r \in Ingredients :
          /\ r # r0 => smokers'[r] = smokers[r]
          /\ r = r0 => smokers'[r] = [smokers[r0] EXCEPT !.smoking = FALSE]
    BY <1>1
  <1>4. \A r \in Ingredients :
          smokers'[r].smoking => smokers[r].smoking
    <2>. SUFFICES ASSUME NEW r \in Ingredients, smokers'[r].smoking
                  PROVE  smokers[r].smoking
      OBVIOUS
    <2>1. CASE r = r0
      <3>1. smokers'[r] = [smokers[r0] EXCEPT !.smoking = FALSE]
        BY <1>3, <2>1
      <3>2. smokers'[r].smoking = FALSE
        BY <3>1
      <3>. QED  BY <3>2
    <2>2. CASE r # r0
      <3>1. smokers'[r] = smokers[r]
        BY <1>3, <2>2
      <3>. QED  BY <3>1
    <2>. QED  BY <2>1, <2>2
  <1>. QED  BY <1>2, <1>4

(***************************************************************************)
(* Main inductive invariant.                                               *)
(***************************************************************************)
Inv == TypeOK /\ AtMostOne

THEOREM AtMostOneCorrect == Spec => []AtMostOne
<1>1. Init => Inv
  <2>. SUFFICES ASSUME Init  PROVE Inv
    OBVIOUS
  <2>. USE DEF Init, Inv, TypeOK
  <2>1. TypeOK
    OBVIOUS
  <2>2. {r \in Ingredients : smokers[r].smoking} = {}
    OBVIOUS
  <2>3. AtMostOne
    <3>1. Cardinality({}) = 0
      BY FS_EmptySet
    <3>. QED  BY <2>2, <3>1 DEF AtMostOne
  <2>. QED  BY <2>1, <2>3
<1>2. Inv /\ [Next]_vars => Inv'
  <2>. SUFFICES ASSUME Inv, [Next]_vars  PROVE Inv'
    OBVIOUS
  <2>. USE DEF Inv
  <2>typok. TypeOK'
    \* Re-derive type-correctness step inline.
    <3>1. CASE startSmoking
      <4>. USE <3>1 DEF startSmoking, TypeOK
      <4>1. smokers' \in [Ingredients -> [smoking : BOOLEAN]]
        OBVIOUS
      <4>2. dealer' = {}
        OBVIOUS
      <4>. QED  BY <4>1, <4>2
    <3>2. CASE stopSmoking
      <4>. USE <3>2 DEF stopSmoking, TypeOK
      <4>. DEFINE r0 == ChooseOne(Ingredients, LAMBDA x : smokers[x].smoking)
      <4>1. smokers' = [smokers EXCEPT ![r0].smoking = FALSE]
        OBVIOUS
      <4>2. smokers' \in [Ingredients -> [smoking : BOOLEAN]]
        BY <4>1
      <4>3. dealer' \in Offers \/ dealer' = {}
        OBVIOUS
      <4>. QED  BY <4>2, <4>3
    <3>3. CASE UNCHANGED vars
      BY <3>3 DEF vars, TypeOK
    <3>. QED  BY <3>1, <3>2, <3>3 DEF Next
  <2>amo. AtMostOne'
    <3>1. CASE startSmoking
      <4>1. dealer \in Offers
        BY <3>1 DEF startSmoking, TypeOK
      <4>2. {r \in Ingredients : smokers'[r].smoking}
              = {r \in Ingredients : {r} \cup dealer = Ingredients}
        BY <3>1, StartSmokingSmokingSet DEF Inv
      <4>3. Cardinality({r \in Ingredients : {r} \cup dealer = Ingredients}) = 1
        BY <4>1, UniqueComplement2 DEF Inv
      <4>4. Cardinality({r \in Ingredients : smokers'[r].smoking}) = 1
        BY <4>2, <4>3
      <4>. QED  BY <4>4 DEF AtMostOne
    <3>2. CASE stopSmoking
      <4>1. {r \in Ingredients : smokers'[r].smoking}
              \subseteq {r \in Ingredients : smokers[r].smoking}
        BY <3>2, StopSmokingSmokingSet DEF Inv
      <4>2. IsFiniteSet({r \in Ingredients : smokers[r].smoking})
            /\ IsFiniteSet({r \in Ingredients : smokers'[r].smoking})
        <5>1. {r \in Ingredients : smokers[r].smoking} \subseteq Ingredients
          OBVIOUS
        <5>2. {r \in Ingredients : smokers'[r].smoking} \subseteq Ingredients
          OBVIOUS
        <5>. QED  BY <5>1, <5>2, IngredientsFinite, FS_Subset
      <4>3. Cardinality({r \in Ingredients : smokers'[r].smoking})
              <= Cardinality({r \in Ingredients : smokers[r].smoking})
        BY <4>1, <4>2, FS_Subset
      <4>4. Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1
        BY DEF AtMostOne
      <4>5. Cardinality({r \in Ingredients : smokers'[r].smoking}) \in Nat
            /\ Cardinality({r \in Ingredients : smokers[r].smoking}) \in Nat
        BY <4>2, FS_CardinalityType
      <4>. QED  BY <4>3, <4>4, <4>5 DEF AtMostOne
    <3>3. CASE UNCHANGED vars
      <4>. smokers' = smokers
        BY <3>3 DEF vars
      <4>. QED  BY DEF AtMostOne
    <3>. QED  BY <3>1, <3>2, <3>3 DEF Next
  <2>. QED  BY <2>typok, <2>amo
<1>3. Inv => AtMostOne
  BY DEF Inv
<1>. QED  BY <1>1, <1>2, <1>3, PTL DEF Spec
============================================================================
