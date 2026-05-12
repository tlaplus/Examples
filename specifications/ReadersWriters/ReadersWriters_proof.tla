--------------------- MODULE ReadersWriters_proof ----------------------------
(***************************************************************************)
(* TLAPS proof of the safety properties of the readers-writers spec:       *)
(*                                                                         *)
(*   Spec => []TypeOK                                                      *)
(*   Spec => []Safety                                                      *)
(*                                                                         *)
(* Both are inductive once we know that the head of `waiting` is a 2-tuple *)
(* with first component "read"/"write" (which TypeOK already gives us).   *)
(* Cardinality(writers) <= 1 follows because:                              *)
(*   - Writes only happen via ReadOrWrite, whose precondition is           *)
(*     `writers = {}`; so writers' = writers \cup {actor} = {actor}.       *)
(*   - StopActivity only removes elements; cardinality cannot grow there.  *)
(***************************************************************************)
EXTENDS ReadersWriters, FiniteSets, FiniteSetTheorems, TLAPS

(***************************************************************************)
(* The spec leaves `NumActors` as an unconstrained CONSTANT.  Make the    *)
(* (TLC-implicit) assumption explicit so the finiteness reasoning goes    *)
(* through.                                                                *)
(***************************************************************************)
ASSUME NumActorsIsNat == NumActors \in Nat

(***************************************************************************)
(* The head of a non-empty Seq(T) is in T.                                 *)
(***************************************************************************)
LEMMA HeadInSeqRange ==
  ASSUME NEW T, NEW s \in Seq(T), s # << >>
  PROVE  Head(s) \in T
  OBVIOUS

LEMMA TailIsSeq ==
  ASSUME NEW T, NEW s \in Seq(T), s # << >>
  PROVE  Tail(s) \in Seq(T)
  OBVIOUS

(***************************************************************************)
(* The set of "read"/"write" labels is closed under SelectSeq, but TypeOK  *)
(* gives us all we need: waiting \in Seq({"read","write"} \X Actors).      *)
(***************************************************************************)

(***************************************************************************)
(* Type correctness.                                                       *)
(***************************************************************************)
THEOREM TypeCorrect == Spec => []TypeOK
<1>1. Init => TypeOK
  BY DEF Init, TypeOK
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  <2>. SUFFICES ASSUME TypeOK, [Next]_vars  PROVE TypeOK'
    OBVIOUS
  <2>. USE DEF TypeOK
  <2>1. ASSUME NEW actor \in Actors, TryRead(actor)
        PROVE  TypeOK'
    <3>. <<"read", actor>> \in {"read","write"} \X Actors
      OBVIOUS
    <3>. QED  BY <2>1 DEF TryRead
  <2>2. ASSUME NEW actor \in Actors, TryWrite(actor)
        PROVE  TypeOK'
    <3>. <<"write", actor>> \in {"read","write"} \X Actors
      OBVIOUS
    <3>. QED  BY <2>2 DEF TryWrite
  <2>3. CASE ReadOrWrite
    <3>. USE <2>3 DEF ReadOrWrite
    <3>1. waiting # << >>
      OBVIOUS
    <3>2. Tail(waiting) \in Seq({"read","write"} \X Actors)
      BY <3>1, TailIsSeq
    <3>3. Head(waiting) \in {"read","write"} \X Actors
      BY <3>1, HeadInSeqRange
    <3>4. Head(waiting)[2] \in Actors
      BY <3>3
    <3>5. CASE Head(waiting)[1] = "read"
      <4>. DEFINE actor == Head(waiting)[2]
      <4>1. Read(actor)
        BY <3>5
      <4>. QED  BY <3>2, <3>4, <4>1 DEF Read
    <3>6. CASE Head(waiting)[1] = "write"
      <4>. DEFINE actor == Head(waiting)[2]
      <4>1. Write(actor)
        BY <3>6
      <4>. QED  BY <3>2, <3>4, <4>1 DEF Write
    <3>7. Head(waiting)[1] \in {"read","write"}
      BY <3>3
    <3>. QED  BY <3>5, <3>6, <3>7
  <2>4. CASE Stop
    <3>. SUFFICES ASSUME NEW actor \in readers \cup writers,
                          StopActivity(actor)
                  PROVE  TypeOK'
      BY <2>4 DEF Stop
    <3>1. CASE actor \in readers
      BY <3>1 DEF StopActivity
    <3>2. CASE actor \notin readers
      <4>1. actor \in writers
        BY <3>2
      <4>. QED  BY <3>2, <4>1 DEF StopActivity
    <3>. QED  BY <3>1, <3>2
  <2>5. CASE UNCHANGED vars
    BY <2>5 DEF vars
  <2>. QED  BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
<1>. QED  BY <1>1, <1>2, PTL DEF Spec

(***************************************************************************)
(* The mutex / single-writer safety property.                              *)
(* Inductive together with TypeOK.                                         *)
(***************************************************************************)
Inv == TypeOK /\ Safety

LEMMA SafetyStep == Inv /\ [Next]_vars => Inv'
  <1>. SUFFICES ASSUME Inv, [Next]_vars  PROVE Inv'
    OBVIOUS
  <1>. USE DEF Inv, TypeOK, Safety
  <1>typok. TypeOK'
    \* Re-derive the type-correctness step inline (same as in TypeCorrect).
    <2>1. ASSUME NEW actor \in Actors, TryRead(actor)
          PROVE  TypeOK'
      <3>. <<"read", actor>> \in {"read","write"} \X Actors
        OBVIOUS
      <3>. QED  BY <2>1 DEF TryRead
    <2>2. ASSUME NEW actor \in Actors, TryWrite(actor)
          PROVE  TypeOK'
      <3>. <<"write", actor>> \in {"read","write"} \X Actors
        OBVIOUS
      <3>. QED  BY <2>2 DEF TryWrite
    <2>3. CASE ReadOrWrite
      <3>. USE <2>3 DEF ReadOrWrite
      <3>1. waiting # << >>
        OBVIOUS
      <3>2. Tail(waiting) \in Seq({"read","write"} \X Actors)
        BY <3>1, TailIsSeq
      <3>3. Head(waiting) \in {"read","write"} \X Actors
        BY <3>1, HeadInSeqRange
      <3>4. Head(waiting)[2] \in Actors
        BY <3>3
      <3>5. CASE Head(waiting)[1] = "read"
        <4>. DEFINE actor == Head(waiting)[2]
        <4>1. Read(actor)
          BY <3>5
        <4>. QED  BY <3>2, <3>4, <4>1 DEF Read
      <3>6. CASE Head(waiting)[1] = "write"
        <4>. DEFINE actor == Head(waiting)[2]
        <4>1. Write(actor)
          BY <3>6
        <4>. QED  BY <3>2, <3>4, <4>1 DEF Write
      <3>7. Head(waiting)[1] \in {"read","write"}
        BY <3>3
      <3>. QED  BY <3>5, <3>6, <3>7
    <2>4. ASSUME NEW actor \in readers \cup writers, StopActivity(actor)
          PROVE  TypeOK'
      <3>1. CASE actor \in readers
        BY <3>1, <2>4 DEF StopActivity
      <3>2. CASE actor \notin readers
        <4>1. actor \in writers
          BY <3>2, <2>4
        <4>. QED  BY <3>2, <4>1, <2>4 DEF StopActivity
      <3>. QED  BY <3>1, <3>2
    <2>5. CASE UNCHANGED vars
      BY <2>5 DEF vars
    <2>. QED  BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next, Stop
  <1>safety. Safety'
    <2>1. ASSUME NEW actor \in Actors, TryRead(actor)
          PROVE  Safety'
      BY <2>1 DEF TryRead
    <2>2. ASSUME NEW actor \in Actors, TryWrite(actor)
          PROVE  Safety'
      BY <2>2 DEF TryWrite
    <2>3. CASE ReadOrWrite
      <3>. USE <2>3 DEF ReadOrWrite
      <3>1. waiting # << >> /\ writers = {}
        OBVIOUS
      <3>2. Head(waiting) \in {"read","write"} \X Actors
        BY <3>1, HeadInSeqRange
      <3>. DEFINE actor == Head(waiting)[2]
      <3>3. actor \in Actors
        BY <3>2
      <3>4. CASE Head(waiting)[1] = "read"
        <4>1. Read(actor)
          BY <3>4
        <4>2. writers' = writers /\ writers = {}
          BY <4>1, <3>1 DEF Read
        <4>3. writers' = {}
          BY <4>2
        <4>4. Cardinality(writers') = 0
          BY <4>3, FS_EmptySet
        <4>5. ~(readers' /= {} /\ writers' /= {})
          BY <4>3
        <4>. QED  BY <4>4, <4>5
      <3>5. CASE Head(waiting)[1] = "write"
        <4>1. Write(actor)
          BY <3>5
        <4>2. readers = {} /\ readers' = readers
          BY <4>1, <3>1 DEF Write
        <4>3. writers' = writers \cup {actor}
          BY <4>1, <3>1 DEF Write
        <4>4. writers' = {actor}
          BY <4>3, <3>1
        <4>5. Cardinality({actor}) = 1
          BY FS_Singleton
        <4>6. Cardinality(writers') = 1
          BY <4>4, <4>5
        <4>7. readers' = {}
          BY <4>2
        <4>8. ~(readers' /= {} /\ writers' /= {})
          BY <4>7
        <4>. QED  BY <4>6, <4>8
      <3>6. Head(waiting)[1] \in {"read","write"}
        BY <3>2
      <3>. QED  BY <3>4, <3>5, <3>6
    <2>4. ASSUME NEW actor \in readers \cup writers, StopActivity(actor)
          PROVE  Safety'
      <3>. USE <2>4 DEF StopActivity
      <3>1. CASE actor \in readers
        <4>1. readers' = readers \ {actor} /\ writers' = writers
          BY <3>1
        <4>2. ~(readers /= {} /\ writers /= {})
          OBVIOUS
        <4>3. readers' \subseteq readers
          BY <4>1
        <4>4. ~(readers' /= {} /\ writers' /= {})
          BY <4>1, <4>3, <4>2
        <4>5. Cardinality(writers') <= 1
          BY <4>1
        <4>. QED  BY <4>4, <4>5
      <3>2. CASE actor \notin readers
        <4>1. actor \in writers
          BY <3>2
        <4>2. readers' = readers /\ writers' = writers \ {actor}
          BY <3>2
        <4>3. writers' \subseteq writers
          BY <4>2
        <4>4. ~(readers' /= {} /\ writers' /= {})
          <5>1. ~(readers /= {} /\ writers /= {})
            OBVIOUS
          <5>. QED  BY <4>2, <4>3, <5>1
        <4>5. IsFiniteSet(Actors)
          BY NumActorsIsNat, FS_Interval DEF Actors
        <4>6. IsFiniteSet(writers)
          BY <4>5, FS_Subset
        <4>7. /\ IsFiniteSet(writers')
              /\ Cardinality(writers') <= Cardinality(writers)
              /\ Cardinality(writers') \in Nat
              /\ Cardinality(writers) \in Nat
          <5>1. Cardinality(writers) \in Nat
            BY <4>6, FS_CardinalityType
          <5>2. IsFiniteSet(writers') /\ Cardinality(writers') <= Cardinality(writers)
            BY <4>3, <4>6, FS_Subset
          <5>3. Cardinality(writers') \in Nat
            BY <5>2, FS_CardinalityType
          <5>. QED  BY <5>1, <5>2, <5>3
        <4>8. Cardinality(writers') <= 1
          BY <4>7
        <4>. QED  BY <4>4, <4>8
      <3>. QED  BY <3>1, <3>2
    <2>5. CASE UNCHANGED vars
      BY <2>5 DEF vars
    <2>. QED  BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next, Stop
  <1>. QED  BY <1>typok, <1>safety

THEOREM SafetyCorrect == Spec => []Safety
<1>1. Init => Inv
  <2>1. Cardinality({}) = 0
    BY FS_EmptySet
  <2>. QED  BY <2>1 DEF Init, Inv, TypeOK, Safety
<1>2. Inv /\ [Next]_vars => Inv'
  BY SafetyStep
<1>3. Inv => Safety
  BY DEF Inv
<1>. QED  BY <1>1, <1>2, <1>3, PTL DEF Spec
============================================================================
