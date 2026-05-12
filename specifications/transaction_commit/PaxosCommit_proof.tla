------------------------- MODULE PaxosCommit_proof -------------------------
(***************************************************************************)
(* TLAPS proof of                                                          *)
(*   THEOREM PCSpec => []PCTypeOK                                          *)
(* stated (as a non-temporal version) in PaxosCommit.tla.                  *)
(*                                                                         *)
(* The inductive strengthening follows the template of the Paxos           *)
(* consensus proof in tlapm/examples/paxos/Paxos.tla.  Beyond PCTypeOK     *)
(* itself we maintain                                                      *)
(*                                                                         *)
(*   AccInv:   for every acceptor state, val = "none" iff bal = -1         *)
(*             (analogue of the first conjunct of AccInv in the Paxos      *)
(*             proof, with None  --> "none" and Values  --> {"prepared",   *)
(*             "aborted"}),                                                *)
(*                                                                         *)
(*   MsgInv1b: every "phase1b" message m with m.bal # -1 has               *)
(*             m.val \in {"prepared", "aborted"}                           *)
(*             (the projection onto Paxos Commit of the first disjunct of  *)
(*             MsgInv for "1b" messages in the Paxos proof).               *)
(*                                                                         *)
(* MsgInv1b is the auxiliary fact alluded to in the original comment of    *)
(* this module: it is what is needed to discharge type-correctness for     *)
(* Phase2a, namely that the value the leader picks for the new "phase2a"  *)
(* message lies in {"prepared", "aborted"}.                                *)
(*                                                                         *)
(* We additionally carry IsFiniteSet(msgs) so that the Maximum operator    *)
(* used in Phase2a behaves as expected on the finite set of phase 1b       *)
(* ballot numbers.                                                         *)
(***************************************************************************)
EXTENDS PaxosCommit, FiniteSets, FiniteSetTheorems, WellFoundedInduction, TLAPS

vars == <<rmState, aState, msgs>>

AccInv ==
  \A rm \in RM, ac \in Acceptor :
       aState[rm][ac].val = "none" <=> aState[rm][ac].bal = -1

MsgInv1b ==
  \A m \in msgs :
       (m.type = "phase1b" /\ m.bal # -1) => m.val \in {"prepared", "aborted"}

Inv == PCTypeOK /\ AccInv /\ MsgInv1b /\ IsFiniteSet(msgs)

(***************************************************************************)
(* The following lemma states the standard fact that for a non-empty       *)
(* finite set of integers all of which are at least -1, the recursive      *)
(* Maximum operator returns an upper bound that is itself in the set.      *)
(*                                                                         *)
(* Notes on the precondition.  Maximum's recursion uses -1 as the result   *)
(* on the empty set, so the result is always in S \cup {-1}.  When some    *)
(* element of S is below -1, Maximum can return -1 (which lies above any  *)
(* such element); the result then need not be in S itself.  All callers   *)
(* in the surrounding spec apply Maximum to a set of phase-1b ballots,    *)
(* which lies in Ballot \cup {-1} \subseteq Nat \cup {-1}, so the         *)
(* "elements >= -1" precondition is always satisfied there.                *)
(*                                                                         *)
(* The proof has two pieces: (i) MaximumRec gives the recursion equation   *)
(* of the inner CHOOSE-defined function `Max[T]` via WFInductiveDef, and   *)
(* (ii) MaximumProp uses well-founded induction over the strict-subset    *)
(* ordering to derive the upper-bound / membership properties.            *)
(***************************************************************************)
MaxDef(g, T) ==
  IF T = {} THEN -1
  ELSE LET n    == CHOOSE n2 \in T : TRUE
           rmax == g[T \ {n}]
       IN  IF n \geq rmax THEN n ELSE rmax

\* The CHOOSE form of the inner recursive function in Maximum(S).
MaxFn(S) == CHOOSE g : g = [T \in SUBSET S |-> MaxDef(g, T)]

LEMMA MaxFnRec ==
  ASSUME NEW S, IsFiniteSet(S), NEW T \in SUBSET S
  PROVE  MaxFn(S)[T] = MaxDef(MaxFn(S), T)
  <1>. DEFINE max == MaxFn(S)
  <1>0a. FiniteSubsetsOf(S) = SUBSET S
    BY FS_FiniteSubsetsOfFinite
  <1>0b. IsWellFoundedOn(StrictSubsetOrdering(S), FiniteSubsetsOf(S))
    BY FS_StrictSubsetOrderingWellFounded
  <1>0c. WFDefOn(StrictSubsetOrdering(S), FiniteSubsetsOf(S), MaxDef)
    <2>. SUFFICES ASSUME NEW g, NEW h, NEW U \in FiniteSubsetsOf(S),
                         \A V \in SetLessThan(U, StrictSubsetOrdering(S),
                                              FiniteSubsetsOf(S)) :
                              g[V] = h[V]
                  PROVE  MaxDef(g, U) = MaxDef(h, U)
      BY Isa DEF WFDefOn
    <2>1. CASE U = {}  BY <2>1 DEF MaxDef
    <2>2. CASE U # {}
      <3>. DEFINE n == CHOOSE n2 \in U : TRUE
      <3>1. n \in U  BY <2>2
      <3>2a. U \in SUBSET S /\ IsFiniteSet(U)
        BY DEF FiniteSubsetsOf
      <3>2e. IsFiniteSet(U \ {n})
        BY <3>2a, FS_RemoveElement
      <3>2f. U \ {n} \in FiniteSubsetsOf(S)
        BY <3>2a, <3>2e DEF FiniteSubsetsOf
      <3>2g. <<U \ {n}, U>> \in StrictSubsetOrdering(S)
        BY <3>1, <3>2a DEF StrictSubsetOrdering
      <3>2. U \ {n} \in SetLessThan(U, StrictSubsetOrdering(S), FiniteSubsetsOf(S))
        BY <3>2f, <3>2g DEF SetLessThan
      <3>3. g[U \ {n}] = h[U \ {n}]
        BY <3>2
      <3>. QED  BY <2>2, <3>3 DEF MaxDef
    <2>. QED  BY <2>1, <2>2
  <1>0d. OpDefinesFcn(max, FiniteSubsetsOf(S), MaxDef)
    BY <1>0a, Isa DEF OpDefinesFcn, MaxFn
  <1>1. WFInductiveDefines(max, FiniteSubsetsOf(S), MaxDef)
    BY <1>0b, <1>0c, <1>0d, WFInductiveDef, Isa
  <1>2. max = [x \in FiniteSubsetsOf(S) |-> MaxDef(max, x)]
    BY <1>1, Zenon DEF WFInductiveDefines
  <1>3. T \in FiniteSubsetsOf(S)
    BY <1>0a
  <1>. QED  BY <1>2, <1>3, Zenon

LEMMA MaximumIsMaxFn ==
  ASSUME NEW S
  PROVE  Maximum(S) = MaxFn(S)[S]
  BY Zenon DEF Maximum, MaxFn, MaxDef

LEMMA MaximumProp ==
  ASSUME NEW S, IsFiniteSet(S), S \subseteq Int, S # {},
         \A x \in S : x >= -1
  PROVE  /\ Maximum(S) \in S
         /\ \A n \in S : n =< Maximum(S)
  <1>. DEFINE max == MaxFn(S)
  <1>. DEFINE P(T) == \/ T = {} /\ max[T] = -1
                      \/ T # {} /\ max[T] \in T
                                /\ \A k \in T : k =< max[T]
  <1>1. ASSUME NEW T \in SUBSET S,
               \A U \in (SUBSET T) \ {T} : P(U)
        PROVE  P(T)
    <2>. T \subseteq Int  OBVIOUS
    <2>. \A x \in T : x >= -1  OBVIOUS
    <2>0. max[T] = MaxDef(max, T)
      BY MaxFnRec
    <2>1. CASE T = {}
      <3>1. MaxDef(max, T) = -1
        BY <2>1 DEF MaxDef
      <3>2. max[T] = -1
        BY <2>0, <3>1
      <3>. QED  BY <2>1, <3>2 DEF P
    <2>2. CASE T # {}
      <3>. DEFINE n == CHOOSE n2 \in T : TRUE
                  rmax == max[T \ {n}]
      <3>1. n \in T  BY <2>2
      <3>2. n \in Int /\ n >= -1  BY <3>1
      <3>3a. T \ {n} \in SUBSET T
        OBVIOUS
      <3>3b. T \ {n} # T
        BY <3>1
      <3>3. T \ {n} \in (SUBSET T) \ {T}
        BY <3>3a, <3>3b
      <3>4. P(T \ {n})
        BY <1>1, <3>3
      <3>6. max[T] = IF n \geq rmax THEN n ELSE rmax
        BY <2>0, <2>2 DEF MaxDef
      <3>7. CASE T \ {n} = {}
        <4>1. T = {n}
          BY <3>1, <3>7
        <4>2. rmax = -1
          BY <3>4, <3>7 DEF P
        <4>3. n \geq rmax
          <5>1. n >= -1  BY <3>2
          <5>. QED  BY <5>1, <4>2
        <4>4. max[T] = n
          BY <3>6, <4>3
        <4>5. max[T] \in T  BY <4>4, <3>1
        <4>6. \A k \in T : k =< max[T]
          <5>. SUFFICES ASSUME NEW k \in T  PROVE k =< max[T]
            OBVIOUS
          <5>1. k = n  BY <4>1
          <5>. QED  BY <5>1, <4>4, <3>2
        <4>. QED  BY <2>2, <4>5, <4>6 DEF P
      <3>8. CASE T \ {n} # {}
        <4>1. rmax \in T \ {n} /\ \A k \in T \ {n} : k =< rmax
          BY <3>4, <3>8 DEF P
        <4>2. rmax \in Int
          BY <4>1, <2>2
        <4>3. CASE n \geq rmax
          <5>1. max[T] = n
            BY <3>6, <4>3
          <5>2. max[T] \in T
            BY <5>1, <3>1
          <5>3. \A k \in T : k =< max[T]
            <6>. SUFFICES ASSUME NEW k \in T  PROVE k =< max[T]
              OBVIOUS
            <6>1. CASE k = n
              BY <5>1, <6>1, <3>2
            <6>2. CASE k # n
              <7>1. k \in T \ {n}
                BY <6>2
              <7>2. k =< rmax
                BY <7>1, <4>1
              <7>3. k \in Int
                BY <7>1
              <7>. QED  BY <7>2, <7>3, <4>2, <3>2, <4>3, <5>1
            <6>. QED  BY <6>1, <6>2
          <5>. QED  BY <2>2, <5>2, <5>3 DEF P
        <4>4. CASE ~(n \geq rmax)
          <5>0. n < rmax
            BY <4>4, <3>2, <4>2
          <5>1. max[T] = rmax
            BY <3>6, <4>4
          <5>2. max[T] \in T
            BY <5>1, <4>1
          <5>3. \A k \in T : k =< max[T]
            <6>. SUFFICES ASSUME NEW k \in T  PROVE k =< max[T]
              OBVIOUS
            <6>1. CASE k = n
              BY <5>0, <5>1, <3>2, <4>2, <6>1
            <6>2. CASE k # n
              <7>1. k \in T \ {n}
                BY <6>2
              <7>2. k =< rmax
                BY <7>1, <4>1
              <7>. QED  BY <5>1, <7>2
            <6>. QED  BY <6>1, <6>2
          <5>. QED  BY <2>2, <5>2, <5>3 DEF P
        <4>. QED  BY <4>3, <4>4
      <3>. QED  BY <3>7, <3>8
    <2>. QED  BY <2>1, <2>2
  <1>2. P(S)
    <2>. HIDE DEF P
    <2>. QED  BY <1>1, FS_WFInduction, IsaM("iprover")
  <1>3. max[S] \in S /\ \A k \in S : k =< max[S]
    BY <1>2 DEF P
  <1>. QED  BY <1>3, MaximumIsMaxFn

(***************************************************************************)
(* Auxiliary fact used in the Phase2a case: any majority is non-empty,     *)
(* since by PaxosCommitAssumptions any two majorities have non-empty       *)
(* intersection (in particular MS \cap MS = MS).                           *)
(***************************************************************************)
LEMMA MajorityNonEmpty == \A MS \in Majority : MS # {}
BY PaxosCommitAssumptions

(***************************************************************************)
(* Initiation: the inductive invariant holds in the initial state.         *)
(***************************************************************************)
LEMMA InitInv == PCInit => Inv
<1> SUFFICES ASSUME PCInit
             PROVE  Inv
  OBVIOUS
<1> USE PaxosCommitAssumptions
<1> USE DEF PCInit, Inv, PCTypeOK, AccInv, MsgInv1b
<1>1. PCTypeOK
  OBVIOUS
<1>2. AccInv
  OBVIOUS
<1>3. MsgInv1b
  OBVIOUS
<1>4. IsFiniteSet(msgs)
  BY FS_EmptySet
<1>. QED  BY <1>1, <1>2, <1>3, <1>4

(***************************************************************************)
(* Consecution: the inductive invariant is preserved by every step of the  *)
(* next-state relation (and trivially by stuttering steps).                *)
(***************************************************************************)
LEMMA NextInv == Inv /\ [PCNext]_vars => Inv'
<1> SUFFICES ASSUME Inv, [PCNext]_vars
             PROVE  Inv'
  OBVIOUS
<1> USE PaxosCommitAssumptions
<1> USE DEF Inv, PCTypeOK, AccInv, MsgInv1b, vars, Send, Message

<1>1. ASSUME NEW rm \in RM, RMPrepare(rm)
      PROVE  Inv'
  BY <1>1, FS_AddElement DEF RMPrepare

<1>2. ASSUME NEW rm \in RM, RMChooseToAbort(rm)
      PROVE  Inv'
  BY <1>2, FS_AddElement DEF RMChooseToAbort

<1>3. ASSUME NEW rm \in RM, RMRcvCommitMsg(rm)
      PROVE  Inv'
  BY <1>3 DEF RMRcvCommitMsg

<1>4. ASSUME NEW rm \in RM, RMRcvAbortMsg(rm)
      PROVE  Inv'
  BY <1>4 DEF RMRcvAbortMsg

<1>5. ASSUME NEW b \in Ballot \ {0}, NEW rm \in RM, Phase1a(b, rm)
      PROVE  Inv'
  BY <1>5, FS_AddElement DEF Phase1a

<1>6. ASSUME NEW b \in Ballot \ {0}, NEW rm \in RM, Phase2a(b, rm)
      PROVE  Inv'
  <2>1. PICK MS \in Majority :
            LET mset == {m \in msgs : /\ m.type = "phase1b"
                                      /\ m.ins  = rm
                                      /\ m.mbal = b
                                      /\ m.acc  \in MS}
                maxbal == Maximum({m.bal : m \in mset})
                val == IF maxbal = -1
                         THEN "aborted"
                         ELSE (CHOOSE m \in mset : m.bal = maxbal).val
            IN  /\ \A ac \in MS : \E m \in mset : m.acc = ac
                /\ Send([type |-> "phase2a", ins |-> rm,
                         bal |-> b, val |-> val])
    BY <1>6, Zenon DEF Phase2a
  <2> DEFINE mset    == {m \in msgs : /\ m.type = "phase1b"
                                      /\ m.ins  = rm
                                      /\ m.mbal = b
                                      /\ m.acc  \in MS}
             bset    == {m.bal : m \in mset}
             maxbal  == Maximum(bset)
             val     == IF maxbal = -1
                          THEN "aborted"
                          ELSE (CHOOSE m \in mset : m.bal = maxbal).val
             nm      == [type |-> "phase2a", ins |-> rm,
                         bal |-> b, val |-> val]
  <2>2. UNCHANGED <<rmState, aState>> /\ msgs' = msgs \cup {nm}
    BY <1>6, <2>1 DEF Phase2a
  <2>3. mset \subseteq msgs
    OBVIOUS
  <2>4. IsFiniteSet(mset)
    BY <2>3, FS_Subset
  <2>5. bset \subseteq Int
    BY DEF Message
  <2>6. IsFiniteSet(bset)
    BY <2>4, FS_Image
  <2>7. MS # {}
    BY MajorityNonEmpty
  <2>8. mset # {}
    <3>1. PICK ac \in MS : TRUE
      BY <2>7
    <3>2. \E m \in mset : m.acc = ac
      BY <2>1, <3>1
    <3>. QED  BY <3>2
  <2>9. bset # {}
    BY <2>8
  <2>5a. \A x \in bset : x >= -1
    BY DEF Message
  <2>10. val \in {"prepared", "aborted"}
    <3>1. CASE maxbal = -1
      BY <3>1
    <3>2. CASE maxbal # -1
      <4>1. maxbal \in bset
        BY <2>5, <2>5a, <2>6, <2>9, MaximumProp
      <4>2. PICK m0 \in mset : m0.bal = maxbal
        BY <4>1
      <4>3. m0.type = "phase1b" /\ m0.bal # -1
        BY <3>2, <4>2
      <4>4. m0.val \in {"prepared", "aborted"}
        BY <4>2, <4>3
      <4>5. \A m \in mset : m.bal = maxbal => m.val \in {"prepared", "aborted"}
        BY <3>2 DEF Message
      <4>6. \E m \in mset : m.bal = maxbal
        BY <4>2
      <4>7. (CHOOSE m \in mset : m.bal = maxbal) \in mset
        /\ (CHOOSE m \in mset : m.bal = maxbal).bal = maxbal
        BY <4>6
      <4>. QED  BY <3>2, <4>5, <4>7
    <3>. QED  BY <3>1, <3>2
  <2>11. nm \in Message
    BY <2>10 DEF Message
  <2>12. PCTypeOK'
    BY <2>2, <2>11
  <2>13. AccInv'
    BY <2>2
  <2>14. MsgInv1b'
    <3>1. \A m \in msgs : (m.type = "phase1b" /\ m.bal # -1)
                          => m.val \in {"prepared","aborted"}
      OBVIOUS
    <3>2. nm.type = "phase2a"
      OBVIOUS
    <3>. QED  BY <2>2, <3>1, <3>2
  <2>15. IsFiniteSet(msgs)'
    BY <2>2, FS_AddElement
  <2>. QED  BY <2>12, <2>13, <2>14, <2>15

<1>7. ASSUME Decide
      PROVE  Inv'
  BY <1>7, FS_AddElement DEF Decide

<1>8. ASSUME NEW ac \in Acceptor, Phase1b(ac)
      PROVE  Inv'
  <2>1. PICK m \in msgs :
              /\ m.type = "phase1a"
              /\ aState[m.ins][ac].mbal < m.bal
              /\ aState' = [aState EXCEPT ![m.ins][ac].mbal = m.bal]
              /\ Send([type |-> "phase1b",
                       ins  |-> m.ins,
                       mbal |-> m.bal,
                       bal  |-> aState[m.ins][ac].bal,
                       val  |-> aState[m.ins][ac].val,
                       acc  |-> ac])
              /\ UNCHANGED rmState
    BY <1>8, Zenon DEF Phase1b
  <2>2. m.ins \in RM /\ m.bal \in Ballot \ {0}
    BY <2>1 DEF Message
  <2> DEFINE nm == [type |-> "phase1b",
                    ins  |-> m.ins,
                    mbal |-> m.bal,
                    bal  |-> aState[m.ins][ac].bal,
                    val  |-> aState[m.ins][ac].val,
                    acc  |-> ac]
  <2>3. nm \in Message
    BY <2>2 DEF Message
  <2>4. msgs' = msgs \cup {nm}
    BY <2>1
  <2>5. PCTypeOK'
    <3>1. aState' \in [RM -> [Acceptor -> [mbal : Ballot,
                                            bal  : Ballot \cup {-1},
                                            val  : {"prepared","aborted","none"}]]]
      BY <2>1, <2>2
    <3>2. msgs' \subseteq Message
      BY <2>3, <2>4
    <3>3. rmState' \in [RM -> {"working", "prepared", "committed", "aborted"}]
      BY <2>1
    <3>. QED  BY <3>1, <3>2, <3>3
  <2>6. AccInv'
    \** Phase1b only updates the mbal field; bal and val are unchanged.
    BY <2>1 DEF Message
  <2>7. MsgInv1b'
    <3>1. nm.bal # -1 => nm.val \in {"prepared","aborted"}
      <4>1. nm.bal = aState[m.ins][ac].bal
        OBVIOUS
      <4>2. nm.val = aState[m.ins][ac].val
        OBVIOUS
      <4>3. aState[m.ins][ac] \in [mbal : Ballot,
                                   bal  : Ballot \cup {-1},
                                   val  : {"prepared","aborted","none"}]
        BY <2>2
      <4>4. CASE aState[m.ins][ac].bal = -1
        BY <4>1, <4>4
      <4>5. CASE aState[m.ins][ac].bal # -1
        <5>1. aState[m.ins][ac].val # "none"
          BY <4>5, <2>2
        <5>2. aState[m.ins][ac].val \in {"prepared","aborted"}
          BY <4>3, <5>1
        <5>. QED  BY <4>2, <5>2
      <4>. QED  BY <4>4, <4>5
    <3>2. \A mm \in msgs : (mm.type = "phase1b" /\ mm.bal # -1)
                            => mm.val \in {"prepared","aborted"}
      OBVIOUS
    <3>. QED  BY <2>4, <3>1, <3>2
  <2>8. IsFiniteSet(msgs)'
    BY <2>4, FS_AddElement
  <2>. QED  BY <2>5, <2>6, <2>7, <2>8

<1>9. ASSUME NEW ac \in Acceptor, Phase2b(ac)
      PROVE  Inv'
  <2>1. PICK m \in msgs :
              /\ m.type = "phase2a"
              /\ aState[m.ins][ac].mbal \leq m.bal
              /\ aState' = [aState EXCEPT ![m.ins][ac].mbal = m.bal,
                                          ![m.ins][ac].bal  = m.bal,
                                          ![m.ins][ac].val  = m.val]
              /\ Send([type |-> "phase2b", ins |-> m.ins, bal |-> m.bal,
                       val |-> m.val, acc |-> ac])
              /\ UNCHANGED rmState
    BY <1>9, Zenon DEF Phase2b
  <2>2. m.ins \in RM /\ m.bal \in Ballot /\ m.val \in {"prepared","aborted"}
    BY <2>1 DEF Message
  <2>3. m.bal # -1
    BY <2>2
  <2> DEFINE nm == [type |-> "phase2b", ins |-> m.ins, bal |-> m.bal,
                    val |-> m.val, acc |-> ac]
  <2>4. nm \in Message
    BY <2>2 DEF Message
  <2>5. msgs' = msgs \cup {nm}
    BY <2>1
  <2>6. PCTypeOK'
    <3>1. aState' \in [RM -> [Acceptor -> [mbal : Ballot,
                                            bal  : Ballot \cup {-1},
                                            val  : {"prepared","aborted","none"}]]]
      BY <2>1, <2>2
    <3>2. msgs' \subseteq Message
      BY <2>4, <2>5
    <3>3. rmState' \in [RM -> {"working", "prepared", "committed", "aborted"}]
      BY <2>1
    <3>. QED  BY <3>1, <3>2, <3>3
  <2>7. AccInv'
    <3> SUFFICES ASSUME NEW rm \in RM, NEW a \in Acceptor
                 PROVE  aState'[rm][a].val = "none" <=> aState'[rm][a].bal = -1
      BY DEF AccInv
    <3>1. CASE rm = m.ins /\ a = ac
      <4>1. aState'[rm][a] = [aState[m.ins][ac] EXCEPT
                                !.mbal = m.bal, !.bal = m.bal, !.val = m.val]
        BY <2>1, <3>1
      <4>2. aState'[rm][a].bal = m.bal /\ aState'[rm][a].val = m.val
        BY <4>1, <2>2 DEF Message
      <4>3. aState'[rm][a].bal # -1 /\ aState'[rm][a].val # "none"
        BY <4>2, <2>2, <2>3
      <4>. QED  BY <4>3
    <3>2. CASE ~(rm = m.ins /\ a = ac)
      <4>1. aState'[rm][a] = aState[rm][a]
        BY <2>1, <3>2, <2>2
      <4>. QED  BY <4>1
    <3>. QED  BY <3>1, <3>2
  <2>8. MsgInv1b'
    <3>1. nm.type = "phase2b"
      OBVIOUS
    <3>2. \A mm \in msgs : (mm.type = "phase1b" /\ mm.bal # -1)
                            => mm.val \in {"prepared","aborted"}
      OBVIOUS
    <3>. QED  BY <2>5, <3>1, <3>2
  <2>9. IsFiniteSet(msgs)'
    BY <2>5, FS_AddElement
  <2>. QED  BY <2>6, <2>7, <2>8, <2>9

<1>10. CASE UNCHANGED vars
  BY <1>10

<1>. QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10
     DEF PCNext

(***************************************************************************)
(* Main theorem: PCTypeOK is an invariant of PCSpec.                       *)
(***************************************************************************)
THEOREM TypeOK_Invariant == PCSpec => []PCTypeOK
<1>1. PCInit => Inv
  BY InitInv
<1>2. Inv /\ [PCNext]_vars => Inv'
  BY NextInv
<1>3. Inv => PCTypeOK
  BY DEF Inv
<1>. QED  BY <1>1, <1>2, <1>3, PTL DEF PCSpec, vars

(***************************************************************************)
(* The non-temporal version of the theorem stated in PaxosCommit.tla       *)
(* (PCSpec => PCTypeOK) is an immediate corollary.                         *)
(***************************************************************************)
THEOREM TypeOK_Init == PCSpec => PCTypeOK
BY TypeOK_Invariant, PTL

============================================================================
