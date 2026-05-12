--------------------------- MODULE Voting_proof ----------------------------
(***************************************************************************)
(* TLAPS proofs of theorems stated in Voting.tla.  The spec is essentially *)
(* the same as Paxos/Voting.tla; the proofs are direct ports.              *)
(*                                                                         *)
(*   AllSafeAtZero    (Band E)                                             *)
(*   ChoosableThm     (Band E)                                             *)
(*   ShowsSafety      (Band M)                                             *)
(*                                                                         *)
(* Invariance and Implementation depend on a SafeAtMonotone lemma not yet *)
(* established; see Paxos/Voting_proof.tla for the same deferral.         *)
(***************************************************************************)
EXTENDS Voting

LEMMA QuorumNonEmpty == \A Q \in Quorum : Q # {}
BY QuorumAssumption

(***************************************************************************)
(*                              HELPERS                                    *)
(***************************************************************************)

THEOREM AllSafeAtZero_T == \A v \in Value : SafeAt(0, v)
BY DEF SafeAt

THEOREM ChoosableThm_T ==
    \A b \in Ballot, v \in Value : ChosenAt(b, v) => NoneOtherChoosableAt(b, v)
<1>1. SUFFICES ASSUME NEW b \in Ballot, NEW v \in Value, ChosenAt(b, v)
               PROVE  NoneOtherChoosableAt(b, v)
  OBVIOUS
<1>2. PICK Q \in Quorum : \A a \in Q : VotedFor(a, b, v)
  BY <1>1 DEF ChosenAt
<1>. QED  BY <1>2 DEF NoneOtherChoosableAt

(***************************************************************************)
(* OneValuePerBallot in ASSUME/PROVE form.                                *)
(***************************************************************************)
LEMMA OneValuePerBallotApply ==
  ASSUME OneValuePerBallot,
         NEW a1 \in Acceptor, NEW a2 \in Acceptor, NEW bb \in Ballot,
         NEW v1 \in Value, NEW v2 \in Value,
         VotedFor(a1, bb, v1), VotedFor(a2, bb, v2)
  PROVE  v1 = v2
BY DEF OneValuePerBallot

(***************************************************************************)
(* Convenience: any two quorums intersect in at least one acceptor.        *)
(***************************************************************************)
LEMMA QuorumIntersect ==
  ASSUME NEW Q1 \in Quorum, NEW Q2 \in Quorum
  PROVE  \E a \in Q1 \cap Q2 : a \in Acceptor
<1>1. Q1 \cap Q2 # {}
  BY QuorumAssumption
<1>2. PICK a \in Q1 \cap Q2 : TRUE
  BY <1>1
<1>3. a \in Acceptor
  BY <1>2, QuorumAssumption
<1>. QED  BY <1>2, <1>3

(***************************************************************************)
(*                          ShowsSafety   (Band M)                         *)
(***************************************************************************)

THEOREM ShowsSafety_T ==
    Inv => \A Q \in Quorum, b \in Ballot, v \in Value :
              ShowsSafeAt(Q, b, v) => SafeAt(b, v)
<1>0. SUFFICES ASSUME Inv,
                      NEW Q \in Quorum, NEW b \in Ballot, NEW v \in Value,
                      ShowsSafeAt(Q, b, v)
               PROVE  SafeAt(b, v)
  OBVIOUS
<1>0a. TypeOK /\ VotesSafe /\ OneValuePerBallot
  BY <1>0 DEF Inv
<1>1. \A a \in Q : maxBal[a] >= b
  BY <1>0 DEF ShowsSafeAt
<1>2. PICK c \in -1..(b-1) :
            /\ (c /= -1) => \E a \in Q : VotedFor(a, c, v)
            /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteAt(a, d)
  BY <1>0 DEF ShowsSafeAt
<1>3. Q \subseteq Acceptor
  BY QuorumAssumption
<1>4. SUFFICES ASSUME NEW c0 \in 0..(b-1)
                PROVE  NoneOtherChoosableAt(c0, v)
  BY DEF SafeAt
<1>5. b \in Nat /\ c0 \in Nat
  BY DEF Ballot
<1>6. CASE c0 > c
  <2>1. c0 \in (c+1)..(b-1)
    BY <1>5, <1>2, <1>6
  <2>2. \A a \in Q : DidNotVoteAt(a, c0)
    BY <1>2, <2>1
  <2>3. \A a \in Q : maxBal[a] \in Ballot \cup {-1}
    BY <1>3, <1>0a DEF TypeOK
  <2>4. \A a \in Q : maxBal[a] > c0
    BY <1>1, <2>3, <1>5, <1>6 DEF Ballot
  <2>5. \A a \in Q : VotedFor(a, c0, v) \/ CannotVoteAt(a, c0)
    BY <2>2, <2>4 DEF CannotVoteAt
  <2>. QED  BY <2>5 DEF NoneOtherChoosableAt
<1>7. CASE c0 = c
  <2>1. c \in Nat
    BY <1>5, <1>7
  <2>2. c \in Ballot
    BY <2>1 DEF Ballot
  <2>3. PICK aStar \in Q : VotedFor(aStar, c, v)
    BY <1>2, <1>5, <1>7
  <2>4. aStar \in Acceptor
    BY <1>3, <2>3
  <2>5. \A a \in Q : VotedFor(a, c, v) \/ DidNotVoteAt(a, c)
    <3> SUFFICES ASSUME NEW a \in Q,
                         ~ DidNotVoteAt(a, c)
                  PROVE  VotedFor(a, c, v)
      OBVIOUS
    <3>1. PICK w \in Value : VotedFor(a, c, w)
      BY DEF DidNotVoteAt
    <3>2. a \in Acceptor
      BY <1>3
    <3>3. w = v
      BY <2>3, <2>4, <3>1, <3>2, <2>2, <1>0a, OneValuePerBallotApply
    <3>. QED  BY <3>1, <3>3
  <2>6. \A a \in Q : maxBal[a] \in Ballot \cup {-1}
    BY <1>3, <1>0a DEF TypeOK
  <2>7. \A a \in Q : maxBal[a] > c
    BY <1>1, <2>6, <1>5, <1>7, <2>1 DEF Ballot
  <2>8. \A a \in Q : VotedFor(a, c, v) \/ CannotVoteAt(a, c)
    BY <2>5, <2>7 DEF CannotVoteAt
  <2>. QED  BY <2>8, <1>7 DEF NoneOtherChoosableAt
<1>8. CASE c0 < c
  <2>1. c \in Nat /\ c0 < c
    BY <1>5, <1>8
  <2>2. c \in Ballot
    BY <2>1 DEF Ballot
  <2>3. PICK aStar \in Q : VotedFor(aStar, c, v)
    BY <1>2, <1>5, <1>8
  <2>4. aStar \in Acceptor
    BY <1>3, <2>3
  <2>5. SafeAt(c, v)
    BY <2>3, <2>4, <2>2, <1>0a DEF VotesSafe
  <2>6. c0 \in 0..(c-1)
    BY <1>5, <2>1
  <2>. QED  BY <2>5, <2>6 DEF SafeAt
<1>. QED  BY <1>6, <1>7, <1>8

============================================================================
