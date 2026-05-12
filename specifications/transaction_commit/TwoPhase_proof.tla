--------------------------- MODULE TwoPhase_proof --------------------------
(***************************************************************************)
(* TLAPS proofs of TwoPhase.tla theorems:                                  *)
(*                                                                         *)
(*   TPSpec => []TPTypeOK            (Band E, directly inductive)          *)
(*   TPSpec => []TC!TCConsistent     (Band M, no conflicting decisions)    *)
(*                                                                         *)
(* TC!TCConsistent says no two RMs end up "committed" and "aborted"        *)
(* simultaneously.  It is not directly inductive; the strengthening below *)
(* tracks the message-sequencing facts that explain why the TM-broadcast  *)
(* "Commit" and "Abort" decisions are mutually exclusive, and how each    *)
(* RM's local state correlates with what is on the wire.                   *)
(*                                                                         *)
(* The candidate inductive invariant was first validated with Apalache    *)
(* (per Konnov/Kuppe/Merz, arXiv:2211.07216 Sec. 3.2) on a finite         *)
(* instance with 3 RMs:                                                    *)
(*                                                                         *)
(*   TPInit  /\ [TPNext]_vars |=0  Inv      (initial states satisfy Inv) *)
(*   InvInit /\ [TPNext]_vars |=1  Inv      (Inv is preserved one step)  *)
(*   Inv => TCConsistent                    (Inv implies the goal)        *)
(***************************************************************************)
EXTENDS TwoPhase, TLAPS

(***************************************************************************)
(*                            TPSpec => []TPTypeOK                         *)
(***************************************************************************)

THEOREM TypeCorrect == TPSpec => []TPTypeOK
<1>1. TPInit => TPTypeOK
  BY DEF TPInit, TPTypeOK
<1>2. TPTypeOK /\ [TPNext]_<<rmState, tmState, tmPrepared, msgs>> => TPTypeOK'
  <2> SUFFICES ASSUME TPTypeOK,
                      [TPNext]_<<rmState, tmState, tmPrepared, msgs>>
               PROVE  TPTypeOK'
    OBVIOUS
  <2>. USE DEF TPTypeOK, Message
  <2>1. CASE TMCommit       BY <2>1 DEF TMCommit
  <2>2. CASE TMAbort        BY <2>2 DEF TMAbort
  <2>3. ASSUME NEW rm \in RM, TMRcvPrepared(rm)
        PROVE  TPTypeOK'
    BY <2>3 DEF TMRcvPrepared
  <2>4. ASSUME NEW rm \in RM, RMPrepare(rm)
        PROVE  TPTypeOK'
    BY <2>4 DEF RMPrepare
  <2>5. ASSUME NEW rm \in RM, RMChooseToAbort(rm)
        PROVE  TPTypeOK'
    BY <2>5 DEF RMChooseToAbort
  <2>6. ASSUME NEW rm \in RM, RMRcvCommitMsg(rm)
        PROVE  TPTypeOK'
    BY <2>6 DEF RMRcvCommitMsg
  <2>7. ASSUME NEW rm \in RM, RMRcvAbortMsg(rm)
        PROVE  TPTypeOK'
    BY <2>7 DEF RMRcvAbortMsg
  <2>8. CASE UNCHANGED <<rmState, tmState, tmPrepared, msgs>>
    BY <2>8
  <2>. QED  BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8 DEF TPNext
<1>. QED  BY <1>1, <1>2, PTL DEF TPSpec

(***************************************************************************)
(*                  TPSpec => []TC!TCConsistent  (Band M)                  *)
(***************************************************************************)

CommitMsg == [type |-> "Commit"]
AbortMsg  == [type |-> "Abort"]
PrepMsg(rm) == [type |-> "Prepared", rm |-> rm]

(***************************************************************************)
(* The strengthened inductive invariant.  Each conjunct is a fact that    *)
(* the protocol's actions preserve and that together imply TCConsistent.  *)
(*                                                                         *)
(*   1. TPTypeOK                                                           *)
(*   2. The TM commits at most one decision (mutex on Commit/Abort msgs). *)
(*   3-5. tmState mirrors which decision message has been broadcast.       *)
(*   6. tmPrepared only contains RMs that actually sent "Prepared".        *)
(*   7. RMs that have a "Prepared" msg in flight are no longer "working". *)
(*   8. "committed" RMs imply CommitMsg has been broadcast.                *)
(*   9. CommitMsg in msgs implies every RM had sent "Prepared" first      *)
(*      (preserved from TMCommit's tmPrepared = RM precondition).          *)
(*  10. "aborted" RMs split into two cases:                                *)
(*        - via RMRcvAbortMsg  (AbortMsg in msgs), or                      *)
(*        - via RMChooseToAbort (the RM never sent "Prepared").            *)
(***************************************************************************)
Inv ==
  /\ TPTypeOK
  /\ ~ (CommitMsg \in msgs /\ AbortMsg \in msgs)
  /\ tmState = "init"      => CommitMsg \notin msgs /\ AbortMsg \notin msgs
  /\ tmState = "committed" => CommitMsg \in msgs
  /\ tmState = "aborted"   => AbortMsg \in msgs
  /\ \A rm \in tmPrepared : PrepMsg(rm) \in msgs
  /\ \A rm \in RM : PrepMsg(rm) \in msgs => rmState[rm] # "working"
  /\ \A rm \in RM : rmState[rm] = "committed" => CommitMsg \in msgs
  /\ CommitMsg \in msgs => \A rm \in RM : PrepMsg(rm) \in msgs
  /\ \A rm \in RM : rmState[rm] = "aborted" =>
        \/ AbortMsg \in msgs
        \/ PrepMsg(rm) \notin msgs

LEMMA InvInductive == TPSpec => []Inv
<1>1. TPInit => Inv
  BY DEF TPInit, Inv, TPTypeOK, Message, CommitMsg, AbortMsg, PrepMsg
<1>2. Inv /\ [TPNext]_<<rmState, tmState, tmPrepared, msgs>> => Inv'
  <2> SUFFICES ASSUME Inv,
                      [TPNext]_<<rmState, tmState, tmPrepared, msgs>>
               PROVE  Inv'
    OBVIOUS
  <2>. USE DEF Inv, TPTypeOK, Message, CommitMsg, AbortMsg, PrepMsg
  <2>1. CASE TMCommit
    \* tmState : init -> committed; CommitMsg added to msgs.
    \* AbortMsg notin msgs in pre-state (tmState=init).  tmPrepared = RM
    \* gives \A rm \in RM : PrepMsg(rm) \in msgs (via conjunct 6).
    BY <2>1 DEF TMCommit
  <2>2. CASE TMAbort
    \* tmState : init -> aborted; AbortMsg added.  CommitMsg notin msgs.
    BY <2>2 DEF TMAbort
  <2>3. ASSUME NEW rm \in RM, TMRcvPrepared(rm)
        PROVE  Inv'
    \* tmPrepared grows by {rm}, msgs unchanged.  PrepMsg(rm) \in msgs is
    \* the precondition, so the new tmPrepared still satisfies conjunct 6.
    BY <2>3 DEF TMRcvPrepared
  <2>4. ASSUME NEW rm \in RM, RMPrepare(rm)
        PROVE  Inv'
    \* rmState[rm] : working -> prepared; PrepMsg(rm) added to msgs.
    BY <2>4 DEF RMPrepare
  <2>5. ASSUME NEW rm \in RM, RMChooseToAbort(rm)
        PROVE  Inv'
    \* rmState[rm] : working -> aborted, no msg change.  PrepMsg(rm)
    \* could only have been in msgs if rmState[rm] # "working", but the
    \* precondition says it WAS "working", so PrepMsg(rm) \notin msgs;
    \* conjunct 10 holds via the second disjunct.
    BY <2>5 DEF RMChooseToAbort
  <2>6. ASSUME NEW rm \in RM, RMRcvCommitMsg(rm)
        PROVE  Inv'
    \* rmState[rm] becomes "committed"; preconditions: CommitMsg \in msgs.
    BY <2>6 DEF RMRcvCommitMsg
  <2>7. ASSUME NEW rm \in RM, RMRcvAbortMsg(rm)
        PROVE  Inv'
    \* rmState[rm] becomes "aborted"; preconditions: AbortMsg \in msgs.
    BY <2>7 DEF RMRcvAbortMsg
  <2>8. CASE UNCHANGED <<rmState, tmState, tmPrepared, msgs>>
    BY <2>8
  <2>. QED  BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8 DEF TPNext
<1>. QED  BY <1>1, <1>2, PTL DEF TPSpec

THEOREM Consistency == TPSpec => []TC!TCConsistent
<1>1. Inv => TC!TCConsistent
  \* Suppose rmState[rm1] = "aborted" and rmState[rm2] = "committed".
  \* From conjunct 8: CommitMsg \in msgs.
  \* From conjunct 9: PrepMsg(rm1) \in msgs.
  \* From conjunct 2: AbortMsg \notin msgs.
  \* From conjunct 10 applied to rm1: AbortMsg \in msgs (false) or
  \* PrepMsg(rm1) \notin msgs (false).  Contradiction.
  BY DEF Inv, TC!TCConsistent, CommitMsg, AbortMsg, PrepMsg
<1>. QED  BY <1>1, InvInductive, PTL

============================================================================
