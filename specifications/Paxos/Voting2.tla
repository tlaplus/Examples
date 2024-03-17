------------------------------- MODULE Voting2 -------------------------------

(***********************************************************************************)
(* This is a version of `^Voting.tla^' that can be analyzed by the `^Apalache^'    *)
(* model-checker. Here are the differences compared to `^Voting.tla^':             *)
(*                                                                                 *)
(*     * We make Ballot a constant in order to be able to substitute a finite set  *)
(*       for model-checking with Apalache.                                         *)
(*                                                                                 *)
(*     * We rewrite SafeAt and ShowsSafeAt to avoid ranges of integers with        *)
(*       non-constant bounds (which `^Apalache^' does not support).                *)
(*                                                                                 *)
(* We also give an inductive invariant that proves the consistency property. On a  *)
(* desktop computer from 2022, `^Apalache^' takes 1 minute and 45 seconds to check *)
(* that the invariant is inductive when there are 3 values, 3 processes, and 4     *)
(* ballots. For model-checking with `^Apalache,^'see `^ApaVoting2.tla^'.           *)
(***********************************************************************************)
                                                                               
EXTENDS Integers

CONSTANTS
    Value,
    Acceptor,
    Quorum,
    Ballot

VARIABLES
    votes,
    maxBal

TypeOK ==
    /\ votes \in [Acceptor -> SUBSET (Ballot\times Value)]
    /\ maxBal \in [Acceptor -> Ballot\cup {-1}]

VotedFor(a, b, v) == <<b, v>> \in votes[a]

ChosenAt(b, v) ==
  \E Q \in Quorum : \A a \in Q : VotedFor(a, b, v)

chosen == {v \in Value : \E b \in Ballot : ChosenAt(b, v)}

DidNotVoteAt(a, b) == \A v \in Value : ~ VotedFor(a, b, v)

CannotVoteAt(a, b) == /\ maxBal[a] > b
                      /\ DidNotVoteAt(a, b)
NoneOtherChoosableAt(b, v) ==
   \E Q \in Quorum :
     \A a \in Q : VotedFor(a, b, v) \/ CannotVoteAt(a, b)

SafeAt(b, v) == \A c \in Ballot : c < b => NoneOtherChoosableAt(c, v)

ShowsSafeAt(Q, b, v) ==
  /\ \A a \in Q : maxBal[a] \geq b
  \* NOTE: `^Apalache^' does not support non-constant integer ranges (e.g. we cannot write (c+1)..(b-1))
  /\ \E c \in Ballot\cup {-1} :
    /\ c < b
    /\ (c # -1) => \E a \in Q : VotedFor(a, c, v)
    /\ \A d \in Ballot : c < d /\ d < b => \A a \in Q : DidNotVoteAt(a, d)

Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ maxBal = [a \in Acceptor |-> -1]

IncreaseMaxBal(a, b) ==
  /\ b > maxBal[a]
  /\ maxBal' = [maxBal EXCEPT ![a] = b]
  /\ UNCHANGED votes

VoteFor(a, b, v) ==
    /\ maxBal[a] \leq b
    /\ \A vt \in votes[a] : vt[1] # b
    /\ \A c \in Acceptor \ {a} :
         \A vt \in votes[c] : (vt[1] = b) => (vt[2] = v)
    /\ \E Q \in Quorum : ShowsSafeAt(Q, b, v)
    /\ votes' = [votes EXCEPT ![a] = @ \cup {<<b, v>>}]
    /\ maxBal' = [maxBal EXCEPT ![a] = b]

Next  ==  \E a \in Acceptor, b \in Ballot :
            \/ IncreaseMaxBal(a, b)
            \/ \E v \in Value : VoteFor(a, b, v)

Spec == Init /\ [][Next]_<<votes, maxBal>>

(********************************************************************************)
(* Next, we define an inductive invariant that shows consistency. We reuse      *)
(* definitions from Voting.tla and add the property NoVoteAfterMaxBal, which is *)
(* needed to make the invariant inductive.                                      *)
(********************************************************************************)

VotesSafe == \A a \in Acceptor, b \in Ballot, v \in Value :
                 VotedFor(a, b, v) => SafeAt(b, v)

OneValuePerBallot ==
    \A a1, a2 \in Acceptor, b \in Ballot, v1, v2 \in Value :
       VotedFor(a1, b, v1) /\ VotedFor(a2, b, v2) => (v1 = v2)

NoVoteAfterMaxBal == \A a \in Acceptor, b \in Ballot, v \in Value :
    <<b,v>> \in votes[a] => /\ b <= maxBal[a]

Consistency == \A v,w \in chosen : v = w

\* This invariant is inductive and establishes consistency:
Invariant ==
  /\ TypeOK
  /\ VotesSafe
  /\ OneValuePerBallot
  /\ NoVoteAfterMaxBal
  /\ Consistency

=====================================================================================
