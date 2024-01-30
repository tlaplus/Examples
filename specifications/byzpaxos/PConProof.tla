---------------------------- MODULE PConProof -------------------------------
(***************************************************************************)
(* This is a specification of a variant of the classic Paxos consensus     *)
(* algorithm described in                                                  *)
(*                                                                         *)
(*    AUTHOR = "Leslie Lamport",                                           *)
(*    TITLE = "The Part-Time Parliament",                                  *)
(*    journal = ACM Transactions on Computing Systems,                     *)
(*    volume = 16,                                                         *)
(*    Number = 2,                                                          *)
(*    Month = may,                                                         *)
(*    Year = 1998,                                                         *)
(*    pages = "133--169"                                                   *)
(*                                                                         *)
(* This algorithm was also described without proof in Brian Oki's Ph.D.    *)
(* thesis.                                                                 *)
(*                                                                         *)
(* It describes the actions that can be performed by leaders, but does not *)
(* introduce explicit leader processes.  More precisely, the specification *)
(* is written as if there were a separate leader for each ballot.          *)
(*                                                                         *)
(* This variant of the classic Paxos algorithm is an abstraction of an     *)
(* algorithm that is used in                                               *)
(*                                                                         *)
(*    AUTHOR = "Leslie Lamport and Dahlia Malkhi and Lidong Zhou ",        *)
(*    TITLE = "Vertical Paxos and Primary-Backup Replication",             *)
(*    Conference = "Proceedings of PODC 2009",                             *)
(*    editor    = {Srikanta Tirthapura and Lorenzo Alvisi},                *)
(*    publisher = {ACM},                                                   *)
(*    YEAR = 2009,                                                         *)
(*    PAGES = "312--313"                                                   *)
(*                                                                         *)
(* and in                                                                  *)
(*                                                                         *)
(*    Cheap paxos                                                          *)
(*    United States Patent 7249280                                         *)
(*    Inventors: Lamport, Leslie B.                                        *)
(*               Massa, Michael T.                                         *)
(*    Filing Date:06/18/2004                                               *)
(*                                                                         *)
(* In the classic Paxos algorithm, the leader sends a phase 2a message for *)
(* a ballot b and value v that instructs acceptors to vote for v in ballot *)
(* b.  In terms of implementing the voting algorithm of module VoteProof,  *)
(* that 2a message serves two functions:                                   *)
(*                                                                         *)
(*   - It asserts that value v is safe at ballot b, so the acceptor        *)
(*     can vote for it without violating invariant VInv2                   *)
(*                                                                         *)
(*   - It tells the acceptors which single safe value they can vote        *)
(*     for in ballot b, so they can vote for that value without            *)
(*     violating VInv3.                                                    *)
(*                                                                         *)
(* The variant of the algorithm we specify here introduces phase 1c        *)
(* messages that perform the first function.  The phase 2a message serves  *)
(* only the first function, being sent only if a 1c message had been sent  *)
(* for the value.                                                          *)
(*                                                                         *)
(* This variant of the algorithm is useful when reconfiguration is         *)
(* performed by using different sets of acceptors for different ballots.   *)
(* The leader propagates knowledge of what values are safe at ballot b so  *)
(* that the acceptors in the current configuration are no longer needed to *)
(* determine that information.  If the ballot b leader determines that all *)
(* values are safe at b, then it sends a 1c message for every value and    *)
(* sends a phase 2a message only when it has a value to propose.  The      *)
(* presence of the 1c messages removes dependency on the acceptors of      *)
(* ballots numbered b or lower for progress.  (If the leader determines    *)
(* that only a single value is safe at b, then it sends the 1c and 2a      *)
(* messages together.)                                                     *)
(*                                                                         *)
(* In the algorithm described here, we do not include reconfiguration.     *)
(* Therefore, the sending of a 1c message serves only as a precondition    *)
(* for the sending of a 2a message with that value.                        *)
(*                                                                         *)
(* Classic Paxos and its variants maintain consensus in the presence of    *)
(* omission faults--faults in which a process fails to perform some        *)
(* enabled action or a message that is sent fails to be received.  The     *)
(* safety specification, which is given by the PlusCal code, does not      *)
(* require that any action need ever be performed.  A process need not     *)
(* execute an enabled action.  Receipt of a message is modeled by a        *)
(* process performing the action enabled by that message having been sent, *)
(* so message loss is also represented by a process not performing an      *)
(* enabled action.  Thus, failures are never mentioned in the description  *)
(* of the algorithm.                                                       *)
(***************************************************************************)
EXTENDS Integers, TLAPS
-----------------------------------------------------------------------------
(***************************************************************************)
(* The constant parameters and the set Ballots are the same as in the      *)
(* voting algorithm.                                                       *)
(***************************************************************************)
CONSTANT Value, Acceptor, Quorum

ASSUME QA == /\ \A Q \in Quorum : Q \subseteq Acceptor 
             /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {} 
                                                                     
Ballot ==  Nat

(***************************************************************************)
(* We are going to have a leader process for each ballot and an acceptor   *)
(* process for each acceptor.  So we can use the ballot numbers and the    *)
(* acceptors themselves as the identifiers for these processes, we assume  *)
(* that the set of ballots and the set of acceptors are disjoint.  For     *)
(* good measure, we also assume that -1 is not an acceptor, although that  *)
(* is probably not necessary.                                              *)
(***************************************************************************)
ASSUME BallotAssump == (Ballot \cup {-1}) \cap Acceptor = {}

(***************************************************************************)
(* We define None to be an unspecified value that is not in the set Value. *)
(***************************************************************************)
None == CHOOSE v : v \notin Value
 
(***************************************************************************)
(* This is a message-passing algorithm, so we begin by defining the set    *)
(* Message of all possible messages.  The messages are explained below     *)
(* with the actions that send them.  A message m with m.type = "1a" is     *)
(* called a 1a message, and similarly for the other message types.         *)
(***************************************************************************)
Message ==      [type : {"1a"}, bal : Ballot]
           \cup [type : {"1b"}, acc : Acceptor, bal : Ballot, 
                 mbal : Ballot \cup {-1}, mval : Value \cup {None}]
           \cup [type : {"1c"}, bal : Ballot, val : Value]
           \cup [type : {"2a"}, bal : Ballot, val : Value]
           \cup [type : {"2b"}, acc : Acceptor, bal : Ballot, val : Value]
-----------------------------------------------------------------------------


(***************************************************************************)
(* The algorithm is easiest to understand in terms of the set msgs of all  *)
(* messages that have ever been sent.  A more accurate model would use one *)
(* or more variables to represent the messages actually in transit, and it *)
(* would include actions representing message loss and duplication as well *)
(* as message receipt.                                                     *)
(*                                                                         *)
(* In the current spec, there is no need to model message loss explicitly. *)
(* The safety part of the spec says only what messages may be received and *)
(* does not assert that any message actually is received.  Thus, there is  *)
(* no difference between a lost message and one that is never received.    *)
(* The liveness property of the spec will make it clear what messages must *)
(* be received (and hence either not lost or successfully retransmitted if *)
(* lost) to guarantee progress.                                            *)
(*                                                                         *)
(* Another advantage of maintaining the set of all messages that have ever *)
(* been sent is that it allows us to define the state function `votes'     *)
(* that implements the variable of the same name in the voting algorithm   *)
(* without having to introduce a history variable.                         *)
(***************************************************************************)
(***********

In addition to the variable msgs, the algorithm uses four variables
whose values are arrays indexed by acceptor, where for any acceptor
`a':

  maxBal[a]  The largest ballot number in which `a' has participated
  
  maxVBal[a] The largest ballot number in which a has voted, or -1
             if it has never voted.   
             
  maxVVal[a] If `a' has voted, then this is the value it voted for in
             ballot maxVBal; otherwise it equals None.
             
As in the voting algorithm, an execution of the algorithm consists of an 
execution of zero or more ballots.  Different ballots may be in progress 
concurrently, and ballots may not complete (and need not even start).
A ballot b consists of the following actions (which need not all occur
in the indicated order).  

  Phase1a : The leader sends a 1a message for ballot b
  
  Phase1b : If maxBal[a] < b, an acceptor `a' responds to the 1a message by
            setting maxBal[a] to b and sending a 1b message to the leader
            containing the values of maxVBal[a] and maxVVal[a].
            
  Phase1c : When the leader has received ballot-b 1b messages from a 
            quorum, it determines some set of values that are safe
            at b and sends 1c messages for them.
            
  Phase2a : The leader sends a 2a message for some value for which it has
            already sent a ballot-b 1c message.
            
  Phase2b : Upon receipt of the 2a message, if maxBal[a] =< b, an
            acceptor `a' sets maxBal[a] and maxVBal[a] to b, sets
            maxVVal[a] to the value in the 2a message, and votes for
            that value in ballot b by sending the appropriate 2b
            message.

Here is the PlusCal code for the algorithm, which we call PCon.

--algorithm PCon {
  variables maxBal  = [a \in Acceptor |-> -1] ,
            maxVBal = [a \in Acceptor |-> -1] ,
            maxVVal = [a \in Acceptor |-> None] ,
            msgs = {}
  define {
    sentMsgs(t, b) == {m \in msgs : (m.type = t) /\ (m.bal = b)}
    
    (***********************************************************************)
    (* We define ShowsSafeAt so that ShowsSafeAt(Q, b, v) is true for a    *)
    (* quorum Q iff msgs contain ballot-b 1b messages from the acceptors   *)
    (* in Q showing that v is safe at b.                                   *)
    (***********************************************************************)
    ShowsSafeAt(Q, b, v) ==
      LET Q1b == {m \in sentMsgs("1b", b) : m.acc \in Q}
      IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a 
          /\ \/ \A m \in Q1b : m.mbal = -1
             \/ \E m1c \in msgs :
                  /\ m1c = [type |-> "1c", bal |-> m1c.bal, val |-> v] 
                  /\ \A m \in Q1b : /\ m1c.bal \geq m.mbal 
                                    /\ (m1c.bal = m.mbal) => (m.mval = v)

    }
  (*************************************************************************)
  (* The following two macros send a message and a set of messages,        *)
  (* respectively.  These macros are so simple that they're hardly worth   *)
  (* introducing, but they do make the processes a little easier to read.  *)
  (*************************************************************************)
  macro SendMessage(m) { msgs := msgs \cup {m} }
  macro SendSetOfMessages(S) { msgs := msgs \cup S }
  
  (*************************************************************************)
  (*                               The Actions                             *)
  (* As before, we describe each action as a macro.                        *)
  (*                                                                       *)
  (* The leader for process `self' can execute a Phase1a() action, which   *)
  (* sends the ballot `self' 1a message.                                   *)
  (*************************************************************************)
  macro Phase1a() { SendMessage([type |-> "1a", bal |-> self])}
  
  (*************************************************************************)
  (* Acceptor `self' can perform a Phase1b(b) action, which is enabled iff *)
  (* b > maxBal[self].  The action sets maxBal[self] to b and sends a      *)
  (* phase 1b message to the leader containing the values of maxVBal[self] *)
  (* and maxVVal[self].                                                    *)
  (*************************************************************************)
  macro Phase1b(b) {
    when (b > maxBal[self]) /\ (sentMsgs("1a", b) # {});
    maxBal[self] := b;
    SendMessage([type |-> "1b", acc |-> self, bal |-> b, 
                        mbal |-> maxVBal[self], mval |-> maxVVal[self]]) ;
   }

  (*************************************************************************)
  (* The ballot `self' leader can perform a Phase1c(S) action, which sends *)
  (* a set S of 1c messages indicating that the value in the val field of  *)
  (* each of them is safe at ballot b.  In practice, S will either contain *)
  (* a single message, or else will have a message for each possible       *)
  (* value, indicating that all values are safe.  In the first case, the   *)
  (* leader will immediately send a 2a message with the value contained in *)
  (* that single message.  (Both logical messages will be sent in the same *)
  (* physical message.) In the latter case, the leader is informing the    *)
  (* acceptors that all values are safe.  (All those logical messages      *)
  (* will, of course, be encoded in a single physical message.)            *)
  (*************************************************************************)
  macro Phase1c(S) {
    when \A v \in S : \E Q \in Quorum : ShowsSafeAt(Q, self, v) ;
    SendSetOfMessages({[type |-> "1c", bal |-> self, val |-> v] : v \in S}) 
   }

  (*************************************************************************)
  (* The ballot `self' leader can perform a Phase2a(v) action, sending a   *)
  (* 2a message for value v, if it has not already sent a 2a message (for  *)
  (* this ballot) and it has sent a ballot `self' 1c message with val      *)
  (* field v.                                                              *)
  (*************************************************************************)
  macro Phase2a(v) {
    when /\ sentMsgs("2a", self) = {} 
         /\ [type |-> "1c", bal |-> self, val |-> v] \in msgs ;
   SendMessage([type |-> "2a", bal |-> self, val |-> v]) 
   }

  (*************************************************************************)
  (* The Phase2b(b) action is executed by acceptor `self' in response to a *)
  (* ballot-b 2a message.  Note this action can be executed multiple times *)
  (* by the acceptor, but after the first one, all subsequent executions   *)
  (* are stuttering steps that do not change the value of any variable.    *)
  (*************************************************************************)
  macro Phase2b(b) {
    when b \geq maxBal[self] ;
    with (m \in sentMsgs("2a", b)) {
      maxBal[self]  := b ;
      maxVBal[self] := b ;
      maxVVal[self] := m.val;
      SendMessage([type |-> "2b", acc |-> self, bal |-> b, val |-> m.val])
    }
   }
   
  (*************************************************************************)
  (* An acceptor performs the body of its `while' loop as a single atomic  *)
  (* action by nondeterministically choosing a ballot in which its Phase1b *)
  (* or Phase2b action is enabled and executing that enabled action.  If   *)
  (* no such action is enabled, the acceptor does nothing.                 *)
  (*************************************************************************)
  process (acceptor \in Acceptor) {
    acc: while (TRUE) { 
           with (b \in Ballot) { either Phase1b(b) or Phase2b(b) 
          }
    }
   }

  (*************************************************************************)
  (* The leader of a ballot nondeterministically chooses one of its        *)
  (* actions that is enabled (and the argument for which it is enabled)    *)
  (* and performs it atomically.  It does nothing if none of its actions   *)
  (* is enabled.                                                           *)
  (*************************************************************************)
  process (leader \in Ballot) {
    ldr: while (TRUE) {
          either Phase1a() 
          or     with (S \in SUBSET Value) { Phase1c(S) }
          or     with (v \in Value) { Phase2a(v) }
         }
   }

}

The translator produces the following TLA+ specification of the algorithm.
Some blank lines have been deleted.
************)
\* BEGIN TRANSLATION
VARIABLES maxBal, maxVBal, maxVVal, msgs

(* define statement *)
sentMsgs(t, b) == {m \in msgs : (m.type = t) /\ (m.bal = b)}

ShowsSafeAt(Q, b, v) ==
  LET Q1b == {m \in sentMsgs("1b", b) : m.acc \in Q}
  IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a
      /\ \/ \A m \in Q1b : m.mbal = -1
         \/ \E m1c \in msgs :
              /\ m1c = [type |-> "1c", bal |-> m1c.bal, val |-> v]
              /\ \A m \in Q1b : /\ m1c.bal \geq m.mbal
                                /\ (m1c.bal = m.mbal) => (m.mval = v)


vars == << maxBal, maxVBal, maxVVal, msgs >>

ProcSet == (Acceptor) \cup (Ballot)

Init == (* Global variables *)
        /\ maxBal = [a \in Acceptor |-> -1]
        /\ maxVBal = [a \in Acceptor |-> -1]
        /\ maxVVal = [a \in Acceptor |-> None]
        /\ msgs = {}

acceptor(self) == \E b \in Ballot:
                    \/ /\ (b > maxBal[self]) /\ (sentMsgs("1a", b) # {})
                       /\ maxBal' = [maxBal EXCEPT ![self] = b]
                       /\ msgs' = (msgs \cup {([type |-> "1b", acc |-> self, bal |-> b,
                                                       mbal |-> maxVBal[self], mval |-> maxVVal[self]])})
                       /\ UNCHANGED <<maxVBal, maxVVal>>
                    \/ /\ b \geq maxBal[self]
                       /\ \E m \in sentMsgs("2a", b):
                            /\ maxBal' = [maxBal EXCEPT ![self] = b]
                            /\ maxVBal' = [maxVBal EXCEPT ![self] = b]
                            /\ maxVVal' = [maxVVal EXCEPT ![self] = m.val]
                            /\ msgs' = (msgs \cup {([type |-> "2b", acc |-> self, bal |-> b, val |-> m.val])})


leader(self) == /\ \/ /\ msgs' = (msgs \cup {([type |-> "1a", bal |-> self])})
                   \/ /\ \E S \in SUBSET Value:
                           /\ \A v \in S : \E Q \in Quorum : ShowsSafeAt(Q, self, v)
                           /\ msgs' = (msgs \cup ({[type |-> "1c", bal |-> self, val |-> v] : v \in S}))
                   \/ /\ \E v \in Value:
                           /\ /\ sentMsgs("2a", self) = {}
                              /\ [type |-> "1c", bal |-> self, val |-> v] \in msgs
                           /\ msgs' = (msgs \cup {([type |-> "2a", bal |-> self, val |-> v])})
                /\ UNCHANGED << maxBal, maxVBal, maxVVal >>


Next == (\E self \in Acceptor: acceptor(self))
           \/ (\E self \in Ballot: leader(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now rewrite the next-state relation in a way that makes it easier to *)
(* use in a proof.  We start by defining the formulas representing the     *)
(* individual actions.  We then use them to define the formula TLANext,    *)
(* which is the next-state relation we would have written had we specified *)
(* the algorithm directly in TLA+ rather than in PlusCal.                  *)
(***************************************************************************)
Phase1a(self) ==
  /\ msgs' = (msgs \cup {[type |-> "1a", bal |-> self]})
  /\ UNCHANGED << maxBal, maxVBal, maxVVal >>

Phase1c(self, S) ==
  /\ \A v \in S : \E Q \in Quorum : ShowsSafeAt(Q, self, v)
  /\ msgs' = (msgs \cup {[type |-> "1c", bal |-> self, val |-> v] : v \in S})
  /\ UNCHANGED << maxBal, maxVBal, maxVVal >>

Phase2a(self, v) ==
  /\ sentMsgs("2a", self) = {}
  /\ [type |-> "1c", bal |-> self, val |-> v] \in msgs
  /\ msgs' = (msgs \cup {[type |-> "2a", bal |-> self, val |-> v]})
  /\ UNCHANGED << maxBal, maxVBal, maxVVal >>

Phase1b(self, b) ==
  /\ b > maxBal[self]
  /\ sentMsgs("1a", b) # {}
  /\ maxBal' = [maxBal EXCEPT ![self] = b]
  /\ msgs' = msgs \cup {[type |-> "1b", acc |-> self, bal |-> b,
                         mbal |-> maxVBal[self], mval |-> maxVVal[self]]}
  /\ UNCHANGED <<maxVBal, maxVVal>>

Phase2b(self, b) ==
  /\ b \geq maxBal[self]
  /\ \E m \in sentMsgs("2a", b):
       /\ maxBal' = [maxBal EXCEPT ![self] = b]
       /\ maxVBal' = [maxVBal EXCEPT ![self] = b]
       /\ maxVVal' = [maxVVal EXCEPT ![self] = m.val]
       /\ msgs' = (msgs \cup {[type |-> "2b", acc |-> self,
                               bal |-> b, val |-> m.val]})

TLANext ==
  \/ \E self \in Acceptor : 
        \E b \in Ballot : \/ Phase1b(self, b) 
                          \/ Phase2b(self,b) 
  \/ \E self \in Ballot :
        \/ Phase1a(self)
        \/ \E S \in SUBSET Value : Phase1c(self, S)
        \/ \E v \in Value : Phase2a(self, v)

(***************************************************************************)
(* The following theorem specifies the relation between the next-state     *)
(* relation Next obtained by translating the PlusCal code and the          *)
(* next-state relation TLANext.                                            *)
(***************************************************************************)
THEOREM NextDef == (Next <=> TLANext) 
<1>2. ASSUME NEW self \in Acceptor
      PROVE  acceptor(self) <=> TLANext!1!(self) 
  BY <1>2, BallotAssump DEF acceptor, ProcSet, Phase1b, Phase2b
<1>3. ASSUME NEW self \in Ballot
      PROVE  leader(self) <=> TLANext!2!(self) 
  BY <1>3, BallotAssump, Zenon DEF leader, ProcSet, Phase1a, Phase1c, Phase2a
<1>4. QED
  BY <1>2, <1>3 DEF Next, TLANext
-----------------------------------------------------------------------------
(***************************************************************************)
(* The type invariant.                                                     *)
(***************************************************************************)
TypeOK == /\ maxBal  \in [Acceptor -> Ballot \cup {-1}]
          /\ maxVBal \in [Acceptor -> Ballot \cup {-1}]
          /\ maxVVal \in [Acceptor -> Value \cup {None}]
          /\ msgs \subseteq Message    

(***************************************************************************)
(* Here is the definition of the state-function `chosen' that implements   *)
(* the state-function of the same name in the voting algorithm.            *)
(***************************************************************************)
chosen == {v \in Value : \E Q \in Quorum, b \in Ballot :
                           \A a \in Q : \E m \in msgs : /\ m.type = "2b"
                                                        /\ m.acc  = a
                                                        /\ m.bal  = b
                                                        /\ m.val  = v} 
----------------------------------------------------------------------------
(***************************************************************************)
(* We now define the refinement mapping under which this algorithm         *)
(* implements the specification in module Voting.                          *)
(***************************************************************************)

(***************************************************************************)
(* As we observed, votes are registered by sending phase 2b messages.  So  *)
(* the array `votes' describing the votes cast by the acceptors is defined *)
(* as follows.                                                             *)
(***************************************************************************)
votes == [a \in Acceptor |->  
           {<<m.bal, m.val>> : m \in {mm \in msgs: /\ mm.type = "2b"
                                                   /\ mm.acc = a }}]
                                                   
(***************************************************************************)
(* We now instantiate module Voting, substituting:                         *)
(*                                                                         *)
(*  - The constants Value, Acceptor, and Quorum declared in this module    *)
(*    for the corresponding constants of that module Voting.               *)
(*                                                                         *)
(*  - The variable maxBal and the defined state function `votes' for the   *)
(*    correspondingly-named variables of module Voting.                    *)
(***************************************************************************)
V == INSTANCE VoteProof 

-----------------------------------------------------------------------------
(***************************************************************************)
(* We now define PInv to be what I believe to be an inductive invariant    *)
(* and assert the theorems for proving that this algorithm implements the  *)
(* voting algorithm under the refinement mapping specified by the INSTANCE *)
(* statement.  Whether PInv really is an inductive invariant will be       *)
(* determined only by a rigorous proof.                                    *)
(***************************************************************************)
PAccInv == \A a \in Acceptor : 
             /\ maxBal[a] >= maxVBal[a]
             /\ \A b \in (maxVBal[a]+1)..(maxBal[a]-1) : V!DidNotVoteIn(a,b)
             /\ (maxVBal[a] # -1) => V!VotedFor(a, maxVBal[a], maxVVal[a])
             
P1bInv == \A m \in msgs :
             (m.type = "1b") => 
               /\ (maxBal[m.acc] >= m.bal) /\ (m.bal > m.mbal)
               /\ \A b \in (m.mbal+1)..(m.bal-1) : V!DidNotVoteIn(m.acc,b)

P1cInv ==  \A m \in msgs : (m.type = "1c") => V!SafeAt(m.bal, m.val)

P2aInv == \A m \in msgs : 
            (m.type = "2a") => \E m1c \in msgs : /\ m1c.type = "1c"
                                                 /\ m1c.bal = m.bal 
                                                 /\ m1c.val = m.val
(***************************************************************************)
(* The following theorem is interesting in its own right.  It essentially  *)
(* asserts the correctness of the definition of ShowsSafeAt.               *)
(***************************************************************************)
THEOREM PT1 == TypeOK /\ P1bInv /\ P1cInv =>
                 \A Q \in Quorum, b \in Ballot, v \in Value :
                     ShowsSafeAt(Q, b, v) => V!SafeAt(b, v) 

PInv == TypeOK /\ PAccInv /\ P1bInv /\ P1cInv /\ P2aInv  

THEOREM Invariance == Spec => []PInv

THEOREM Implementation == Spec => V!Spec

(***************************************************************************)
(* The following result shows that our definition of `chosen' is the       *)
(* correct one, because it implements the state-function `chosen' of the   *)
(* voting algorithm.                                                       *)
(***************************************************************************)
THEOREM Spec => [](chosen = V!chosen)

(***************************************************************************)
(* The four theorems above have been checked by TLC for a model with 3     *)
(* acceptors, 2 values, and 3 ballot numbers.  Theorem PT1 was checked as  *)
(* an invariant, therefore checking only that it is true for all reachable *)
(* states.  This model is large enough that it would most likely have      *)
(* revealed any "coding" errors in the algorithm.  We believe that the     *)
(* algorithm is well-enough understood that it is unlikely to contain any  *)
(* fundamental errors.                                                     *)
(***************************************************************************)
=============================================================================
\* Modification History
\* Last modified Fri May 22 09:20:18 CEST 2020 by merz
\* Last modified Fri Jul 15 11:31:15 PDT 2011 by lamport

-----------------------------------------------------------------------------
(***************************************************************************)
(*                               Liveness                                  *)
(*                                                                         *)
(* The liveness property satisfied by PCon (and classic Paxos) is:         *)
(*                                                                         *)
(* If there is some ballot b and quorum Q such that                        *)
(*                                                                         *)
(*  1. No phase 1a messages (a) have been or (b) ever will be sent for any *)
(*     ballot number greater than b.                                       *)
(*                                                                         *)
(*  2. The ballot b leader eventually sends a phase 1a message for ballot  *)
(*     b.                                                                  *)
(*                                                                         *)
(*  3. Each acceptor in Q eventually responds to ballot b messages sent    *)
(*     by the ballot b leader--which implies that it eventually receives   *)
(*     those messages.                                                     *)
(*                                                                         *)
(*  4. The ballot b leader eventually executes its Phase2a action for      *)
(*     ballot b if it can.                                                 *)
(*                                                                         *)
(* then some value is eventually chosen.                                   *)
(*                                                                         *)
(* Note that Phase2a(b) is enabled if msgs contains a ballot b phase 1b    *)
(* message from every acceptor in Q.  Hence, 4 implies that if the leader  *)
(* eventually receives those messages, then it must perform its Phase2a(b) *)
(* action.  (It might perform that action before it receives those         *)
(* messages if it has received phase 1b messages from all the acceptors in *)
(* a different quorum.)                                                    *)
(***************************************************************************)
THEOREM Liveness ==
  Spec => \A b \in Ballot, Q \in Quorum :
           ( ( /\ (*********************************************************)
                  (* Assumption 1a.                                        *)
                  (*********************************************************)
                  \A m \in msgs : (m.type = "1a") => (m.bal < b)
               /\ (*********************************************************)
                  (* Assumption 1b.                                        *)
                  (*********************************************************)
                  \A c \in Ballot : (c > b) => [][~Phase1a(c)]_vars
               /\ (*********************************************************)
                  (* Assumption 2.                                         *)
                  (*********************************************************)
                  WF_vars(Phase1a(b))  
               /\ (*********************************************************)
                  (* Assumption 4.                                         *)
                  (*********************************************************)
                  WF_vars(\E v \in Value : Phase2a(b, v))  
               /\ (*********************************************************)
                  (* Assumption 3.                                         *)
                  (*********************************************************)
                  \A a \in Q : /\ WF_vars(Phase1b(a, b))
                               /\ WF_vars(Phase2b(a, b))
            )     
            ~> (chosen # {}) )
=============================================================================

\* The following is used to check theorem Liveness

CONSTANTS bb, QQ
           
CSpec == /\ Init
         /\ [][ /\ Next
                /\ \A c \in Ballot : (c > bb) => ~Phase1a(c)]_vars
         /\ WF_vars(Phase1a(bb))
         /\ WF_vars(\E v \in Value : Phase2a(bb, v))  
         /\ \A a \in QQ : /\ WF_vars(Phase1bForBallot(a, bb))
                               /\ WF_vars(Phase2bForBallot(a, bb))

CLiveness == (\A m \in msgs : (m.type = "1a") => (m.bal < bb))~>(chosen # {})

