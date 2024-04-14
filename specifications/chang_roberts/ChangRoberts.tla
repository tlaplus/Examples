---------------------------- MODULE ChangRoberts ----------------------------
(***************************************************************************)
(* Algorithm by Chang and Roberts for electing a leader on a               *)
(* unidirectional ring. The algorithm originally appeared as               *)
(* E. Chang, R. Roberts: An improved algorithm for decentralized           *)
(* extrema-finding in circular configurations of processes,                *)
(* CACM 22(5): 281-283, 1979.                                              *)
(***************************************************************************)
EXTENDS Naturals, Sequences

(***************************************************************************)
(* Constant parameters:                                                    *)
(* - N is the number of nodes                                              *)
(* - Id is a sequence of natural numbers of length N such that             *)
(*   Id[i] denotes the identity of node i.                                 *)
(*   The algorithm can be initiated by several nodes, and the node with    *)
(*   the smallest identity will be elected as the leader.                  *)
(***************************************************************************)
CONSTANTS N, Id

Node == 1 .. N

ASSUME
  /\ N \in Nat \ {0}
  /\ Id \in Seq(Nat)
  /\ Len(Id) = N
  /\ \A m,n \in Node : m # n => Id[m] # Id[n]  \* IDs are unique

succ(n) == IF n=N THEN 1 ELSE n+1  \* successor along the ring

(** Chang-Roberts algorithm written in PlusCal
--algorithm ChangRoberts {
  (* msgs[n]: messages waiting to be received by node n *)
  variable msgs = [n \in Node |-> {}];
  fair process (node \in Node)
     variables
       (* this node may be an initiator or not *)
       initiator \in BOOLEAN,
       state = IF initiator THEN "cand" ELSE "lost";
  {
       \* initiators send their own ID to their neighbor
   n0: if (initiator) {
          msgs[succ(self)] := @ \cup {Id[self]}
       };
   n1: while (TRUE) {
         \* handle some incoming message
         with (id \in msgs[self],
               _msgs = [msgs EXCEPT ![self] = @ \ {id}]) {
           if (state = "lost") {  \* nodes that have already lost forward the message
              msgs := [_msgs EXCEPT ![succ(self)] = @ \cup {id}]
           } else if (id < Id[self]) {
             \* received smalled ID: record loss and forward the message
              state := "lost";
              msgs := [_msgs EXCEPT ![succ(self)] = @ \cup {id}]
           } else {
             \* do not forward the message; if it's the own ID, declare win
              msgs := _msgs;
              if (id = Id[self]) { state := "won" }
           }
         } \* end with
       } \* end while
   } \* end process
}  \* end algorithm
**)
\* BEGIN TRANSLATION
VARIABLES msgs, pc, initiator, state

vars == << msgs, pc, initiator, state >>

ProcSet == (Node)

Init == (* Global variables *)
        /\ msgs = [n \in Node |-> {}]
        (* Process node *)
        /\ initiator \in [Node -> BOOLEAN]
        /\ state = [self \in Node |-> IF initiator[self] THEN "cand" ELSE "lost"]
        /\ pc = [self \in ProcSet |-> "n0"]

n0(self) == /\ pc[self] = "n0"
            /\ IF initiator[self]
                  THEN /\ msgs' = [msgs EXCEPT ![succ(self)] = @ \cup {Id[self]}]
                  ELSE /\ TRUE
                       /\ msgs' = msgs
            /\ pc' = [pc EXCEPT ![self] = "n1"]
            /\ UNCHANGED << initiator, state >>

n1(self) == /\ pc[self] = "n1"
            /\ \E id \in msgs[self]:
                 LET _msgs == [msgs EXCEPT ![self] = @ \ {id}] IN
                   IF state[self] = "lost"
                      THEN /\ msgs' = [_msgs EXCEPT ![succ(self)] = @ \cup {id}]
                           /\ state' = state
                      ELSE /\ IF id < Id[self]
                                 THEN /\ state' = [state EXCEPT ![self] = "lost"]
                                      /\ msgs' = [_msgs EXCEPT ![succ(self)] = @ \cup {id}]
                                 ELSE /\ msgs' = _msgs
                                      /\ IF id = Id[self]
                                            THEN /\ state' = [state EXCEPT ![self] = "won"]
                                            ELSE /\ TRUE
                                                 /\ state' = state
            /\ pc' = [pc EXCEPT ![self] = "n1"]
            /\ UNCHANGED initiator

node(self) == n0(self) \/ n1(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Node: node(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Node : WF_vars(node(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
-----------------------------------------------------------------------------
(* type correctness *)
TypeOK ==
  /\ pc \in [Node -> {"n0", "n1", "Done"}]
  /\ msgs \in [Node -> SUBSET {Id[n] : n \in Node}]
  /\ initiator \in [Node -> BOOLEAN]
  /\ state \in [Node -> {"cand", "lost", "won"}]

(***************************************************************************)
(* Safety property: when node n wins the election, it is the initiator     *)
(* with the smallest ID, and all other nodes know that they lost.          *)
(***************************************************************************)
Correctness ==
  \A n \in Node : state[n] = "won" =>
     /\ initiator[n]
     /\ \A m \in Node \ {n} : 
           /\ state[m] = "lost"
           /\ initiator[m] => Id[m] > Id[n]

Liveness == (\E n \in Node : state[n] = "cand") => <>(\E n \in Node : state[n] = "won")
=============================================================================
\* Modification History
\* Last modified Tue Apr 27 20:05:58 PDT 2021 by markus
\* Last modified Sat Mar 24 10:00:11 CET 2018 by merz
\* Created Sat Apr 23 14:05:31 CEST 2016 by merz
