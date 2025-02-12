------------------------------- MODULE CRDT ---------------------------------

EXTENDS Naturals

CONSTANT Node

VARIABLE counter
vars == counter

TypeOK == counter \in [Node -> [Node -> Nat]]

Safety == \A n, o \in Node : counter[n][n] >= counter[o][n]

Monotonic == \A n, o \in Node : counter'[n][o] >= counter[n][o]

Monotonicity == [][Monotonic]_counter

\* Repeatedly, the counters at all nodes are in sync.
Convergence == []<>(\A n, o \in Node : counter[n] = counter[o])

Init == counter = [n \in Node |-> [o \in Node |-> 0]]

Increment(n) == counter' = [counter EXCEPT ![n][n] = @ + 1]

Gossip(n, o) ==
  LET Max(a, b) == IF a > b THEN a ELSE b IN
  counter' = [
    counter EXCEPT ![o] = [
      nodeView \in Node |->
        Max(counter[n][nodeView], counter[o][nodeView])
      ]
    ]

Next ==
  \/ \E n \in Node : Increment(n)
  \/ \E n, o \in Node : Gossip(n, o)

Spec ==
  /\ Init
  /\ [][Next]_counter

THEOREM Spec => []Safety
THEOREM Spec => []TypeOK

(***************************************************************************)
(* Fairness and liveness assumptions.                                      *)
(* We assume that Gossip actions will eventually occur when enabled, and   *)
(* that from some point onwards, only Gossip actions will be performed.    *)
(* In other words, incrementation of counters happens only finitely often. *)
(* Note that the second conjunct is not a standard fairness condition,     *)
(* yet the overall specification is machine closed.                        *)
(***************************************************************************)
Fairness ==
    /\ \A n, o \in Node : WF_vars(Gossip(n,o))
    /\ <>[][\E n, o \in Node : Gossip(n,o)]_vars

FairSpec ==
  /\ Spec
  /\ Fairness

THEOREM FairSpec => Convergence
THEOREM FairSpec => Monotonicity
=============================================================================

