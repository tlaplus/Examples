------------------------------- MODULE CRDT ---------------------------------

EXTENDS Naturals

CONSTANT Node

VARIABLE counter

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

FairSpec ==
  /\ Spec
  /\ \A n, o \in Node : WF_counter(Gossip(n,o))
  \* The following conjunct causes the spec to not be machine
  \* closed. This is orthogonal to the Finite Monotonic
  \* approach. Instead, it is an artifact of this particular
  \* spec. Alternatively, we could amend Spec to the effect that
  \* there is a sufficient number of successive Gossip actions.
  /\ \A n, o \in Node : <>[][Gossip(n,o)]_counter

THEOREM FairSpec => Convergence
THEOREM FairSpec => Monotonicity
=============================================================================

