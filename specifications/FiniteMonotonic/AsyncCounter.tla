---------------------------- MODULE AsyncCounter ----------------------------
EXTENDS Naturals

CONSTANT Node

VARIABLES counter, converge

vars == <<counter, converge>>

Max(a, b) == IF a > b THEN a ELSE b

TypeOK == counter \in [Node -> Nat] /\ converge \in BOOLEAN

Liveness == converge ~> \A n, o \in Node : counter[n] = counter[o]

Init == counter = [n \in Node |-> 0] /\ converge = FALSE

Increment(n) ==
  /\ ~converge
  /\ counter' = [counter EXCEPT ![n] = @ + 1]
  /\ UNCHANGED converge

Gossip(n, o) ==
  /\ counter' = [counter EXCEPT ![o] = Max(counter[n], @)]
  /\ UNCHANGED converge

Converge == converge' = FALSE /\ UNCHANGED counter

Next ==
  \/ \E n \in Node : Increment(n)
  \/ \E n, o \in Node : Gossip(n, o)
  \/ Converge

Fairness == \A n, o \in Node : WF_vars(Gossip(n, o))

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ Fairness

THEOREM Spec =>
  /\ TypeOK
  /\ Liveness

=============================================================================

