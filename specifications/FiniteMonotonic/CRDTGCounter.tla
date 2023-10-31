---------------------------- MODULE CRDTGCounter ----------------------------
EXTENDS Naturals

CONSTANT Node

VARIABLES counter, converge

vars == <<counter, converge>>

Max(a, b) == IF a > b THEN a ELSE b

TypeInvariant ==
  /\ counter \in [Node -> [Node -> Nat]]
  /\ converge \in BOOLEAN

Safety == \A n, o \in Node : counter[n][n] >= counter[o][n]

Monotonicity == [][\A n, o \in Node : counter'[n][o] >= counter[n][o]]_vars

Liveness == converge ~> \A n, o \in Node : counter[n] = counter[o]

Init ==
  /\ counter = [n \in Node |-> [o \in Node |-> 0]]
  /\ converge = FALSE

Increment(n) ==
  /\ ~converge
  /\ counter' = [counter EXCEPT ![n][n] = @ + 1]
  /\ UNCHANGED converge

Gossip(n, o) ==
  /\ counter' = [
    counter EXCEPT ![o] = [
      nodeView \in Node |->
        Max(counter[n][nodeView], counter[o][nodeView])
      ]
    ]
  /\ UNCHANGED converge

Converge ==
  /\ converge' = TRUE
  /\ UNCHANGED counter

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
  /\ TypeInvariant
  /\ Safety
  /\ Monotonicity
  /\ Liveness

=============================================================================

