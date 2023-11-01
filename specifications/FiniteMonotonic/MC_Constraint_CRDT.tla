------------------------- MODULE MC_Constraint_CRDT -------------------------
EXTENDS Naturals

CONSTANT Node

VARIABLES counter, converge

vars == <<counter, converge>>

S == INSTANCE CRDT

TypeOK ==
  /\ S!TypeOK
  /\ converge \in BOOLEAN

Safety == S!Safety

Monotonicity == S!Monotonicity

Liveness == converge ~> S!Convergence

Init ==
  /\ S!Init
  /\ converge = FALSE

Increment(n) ==
  /\ ~converge
  /\ S!Increment(n)
  /\ UNCHANGED converge

Gossip(n, o) ==
  /\ S!Gossip(n, o)
  /\ UNCHANGED converge

Converge ==
  /\ converge' = TRUE
  /\ UNCHANGED counter

Next ==
  \/ \E n \in Node : Increment(n)
  \/ \E n, o \in Node : Gossip(n, o)
  \/ Converge

Fairness == \A n, o \in Node : WF_vars(Gossip(n, o))

StateConstraint == \A n, o \in Node : counter[n][o] <= 3

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ Fairness

=============================================================================

