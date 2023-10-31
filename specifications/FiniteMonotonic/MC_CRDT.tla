------------------------------- MODULE MC_CRDT ------------------------------
EXTENDS Naturals

CONSTANTS Node, Divergence

VARIABLES counter, converge

vars == <<counter, converge>>

S == INSTANCE CRDT

TypeOK ==
  /\ counter \in [Node -> [Node -> 0 .. Divergence]]
  /\ converge \in BOOLEAN

Safety == S!Safety

Monotonicity == S!Monotonicity

Liveness == converge ~> S!Convergence

Init ==
  /\ S!Init
  /\ converge = FALSE

Increment(n) ==
  /\ ~converge
  /\ counter[n][n] < Divergence
  /\ S!Increment(n)
  /\ UNCHANGED converge

Gossip(n, o) ==
  /\ S!Gossip(n, o)
  /\ UNCHANGED converge

Converge ==
  /\ converge' = TRUE
  /\ UNCHANGED counter

GarbageCollect ==
  LET SetMin(s) == CHOOSE e \in s : \A o \in s : e <= o IN
  LET Transpose == SetMin({counter[n][o] : n, o \in Node}) IN
  /\ counter' = [
      n \in Node |-> [
        o \in Node |-> counter[n][o] - Transpose
      ]
    ]
  /\ UNCHANGED converge

Next ==
  \/ \E n \in Node : Increment(n)
  \/ \E n, o \in Node : Gossip(n, o)
  \/ Converge
  \/ GarbageCollect

Fairness == \A n, o \in Node : WF_vars(Gossip(n, o))

StateConstraint == \A n, o \in Node : counter[n][o] <= 4

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ Fairness

=============================================================================

