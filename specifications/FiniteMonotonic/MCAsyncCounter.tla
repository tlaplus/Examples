---------------------------- MODULE MCAsyncCounter --------------------------
EXTENDS Naturals

CONSTANT Node, Divergence

VARIABLES counter, converge

StateView == <<counter>>

vars == <<counter, converge>>

S == INSTANCE AsyncCounter

TypeOK == S!TypeOK

Liveness == S!Liveness

Increment(n) ==
  /\ counter[n] < Divergence
  /\ S!Increment(n)

SetMin(s) == CHOOSE e \in s : \A o \in s : e <= o

GarbageCollect ==
  LET allHavePassed == SetMin({counter[n] : n \in Node}) IN
  /\ counter' = [n \in Node |-> counter[n] - allHavePassed]
  /\ UNCHANGED converge

Next ==
  \/ \E n \in Node : Increment(n)
  \/ \E n, o \in Node : S!Gossip(n, o)
  \/ S!Converge
  \/ GarbageCollect

Fairness == \A n, o \in Node : WF_vars(S!Gossip(n, o))

Spec ==
  /\ S!Init
  /\ [][Next]_vars
  /\ Fairness

THEOREM Spec =>
  /\ TypeOK
  /\ Liveness

=============================================================================

