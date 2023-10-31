-------------------------- MODULE MCCRDTGCounter ----------------------------
EXTENDS Naturals

CONSTANTS Node, Divergence

VARIABLES counter, converge

vars == <<counter, converge>>

S == INSTANCE CRDTGCounter

TypeInvariant ==
  /\ counter \in [Node -> [Node -> 0 .. Divergence]]
  /\ converge \in BOOLEAN

Safety == S!Safety

Liveness == S!Liveness

Monotonicity ==
  \/ S!Monotonicity
  \/ [][]_vars

Increment(n) ==
  /\ counter[n][n] < Divergence
  /\ S!Increment(n)

SetMin(s) == CHOOSE e \in s : \A o \in s : e <= o

GarbageCollect ==
  LET transpose == SetMin({counter[n][o] : n, o \in Node}) IN
  /\ counter' = [
      n \in Node |-> [
        o \in Node |-> counter[n][o] - transpose
      ]
    ]
  /\ UNCHANGED converge

Next ==
  \/ \E n \in Node : Increment(n)
  \/ \E n, o \in Node : S!Gossip(n, o)
  \/ S!Converge
  \/ GarbageCollect

Spec ==
  /\ S!Init
  /\ [][Next]_vars
  /\ S!Fairness

THEOREM Spec =>
  /\ TypeInvariant
  /\ Safety
  /\ Liveness
  /\ Monotonicity

=============================================================================

