------ MODULE MCCRDT -----
EXTENDS CRDT, IOUtils, TLC

Divergence == 
    \* D=0 means there is no divergence. D=1 means Gossip synchronizes the system in a single step. 
    atoi(IOEnv.D)
ASSUME Divergence \in Nat

Constraint ==
    IOEnv.C = ToString(TRUE)
ASSUME Constraint \in BOOLEAN

GB ==
    IOEnv.G = ToString(TRUE)
ASSUME GB \in BOOLEAN

F ==
    atoi(IOEnv.F)
ASSUME F \in 0..6

------

GarbageCollect ==
  LET SetMin(s) == CHOOSE e \in s : \A o \in s : e <= o IN
  LET Transpose == SetMin({counter[n][o] : n, o \in Node}) IN
  counter' = [
      n \in Node |-> [
        o \in Node |-> counter[n][o] - Transpose
      ]
    ]

------

S == INSTANCE CRDT

MCIncrement(n) ==
  /\ IF Constraint THEN TRUE ELSE counter[n][n] < Divergence
  /\ S!Increment(n)

MCNext ==
  \/ S!Next
  \/ GB /\ GarbageCollect

MCFairness ==
    \* Note that TLC doesn't accept the following fairness condition if written with CASE.
    IF      F = 0 THEN WF_vars(Next) 
    ELSE IF F = 1 THEN WF_vars(GarbageCollect)
    ELSE IF F = 2 THEN WF_vars(Next) /\ ~ \E n \in Node : <>[][Increment(n)]_vars
    ELSE IF F = 3 THEN \A n, o \in Node : WF_vars(Gossip(n,o))
    ELSE IF F = 4 THEN \A n    \in Node : WF_vars(Increment(n))
    \* Fairness below are expected to to hold for an Divergence.
    ELSE IF F = 5 THEN WF_vars(Next) /\ \A n, o \in Node : <>[][Gossip(n,o)]_vars
    ELSE IF F = 6 THEN Convergence
    ELSE FALSE

MCMonotonicity == [][
  \/ S!Monotonic
  \/ \A a, b, c, d \in Node :
    (counter'[a][b] - counter[a][b]) = (counter'[c][d] - counter[c][d])
]_vars

------

StateConstraint == 
    IF Constraint THEN \A n, o \in Node : counter[n][o] <= Divergence ELSE TRUE

======