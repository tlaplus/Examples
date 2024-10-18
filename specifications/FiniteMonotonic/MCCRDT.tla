------ MODULE MCCRDT -----
EXTENDS CRDT, IOUtils, TLC, TLCExt, Sequences, CSV

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
ASSUME F \in 0..7

------

SetMin(s) == CHOOSE e \in s : \A o \in s : e <= o

GarbageCollect ==
  LET Transpose == SetMin({counter[n][o] : n, o \in Node}) IN
  counter' = [
      n \in Node |-> [
        o \in Node |-> counter[n][o] - Transpose
      ]
    ]

------

View ==
    IF GB THEN vars ELSE 
        LET Transpose == SetMin({counter[n][o] : n, o \in Node}) IN
        [
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
    IF      F = 0 THEN TRUE
    ELSE IF F = 1 THEN WF_vars(GarbageCollect)
    ELSE IF F = 2 THEN \A n    \in Node : WF_vars(Increment(n))
    ELSE IF F = 3 THEN WF_vars(Next)
    ELSE IF F = 4 THEN \A n, o \in Node : WF_vars(Gossip(n,o))
    ELSE IF F = 5 THEN WF_vars(Next) /\ ~ \E n \in Node : <>[][Increment(n)]_vars
    ELSE IF F = 6 THEN WF_vars(Next) /\ \A n, o \in Node : <>[][Gossip(n,o)]_vars
    ELSE IF F = 7 THEN Convergence
    ELSE FALSE

MCMonotonicity == [][
  \/ S!Monotonic
  \/ \A a, b, c, d \in Node :
    (counter'[a][b] - counter[a][b]) = (counter'[c][d] - counter[c][d])
]_vars

------

StateConstraint == 
    IF Constraint THEN \A n, o \in Node : counter[n][o] <= Divergence ELSE TRUE

------

CSVFile ==
    IOEnv.O

NoCounterExample ==
    CounterExample.action = {} /\ CounterExample.state = {}

CounterExampleWithStuttering ==
    \E a \in CounterExample.action : a[1][1] = a[3][1] \* stuttering condition

CounterExampleWithLasso ==
    \E a \in CounterExample.action : a[1][1] > a[3][1] \* lasso condition

CounterExampleShape ==
    CASE NoCounterExample -> "none"
      [] CounterExampleWithStuttering -> "stuttering"
      [] CounterExampleWithLasso -> "lasso"
      [] OTHER -> "unexpected"

PostCondition ==
    CASE Divergence = 0 /\ NoCounterExample -> TRUE
      [] Divergence > 0 /\ F \in 0..1 /\ CounterExampleWithStuttering -> TRUE
      [] Divergence > 0 /\ F \in 0..1 /\ CounterExampleWithStuttering -> TRUE

      \* Changing Increment's enablement by conjoining counter[n][n] < Divergence causes (bogus) stuttering.
      [] Divergence = 1 /\ F = 2 /\~Constraint /\ CounterExampleWithStuttering -> TRUE
      [] Divergence > 1 /\ F = 2 /\~Constraint /\ CounterExampleWithStuttering -> TRUE

      [] Divergence = 1 /\ F = 2 /\ Constraint /\ NoCounterExample -> TRUE
      [] Divergence > 1 /\ F = 2 /\ Constraint /\ CounterExampleWithLasso -> TRUE

      [] Divergence = 1 /\ F \in 3..7 /\ NoCounterExample -> TRUE
      [] Divergence > 1 /\ F \in 3..5 /\ CounterExampleWithLasso -> TRUE
      [] Divergence > 1 /\ F \in 6..7 /\ NoCounterExample -> TRUE
      [] OTHER -> 
            /\ CSVRecords(CSVFile) = 0 => CSVWrite("F#D#G#C#CounterExample", <<>>, CSVFile) \* Write header if file is empty.
            /\ CSVWrite("%1$s#%2$s#%3$s#%4$s#%5$s", <<F, Divergence, GB, Constraint, CounterExampleShape>>, CSVFile)

======
