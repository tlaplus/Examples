-------------------------- MODULE MC_ReplicatedLog --------------------------
EXTENDS Naturals, Sequences

CONSTANTS Node, Transaction, Divergence

VARIABLES log, executed, converge

vars == <<log, executed, converge>>

S == INSTANCE ReplicatedLog

TypeOK ==
  /\ log \in Seq(Transaction)
  /\ Len(log) <= Divergence
  /\ executed \in [Node -> 0 .. Divergence]

Liveness == converge ~> S!Convergence

Init ==
  /\ S!Init
  /\ converge = FALSE

\* Experiment with combining the write & garbage collect steps
GCWriteTx(n, tx) ==
  LET SetMin(s) == CHOOSE e \in s : \A o \in s : e <= o IN
  LET MinExecuted == SetMin({executed[o] : o \in Node}) IN
  LET NewTxId == Len(log) - MinExecuted + 1 IN
  /\ ~converge
  /\ executed[n] = Len(log)
  /\ NewTxId <= Divergence
  /\ log' = [
      i \in 1 .. NewTxId |->
        IF i < NewTxId THEN log[i + MinExecuted] ELSE tx
    ]
  /\ executed' = [
      o \in Node |->
        IF o = n THEN NewTxId ELSE executed[o] - MinExecuted
    ]
  /\ UNCHANGED converge

\* Experiment with combining the execute & garbage collect steps
GCExecuteTx(n) ==
  LET SetMin(s) == CHOOSE e \in s : \A o \in s : e <= o IN
  LET MinExecuted == SetMin({
    IF o = n THEN executed[o] + 1 ELSE executed[o] : o \in Node
  }) IN
  /\ log' = [i \in 1 .. Len(log) - MinExecuted |-> log[i + MinExecuted]]
  /\ executed' = [
      o \in Node |->
        IF o = n
        THEN executed[o] - MinExecuted + 1
        ELSE executed[o] - MinExecuted
    ]
  /\ UNCHANGED converge

SimpleWriteTx(n, tx) ==
  /\ ~converge
  /\ Len(log) < Divergence
  /\ S!WriteTx(n, tx)
  /\ UNCHANGED converge

SimpleExecuteTx(n) ==
  /\ S!ExecuteTx(n)
  /\ UNCHANGED converge

GarbageCollect ==
  LET SetMin(s) == CHOOSE e \in s : \A o \in s : e <= o IN
  LET MinExecuted == SetMin({executed[o] : o \in Node}) IN
  /\ log' = [i \in 1 .. Len(log) - MinExecuted |-> log[i + MinExecuted]]
  /\ executed' = [n \in Node |-> executed[n] - MinExecuted]
  /\ UNCHANGED converge

Converge ==
  /\ converge' = TRUE
  /\ UNCHANGED <<log, executed>>

GCWriteNext ==
  \/ \E n \in Node : \E tx \in Transaction : GCWriteTx(n, tx)
  \/ \E n \in Node : SimpleExecuteTx(n)
  \/ Converge

SimpleFairness == \A n \in Node : WF_vars(SimpleExecuteTx(n))

GCWriteSpec ==
  /\ Init
  /\ [][GCWriteNext]_vars
  /\ SimpleFairness

GCExecuteNext ==
  \/ \E n \in Node : \E tx \in Transaction : GCWriteTx(n, tx)
  \/ \E n \in Node : SimpleExecuteTx(n)
  \/ Converge

GCFairness == \A n \in Node : WF_vars(GCExecuteTx(n))

GCExecuteSpec ==
  /\ Init
  /\ [][GCExecuteNext]_vars
  /\ GCFairness

SimpleNext ==
  \/ \E n \in Node : \E tx \in Transaction : SimpleWriteTx(n, tx)
  \/ \E n \in Node : SimpleExecuteTx(n)
  \/ GarbageCollect
  \/ Converge

SimpleSpec ==
  /\ Init
  /\ [][SimpleNext]_vars
  /\ SimpleFairness

=============================================================================

