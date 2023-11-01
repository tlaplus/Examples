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
WriteTx(n, tx) ==
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
        IF o /= n THEN executed[o] - MinExecuted ELSE NewTxId
    ]
  /\ UNCHANGED converge

ExecuteTx(n) ==
  /\ S!ExecuteTx(n)
  /\ UNCHANGED converge

Converge ==
  /\ converge' = TRUE
  /\ UNCHANGED <<log, executed>>

Next ==
  \/ \E n \in Node : \E tx \in Transaction : WriteTx(n, tx)
  \/ \E n \in Node : ExecuteTx(n)
  \/ Converge

Fairness == \A n \in Node : WF_vars(ExecuteTx(n))

Test == Len(log) /= Divergence

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ Fairness

=============================================================================

