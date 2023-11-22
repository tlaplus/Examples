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

WriteTx(n, tx) ==
  /\ ~converge
  /\ Len(log) < Divergence
  /\ S!WriteTx(n, tx)
  /\ UNCHANGED converge

ExecuteTx(n) ==
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

Fairness == \A n \in Node : WF_vars(ExecuteTx(n))

Next ==
  \/ \E n \in Node : \E tx \in Transaction : WriteTx(n, tx)
  \/ \E n \in Node : ExecuteTx(n)
  \/ GarbageCollect
  \/ Converge

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ Fairness

=============================================================================

