--------------------------- MODULE ReplicatedLog ----------------------------
EXTENDS Naturals, Sequences

CONSTANTS Node, Transaction

VARIABLES log, executed

vars == <<log, executed>>

TypeOK ==
  /\ log \in Seq(Transaction)
  /\ executed \in [Node -> Nat]

Convergence == []<>(\A n \in Node : executed[n] = Len(log))

Safety ==
    \A n \in Node : executed[n] <= Len(log)

Init ==
  /\ log = <<>>
  /\ executed = [n \in Node |-> 0]

WriteTx(n, tx) ==
  /\ executed[n] = Len(log)
  /\ log' = Append(log, tx)
  /\ executed' = [executed EXCEPT ![n] = @ + 1]

ExecuteTx(n) ==
  /\ executed[n] < Len(log)
  /\ executed' = [executed EXCEPT ![n] = @ + 1]
  /\ UNCHANGED log

\* Why does WriteTx also increment executed?
\* It increments executed[n] for one of the nodes n.
\* ExecuteTx catches up the other nodes.
\* With a single node, ExecuteTx is a no-op because
\* t is never enabled.

Next ==
  \/ \E n \in Node : \E tx \in Transaction: WriteTx(n, tx)
  \/ \E n \in Node : ExecuteTx(n)

Spec ==
  /\ Init
  /\ [][Next]_vars

THEOREM Spec => []Safety
THEOREM Spec => []TypeOK

ExecFairSpec ==
  /\ Spec
  /\ \A n \in Node : WF_vars(ExecuteTx(n))
  \* The following conjunct causes the spec to not be machine
  \* closed. This is orthogonal to the Finite Monotonic
  \* approach.
  /\ \A n \in Node : <>[][ExecuteTx(n)]_vars

WriteFairSpec ==
  /\ Spec
  /\ \A n \in Node : \A tx \in Transaction: WF_vars(WriteTx(n, tx))
  \* The following conjunct causes the spec to not be machine
  \* closed. This is orthogonal to the Finite Monotonic
  \* approach.
  /\ \A n \in Node : \A tx \in Transaction: <>[][WriteTx(n, tx)]_vars

\* ExecFairSpec and WriteFairSpec both work because every suffix with
\* infinitely many WriteTx implies Convergence to WriteTx's enablement
\* condition.  Likewise, every suffix with infinitely many ExecuteTx
\* implies Convergence.
THEOREM ExecFairSpec => Convergence
THEOREM WriteFairSpec => Convergence

-----------------------------------------------------------------------------

InsufficientlyFairSpecA ==
    /\ Spec
    /\ WF_vars(Next)

InsufficientlyFairSpecB ==
    /\ Spec
    /\ \A n \in Node : \A tx \in Transaction: WF_vars(WriteTx(n, tx))

InsufficientlyFairSpecC ==
    /\ Spec
    /\ \A n \in Node : \A tx \in Transaction : WF_vars(ExecuteTx(n))

-----------------------------------------------------------------------------

EffectivelyFalseSpecA ==
    /\ Spec
    /\ \A n \in Node : \A tx \in Transaction : WF_vars(ExecuteTx(n))
    /\ \A n \in Node : \A tx \in Transaction: <>[][WriteTx(n, tx)]_vars

EffectivelyFalseSpecB ==
    /\ Spec
    /\ \A n \in Node : \A tx \in Transaction: WF_vars(WriteTx(n, tx))
    /\ \A n \in Node : <>[][ExecuteTx(n)]_vars

=============================================================================

