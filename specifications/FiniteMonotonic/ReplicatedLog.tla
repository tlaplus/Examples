--------------------------- MODULE ReplicatedLog ----------------------------
EXTENDS Naturals, Sequences

CONSTANTS Node, Transaction

VARIABLES log, executed

vars == <<log, executed>>

TypeOK ==
  /\ log \in Seq(Transaction)
  /\ executed \in [Node -> Nat]

Convergence == \A n \in Node : executed[n] = Len(log)

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

Next ==
  \/ \E n \in Node : \E tx \in Transaction: WriteTx(n, tx)
  \/ \E n \in Node : ExecuteTx(n)

Spec ==
  /\ Init
  /\ [][Next]_vars

=============================================================================

