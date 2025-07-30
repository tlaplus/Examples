------------------------------- MODULE Barrier --------------------------------
EXTENDS Integers

CONSTANTS 
  N

VARIABLES pc

vars == << pc >>

ProcSet == (1..N)

Init == 
  /\ pc = [p \in ProcSet |-> "b0"]

b0(self) ==
  /\ pc[self] = "b0"
  /\ pc' = [pc EXCEPT ![self] = "b1"]

b1 ==
  /\ \A p \in ProcSet : pc[p] = "b1"
  /\ pc' = [p \in ProcSet |-> "b0"]

Next == 
  \/ \E p \in ProcSet : b0(p)
  \/ b1

Spec == Init /\ [][Next]_vars

-------------------------------------------------------------------------------

TypeOK ==
  /\ pc \in [ProcSet -> {"b0", "b1"}]

\* A process cannot leave the barrier if there are still other processes
\* that need to enter it
BarrierProperty ==
  /\ [][\A p,q \in ProcSet : pc[p] = "b0" /\ pc[q] = "b1" => pc'[q] = "b1"]_vars

===============================================================================