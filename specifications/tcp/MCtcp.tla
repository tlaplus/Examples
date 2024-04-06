---- MODULE MCtcp ----
EXTENDS tcp, TLC

CONSTANTS A, B
peers == {A, B}
Symmetry == Permutations(peers)

MCInit ==
    \* One node starts in the SYN-SENT state, i.e., one node has already received the active open command. The other node
    \* is in the listen state, i.e., it has received the passive open command.
    \E node \in Peers:
        /\ tcb = [p \in Peers |-> TRUE]
        /\ connstate = [p \in Peers |-> IF p = node THEN "SYN-SENT" ELSE "LISTEN"]
        /\ network = [p \in Peers |-> IF p = node THEN <<>> ELSE << "SYN" >>]

NoRetransmission ==
    \A p \in Peers :
        \A i \in 1..Len(network[p]) - 1 :
            network[p][i] # network[p][i + 1]

SingleActiveOpen ==
    \* A real system will allow infinitely many active opens of TCP connections. An
    \* explicit state model checker like TLC cannot enumerate infinitely many states.
    \* Thus, do not allow multiple active opens (the first active open is implicit in Init).
    ~ \E local, remote \in Peers:
        \/ ACTIVE_OPEN(local, remote)
        \/ PASSIVE_OPEN(local, remote)
        \/ SEND(local, remote)

=============================================================================
\* Modification History
\* Created Tue Apr 02 10:38:50 PDT 2024 by markus
