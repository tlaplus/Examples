---- MODULE MCtcp ----
EXTENDS tcp, TLC

CONSTANTS A, B
peers == {A, B}
Symmetry == Permutations(peers)

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
