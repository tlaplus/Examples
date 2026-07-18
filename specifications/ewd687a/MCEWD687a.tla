---- MODULE MCEWD687a ----
EXTENDS EWD687a, TLC

CONSTANTS 
    L, P1, P2, P3, \* constants representing the processes in the MC instance
    MaxCounter     \* bound on counter values

MCProcs == {L, P1, P2, P3}
MCEdges == 
    {<<L, P1>>, <<P1, P2>>, <<P1, P2>>, <<P2, P1>>, <<P2,P3>>}

StateConstraint == \A e \in Edges : 
    /\ msgs[e] < MaxCounter
    /\ acks[e] < MaxCounter 
    /\ sentUnacked[e] < MaxCounter 
    /\ rcvdUnacked[e] < MaxCounter

=============================================================================
\* Modification History
\* Created Fri Oct 01 12:28:54 PDT 2021 by lamport
