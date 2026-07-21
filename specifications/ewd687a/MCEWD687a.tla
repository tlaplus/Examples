---- MODULE MCEWD687a ----
EXTENDS EWD687a, TLC

CONSTANTS 
    P1, P2, P3, \* constants representing the non-leader processes in the MC instance
    MaxCounter  \* bound on counter values

MCProcs == {Leader, P1, P2, P3}
MCEdges == 
    {<<Leader, P1>>, <<P1, P2>>, <<P1, P2>>, <<P2, P1>>, <<P2,P3>>}

StateConstraint == \A e \in Edges : 
    /\ msgs[e] < MaxCounter
    /\ acks[e] < MaxCounter 
    /\ sentUnacked[e] < MaxCounter 
    /\ rcvdUnacked[e] < MaxCounter

=============================================================================
\* Modification History
\* Created Fri Oct 01 12:28:54 PDT 2021 by lamport
