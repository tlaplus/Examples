--------------------------- MODULE MCBoulanger ------------------------------
EXTENDS Boulanger
CONSTANT MaxNat
NatOverride == 0 .. MaxNat
StateConstraint == \A process \in Procs : num[process] < MaxNat
=============================================================================

