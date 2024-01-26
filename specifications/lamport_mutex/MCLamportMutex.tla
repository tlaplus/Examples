--------------------------- MODULE MCLamportMutex ---------------------------
EXTENDS LamportMutex
CONSTANT MaxNat
ASSUME MaxNat \in Nat
NatOverride == 0 .. MaxNat
=============================================================================

