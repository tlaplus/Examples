--------------------------- MODULE MCChangRoberts ---------------------------
EXTENDS Naturals
CONSTANT N
VARIABLES msgs, pc, initiator, state
ASSUME N \in Nat
Id == [i \in 1 .. N |-> i]
INSTANCE ChangRoberts
=============================================================================

