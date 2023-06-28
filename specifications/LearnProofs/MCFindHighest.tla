--------------------------- MODULE MCFindHighest ----------------------------
EXTENDS FindHighest

CONSTANTS MaxLength, MaxNat
ASSUME MaxLength \in Nat
ASSUME MaxNat \in Nat

MCConstraint == Len(f) <= MaxLength
MCNat == 0..MaxNat
MCSeq(S) == UNION {[1..n -> S] : n \in Nat}

=============================================================================

