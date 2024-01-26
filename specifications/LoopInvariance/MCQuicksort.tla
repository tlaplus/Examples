---------------------------- MODULE MCQuicksort -----------------------------
EXTENDS Quicksort
CONSTANT MaxSeqLen
ASSUME MaxSeqLen \in Nat
LimitedSeq(S) == UNION {[1 .. n -> S] : n \in 1 .. MaxSeqLen}
=============================================================================

