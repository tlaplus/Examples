---- MODULE MC_HDiskSynod ----
EXTENDS HDiskSynod, TLC
CONSTANT BallotCountPerProcess
BallotImpl(p) ==
  LET start == p * BallotCountPerProcess IN
  start .. (start + BallotCountPerProcess - 1)
IsMajorityImpl(s) == Cardinality(s) * 2 > N
==============================

