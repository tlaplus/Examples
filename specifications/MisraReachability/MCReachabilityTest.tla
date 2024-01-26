---- MODULE MCReachabilityTest ----
EXTENDS ReachabilityTest, Sequences

CONSTANT RandomSuccCount

RandomSuccSet == SuccSet2(RandomSuccCount)

ASSUME \A i \in DOMAIN Test : Test[i]

LimitedSeq(S) == UNION {
  [1 .. len -> S]
  : len \in 0 .. Cardinality(Nodes)
}
===================================

