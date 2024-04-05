---- MODULE MCReachable ----
EXTENDS Reachable

ConnectedToSomeButNotAll ==
  CHOOSE succ \in [Nodes -> SUBSET Nodes]
  : \A n \in Nodes : Cardinality(succ[n]) = 2

LimitedSeq(S) == UNION {
  [1 .. len -> S]
  : len \in 0 .. Cardinality(Nodes)
}

============================

