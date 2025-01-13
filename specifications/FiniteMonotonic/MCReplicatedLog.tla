--------------------------- MODULE MCReplicatedLog ----------------------------
EXTENDS ReplicatedLog, FiniteSetsExt, TLC

\* Check that the (experimental) support for action composition
\* is enabled (see https://github.com/tlaplus/tlaplus/pull/805). 
\* Compare the DistributedReplicatedLog example for an alternative
\* that does not require action composition but comes with its
\* own set of trade-offs.
ASSUME TLCGet("-Dtlc2.tool.impl.Tool.cdot") = "true"

Constraint ==
    \* The bounds are educated guesses.
    /\ Len(log) < 5
    /\ \A n \in Node : Len(log) - executed[n] < 5

Reduction ==
    LET m == Min(Range(executed)) IN
    /\ executed' = [ n \in Node |-> executed[n] - m ]
    /\ log' = SubSeq(log, m + 1, Len(log))

WriteTxAndReduction(n, tx) ==
    WriteTx(n, tx) \cdot Reduction

ExecuteTxAndReduction(n) ==
    ExecuteTx(n) \cdot Reduction

ReductionNext ==
    \E n \in Node : 
        \/ ExecuteTx(n)
        \/ ExecuteTxAndReduction(n)
        \/ \E tx \in Transaction: 
            \/ WriteTx(n, tx)
            \/ WriteTxAndReduction(n, tx)

=============================================================================
