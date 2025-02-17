These specifications illustrate a technique for taking ordinarily-infinite monotonic systems and turning them finite for the purposes of model-checking.
Briefly, this is accomplished by limiting the maximum divergence (difference between lowest and highest value) of any monotonic variable across the system, then continually transposing the set of monotonic variables to their lowest value.
Neither this approach nor the older approach have a proof of soundness and completeness.  They have been tested on a few examples and seem to work well in practice.

Specs & models include:
- `CRDT.tla`: the spec of a basic grow-only counter CRDT
- `ReplicatedLog.tla`: the spec of a basic append-only replicated log
- `DistributedReplicatedLog.tla`: a spec of a distributed replicated log that demonstrates how the technique can be used to find violations of a liveness property (`Insync`).
