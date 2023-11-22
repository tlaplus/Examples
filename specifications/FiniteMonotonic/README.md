These specifications illustrate a technique for taking ordinarily-infinite monotonic systems and turning them finite for the purposes of model-checking.
Briefly, this is accomplished by limiting the maximum divergence (difference between lowest and highest value) of any monotonic variable across the system, then continually transposing the set of monotonic variables to their lowest value.
The technique is explained at length in [this](https://ahelwer.ca/post/2023-11-01-tla-finite-monotonic/) blog post.

Specs & models include:
- `CRDT.tla`: the "good copy" spec of a basic grow-only counter CRDT
- `MC_CRDT.tla`: wraps `CRDT.tla` and implements the finitization technique
- `MC_CRDT.cfg`: a model for `MC_CRDT.tla`
- `MC_Constraint_CRDT.tla`: finitizes `CRDT.tla` using state constraints instead; included for comparison
- `MC_Constraint_CRDT.cfg`: a model for `MC_Constraint_CRDT.tla`
- `ReplicatedLog.tla`: the "good copy" spec of a basic append-only replicated log
- `MC_ReplicatedLog.tla`: wraps `ReplicatedLog.tla` and implements the finitization technique
- `MC_ReplicatedLog.cfg`: a model for `MC_ReplicatedLog.tla`

