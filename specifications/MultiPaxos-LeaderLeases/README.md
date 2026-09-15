## MultiPaxos Leader Leases Spec

This folder contains a TLA+ specification for MultiPaxos with leader leases. It builds on top of the [MultiPaxos-SMR spec](https://github.com/tlaplus/Examples/tree/master/specifications/MultiPaxos-SMR), adds the leasing mechanism between nodes, and builds a leader leases algorithm with these building blocks.

Replicas grant leases to their believed leader, promising not to step up as a competing leader or vote for another node while the lease is active. Consequently, a leader is considered *stable* when holding >= majority number of leases, where it can be confident it is the only such leader of the cluster. The stable leader hence can serve linearizable reads directly from it's latest committed value, without involving a quorum round. A lease is usually kept refreshed, but reacts to failures via expiration.

### Files List

The files include:

- `MultiPaxos.tla`: full protocol spec written in PlusCal and with translation attached
- `MultiPaxos_MC.tla`: entrance of running model checking; contains the checked constraints
- `MultiPaxos_MC.cfg`: recommended model inputs and configurations (checks in ~20 hours on an EC2 `r7i.24xlarge` instance)
- `MultiPaxos_MC_short.cfg`: config with one fewer write and one fewer timer tick in the input (checks in ~1 minute)

To play with the spec and fail the check, try for example:

- Change the `await` condition in `HandleAcceptReplies` from `>= MajorityNum` to `>= MajorityNum - 1`: this will fail the linearizability check
- Comment out the `Send` of `AcceptReplyMsg` in `HandleAccept`: this will lead to deadlocks and thus reveal a certain "liveness" problem
- Remove the third clause of the `ThinkAmLeader` condition which gates the stable leader condition by majority: this will fail the linearizability check
- Remove the `+ TLease` grantor-side extension in the `SpontaneousRenew` action: this breaks the lease's fundamental coverage property

---

**External links**:

- Link to a rundown of distributed leases, covering leader leases and more: <https://bodega-consensus.com/>
  - Plain blog post version: <https://www.josehu.com/technical/2026/07/07/distributed-lease-and-consensus.html>
- Link to the Summerset codebase: <https://github.com/josehu07/summerset>
  - It is a protocol-generic distributed KV-store written in async Rust
  - You can find the corresponding Rust implementation of a replication KV-store using almost the exact MultiPaxos protocol (with leader leases as an optional feature) as modeled in this spec
