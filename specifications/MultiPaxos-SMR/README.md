## Practical SMR-style MultiPaxos Spec

This folder contains a practical state machine replication (SMR) style TLA+ specification of the MultiPaxos protocol. It very closely models how a real SMR system would implement MultiPaxos for strongly-consistent replication of a log of state machine commands.

### Files List

The files include:

- `MultiPaxos.tla`: main protocol spec written in PlusCal and with translation attached
- `MultiPaxos_MC.tla`: entrance of running model checking; contains the checked `TypeOK` and `Linearizability` constraints
- `MultiPaxos_MC.cfg`: recommended model inputs and configurations (checks < 8 min on a 40-core machine)
- `MultiPaxos_MC_small.cfg`: config with one fewer write request in input (checks < 10 seconds)

To play with the spec and fail the check, try for example:

- Change the `await` condition in `HandleAcceptReplies` from `>= MajorityNum` to `>= MajorityNum - 1`: this will fail the linearizability check
- Comment out the `Send` of `AcceptReplyMsg` in `HandleAccept`: this will lead to deadlocks and thus reveal a certain "liveness" problem

### What’s Good About This Spec

This spec differs from traditional, general descriptions of Paxos/MultiPaxos in the following aspects:

- It models MultiPaxos in a practical SMR system style that’s much closer to real implementations than those classic, abstract specs (e.g., [this](https://github.com/josehu07/tla-examples/tree/master/specifications/Paxos) or [this](https://github.com/nano-o/MultiPaxos))
  - All servers explicitly replicate a log of instances, each holding a command
  - Numbers of client write/read commands are made model inputs
  - Explicit termination condition is defined, thus semi-liveness can be checked by not having deadlocks
  - Safety constraint is defined as a clean client-viewed linearizability property upon termination
  - See the comments in the source files for more details…
- Optimizations are applied to the spec to reduce the state space W.L.O.G.
  - Model checking with recommended inputs completes in < 8 min on a 40-core server machine
  - Commenting out the `HandleCommitNotice` action (which is the least significant) reduces check time down to < 2 min
- It is easy to extend this spec and add more interesting features, for example:
  - Node failure injection
  - Leader lease and local read

---

**External links**:

- Link to blog post: [https://www.josehu.com/technical/2024/02/19/practical-MultiPaxos-TLA-spec.html](https://www.josehu.com/technical/2024/02/19/practical-MultiPaxos-TLA-spec.html)
- Link to the Summerset codebase: [https://github.com/josehu07/summerset](https://github.com/josehu07/summerset)
  - It is a protocol-generic distributed KV-store written in async Rust
  - You can find the corresponding Rust implementation of a replication KV-store using almost the exact MultiPaxos protocol as modeled in this spec
