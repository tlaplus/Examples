# Formal specifications of DAG-based consensus protocols

Copied from [nano-o/dag-consensus](https://github.com/nano-o/dag-consensus).

## Block DAGs

[BlockDag.tla](./BlockDag.tla) defines block DAGs and how DAG-based consensus protocols linearize them.
This specification should be reusable for other DAG-based consensus protocols.
To run some basic tests, run `make block-dag-test`.

## Sailfish

[Sailfish.tla](./Sailfish.tla) contains a high-level formal specification modeling both the Sailfish and Sailfish++ protocols (at the level of abstraction of the specification, the differences between the protocols are not visible).

Sailfish is described in the paper ["Sailfish: Towards Improving the Latency of DAG-based BFT"](https://eprint.iacr.org/2024/472), S&P 2025, and Sailfish++ appears in the paper ["Optimistic, Signature-Free Reliable Broadcast and Its Applications"](https://arxiv.org/abs/2505.02761), CCS 2025.

To run TLC on the specification, first translate the PlusCal part to TLA+ with `make trans TLA_SPEC=Sailfish.tla` and then run `make run-tlc TLA_SPEC=TLCSailfish1.tla`. The specification `TLCSailfish1.tla` and the associated config file `TLCSailfish1.cfg` fix a concrete system size, model-checking bounds, and the properties to check (typing invariant, agreement, and liveness).

Have a look at the Makefile to tweak TLC options.

Notes:
- `make trans` rewrites the TLA+ module in place after PlusCal translation.
- The Makefile expects `java` and `wget` to be available to download/run `tla2tools.jar`.
