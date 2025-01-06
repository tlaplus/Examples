# TLA<sup>+</sup> Examples
[![Gitpod ready-to-code](https://img.shields.io/badge/Gitpod-ready--to--spec-908a85?logo=gitpod)](https://gitpod.io/#https://github.com/tlaplus/examples/)
[![Validate Specs & Models](https://github.com/tlaplus/Examples/actions/workflows/CI.yml/badge.svg)](https://github.com/tlaplus/Examples/actions/workflows/CI.yml)

This is a repository of TLA<sup>+</sup> specifications and models covering applications in a variety of fields.
It serves as:
- a comprehensive example library demonstrating how to specify an algorithm in TLA<sup>+</sup>
- a diverse corpus facilitating development & testing of TLA<sup>+</sup> language tools
- a collection of case studies in the application of formal specification in TLA<sup>+</sup>

All TLA<sup>+</sup> specs can be found in the [`specifications`](specifications) directory.
The table below lists all specs and indicates whether a spec is beginner-friendly, includes an additional PlusCal variant `(✔)`, or uses PlusCal exclusively. Additionally, the table specifies which verification tool—[TLC](https://github.com/tlaplus/tlaplus), [Apalache](https://github.com/apalache-mc/apalache), or [TLAPS](https://github.com/tlaplus/tlapm)—can be used to verify each specification.

## Examples Included Here
Here is a list of specs included in this repository, with links to the relevant directory and flags for various features:
| Name                                                                                                | Author(s)                                           | Beginner | TLAPS Proof | PlusCal | TLC Model | Apalache |
| --------------------------------------------------------------------------------------------------- | --------------------------------------------------- | :------: | :---------: | :-----: | :-------: | :------: |
| [Teaching Concurrency](specifications/TeachingConcurrency)                                          | Leslie Lamport                                      |    ✔     |      ✔      |    ✔    |     ✔     |          |
| [Loop Invariance](specifications/LoopInvariance)                                                    | Leslie Lamport                                      |    ✔     |      ✔      |    ✔    |     ✔     |          |
| [Learn TLA⁺ Proofs](specifications/LearnProofs)                                                     | Andrew Helwer                                       |    ✔     |      ✔      |    ✔    |     ✔     |          |
| [Boyer-Moore Majority Vote](specifications/Majority)                                                | Stephan Merz                                        |    ✔     |      ✔      |         |     ✔     |          |
| [Proof x+x is Even](specifications/sums_even)                                                       | Stephan Merz                                        |    ✔     |      ✔      |         |     ✔     |          |
| [The N-Queens Puzzle](specifications/N-Queens)                                                      | Stephan Merz                                        |    ✔     |             |    ✔    |     ✔     |          |
| [The Dining Philosophers Problem](specifications/DiningPhilosophers)                                | Jeff Hemphill                                       |    ✔     |             |    ✔    |     ✔     |          |
| [The Car Talk Puzzle](specifications/CarTalkPuzzle)                                                 | Leslie Lamport                                      |    ✔     |             |         |     ✔     |          |
| [The Die Hard Problem](specifications/DieHard)                                                      | Leslie Lamport                                      |    ✔     |             |         |     ✔     |          |
| [The Prisoners & Switches Puzzle](specifications/Prisoners)                                         | Leslie Lamport                                      |    ✔     |             |         |     ✔     |          |
| [Specs from Specifying Systems](specifications/SpecifyingSystems)                                   | Leslie Lamport                                      |    ✔     |             |         |     ✔     |          |
| [The Tower of Hanoi Puzzle](specifications/tower_of_hanoi)                                          | Markus Kuppe, Alexander Niederbühl                  |    ✔     |             |         |     ✔     |          |
| [Missionaries and Cannibals](specifications/MissionariesAndCannibals)                               | Leslie Lamport                                      |    ✔     |             |         |     ✔     |          |
| [Stone Scale Puzzle](specifications/Stones)                                                         | Leslie Lamport                                      |    ✔     |             |         |     ✔     |          |
| [The Coffee Can Bean Problem](specifications/CoffeeCan)                                             | Andrew Helwer                                       |    ✔     |             |         |     ✔     |          |
| [EWD687a: Detecting Termination in Distributed Computations](specifications/ewd687a)                | Stephan Merz, Leslie Lamport, Markus Kuppe          |    ✔     |             |   (✔)   |     ✔     |          |
| [The Boulangerie Algorithm](specifications/Bakery-Boulangerie)                                      | Leslie Lamport, Stephan Merz                        |          |      ✔      |    ✔    |     ✔     |          |
| [Misra Reachability Algorithm](specifications/MisraReachability)                                    | Leslie Lamport                                      |          |      ✔      |    ✔    |     ✔     |          |
| [Byzantizing Paxos by Refinement](specifications/byzpaxos)                                          | Leslie Lamport                                      |          |      ✔      |    ✔    |     ✔     |          |
| [EWD840: Termination Detection in a Ring](specifications/ewd840)                                    | Stephan Merz                                        |          |      ✔      |         |     ✔     |          |
| [EWD998: Termination Detection in a Ring with Asynchronous Message Delivery](specifications/ewd998) | Stephan Merz, Markus Kuppe                          |          |      ✔      |   (✔)   |     ✔     |          |
| [The Paxos Protocol](specifications/Paxos)                                                          | Leslie Lamport                                      |          |      ✔      |         |     ✔     |          |
| [Asynchronous Reliable Broadcast](specifications/bcastByz)                                          | Thanh Hai Tran, Igor Konnov, Josef Widder           |          |      ✔      |         |     ✔     |          |
| [Distributed Mutual Exclusion](specifications/lamport_mutex)                                        | Stephan Merz                                        |          |      ✔      |         |     ✔     |          |
| [Two-Phase Handshaking](specifications/TwoPhase)                                                    | Leslie Lamport, Stephan Merz                        |          |      ✔      |         |     ✔     |          |
| [Paxos (How to Win a Turing Award)](specifications/PaxosHowToWinATuringAward)                       | Leslie Lamport                                      |          |      ✔      |         |     ✔     |          |
| [Dijkstra's Mutual Exclusion Algorithm](specifications/dijkstra-mutex)                              | Leslie Lamport                                      |          |             |    ✔    |     ✔     |          |
| [The Echo Algorithm](specifications/echo)                                                           | Stephan Merz                                        |          |             |    ✔    |     ✔     |          |
| [The TLC Safety Checking Algorithm](specifications/TLC)                                             | Markus Kuppe                                        |          |             |    ✔    |     ✔     |          |
| [Transaction Commit Models](specifications/transaction_commit)                                      | Leslie Lamport, Jim Gray, Murat Demirbas            |          |             |    ✔    |     ✔     |          |
| [The Slush Protocol](specifications/SlushProtocol)                                                  | Andrew Helwer                                       |          |             |    ✔    |     ✔     |          |
| [Minimal Circular Substring](specifications/LeastCircularSubstring)                                 | Andrew Helwer                                       |          |             |    ✔    |     ✔     |          |
| [Snapshot Key-Value Store](specifications/KeyValueStore)                                            | Andrew Helwer, Murat Demirbas                       |          |             |    ✔    |     ✔     |          |
| [Chang-Roberts Algorithm for Leader Election in a Ring](specifications/chang_roberts)               | Stephan Merz                                        |          |             |    ✔    |     ✔     |          |
| [MultiPaxos in SMR-Style](specifications/MultiPaxos-SMR)                                            | Guanzhou Hu                                         |          |             |    ✔    |     ✔     |          |
| [Einstein's Riddle](specifications/EinsteinRiddle)                                                  | Isaac DeFrain, Giuliano Losa                        |          |             |         |           |    ✔     |
| [Resource Allocator](specifications/allocator)                                                      | Stephan Merz                                        |          |             |         |     ✔     |          |
| [Transitive Closure](specifications/TransitiveClosure)                                              | Stephan Merz                                        |          |             |         |     ✔     |          |
| [Atomic Commitment Protocol](specifications/acp)                                                    | Stephan Merz                                        |          |             |         |     ✔     |          |
| [SWMR Shared Memory Disk Paxos](specifications/diskpaxos)                                           | Leslie Lamport, Giuliano Losa                       |          |             |         |     ✔     |          |
| [Span Tree Exercise](specifications/SpanningTree)                                                   | Leslie Lamport                                      |          |             |         |     ✔     |          |
| [The Knuth-Yao Method](specifications/KnuthYao)                                                     | Ron Pressler, Markus Kuppe                          |          |             |         |     ✔     |          |
| [Huang's Algorithm](specifications/Huang)                                                           | Markus Kuppe                                        |          |             |         |     ✔     |          |
| [EWD 426: Token Stabilization](specifications/ewd426)                                               | Murat Demirbas, Markus Kuppe                        |          |             |         |     ✔     |          |
| [Sliding Block Puzzle](specifications/SlidingPuzzles)                                               | Mariusz Ryndzionek                                  |          |             |         |     ✔     |          |
| [Single-Lane Bridge Problem](specifications/SingleLaneBridge)                                       | Younes Akhouayri                                    |          |             |         |     ✔     |          |
| [Software-Defined Perimeter](specifications/SDP_Verification)                                       | Luming Dong, Zhi Niu                                |          |             |         |     ✔     |          |
| [Simplified Fast Paxos](specifications/SimplifiedFastPaxos)                                         | Lim Ngian Xin Terry, Gaurav Gandhi                  |          |             |         |     ✔     |          |
| [Checkpoint Coordination](specifications/CheckpointCoordination)                                    | Andrew Helwer                                       |          |             |         |     ✔     |          |
| [Finitizing Monotonic Systems](specifications/FiniteMonotonic)                                      | Andrew Helwer                                       |          |             |         |     ✔     |          |
| [Multi-Car Elevator System](specifications/MultiCarElevator)                                        | Andrew Helwer                                       |          |             |         |     ✔     |          |
| [Nano Blockchain Protocol](specifications/NanoBlockchain)                                           | Andrew Helwer                                       |          |             |         |     ✔     |          |
| [The Readers-Writers Problem](specifications/ReadersWriters)                                        | Isaac DeFrain                                       |          |             |         |     ✔     |          |
| [Asynchronous Byzantine Consensus](specifications/aba-asyn-byz)                                     | Thanh Hai Tran, Igor Konnov, Josef Widder           |          |             |         |     ✔     |          |
| [Folklore Reliable Broadcast](specifications/bcastFolklore)                                         | Thanh Hai Tran, Igor Konnov, Josef Widder           |          |             |         |     ✔     |          |
| [The Bosco Byzantine Consensus Algorithm](specifications/bosco)                                     | Thanh Hai Tran, Igor Konnov, Josef Widder           |          |             |         |     ✔     |          |
| [Consensus in One Communication Step](specifications/c1cs)                                          | Thanh Hai Tran, Igor Konnov, Josef Widder           |          |             |         |     ✔     |          |
| [One-Step Consensus with Zero-Degradation](specifications/cf1s-folklore)                            | Thanh Hai Tran, Igor Konnov, Josef Widder           |          |             |         |     ✔     |          |
| [Failure Detector](specifications/detector_chan96)                                                  | Thanh Hai Tran, Igor Konnov, Josef Widder           |          |             |         |     ✔     |          |
| [Asynchronous Non-Blocking Atomic Commit](specifications/nbacc_ray97)                               | Thanh Hai Tran, Igor Konnov, Josef Widder           |          |             |         |     ✔     |          |
| [Asynchronous Non-Blocking Atomic Commitment with Failure Detectors](specifications/nbacg_guer01)   | Thanh Hai Tran, Igor Konnov, Josef Widder           |          |             |         |     ✔     |          |
| [Spanning Tree Broadcast Algorithm](specifications/spanning)                                        | Thanh Hai Tran, Igor Konnov, Josef Widder           |          |             |         |     ✔     |          |
| [The Cigarette Smokers Problem](specifications/CigaretteSmokers)                                    | Mariusz Ryndzionek                                  |          |             |         |     ✔     |          |
| [Conway's Game of Life](specifications/GameOfLife)                                                  | Mariusz Ryndzionek                                  |          |             |         |     ✔     |          |
| [Chameneos, a Concurrency Game](specifications/Chameneos)                                           | Mariusz Ryndzionek                                  |          |             |         |     ✔     |          |
| [PCR Testing for Snippets of DNA](specifications/glowingRaccoon)                                    | Martin Harrison                                     |          |             |         |     ✔     |          |
| [RFC 3506: Voucher Transaction System](specifications/byihive)                                      | Santhosh Raju, Cherry G. Mathew, Fransisca Andriani |          |             |         |     ✔     |          |
| [Yo-Yo Leader Election](specifications/YoYo)                                                        | Ludovic Yvoz, Stephan Merz                          |          |             |         |      ✔    |          |
| [TCP as defined in RFC 9293](specifications/tcp)                                                    | Markus Kuppe                                        |          |             |         |      ✔    |          |
| [TLA⁺ Level Checking](specifications/LevelChecking)                                                 | Leslie Lamport                                      |          |             |         |           |          |
| [Condition-Based Consensus](specifications/cbc_max)                                                 | Thanh Hai Tran, Igor Konnov, Josef Widder           |          |             |         |           |          |
| [Buffered Random Access File](specifications/braf)                                                  | Calvin Loncaric                                     |          |             |         |     ✔     |          |
| [Disruptor](specifications/Disruptor)                                                               | Nicholas Schultz-Møller                             |          |             |         |     ✔     |          |

## Examples Elsewhere
Here is a list of specs stored in locations outside this repository, including submodules.
They are not covered by CI testing so it is possible they contain errors, the reported details are incorrect, or they are no longer available.
Ideally these will be moved into this repo over time.
| Spec                                                                                                                              | Details                                                                                                                                   | Author(s)                                                                  | Beginner | TLAPS Proof | TLC Model | PlusCal | Apalache |
| --------------------------------------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------- | -------------------------------------------------------------------------- | :------: | :---------: | :-------: | :-----: | :------: |
| [Blocking Queue](https://github.com/lemmy/BlockingQueue)                                                                          | BlockingQueue                                                                                                                             | Markus Kuppe                                                               |    ✔     |      ✔      |     ✔     |    (✔)  |          |
| IEEE 802.16 WiMAX Protocols                                                                                                       | 2006, [paper](https://users.cs.northwestern.edu/~ychen/Papers/npsec06.pdf), [specs](http://list.cs.northwestern.edu/802.16/)              | Prasad Narayana, Ruiming Chen, Yao Zhao, Yan Chen, Zhi (Judy) Fu, Hai Zhou |          |             |           |         |          |
| On the diversity of asynchronous communication                                                                                    | 2016, [paper](https://dl.acm.org/doi/10.1007/s00165-016-0379-x), [specs](http://hurault.perso.enseeiht.fr/asynchronousCommunication/)     | Florent Chevrou, Aurélie Hurault, Philippe Quéinnec                        |          |             |           |         |          |
| [Caesar](specifications/Caesar)                                                                                                   | Multi-leader generalized consensus protocol (Arun et al., 2017)                                                                           | Giuliano Losa                                                              |          |             |     ✔     |    ✔    |          |
| [CASPaxos](specifications/CASPaxos)                                                                                               | An extension of the single-decree Paxos algorithm to a compare-and-swap type register (Rystsov)                                           | Tobias Schottdorf                                                          |          |             |     ✔     |         |          |
| [DataPort](specifications/DataPort)                                                                                               | Dataport protocal 505.89PT, only PDF files (Biggs & Noriaki, 2016)                                                                        | Geoffrey Biggs, Noriaki Ando                                               |          |             |           |         |          |
| [egalitarian-paxos](specifications/egalitarian-paxos)                                                                             | Leaderless replication protocol based on Paxos (Moraru et al., 2013)                                                                      | Iulian Moraru                                                              |          |             |     ✔     |         |          |
| [fastpaxos](specifications/fastpaxos)                                                                                             | An extension of the classic Paxos algorithm, only PDF files (Lamport, 2006)                                                               | Leslie Lamport                                                             |          |             |           |         |          |
| [fpaxos](specifications/fpaxos)                                                                                                   | A variant of Paxos with flexible quorums (Howard et al., 2017)                                                                            | Heidi Howard                                                               |          |             |     ✔     |         |          |
| [HLC](specifications/HLC)                                                                                                         | Hybrid logical clocks and hybrid vector clocks (Demirbas et al., 2014)                                                                    | Murat Demirbas                                                             |          |             |     ✔     |    ✔    |          |
| [L1](specifications/L1)                                                                                                           | Data center network L1 switch protocol, only PDF files (Thacker)                                                                          | Tom Rodeheffer                                                             |          |             |           |         |          |
| [leaderless](specifications/leaderless)                                                                                           | Leaderless generalized-consensus algorithms (Losa, 2016)                                                                                  | Giuliano Losa                                                              |          |             |     ✔     |    ✔    |          |
| [losa_ap](specifications/losa_ap)                                                                                                 | The assignment problem, a variant of the allocation problem (Delporte-Gallet, 2018)                                                       | Giuliano Losa                                                              |          |             |     ✔     |    ✔    |          |
| [losa_rda](specifications/losa_rda)                                                                                               | Applying peculative linearizability to fault-tolerant message-passing algorithms and shared-memory consensus, only PDF files (Losa, 2014) | Giuliano Losa                                                              |          |             |           |         |          |
| [m2paxos](specifications/m2paxos)                                                                                                 | Multi-leader consensus protocols (Peluso et al., 2016)                                                                                    | Giuliano Losa                                                              |          |             |     ✔     |         |          |
| [mongo-repl-tla](specifications/mongo-repl-tla)                                                                                   | A simplified part of Raft in MongoDB (Ongaro, 2014)                                                                                       | Siyuan Zhou                                                                |          |             |     ✔     |         |          |
| [MultiPaxos](specifications/MultiPaxos)                                                                                           | The abstract specification of Generalized Paxos (Lamport, 2004)                                                                           | Giuliano Losa                                                              |          |             |     ✔     |         |          |
| [naiad](specifications/naiad)                                                                                                     | Naiad clock protocol, only PDF files (Murray et al., 2013)                                                                                | Tom Rodeheffer                                                             |          |             |     ✔     |         |          |
| [nfc04](specifications/nfc04)                                                                                                     | Non-functional properties of component-based software systems (Zschaler, 2010)                                                            | Steffen Zschaler                                                           |          |             |     ✔     |         |          |
| [raft](specifications/raft)                                                                                                       | Raft consensus algorithm (Ongaro, 2014)                                                                                                   | Diego Ongaro                                                               |          |             |     ✔     |         |          |
| [SnapshotIsolation](specifications/SnapshotIsolation)                                                                             | Serializable snapshot isolation (Cahill et al., 2010)                                                                                     | Michael J. Cahill, Uwe Röhm, Alan D. Fekete                                |          |             |     ✔     |         |          |
| [SyncConsensus](specifications/SyncConsensus)                                                                                     | Synchronized round consensus algorithm (Demirbas)                                                                                         | Murat Demirbas                                                             |          |             |     ✔     |    ✔    |          |
| [Termination](specifications/Termination)                                                                                         | Channel-counting algorithm (Kumar, 1985)                                                                                                  | Giuliano Losa                                                              |          |      ✔      |     ✔     |    ✔    |    ✔     |
| [Tla-tortoise-hare](specifications/Tla-tortoise-hare)                                                                             | Robert Floyd's cycle detection algorithm                                                                                                  | Lorin Hochstein                                                            |          |             |     ✔     |    ✔    |          |
| [VoldemortKV](specifications/VoldemortKV)                                                                                         | Voldemort distributed key value store                                                                                                     | Murat Demirbas                                                             |          |             |     ✔     |    ✔    |          |
| [Tencent-Paxos](specifications/TencentPaxos)                                                                                      | PaxosStore: high-availability storage made practical in WeChat. Proceedings of the VLDB Endowment(Zheng et al., 2017)                     | Xingchen Yi, Hengfeng Wei                                                  |          |      ✔      |     ✔     |         |          |
| [Paxos](https://github.com/neoschizomer/Paxos)                                                                                    | Paxos                                                                                                                                     |                                                                            |          |             |     ✔     |         |          |
| [Lock-Free Set](https://github.com/tlaplus/tlaplus/blob/master/tlatools/org.lamport.tlatools/src/tlc2/tool/fp/OpenAddressing.tla) | PlusCal spec of a lock-Free set used by TLC                                                                                               | Markus Kuppe                                                               |          |             |     ✔     |    ✔    |          |
| [ParallelRaft](specifications/ParalleRaft)                                                                                        | A variant of Raft                                                                                                                         | Xiaosong Gu, Hengfeng Wei, Yu Huang                                        |          |             |     ✔     |         |          |
| [CRDT-Bug](https://github.com/Alexander-N/tla-specs/tree/main/crdt-bug)                                                           | CRDT algorithm with defect and fixed version                                                                                              | Alexander Niederbühl                                                       |          |             |     ✔     |         |          |
| [asyncio-lock](https://github.com/Alexander-N/tla-specs/tree/main/asyncio-lock)                                                   | Bugs from old versions of Python's asyncio lock                                                                                           | Alexander Niederbühl                                                       |          |             |     ✔     |         |          |
| [Raft (with cluster changes)](https://github.com/dranov/raft-tla)                                                                 | Raft with cluster changes, and a version with Apalache type annotations but no cluster changes                                            | George Pîrlea, Darius Foom, Brandon Amos, Huanchen Zhang, Daniel Ricketts  |          |             |     ✔     |         |    ✔     |
| [MET for CRDT-Redis](https://github.com/elem-azar-unis/CRDT-Redis/tree/master/MET/TLA)                                            | Model-check the CRDT designs, then generate test cases to test CRDT implementations                                                       | Yuqi Zhang                                                                 |          |             |     ✔     |    ✔    |          |
| [Parallel increment](https://github.com/Cjen1/tla_increment)                                                                      | Parallel threads incrementing a shared variable. Demonstrates invariants, liveness, fairness and symmetry                                 | Chris Jensen                                                               |          |             |     ✔     |         |          |
| [The Streamlet consensus algorithm](https://github.com/nano-o/streamlet)                                                          | Specification and model-checking of both safety and liveness properties of Streamlet with TLC                                             | Giuliano Losa                                                              |          |             |     ✔     |    ✔    |          |
| [Petri Nets](https://github.com/elh/petri-tlaplus)                                                                                | Instantiable Petri Nets with liveness properties                                                                                          | Eugene Huang                                                               |          |             |     ✔     |         |          |
| [CRDT](https://github.com/JYwellin/CRDT-TLA)                                                                                      | Specifying and Verifying CRDT Protocols                                                                                                   | Ye Ji, Hengfeng Wei                                                        |          |             |     ✔     |         |          |
| [Azure Cosmos DB](https://github.com/tlaplus/azure-cosmos-tla)                                                                    | Consistency models provided by Azure Cosmos DB                                                                                            | Dharma Shukla, Ailidani Ailijiang, Murat Demirbas, Markus Kuppe            |          |             |     ✔     |    ✔    |          |

## License
The repository is under the MIT license and you are encouraged to publish your spec under a similarly-permissive license.
However, your spec can be included in this repo along with your own license if you wish.

## Support or Contact
Do you have any questions or comments?
Please open an issue or send an email to the [TLA+ group](https://groups.google.com/g/tlaplus).

## Contributing
Do you have your own case study or TLA<sup>+</sup> specification you'd like to share with the community?
Follow these instructions:
1. Fork this repository and create a new directory under `specifications` with the name of your spec
1. Place all TLA<sup>+</sup> files in the directory, along with their `.cfg` model files
1. You are encouraged to include at least one model that completes execution in less than 10 seconds, and (if possible) a model that fails in an interesting way - for example illustrating a system design you previously attempted that was found unsound by TLC
1. Ensure name of each `.cfg` file matches the `.tla` file it models, or has its name as a prefix; for example `SpecName.tla` can have the models `SpecName.cfg` and `SpecNameLiveness.cfg`, etc.
1. Consider including a `README.md` in the spec directory explaining the significance of the spec with links to any relevant websites or publications, or integrate this info as comments in the spec itself
1. Add an entry to the table of specs included in this repo, summarizing your spec and its attributes

The [`manifest.json`](manifest.json) file is the source of truth for this table, and is a detailed human- & machine-readable description of the specs & their models.
Its schema is [`manifest-schema.json`](manifest-schema.json).
All specs in this repository are subject to CI validation to ensure quality.

## Adding Spec to Continuous Integration
To combat bitrot, it is important to add your spec and model to the continuous integration system.
To do this, you'll have to update the [`manifest.json`](manifest.json) file with machine-readable records of your spec files.
If this process doesn't work for you, you can alternatively modify the [`.ciignore`](.ciignore) file to exclude your spec from validation.
Modifying the `manifest.json` can be done manually or (recommended) following these directions:
1. Ensure you have Python 3.11+ installed
1. It is considered best practice to create & initialize a Python virtual environment to preserve your system package store; run `python -m venv .` then `source ./bin/activate` on Linux & macOS or `.\Scripts\activate.bat` on Windows (run `deactivate` to exit)
1. Run `pip install -r .github/scripts/requirements.txt`
1. Run `python .github/scripts/generate_manifest.py`
1. Locate your spec's entry in the [`manifest.json`](manifest.json) file and ensure the following fields are filled out:
   - Spec title: an appropriate title for your specification
   - Spec description: a short description of your specification
   - Spec sources: links relevant to the source of the spec (papers, blog posts, repositories)
   - Spec authors: a list of people who authored the spec
   - Spec tags:
     - `"beginner"` if your spec is appropriate for TLA<sup>+</sup> newcomers
   - Model runtime: approximate model runtime on an ordinary workstation, in `"HH:MM:SS"` format
   - Model size:
     - `"small"` if the model can be executed in less than 10 seconds
     - `"medium"` if the model can be executed in less than five minutes
     - `"large"` if the model takes more than five minutes to execute
   - Model mode:
     - `"exhaustive search"` by default
     - `{"simulate": {"traceCount": N}}` for a simulation model
     - `"generate"` for model trace generation
   - Model result:
     - `"success"` if the model completes successfully
     - `"assumption failure"` if the model violates an assumption
     - `"safety failure"` if the model violates an invariant
     - `"liveness failure"` if the model fails to satisfy a liveness property
     - `"deadlock failure"` if the model encounters deadlock
   - (Optional) Model state count info: distinct states, total states, and state depth
     - These are all individually optional and only valid if your model uses exhaustive search and results in success
     - Recording these turns your model into a powerful regression test for TLC
   - Other fields are auto-generated by the script; if you are adding an entry manually, ensure their values are present and correct (see other entries or the [`manifest-schema.json`](manifest-schema.json) file)

Before submitted your changes to run in the CI, you can quickly check your [`manifest.json`](manifest.json) for errors and also check it against [`manifest-schema.json`](manifest-schema.json) at https://www.jsonschemavalidator.net/.

