#### <a href="https://github.com/nano-o/MultiPaxos/blob/master/DiskPaxos.tla">diskpaxos</a>
- TLA<sup>+</sup> specification's authors: Leslie Lamport
- Pluscal specification's authors: Giuliano Losa
- <a href="https://github.com/nano-o/MultiPaxos/blob/master/DiskPaxos.tla">Pluscal files</a>
- First, Lamport wrote the TLA<sup>+</sup> specifications in his paper. Because we could not find Lamport's TLA files, we translated his writing in PDF format to TLA<sup>+</sup> and pushed them in this repository. Later, Losa wrote another specification for this algorithm in Pluscal.
- Original paper: <a href="https://lamport.azurewebsites.net/pubs/disk-paxos.pdf">Gafni, Eli, and Leslie Lamport. Disk paxos. Distributed Computing 16.1 (2003): 1-20.</a>
- Extended modules: Int
- Computation models: crashes, inaccessibility
- Some properties checked with TLC: SynodSpec
