# Barrier synchronization

*This specification comes from a 
[Master's thesis](http://hdl.handle.net/2268.2/23374)*

A barrier 
([Wikipedia](https://en.wikipedia.org/wiki/Barrier_(computer_science)))
is a synchronization facility which ensures that a group of threads all reach 
the barrier before they can advance.

Such a barrier is useful when parallel computations are done in two or more
steps and results from all threads are needed to continue.

## Barrier.tla

A specification of an abstract Barrier.

The usual typing `TypeOK` invariant is defined.

Another property to show that processes cannot leave the barrier as long as 
there are others outside of it is also given. (see `BarrierProperty`)

A model with $N = 6$ that verifies both properties is provided. 

## Barriers.tla

A specification of a Reusable Barrier synchronization facility using as
presented in the INFO09012 Parallel Programming course in ULiège by 
Prof. Pascal Fontaine.

The barrier consists of two waiting chambers `a1-a6` and `a7-a12`. 
The last process entering a waiting chamber signals the appropriate semaphore
and allows processes to pass to the next section.
Using two such waiting chambers makes sure a process leaving the barrier cannot
reenter and pass through the whole barrier again and possibly blocking a 
process inside.

## Invariants

- `TypeOK` is the usual typing invariant. The typing invariant alone cannot
  determine the range of values the semaphores can take.
- `LockInv` is used to represent the mutual exclusion inside critical sections
  present in the specification.
- `Inv` is the main invariant representing most properties of this double 
  barrier construction.
  Each clause is explained with a comment inside the specification.
  Due to the symmetry between the two waiting rooms, there are pairs of clauses
  that represent the same property for each section.
- `FlushInv` are two additional clauses needed to prove the refinement.
  It shows that once a waiting section is opened, all processes can pass.

A model `Barriers.cfg` with $N = 6$ that verifies these four invariants is 
provided.

The invariants are also proven correct using TLAPS.

## Refinement

A refinement towards an abstract Barrier specification is given by translating
the program counter. 
This translation must take into account the simultaneous movement of all
processes done by action `b1` of `Barrier.tla`.
In the refinement, processes at `a11-a12` while the second waiting chamber is
opened are already considered outside the barrier.
This emulates a simultaneous movement of all process for the refinement.

The correctness of the refinement is checked in `Barriers.cfg` and proven with 
TLAPS.
