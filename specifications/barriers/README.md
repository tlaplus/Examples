# Barrier synchronization
-

## Barriers.tla

A specification of a Reusable Barrier synchronization facility using as
presented in the INFO09012 Parallel Programming course in ULiège by 
Prof. Pascal Fontaine.

The barrier consists of two waiting rooms `a1-a6` and `a7-a12`. 
The last process entering a waiting room signals the appropriate semaphore
and allows processes to pass to the next section.
Using two such waiting rooms makes sure a process leaving the barrier cannot
reenter and pass through the whole barrier again.

## Invariants

- `TypeOK` is the usual typing invariant. The typing invariant alone cannot
  determine the range of values the semaphores can take.
- `LockInv` is used to represent the mutual exclusion inside critical sections
  present in the specification.
- `Inv` is the main invariant representing most properties of this double 
  barrier construction.
  Due to the symmetry between the two waiting rooms, there are pairs of clauses
  that represent the same property for each section.
- `FlushInv` are two additional clauses needed to prove the refinement.
  It shows that once a waiting section is opened, all processes can pass.

A model `Barriers.cfg` with $N = 7$ that verifies these four invariants is 
provided.

## Refinement

A refinement towards an abstract Barrier specification is proven with TLAPS.

## Barrier.tla

A specification of an abstract Barrier.

The usual typing invariant is defined.

A model with the same amount of processes as above is provided. 