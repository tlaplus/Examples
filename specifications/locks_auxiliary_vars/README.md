# Two-way refinement using auxiliary variables

*This specification comes from a 
[Master's thesis](http://hdl.handle.net/2268.2/23374)*

Refinement proves that all behaviors implementation are a valid behavior of
an abstract specification. It is usually not done from the abstract 
specification to the implementation.

This example shows an example of this second, unusual, case using auxiliary 
variables, as presented in **Prophecy made simple** by *Lamport and Merz*.

First a refinement from Peterson's algorithm to an abstract lock is provided
in `Peterson.tla`. Second a refinement from an abstract lock with auxiliary
variables towards Peterson's algorithm is provided in `LockHS.tla`

## Lock.tla

The specification of an abstract lock for two processes in PlusCal.
In this abstract lock, lock acquisition is done atomically.

The usual typing invariant and mutual exclusion are checked within the
`Lock.cfg` model and proven using TLAPS.

## Peterson.tla

Peterson's algorithm is a solution for mutual exclusion for 2 processes.
Each process shows its intent to enter the critical section by raising a flag
`c[self]` and can proceed if the other process does not intend to enter the 
critical section or it is its turn.

[Wikipedia](https://en.wikipedia.org/wiki/Peterson%27s_algorithm)

This module contains the specification of Peterson's algorithm in PlusCal, and 
the refinement proof towards `Lock!Spec`.

A model that checks each invariant presented in the specification and the 
refinement is given in `Peterson.cfg`.

## LockHS.tla

This module contains the extension of `Lock.tla` using auxiliary variables
to allow a refinement towards Peterson's algorithm.
1. The history variable `h_turn` is used to emulate the `turn` variable of
   Peterson.
1. The stutter variable `s`, introduced with the `Stuttering` module, is 
   used to force 2 stutter steps during lock acquisition.
   This allows `LockHS` to take three steps for acquiring the lock, like 
   `Peterson`.

A refinement proof towards `Peterson!Spec` is presented within.

The refinement as well as the invariants used to prove the refinement are 
checked within the model `LockHS.cfg`.

## Stuttering.tla

This module was written for the **Auxiliary variables in TLA+** paper by
*Lamport and Merz*. (see comment at the top of the module) It eases the 
addition of a stutter variable.

For the specifications above, the module has been slightly modified, see comment
at the end of the file.