# Two-way refinement using auxiliary variables

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

## Peterson.tla

The specification of Peterson's algorithm in PlusCal, and the refinement proof
towards `Lock!Spec`.

The refinement can be verified with TLC with `MCPeterson.tla/cfg`.

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

The refinement can be verified with TLC with `MCLockHS.tla/cfg`. 

## Stuttering.tla

This module was written for the **Auxiliary variables in TLA+** paper by
*Lamport and Merz*. (see comment at the top of the module) It eases the 
addition of a stutter variable.

For the specifications above, the module has been slightly modified, see comment
at the end of the file.