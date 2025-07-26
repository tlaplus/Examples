# Two-way refinement using auxiliary variables

Refinement proves that all behaviors implementation are a valid behavior of
an abstract specification. It is usually not done from the abstract 
specification to the implementation.

This example shows an example of this second, unusual, case using auxiliary 
variables, as presented in **Prophecy made simple** by *Lamport and Merz*.

First a refinement from Peterson's algorithm to an abstract lock is provided
in `Peterson.tla`. Second a refinement from an abstract lock with auxiliary
variables is provided in `LockHS.tla`

## Lock.tla

The specification of an abstract lock for two processes in PlusCal

## Peterson.tla

The specification of Peterson's algorithm in PlusCal, and the refinement proof
towards `Lock!Spec`

## LockHS.tla

The extension of `Lock.tla` using a history variable `h_turn` and a stutter
variable `s`, provided by the `Stuttering.tla` module. 
A refinement proof towards `Peterson!Spec` is presented within.

## Stuttering.tla

This module was written for the **Auxiliary variables in TLA+** paper by
*Lamport and Merz*. (see comment at the top of the module) It eases the 
addition of a stutter variable.

For the specifications above, the module has been slightly modified, see comment
at the end of the file.