This directory contains three simple sequential algorithms, written in
PlusCal, in the modules SumSequence, BinarySearch, and Quicksort.
They are the three examples in Section 7.3 of "Proving Safety
Properties", which is at

  http://lamport.azurewebsites.net/tla/proving-safety.pdf .

They appear there as exercises in finding a loop invariant and writing
an informal proof of partial correctness.  You should try to find the
loop invariants and write your own proofs before looking at the ones
in the modules.

Loop invariants appear in each of the three specs, where they are
named Inv.  Modules SumSequence and BinarySearch contain complete
TLAPS-checked proofs of partial correctness.  Module Quicksort
contains a partly checked, partly informal proof.
