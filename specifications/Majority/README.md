# Efficient majority vote algorithm

A specification of an efficient algorithm due to R.S. Boyer and J.S. Moore
for computing the only candidate in a sequence who may occur in a strict
majority of positions in the sequence. The algorithm makes a single pass
over the sequence and uses only two integer variables and one variable
holding the current candidate. A very simple second pass over the sequence
could then detect whether the candidate actually holds a majority.

The algorithm was published in a technical report in 1981, but only
appeared in print ten years later.

R.S. Boyer, J.S. Moore: MJRTY - A Fast Majority Vote Algorithm.
In: R.S. Boyer (ed.): Automated Reasoning: Essays in Honor of Woody
Bledsoe, pp. 105-117. Dordrecht, The Netherlands, 1991.


The module Majority contains the specification of the algorithm in TLA+, as well
as its main correctness property, a type-correctness invariant, and an
inductive invariant used for establishing correctness. Module MCMajority
can be used to model check the algorithm for all sequences of three elements
of bounded length. Module MajorityProof contains an interactive proof of
correctness that can be checked using TLAPS.
