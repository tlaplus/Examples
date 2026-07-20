--------------------------- MODULE MCGermanControl ---------------------------
EXTENDS GermanControl, TLC

CONSTANT Other
ASSUME Other \notin NODE /\ Other # NoNode

\* The concrete finite-node protocol refines the CMP abstraction by the
\* identity mapping; it simply never exercises the abstract node Other.
Abstract == INSTANCE GermanCMPWithMutex

Refinement == Abstract!Spec

\* Nodes are interchangeable, so collapse permutations of NODE.
Symmetry == Permutations(NODE)

==============================================================================
