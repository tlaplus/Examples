------------------------- MODULE MCGermanCoherence -------------------------
EXTENDS GermanCoherence, TLC

CONSTANT Other
ASSUME Other \notin NODE /\ Other # NoNode

\* The concrete finite-node protocol refines the CMP abstraction by the
\* identity mapping; it simply never exercises the abstract node Other.
Abstract == INSTANCE German

Refinement == Abstract!Spec

\* Nodes are interchangeable, so collapse permutations of NODE.
Symmetry == Permutations(NODE)

==============================================================================
