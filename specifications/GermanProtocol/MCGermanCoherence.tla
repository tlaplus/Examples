------------------------- MODULE MCGermanCoherence -------------------------
EXTENDS GermanCoherence, TLC

\* Nodes are interchangeable, so collapse permutations of NODE.
Symmetry == Permutations(NODE)

==============================================================================
