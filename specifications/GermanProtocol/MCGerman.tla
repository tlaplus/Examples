----------------------------- MODULE MCGerman -----------------------------
EXTENDS German, TLC

\* The concrete nodes are interchangeable, so collapse permutations of NODE.
\* Other and NoNode are fixed sentinels and are not permuted.
Symmetry == Permutations(NODE)

==============================================================================
