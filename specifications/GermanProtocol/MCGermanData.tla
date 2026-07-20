----------------------------- MODULE MCGermanData -----------------------------
EXTENDS GermanData, TLC

\* Nodes and data values are independently interchangeable.  The NoNode and
\* NoData sentinels are fixed because they are outside these sets.
Symmetry == Permutations(NODE) \union Permutations(DATA)

==============================================================================
