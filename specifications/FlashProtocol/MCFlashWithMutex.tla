------------------------- MODULE MCFlashWithMutex -------------------------
EXTENDS FlashWithMutex, TLC

\* Nodes and data values are independently interchangeable.  The Other and
\* Undefined sentinels are fixed because they are outside these sets.
Symmetry == Permutations(NODE) \union Permutations(DATA)

==============================================================================
