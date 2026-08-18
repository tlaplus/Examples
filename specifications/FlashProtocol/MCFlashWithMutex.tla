------------------------- MODULE MCFlashWithMutex -------------------------
EXTENDS FlashWithMutex, TLC

\* Nodes and data values are independently interchangeable.  The Undefined
\* sentinel is fixed because it is outside these sets.
Symmetry == Permutations(NODE) \union Permutations(DATA)

==============================================================================
