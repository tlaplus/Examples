# Least Circular Substring

This is a spec the least circular substring algorithm described in [*Lexicographically Least Circular Substrings*](https://doi.org/10.1016/0020-0190(80)90149-0) by Kellogg S. Booth.
The spec is notable for being a PlusCal implementation of a complicated sequential string algorithm.
It was written to explore the feasibility of using PlusCal as a replacement for pseudocode in published papers and textbooks.
You can read about the findings [here](https://ahelwer.ca/post/2023-03-30-pseudocode/).
PlusCal was compared against a Python implementation of the same algorithm; the Python implementation is also included in this directory.

Since the algorithm as given in the paper uses 0-indexed strings and TLA⁺ uses 1-indexed sequences, a `ZSequences.tla` module was written that behaves similar to `Sequences.tla` but indexed from 0.

