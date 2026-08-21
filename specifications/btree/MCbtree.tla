---- MODULE MCbtree ----
\* The B-tree in btree.tla draws keys from an unbounded domain and allocates
\* nodes from an unbounded pool.  This module bounds both, so that TLC has a
\* finite state space, and reports when a bound was the binding constraint.
EXTENDS btree

CONSTANTS MaxKey,
          MaxNode

\* With no key at all, no request action is ever enabled and the tree never
\* leaves its initial state.
ASSUME KeyDomainIsNonEmpty == MaxKey \in Nat \ {0}

\* Only that the bound is a number: btree's NodePoolIsNonEmpty already rules out
\* an empty pool.
ASSUME NodeBoundIsNat == MaxNode \in Nat

MCKeys == 1..MaxKey
MCNodes == 1..MaxNode

\* The tree allocates a node whenever a split needs one, so running out means
\* MaxNode was too small for the keys this model inserts, not that the tree
\* misbehaved.  This is a statement about the model, not a property of the
\* B-tree, which is why it lives here and not in btree.tla.
FreeNodesRemain == \E n \in Nodes : IsFree(n)

====
