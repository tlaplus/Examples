---- MODULE MCKeyValueStore ----
EXTENDS KeyValueStore, TLC
TxIdSymmetric == Permutations(TxId)
====

