---- MODULE MCKVsnap ----
EXTENDS KVsnap, TLC
TxIdSymmetric == Permutations(TxId)

\* To get debugging information from KVsnap.tla
BaitInv == TLCGet("level")>7 => ~(\E k1,k2 \in Key: store[k1]#store[k2] /\ k1#k2 /\ store[k1] # NoVal /\ store[k2] # NoVal)

====

