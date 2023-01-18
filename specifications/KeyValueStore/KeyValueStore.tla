--------------------------- MODULE KeyValueStore ---------------------------
(**************************************************************************)
(* A simple key-value store exhibiting snapshot isolation. If two         *)
(* concurrent transactions write to the same key, the one merging later   *)
(* will be rejected. If they write different keys both will succeed. For  *)
(* a more-detailed specification of snapshot isolation, look at the       *)
(* specifications/SnapshotIsolation specs in the tlaplus/examples repo.   *)
(**************************************************************************)

CONSTANTS   Key,            \* The set of all keys.
            Val,            \* The set of all values.
            TxId            \* The set of all transaction IDs.
VARIABLES   store,          \* A data store mapping keys to values.
            tx,             \* The set of open snapshot transactions.
            snapshotStore,  \* Snapshots of the store for each transaction.
            written,        \* A log of writes performed within each transaction.
            missed          \* The set of writes invisible to each transaction.
----------------------------------------------------------------------------
NoVal ==    \* Choose something to represent the absence of a value.
    CHOOSE v : v \notin Val

Store ==    \* The set of all key-value stores.
    [Key -> Val \cup {NoVal}]

Init == \* The initial predicate.
    /\ store = [k \in Key |-> NoVal]        \* All store values are initially NoVal.
    /\ tx = {}                              \* The set of open transactions is initially empty.
    /\ snapshotStore =                      \* All snapshotStore values are initially NoVal.
        [t \in TxId |-> [k \in Key |-> NoVal]]
    /\ written = [t \in TxId |-> {}]        \* All write logs are initially empty.
    /\ missed = [t \in TxId |-> {}]         \* All missed writes are initially empty.
    
TypeInvariant ==    \* The type invariant.
    /\ store \in Store
    /\ tx \subseteq TxId
    /\ snapshotStore \in [TxId -> Store]
    /\ written \in [TxId -> SUBSET Key]
    /\ missed \in [TxId -> SUBSET Key]
    
TxLifecycle ==
    /\ \A t \in tx :    \* If store != snapshot & we haven't written it, we must have missed a write.
        \A k \in Key : (store[k] /= snapshotStore[t][k] /\ k \notin written[t]) => k \in missed[t]
    /\ \A t \in TxId \ tx : \* Checks transactions are cleaned up after disposal.
        /\ \A k \in Key : snapshotStore[t][k] = NoVal
        /\ written[t] = {}
        /\ missed[t] = {}

OpenTx(t) ==    \* Open a new transaction.
    /\ t \notin tx
    /\ tx' = tx \cup {t}
    /\ snapshotStore' = [snapshotStore EXCEPT ![t] = store]
    /\ UNCHANGED <<written, missed, store>>

Add(t, k, v) == \* Using transaction t, add value v to the store under key k.
    /\ t \in tx
    /\ snapshotStore[t][k] = NoVal
    /\ snapshotStore' = [snapshotStore EXCEPT ![t][k] = v]
    /\ written' = [written EXCEPT ![t] = @ \cup {k}]
    /\ UNCHANGED <<tx, missed, store>>
    
Update(t, k, v) ==  \* Using transaction t, update the value associated with key k to v.
    /\ t \in tx
    /\ snapshotStore[t][k] \notin {NoVal, v}
    /\ snapshotStore' = [snapshotStore EXCEPT ![t][k] = v]
    /\ written' = [written EXCEPT ![t] = @ \cup {k}]
    /\ UNCHANGED <<tx, missed, store>>
    
Remove(t, k) == \* Using transaction t, remove key k from the store.
    /\ t \in tx
    /\ snapshotStore[t][k] /= NoVal
    /\ snapshotStore' = [snapshotStore EXCEPT ![t][k] = NoVal]
    /\ written' = [written EXCEPT ![t] = @ \cup {k}]
    /\ UNCHANGED <<tx, missed, store>>
    
RollbackTx(t) ==    \* Close the transaction without merging writes into store.
    /\ t \in tx
    /\ tx' = tx \ {t}
    /\ snapshotStore' = [snapshotStore EXCEPT ![t] = [k \in Key |-> NoVal]]
    /\ written' = [written EXCEPT ![t] = {}]
    /\ missed' = [missed EXCEPT ![t] = {}]
    /\ UNCHANGED store

CloseTx(t) ==   \* Close transaction t, merging writes into store.
    /\ t \in tx
    /\ missed[t] \cap written[t] = {}   \* Detection of write-write conflicts.
    /\ store' =                         \* Merge snapshotStore writes into store.
        [k \in Key |-> IF k \in written[t] THEN snapshotStore[t][k] ELSE store[k]]
    /\ tx' = tx \ {t}
    /\ missed' =    \* Update the missed writes for other open transactions.
        [otherTx \in TxId |-> IF otherTx \in tx' THEN missed[otherTx] \cup written[t] ELSE {}]
    /\ snapshotStore' = [snapshotStore EXCEPT ![t] = [k \in Key |-> NoVal]]
    /\ written' = [written EXCEPT ![t] = {}]

Next == \* The next-state relation.
    \/ \E t \in TxId : OpenTx(t)
    \/ \E t \in tx : \E k \in Key : \E v \in Val : Add(t, k, v)
    \/ \E t \in tx : \E k \in Key : \E v \in Val : Update(t, k, v)
    \/ \E t \in tx : \E k \in Key : Remove(t, k)
    \/ \E t \in tx : RollbackTx(t)
    \/ \E t \in tx : CloseTx(t)
        
Spec == \* Initialize state with Init and transition with Next.
    Init /\ [][Next]_<<store, tx, snapshotStore, written, missed>>
----------------------------------------------------------------------------
THEOREM Spec => [](TypeInvariant /\ TxLifecycle)
=============================================================================

