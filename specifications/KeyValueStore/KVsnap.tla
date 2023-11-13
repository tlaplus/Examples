--------------------------- MODULE KVsnap ---------------------------------
(**************************************************************************)
(* Pluscal algorithm for a simple key-value store with snapshot isolation  *)
(* This version has atomic updates of store and missed sets of txns       *)
(**************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, Util

CONSTANTS   Key,            \* The set of all keys.
            TxId,           \* The set of all transaction IDs.
            NoVal           \* NoVal, which all keys are initialized with.

\* Instantiating ClientCentric enables us to check transaction isolation guarantees this model satisfies
\* https://muratbuffalo.blogspot.com/2022/07/automated-validation-of-state-based.html         
CC == INSTANCE ClientCentric WITH Keys <- Key, Values <- TxId \union {NoVal}          
    
\* for instantiating the ClientCentric module
wOp(k,v) == CC!w(k,v)
rOp(k,v) == CC!r(k,v)
InitialState == [k \in Key |-> NoVal]   
SetToSeq(S) == CHOOSE f \in [1..Cardinality(S) -> S] : IsInjective(f)

(* --algorithm KVsnap {

variables 
    \* A data store mapping keys to values
    store = [k \in Key |-> NoVal],

    \* The set of open snapshot transactions
    tx = {},

    \* The set of writes invisible to each transaction
    missed = [t \in TxId |-> {}];

\* See end of file for invariants


\* Transaction processing
fair process (t \in TxId)
variables
    snapshotStore = [k \in Key |-> NoVal], \* local snapshot of the store
    read_keys  = {},    \* read keys  for the transaction
    write_keys = {},    \* write keys for the transaction
    ops = <<>>;   \* a log of reads & writes this transaction executes; used for interfacing to CC
{
START: \* Start the transaction
    tx := tx \union {self};
    snapshotStore := store; \* take my snapshot of store

    with (rk \in SUBSET Key \ { {} }; wk \in SUBSET Key \ { {} }) {
        read_keys := rk;     \* select a random read-key-set  from possible read-keys
        write_keys := wk;    \* select a random write-key-set from possible write-keys  
    };


READ: \* Process reads on my snapshot          
    \* log reads for CC isolation check 
    ops := ops \o SetToSeq({rOp(k, snapshotStore[k]): k \in read_keys}); 
    
UPDATE: \* Process writes on my snapshot, write 'self' as value
    snapshotStore := [k \in Key |-> IF k \in write_keys THEN self ELSE snapshotStore[k] ];    

COMMIT: \* Commit the transaction to the database if there is no conflict   
    if (missed[self] \intersect write_keys = {}) { 
        \* take self off of active txn set
        tx := tx \ {self}; 

        \* Update the missed writes for other open transactions (nonlocal update!)
        missed := [o \in TxId |-> IF o \in tx THEN missed[o] \union write_keys ELSE missed[o]];
        
        \* update store
        store := [k \in Key |-> IF k \in write_keys THEN snapshotStore[k] ELSE store[k] ];  
        
        \* log reads for CC isolation check 
        ops := ops \o SetToSeq({wOp(k, self): k \in write_keys}); 
    }
}


}
*)

\* BEGIN TRANSLATION (chksum(pcal) = "1adfcb46" /\ chksum(tla) = "5b28617f")
VARIABLES store, tx, missed, pc, snapshotStore, read_keys, write_keys, ops

vars == << store, tx, missed, pc, snapshotStore, read_keys, write_keys, ops
        >>

ProcSet == (TxId)

Init == (* Global variables *)
        /\ store = [k \in Key |-> NoVal]
        /\ tx = {}
        /\ missed = [t \in TxId |-> {}]
        (* Process t *)
        /\ snapshotStore = [self \in TxId |-> [k \in Key |-> NoVal]]
        /\ read_keys = [self \in TxId |-> {}]
        /\ write_keys = [self \in TxId |-> {}]
        /\ ops = [self \in TxId |-> <<>>]
        /\ pc = [self \in ProcSet |-> "START"]

START(self) == /\ pc[self] = "START"
               /\ tx' = (tx \union {self})
               /\ snapshotStore' = [snapshotStore EXCEPT ![self] = store]
               /\ \E rk \in SUBSET Key \ { {} }:
                    \E wk \in SUBSET Key \ { {} }:
                      /\ read_keys' = [read_keys EXCEPT ![self] = rk]
                      /\ write_keys' = [write_keys EXCEPT ![self] = wk]
               /\ pc' = [pc EXCEPT ![self] = "READ"]
               /\ UNCHANGED << store, missed, ops >>

READ(self) == /\ pc[self] = "READ"
              /\ ops' = [ops EXCEPT ![self] = ops[self] \o SetToSeq({rOp(k, snapshotStore[self][k]): k \in read_keys[self]})]
              /\ pc' = [pc EXCEPT ![self] = "UPDATE"]
              /\ UNCHANGED << store, tx, missed, snapshotStore, read_keys, 
                              write_keys >>

UPDATE(self) == /\ pc[self] = "UPDATE"
                /\ snapshotStore' = [snapshotStore EXCEPT ![self] = [k \in Key |-> IF k \in write_keys[self] THEN self ELSE snapshotStore[self][k] ]]
                /\ pc' = [pc EXCEPT ![self] = "COMMIT"]
                /\ UNCHANGED << store, tx, missed, read_keys, write_keys, ops >>

COMMIT(self) == /\ pc[self] = "COMMIT"
                /\ IF missed[self] \intersect write_keys[self] = {}
                      THEN /\ tx' = tx \ {self}
                           /\ missed' = [o \in TxId |-> IF o \in tx' THEN missed[o] \union write_keys[self] ELSE missed[o]]
                           /\ store' = [k \in Key |-> IF k \in write_keys[self] THEN snapshotStore[self][k] ELSE store[k] ]
                           /\ ops' = [ops EXCEPT ![self] = ops[self] \o SetToSeq({wOp(k, self): k \in write_keys[self]})]
                      ELSE /\ TRUE
                           /\ UNCHANGED << store, tx, missed, ops >>
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << snapshotStore, read_keys, write_keys >>

t(self) == START(self) \/ READ(self) \/ UPDATE(self) \/ COMMIT(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in TxId: t(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in TxId : WF_vars(t(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 



\* Snapshot isolation invariant
SnapshotIsolation == CC!SnapshotIsolation(InitialState, Range(ops))

TypeOK == \* type invariant
    /\ store \in [Key -> TxId \union {NoVal}]
    /\ tx \subseteq TxId
    /\ missed \in [TxId -> SUBSET Key] 


\* Serializability would not be satisfied due to write-skew
Serialization == CC!Serializability(InitialState, Range(ops))

===========================================================================
As an exercise try to add more yield points, make the actions smaller. 
Especially see if you can pull out something from the atomic "COMMIT" label to earlier, and see what breaks.



