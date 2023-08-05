--------------------------- MODULE KVsnap ---------------------------------
(**************************************************************************)
(* Pluscal algoritm for a simple key-value store with snapshot isolation  *)
(* This version has atomic updates of store and missed sets of txns       *)
(**************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Util

CONSTANTS   Key,            \* The set of all keys.
            TxId,           \* The set of all transaction IDs.
            NoVal           \* NoVal, which all keys are initialized with.

\* Instantiating ClientCentric enables us to check transaction isolation guarantees this model satisfies
\* https://muratbuffalo.blogspot.com/2022/07/automated-validation-of-state-based.html         
CC == INSTANCE ClientCentric WITH Keys <- Key, Values <- TxId \union {NoVal}          

wOp(k,v) == CC!w(k,v)
rOp(k,v) == CC!r(k,v)

(* --algorithm KVsnap {

variables 
    \* A data store mapping keys to values
    store = [k \in Key |-> NoVal],

    \* The set of open snapshot transactions
    tx = {},

    \* Snapshots of the store for each transaction
    snapshotStore = [t \in TxId |-> [k \in Key |-> NoVal]],

    \* A log of writes performed within each transaction 
    written = [t \in TxId |-> {}],

    \* The set of writes invisible to each transaction
    missed = [t \in TxId |-> {}],

    \*  reads/writes per txn_id, used for interfacing to CC
    ops = [ tId \in TxId |-> <<>> ];     

define {
    \* for instantiating the ClientCentric module
    InitialState == [k \in Key |-> NoVal]   
    SetToSeq(S) == CHOOSE f \in [1..Cardinality(S) -> S] : IsInjective(f)

    \* snapshot isolation invariant
    SnapshotIsolation == CC!SnapshotIsolation(InitialState, Range(ops))

\*    Serialization == CC!Serializability(InitialState, Range(ops))
    
    TypeOK == \* type invariant
        /\ store \in [Key -> TxId \union {NoVal}]
        /\ tx \subseteq TxId
        /\ snapshotStore \in [TxId -> [Key -> TxId \union {NoVal}]]
        /\ written \in [TxId -> SUBSET Key]
        /\ missed \in [TxId -> SUBSET Key] 
}


\* Transaction processing
fair process (t \in TxId)
variables
    read_keys={},    \* read keys for the transaction
    write_keys={};   \* write keys for the transaction    
{
START: \* Start the transaction
    tx := tx \union {self};
    snapshotStore[self] := store; \* take my snapshot of store

    with (rk \in SUBSET Key; wk \in SUBSET Key \ {}) {
        read_keys := rk;     \* select a random read-key-set  from possible read-keys
        write_keys := wk;    \* select a random write-key-set from possible write-keys  
    };


READ: \* Process reads on my snapshot          
    \* log reads for CC isolation check 
    ops[self] := ops[self] \o SetToSeq({rOp(k, snapshotStore[self][k]): k \in read_keys}); 
    
UPDATE: \* Process writes on my snapshot, write 'self' as value
    snapshotStore[self] := [k \in Key |-> IF k \in write_keys THEN self ELSE snapshotStore[self][k] ];    
    written[self] := write_keys;

COMMIT: \* Commit the transaction to the database if there is no conflict   
    if (missed[self] \intersect written[self] = {}) { 
        \* take self off of active txn set
        tx := tx \ {self}; 

        \* Update the missed writes for other open transactions (nonlocal update!)
        missed := [o \in TxId |-> IF o \in tx THEN missed[o] \union written[self] ELSE missed[o]];
        
        \* update store
        store := [k \in Key |-> IF k \in written[self] THEN snapshotStore[self][k] ELSE store[k] ];  
        
        \* log reads for CC isolation check 
        ops[self] := ops[self] \o SetToSeq({wOp(k, self): k \in written[self]}); 
    }
}


}
*)

\* BEGIN TRANSLATION (chksum(pcal) = "2e9a6c18" /\ chksum(tla) = "5ad2eccd")
VARIABLES store, tx, snapshotStore, written, missed, ops, pc

(* define statement *)
InitialState == [k \in Key |-> NoVal]

SetToSeq(S) == CHOOSE f \in [1..Cardinality(S) -> S] : IsInjective(f)


SnapshotIsolation == CC!SnapshotIsolation(InitialState, Range(ops))



TypeOK ==
    /\ store \in [Key -> TxId \union {NoVal}]
    /\ tx \subseteq TxId
    /\ snapshotStore \in [TxId -> [Key -> TxId \union {NoVal}]]
    /\ written \in [TxId -> SUBSET Key]
    /\ missed \in [TxId -> SUBSET Key]

VARIABLES read_keys, write_keys

vars == << store, tx, snapshotStore, written, missed, ops, pc, read_keys, 
           write_keys >>

ProcSet == (TxId)

Init == (* Global variables *)
        /\ store = [k \in Key |-> NoVal]
        /\ tx = {}
        /\ snapshotStore = [t \in TxId |-> [k \in Key |-> NoVal]]
        /\ written = [t \in TxId |-> {}]
        /\ missed = [t \in TxId |-> {}]
        /\ ops = [ tId \in TxId |-> <<>> ]
        (* Process t *)
        /\ read_keys = [self \in TxId |-> {}]
        /\ write_keys = [self \in TxId |-> {}]
        /\ pc = [self \in ProcSet |-> "START"]

START(self) == /\ pc[self] = "START"
               /\ tx' = (tx \union {self})
               /\ snapshotStore' = [snapshotStore EXCEPT ![self] = store]
               /\ \E rk \in SUBSET Key:
                    \E wk \in SUBSET Key \ {}:
                      /\ read_keys' = [read_keys EXCEPT ![self] = rk]
                      /\ write_keys' = [write_keys EXCEPT ![self] = wk]
               /\ pc' = [pc EXCEPT ![self] = "READ"]
               /\ UNCHANGED << store, written, missed, ops >>

READ(self) == /\ pc[self] = "READ"
              /\ ops' = [ops EXCEPT ![self] = ops[self] \o SetToSeq({rOp(k, snapshotStore[self][k]): k \in read_keys[self]})]
              /\ pc' = [pc EXCEPT ![self] = "UPDATE"]
              /\ UNCHANGED << store, tx, snapshotStore, written, missed, 
                              read_keys, write_keys >>

UPDATE(self) == /\ pc[self] = "UPDATE"
                /\ snapshotStore' = [snapshotStore EXCEPT ![self] = [k \in Key |-> IF k \in write_keys[self] THEN self ELSE snapshotStore[self][k] ]]
                /\ written' = [written EXCEPT ![self] = write_keys[self]]
                /\ pc' = [pc EXCEPT ![self] = "COMMIT"]
                /\ UNCHANGED << store, tx, missed, ops, read_keys, write_keys >>

COMMIT(self) == /\ pc[self] = "COMMIT"
                /\ IF missed[self] \intersect written[self] = {}
                      THEN /\ tx' = tx \ {self}
                           /\ missed' = [o \in TxId |-> IF o \in tx' THEN missed[o] \union written[self] ELSE missed[o]]
                           /\ store' = [k \in Key |-> IF k \in written[self] THEN snapshotStore[self][k] ELSE store[k] ]
                           /\ ops' = [ops EXCEPT ![self] = ops[self] \o SetToSeq({wOp(k, self): k \in written[self]})]
                      ELSE /\ TRUE
                           /\ UNCHANGED << store, tx, missed, ops >>
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << snapshotStore, written, read_keys, write_keys >>

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


===========================================================================
nonatomic version would be as follows. It would be interesting to model check this with nanatomic version, with more yield points with labels to see where we need the latches.  

    \* while (write_keys #{}){
    \*     \* all values being distinct works best for checking, so use self??
    \*     with (k \in write_keys) {
    \*         snapshotStore[self][k] := self;
    \*         written[self] := written[self] \union {k};
    \*     } 
    \* };


