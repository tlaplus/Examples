------------------------- MODULE KeyValueStore_proof -----------------------
(***************************************************************************)
(* TLAPS proof of                                                          *)
(*   THEOREM Spec => [](TypeInvariant /\ TxLifecycle)                      *)
(* stated in KeyValueStore.tla.                                            *)
(***************************************************************************)
EXTENDS KeyValueStore, TLAPS

Inv == TypeInvariant /\ TxLifecycle

THEOREM TypeAndLifecycle == Spec => []Inv
<1>1. Init => Inv
  BY DEF Init, Inv, TypeInvariant, TxLifecycle, Store
<1>2. Inv /\ [Next]_<<store, tx, snapshotStore, written, missed>> => Inv'
  <2> SUFFICES ASSUME Inv,
                      [Next]_<<store, tx, snapshotStore, written, missed>>
               PROVE  Inv'
    OBVIOUS
  <2>. USE DEF Inv, TypeInvariant, TxLifecycle, Store
  <2>1. ASSUME NEW t \in TxId, OpenTx(t)
        PROVE  Inv'
    BY <2>1 DEF OpenTx
  <2>2. ASSUME NEW t \in tx, NEW k \in Key, NEW v \in Val, Add(t, k, v)
        PROVE  Inv'
    BY <2>2 DEF Add
  <2>3. ASSUME NEW t \in tx, NEW k \in Key, NEW v \in Val, Update(t, k, v)
        PROVE  Inv'
    BY <2>3 DEF Update
  <2>4. ASSUME NEW t \in tx, NEW k \in Key, Remove(t, k)
        PROVE  Inv'
    BY <2>4 DEF Remove
  <2>5. ASSUME NEW t \in tx, RollbackTx(t)
        PROVE  Inv'
    BY <2>5 DEF RollbackTx
  <2>6. ASSUME NEW t \in tx, CloseTx(t)
        PROVE  Inv'
    BY <2>6 DEF CloseTx
  <2>7. CASE UNCHANGED <<store, tx, snapshotStore, written, missed>>
    BY <2>7
  <2>. QED  BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF Next
<1>. QED  BY <1>1, <1>2, PTL DEF Spec, Inv

============================================================================
