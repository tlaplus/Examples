---------------------- MODULE Vortex_DSE_CSlot_Proofs ----------------------
(***************************************************************************)
(* TLAPS (machine-checked, unbounded) proofs for Vortex_DSE_CSlot.        *)
(*                                                                          *)
(* These are DEDUCTIVE proofs, not model checking. They establish          *)
(*   (A) Spec => []TypeInvariant      (type-correctness)                   *)
(*   (B) Spec => []NoFutureAdmission  (the headline core safety property)  *)
(* for ANY constants — any Nodes set, any MsgIDs set, any finite MaxSlot   *)
(* in Nat — each in a single proof, whereas the TLC/Apalache results hold  *)
(* only for the specific small instances they enumerated (e.g. 2 nodes,    *)
(* MaxSlot=4). NOTE: unbounded over the PARAMETERS, not "infinite slots":  *)
(* each instance still has a finite slot domain 0..MaxSlot.                *)
(*                                                                          *)
(* Standard inductive-invariant pattern:                                   *)
(*   (1) Init => Inv                                                       *)
(*   (2) Inv /\ [Next]_vars => Inv'                                        *)
(*   (3) therefore Spec => []Inv   (temporal induction, PTL)               *)
(*                                                                          *)
(* WHY NoFutureAdmission needs strengthening (honest scope note):          *)
(*   NoFutureAdmission alone is NOT inductive. The Rejoin action restores  *)
(*   processed[n] := persisted[n], but NoFutureAdmission says nothing      *)
(*   about persisted[n], so the induction step for Rejoin cannot close.    *)
(*   We therefore prove the strengthened invariant                         *)
(*       SafeInv == TypeInvariant /\ NoFutureAdmission /\ PersistedSafe    *)
(*   where PersistedSafe constrains the mmap snapshot the same way. The    *)
(*   two safety conjuncts close MUTUALLY: Crash feeds PersistedSafe from   *)
(*   NoFutureAdmission, and Rejoin feeds NoFutureAdmission from            *)
(*   PersistedSafe. NoFutureAdmission is a conjunct of SafeInv, so         *)
(*   Spec => []SafeInv yields Spec => []NoFutureAdmission.                 *)
(*                                                                          *)
(* Only typing assumption on the constants (a slot horizon is a natural).  *)
(***************************************************************************)

EXTENDS Vortex_DSE_CSlot, TLAPS

ASSUME MaxSlotType == MaxSlot \in Nat

-------------------------------------------------------------------------------
(*                  PART A — TYPE INVARIANT (type-correctness)             *)

\* (1) The initial state satisfies the type invariant.
LEMMA InitType == Init => TypeInvariant
  BY MaxSlotType DEF Init, TypeInvariant, MsgRecord

\* (2) Every step (or stutter) preserves the type invariant.
LEMMA NextType == TypeInvariant /\ [Next]_vars => TypeInvariant'
  <1> USE MaxSlotType DEF TypeInvariant, MsgRecord, vars
  <1> SUFFICES ASSUME TypeInvariant, [Next]_vars
               PROVE  TypeInvariant'
      OBVIOUS
  <1>1. CASE \E id \in MsgIDs : Submit(id)
        BY <1>1 DEF Submit
  <1>2. CASE \E n \in Nodes, m \in network : Process(n, m)
        BY <1>2 DEF Process
  <1>3. CASE \E n \in Nodes : Crash(n)
        BY <1>3 DEF Crash
  <1>4. CASE \E n \in Nodes : Rejoin(n)
        BY <1>4 DEF Rejoin
  <1>5. CASE \E id \in MsgIDs, k \in 0..MaxSlot : DuplicateInject(id, k)
        BY <1>5 DEF DuplicateInject
  <1>6. CASE Tick
        BY <1>6 DEF Tick
  <1>7. CASE UNCHANGED vars
        BY <1>7
  <1>8. QED
        BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7 DEF Next

\* (3) Temporal induction: the invariant holds in every reachable state.
THEOREM TypeCorrect == Spec => []TypeInvariant
  <1>1. Init => TypeInvariant
        BY InitType
  <1>2. TypeInvariant /\ [Next]_vars => TypeInvariant'
        BY NextType
  <1>3. QED
        BY <1>1, <1>2, PTL DEF Spec

-------------------------------------------------------------------------------
(*           PART B — NO FUTURE ADMISSION (the headline safety)            *)

\* Auxiliary invariant: the mmap snapshot never holds an id without a real,
\* present-or-past witness in the network. This is the missing piece that
\* makes NoFutureAdmission survive the Rejoin (processed := persisted) step.
PersistedSafe ==
    \A n \in Nodes : \A id \in persisted[n] :
        \E m \in network : m.id = id /\ m.cslot <= current_slot

\* The strengthened, inductive safety invariant.
SafeInv == TypeInvariant /\ NoFutureAdmission /\ PersistedSafe

\* (1) Init.
LEMMA InitSafe == Init => SafeInv
  BY InitType DEF Init, SafeInv, NoFutureAdmission, PersistedSafe

\* (2) Inductive step for the strengthened invariant.
LEMMA NextSafe == SafeInv /\ [Next]_vars => SafeInv'
  <1> USE MaxSlotType DEF SafeInv, TypeInvariant, MsgRecord,
                          NoFutureAdmission, PersistedSafe, vars
  <1> SUFFICES ASSUME SafeInv, [Next]_vars
               PROVE  SafeInv'
      OBVIOUS
  <1>0. TypeInvariant'
        BY NextType
  <1> SUFFICES NoFutureAdmission' /\ PersistedSafe'
        BY <1>0 DEF SafeInv
  \* ---- Submit: network grows, processed/persisted/slot unchanged. ----
  <1>1. CASE \E id \in MsgIDs : Submit(id)
        <2> PICK i \in MsgIDs : Submit(i)
            BY <1>1
        <2>1. /\ network'      = network \cup {[id |-> i, cslot |-> current_slot]}
              /\ processed'    = processed
              /\ persisted'    = persisted
              /\ current_slot' = current_slot
              BY DEF Submit
        <2>2. \A m \in network : m \in network'
              BY <2>1
        <2>3. NoFutureAdmission'
              BY <2>1, <2>2
        <2>4. PersistedSafe'
              BY <2>1, <2>2
        <2> QED BY <2>3, <2>4
  \* ---- Process: processed[nn] gains mm.id; the guard gives the witness. ----
  <1>2. CASE \E n \in Nodes, m \in network : Process(n, m)
        <2> PICK nn \in Nodes, mm \in network : Process(nn, mm)
            BY <1>2
        <2>1. /\ network'      = network
              /\ persisted'    = persisted
              /\ current_slot' = current_slot
              /\ processed'    = [processed EXCEPT ![nn] = processed[nn] \cup {mm.id}]
              /\ mm \in network
              /\ mm.cslot <= current_slot
              BY DEF Process
        <2>2. PersistedSafe'
              BY <2>1
        <2>3. NoFutureAdmission'
              <3> SUFFICES ASSUME NEW n \in Nodes, NEW id \in processed'[n]
                           PROVE  \E m \in network' : m.id = id /\ m.cslot <= current_slot'
                    OBVIOUS
              <3>1. CASE n = nn
                    <4>1. id \in processed[nn] \/ id = mm.id
                          BY <2>1, <3>1
                    <4>2. CASE id \in processed[nn]
                          BY <4>2, <2>1
                    <4>3. CASE id = mm.id
                          BY <4>3, <2>1
                    <4> QED BY <4>1, <4>2, <4>3
              <3>2. CASE n # nn
                    BY <3>2, <2>1
              <3> QED BY <3>1, <3>2
        <2> QED BY <2>2, <2>3
  \* ---- Crash: processed[nn] -> {} (vacuous); persisted[nn] := processed[nn]. ----
  <1>3. CASE \E n \in Nodes : Crash(n)
        <2> PICK nn \in Nodes : Crash(nn)
            BY <1>3
        <2>1. /\ network'      = network
              /\ current_slot' = current_slot
              /\ persisted'    = [persisted EXCEPT ![nn] = processed[nn]]
              /\ processed'    = [processed EXCEPT ![nn] = {}]
              BY DEF Crash
        <2>2. NoFutureAdmission'
              <3> SUFFICES ASSUME NEW n \in Nodes, NEW id \in processed'[n]
                           PROVE  \E m \in network' : m.id = id /\ m.cslot <= current_slot'
                    OBVIOUS
              <3>1. CASE n = nn
                    BY <3>1, <2>1
              <3>2. CASE n # nn
                    BY <3>2, <2>1
              <3> QED BY <3>1, <3>2
        <2>3. PersistedSafe'
              <3> SUFFICES ASSUME NEW n \in Nodes, NEW id \in persisted'[n]
                           PROVE  \E m \in network' : m.id = id /\ m.cslot <= current_slot'
                    OBVIOUS
              <3>1. CASE n = nn
                    BY <3>1, <2>1
              <3>2. CASE n # nn
                    BY <3>2, <2>1
              <3> QED BY <3>1, <3>2
        <2> QED BY <2>2, <2>3
  \* ---- Rejoin: processed[nn] := persisted[nn]; PersistedSafe gives witness. ----
  <1>4. CASE \E n \in Nodes : Rejoin(n)
        <2> PICK nn \in Nodes : Rejoin(nn)
            BY <1>4
        <2>1. /\ network'      = network
              /\ current_slot' = current_slot
              /\ persisted'    = persisted
              /\ processed'    = [processed EXCEPT ![nn] = persisted[nn]]
              BY DEF Rejoin
        <2>2. PersistedSafe'
              BY <2>1
        <2>3. NoFutureAdmission'
              <3> SUFFICES ASSUME NEW n \in Nodes, NEW id \in processed'[n]
                           PROVE  \E m \in network' : m.id = id /\ m.cslot <= current_slot'
                    OBVIOUS
              <3>1. CASE n = nn
                    BY <3>1, <2>1
              <3>2. CASE n # nn
                    BY <3>2, <2>1
              <3> QED BY <3>1, <3>2
        <2> QED BY <2>2, <2>3
  \* ---- DuplicateInject: network grows with an arbitrary cslot; gate holds. ----
  <1>5. CASE \E id \in MsgIDs, k \in 0..MaxSlot : DuplicateInject(id, k)
        <2> PICK i \in MsgIDs, k \in 0..MaxSlot : DuplicateInject(i, k)
            BY <1>5
        <2>1. /\ network'      = network \cup {[id |-> i, cslot |-> k]}
              /\ processed'    = processed
              /\ persisted'    = persisted
              /\ current_slot' = current_slot
              BY DEF DuplicateInject
        <2>2. \A m \in network : m \in network'
              BY <2>1
        <2>3. NoFutureAdmission'
              BY <2>1, <2>2
        <2>4. PersistedSafe'
              BY <2>1, <2>2
        <2> QED BY <2>3, <2>4
  \* ---- Tick: current_slot += 1; monotonicity keeps every past witness valid. ----
  <1>6. CASE Tick
        <2>1. /\ network'      = network
              /\ processed'    = processed
              /\ persisted'    = persisted
              /\ current_slot' = current_slot + 1
              BY <1>6 DEF Tick
        <2>2. current_slot \in Nat
              OBVIOUS
        <2>3. NoFutureAdmission'
              <3> SUFFICES ASSUME NEW n \in Nodes, NEW id \in processed[n]
                           PROVE  \E m \in network : m.id = id /\ m.cslot <= current_slot'
                    BY <2>1
              <3>1. PICK m \in network : m.id = id /\ m.cslot <= current_slot
                    OBVIOUS
              <3>2. m.cslot \in Nat
                    BY <3>1 DEF MsgRecord
              <3>3. m.cslot <= current_slot'
                    BY <3>1, <3>2, <2>1, <2>2
              <3> QED BY <3>1, <3>3
        <2>4. PersistedSafe'
              <3> SUFFICES ASSUME NEW n \in Nodes, NEW id \in persisted[n]
                           PROVE  \E m \in network : m.id = id /\ m.cslot <= current_slot'
                    BY <2>1
              <3>1. PICK m \in network : m.id = id /\ m.cslot <= current_slot
                    OBVIOUS
              <3>2. m.cslot \in Nat
                    BY <3>1 DEF MsgRecord
              <3>3. m.cslot <= current_slot'
                    BY <3>1, <3>2, <2>1, <2>2
              <3> QED BY <3>1, <3>3
        <2> QED BY <2>3, <2>4
  \* ---- Stutter. ----
  <1>7. CASE UNCHANGED vars
        BY <1>7
  <1>8. QED
        BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7 DEF Next

\* (3) Temporal induction, then project onto the headline conjunct.
THEOREM NoFutureAdmissionCorrect == Spec => []NoFutureAdmission
  <1>1. Init => SafeInv
        BY InitSafe
  <1>2. SafeInv /\ [Next]_vars => SafeInv'
        BY NextSafe
  <1>3. SafeInv => NoFutureAdmission
        BY DEF SafeInv
  <1>4. QED
        BY <1>1, <1>2, <1>3, PTL DEF Spec

=============================================================================
