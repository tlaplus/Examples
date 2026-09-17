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


-------------------------------------------------------------------------------
(*                  PART A — TYPE INVARIANT (type-correctness)             *)

\* (1) The initial state satisfies the type invariant.
LEMMA InitType == Init => TypeInvariant
  BY DEF Init, TypeInvariant, MsgRecord

\* (2) Every step (or stutter) preserves the type invariant.
LEMMA NextType == TypeInvariant /\ [Next]_vars => TypeInvariant'
  BY DEF TypeInvariant, MsgRecord, vars, Next, Send, Process, Crash, Rejoin, Tick

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
  BY DEF SafeInv, TypeInvariant, MsgRecord, NoFutureAdmission,
         PersistedSafe, vars, Next, Send, Process, Crash, Rejoin, Tick

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
