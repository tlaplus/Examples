-------------------- MODULE Vortex_DSE_CSlot_AE --------------------
(***************************************************************************)
(* Vortex DSE — Agreement Extension Layer (L4)                              *)
(*                                                                          *)
(* Companion module to Vortex_DSE_CSlot.tla. The core module models the     *)
(* C-slot strict admission gate (per-node, per-message) plus crash/rejoin   *)
(* via mmap snapshot. This module adds the per-cslot Agreement Extension    *)
(* (AE) phase: after admission, live nodes Freeze their local processed     *)
(* set, Reconcile via an abstract AE protocol (in implementation: Bloom    *)
(* round + repeated Merkle/hashlist), and Commit a cslot-final input set   *)
(* that is bit-identical across all correct live nodes.                    *)
(*                                                                          *)
(* The headline property (MerkleAgreement) is the formal counterpart of    *)
(* the claim: "all live nodes converge on the same input set per cslot,   *)
(* cryptographically verified via Merkle root".                           *)
(*                                                                          *)
(*--------------------------------------------------------------------------*)
(* SCOPE DELIMITATION (important):                                         *)
(*                                                                          *)
(*  This module deliberately does NOT model crash/rejoin. The core module  *)
(*  Vortex_DSE_CSlot.tla already covers crash semantics via the persisted *)
(*  mmap snapshot. Composing the two failure models in one module conflates*)
(*  two concerns: AE freeze/reconcile correctness vs. crash recovery       *)
(*  bookkeeping. Initial attempt to combine them produced a spurious      *)
(*  counterexample (TLC trace 2026-05-27): a rejoin advanced a node to    *)
(*  "committed" while its processed view was stale, violating             *)
(*  CommittedSupersetsProcessed. The clean separation is:                *)
(*                                                                          *)
(*    - Core module: admission + persistence under crash                  *)
(*    - This module: agreement under bounded network loss, all-live      *)
(*    - Future composed module: cross-cuts both (out of scope here)      *)
(*                                                                          *)
(*--------------------------------------------------------------------------*)
(* ENVIRONMENTAL ASSUMPTIONS (kept out of the state machine, declared      *)
(* here so they are visible at spec level):                                *)
(*                                                                          *)
(*  A1. Bounded clock skew. Let Delta_t be the slot duration and let       *)
(*      Delta_skew be the maximum pairwise wall-clock drift between any    *)
(*      two correct nodes. We require:                                     *)
(*                                                                          *)
(*          Delta_skew < Delta_t / 2                                       *)
(*                                                                          *)
(*      Justification: the admission gate is m.cslot = node.current_slot.  *)
(*      A producer stamps m.cslot from its own clock; a consumer evaluates *)
(*      the gate from its own clock. If skew < Delta_t/2, then at any      *)
(*      real-time instant all correct nodes observe the same current_slot *)
(*      modulo edge transitions, so a message admitted by one correct      *)
(*      node is admissible by every other correct node that receives it    *)
(*      in time. This justifies abstracting the per-node clock as a       *)
(*      single global current_slot variable.                              *)
(*                                                                          *)
(*  A2. Freeze barrier within slot. The AE phase runs in the residual      *)
(*      portion of the slot after the admission deadline. This module      *)
(*      abstracts the timing: Freeze, Reconcile, and Commit fire as       *)
(*      separate atomic actions, ordered by guard.                        *)
(*                                                                          *)
(*  A3. Reconcile completeness under bounded loss. Within a bounded-loss   *)
(*      envelope the reconcile phase recovers the full union of admitted   *)
(*      messages; beyond that envelope the layer falls back to soft-commit *)
(*      (out-of-spec). This module models only the in-spec case: Reconcile *)
(*      atomically computes the union of frozen views across live nodes.   *)
(*      Out-of-spec behavior is a separate spec (future work).            *)
(*                                                                          *)
(*  A4. All-live duration of AE phase. For each cslot k, the set of nodes *)
(*      participating in AE is fixed at the moment of Freeze. Crash       *)
(*      during AE phase is out of scope here (see SCOPE DELIMITATION).    *)
(***************************************************************************)

EXTENDS Naturals, FiniteSets

CONSTANTS
    \* @type: Set(Str);
    Nodes,           \* finite set of node identifiers
    \* @type: Set(Str);
    MsgIDs,          \* finite set of distinct message identifiers
    \* @type: Int;
    MaxSlot          \* slot horizon (state-space bound)

VARIABLES
    \* @type: Int;
    current_slot,    \* global slot counter (justified by A1)
    \* @type: Set({ id: Str, cslot: Int });
    network,         \* in-flight messages (SET)
    \* @type: Str -> Set(Str);
    processed,       \* processed[n] = msg ids admitted by n in current cslot
    \* @type: Str -> Str;
    phase,           \* phase[n] \in {"open", "frozen", "committed"}
    \* @type: Str -> Set(Str);
    committed_set    \* committed_set[n] = AE-final input set for n at current cslot

vars == <<current_slot, network, processed, phase, committed_set>>

MsgRecord == [id: MsgIDs, cslot: 0..MaxSlot]

-------------------------------------------------------------------------------
(*                              INITIAL STATE                               *)

Init ==
    /\ current_slot   = 0
    /\ network        = {}
    /\ processed      = [n \in Nodes |-> {}]
    /\ phase          = [n \in Nodes |-> "open"]
    /\ committed_set  = [n \in Nodes |-> {}]

-------------------------------------------------------------------------------
(*                                ACTIONS                                   *)

\* Submit: producer stamps cslot from its own clock (= current_slot under A1).
Submit(id) ==
    /\ id \in MsgIDs
    /\ id \notin {m.id : m \in network}
    /\ network' = network \cup {[id |-> id, cslot |-> current_slot]}
    /\ UNCHANGED <<current_slot, processed, phase, committed_set>>

\* Process: C-slot strict admission. Only enabled in the open phase.
\* Once a node is frozen, it stops admitting new messages for this cslot.
Process(n, m) ==
    /\ n \in Nodes
    /\ m \in network
    /\ phase[n] = "open"
    /\ m.id \notin processed[n]
    /\ m.cslot = current_slot
    /\ processed' = [processed EXCEPT ![n] = @ \cup {m.id}]
    /\ UNCHANGED <<current_slot, network, phase, committed_set>>

\* Freeze: node closes its admission window for this cslot.
\* In implementation: triggered by reaching the freeze deadline (~0.75 * Delta_t).
Freeze(n) ==
    /\ n \in Nodes
    /\ phase[n] = "open"
    /\ phase' = [phase EXCEPT ![n] = "frozen"]
    /\ UNCHANGED <<current_slot, network, processed, committed_set>>

\* Reconcile: abstract AE protocol. When ALL nodes are frozen, they
\* exchange their views and converge on the union, verified by Merkle root
\* equality. Atomic step at spec level; multi-round Bloom+Merkle at impl level.
\* Models assumption A3 (in-spec loss envelope).
Reconcile ==
    /\ \A n \in Nodes : phase[n] = "frozen"
    /\ LET union_view == UNION { processed[n] : n \in Nodes }
       IN committed_set' = [n \in Nodes |-> union_view]
    /\ phase' = [n \in Nodes |-> "committed"]
    /\ UNCHANGED <<current_slot, network, processed>>

\* Adversarial duplicate / replay injection.
DuplicateInject(id, fake_cslot) ==
    /\ id \in MsgIDs
    /\ fake_cslot \in 0..MaxSlot
    /\ network' = network \cup {[id |-> id, cslot |-> fake_cslot]}
    /\ UNCHANGED <<current_slot, processed, phase, committed_set>>

\* NextCslot: advance to next slot. Only enabled when all nodes have
\* committed the current cslot (closing the AE phase deterministically).
\* Resets processed and phase for the new cslot. committed_set is overwritten
\* on next Reconcile (we do not retain history in-model; the implementation
\* logs each committed_set externally as the cslot-final ledger entry).
NextCslot ==
    /\ current_slot < MaxSlot
    /\ \A n \in Nodes : phase[n] = "committed"
    /\ current_slot' = current_slot + 1
    /\ processed' = [n \in Nodes |-> {}]
    /\ phase'     = [n \in Nodes |-> "open"]
    /\ UNCHANGED <<network, committed_set>>

Next ==
    \/ \E id \in MsgIDs : Submit(id)
    \/ \E n \in Nodes, m \in network : Process(n, m)
    \/ \E n \in Nodes : Freeze(n)
    \/ Reconcile
    \/ \E id \in MsgIDs, k \in 0..MaxSlot : DuplicateInject(id, k)
    \/ NextCslot

Spec == Init /\ [][Next]_vars

-------------------------------------------------------------------------------
(*                              TYPE INVARIANT                              *)

TypeInvariant ==
    /\ current_slot   \in 0..MaxSlot
    /\ network        \subseteq MsgRecord
    /\ processed      \in [Nodes -> SUBSET MsgIDs]
    /\ phase          \in [Nodes -> {"open", "frozen", "committed"}]
    /\ committed_set  \in [Nodes -> SUBSET MsgIDs]

-------------------------------------------------------------------------------
(*                         CORE SAFETY INVARIANTS                           *)

\* AE-I1: MERKLE AGREEMENT (headline property of this module).
\* Any two nodes that have committed for the current cslot hold identical
\* committed_set. In implementation: equal Merkle roots.
\* This is the formal counterpart of the AE design guarantee.
MerkleAgreement ==
    \A n1, n2 \in Nodes :
        (phase[n1] = "committed" /\ phase[n2] = "committed")
            => committed_set[n1] = committed_set[n2]

\* AE-I2: COMMITTED IS SUPERSET OF LOCAL PROCESSED.
\* AE Reconcile only adds, never removes. A node's committed_set always
\* contains every message it locally admitted (no in-spec rollback of local
\* admission). Local processed view is monotonically a subset of the merged
\* view. (This rules out the "frozen and then dropped" failure mode.)
CommittedSupersetsProcessed ==
    \A n \in Nodes :
        phase[n] = "committed" => processed[n] \subseteq committed_set[n]

\* AE-I3: NO PHANTOM IN COMMITTED.
\* Every id in any committed_set corresponds to a real network record with
\* m.cslot = current_slot. AE cannot fabricate messages, only union real
\* admissions.
NoPhantomInCommitted ==
    \A n \in Nodes :
        phase[n] = "committed" =>
            \A id \in committed_set[n] :
                \E m \in network : m.id = id /\ m.cslot = current_slot

\* AE-I4: NO REORDER ACROSS CSLOT.
\* A message admitted in cslot k carries the cslot stamp k, never
\* re-attributed to another cslot. (Trivially follows from the gate
\* m.cslot = current_slot at admission time.)
NoReorderAcrossCslot ==
    \A n \in Nodes : \A id \in processed[n] :
        \E m \in network : m.id = id /\ m.cslot = current_slot

\* AE-I5: PHASE PROGRESSION VALID.
\* A node's phase is always one of the three legal states. Forward-only
\* transitions are enforced structurally by the Freeze, Reconcile, NextCslot
\* guards; declared here as an explicit type-level safety net.
PhaseProgressionValid ==
    \A n \in Nodes : phase[n] \in {"open", "frozen", "committed"}

-------------------------------------------------------------------------------
(*                          STATE-SPACE CONSTRAINT                          *)

StateConstraint ==
    current_slot <= MaxSlot

-------------------------------------------------------------------------------
(*                              LIVENESS LAYER                              *)
(*                                                                          *)
(* Fairness assignment:                                                     *)
(*  - SF(Reconcile): once all nodes are frozen, AE must run.               *)
(*  - SF(NextCslot): once all nodes are committed, slot must advance.      *)
(*  - WF(Freeze(n)) per node: each node eventually freezes.                *)
(*  - NO fairness on Process / Submit / DuplicateInject (same rationale as *)
(*    core module: late delivery is dropped by design; adversary unfair).  *)
(***************************************************************************)

Fairness ==
    /\ SF_vars(Reconcile)
    /\ SF_vars(NextCslot)
    /\ \A n \in Nodes : WF_vars(Freeze(n))

LiveSpec == Init /\ [][Next]_vars /\ Fairness

\* AE-L1: EVENTUAL COMMIT.
\* Every node eventually commits for the cslot it participates in.
EventualCommit ==
    \A n \in Nodes :
        (phase[n] = "open") ~> (phase[n] = "committed")

\* AE-L2: EVENTUAL AGREEMENT.
\* If two nodes both reach the committed phase, MerkleAgreement holds.
\* (Safety + liveness composition.)
EventualAgreement ==
    \A n1, n2 \in Nodes :
        (phase[n1] = "open" /\ phase[n2] = "open")
            ~> (phase[n1] = "committed" /\ phase[n2] = "committed"
                /\ committed_set[n1] = committed_set[n2])

=============================================================================
