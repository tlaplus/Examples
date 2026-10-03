---------------------- MODULE Vortex_DSE_CSlot ----------------------
(***************************************************************************)
(* Vortex DSE — Deterministic C-Slot Admission (V. Nasopoulos)             *)
(*                                                                          *)
(* C-slot law :                                        *)
(*   C_slot(TX) = floor( (T_hw - T_0) / Delta_t )                           *)
(*                                                                          *)
(* Admission rule (DEFAULT no-flag build — matches the running C code):     *)
(*   place tx into bucket[tx.C_slot]; admit once that slot is reached.      *)
(*                                                                          *)
(* A message keeps its OWN content-derived C_slot and is admitted into      *)
(* THAT slot. Late delivery (the slot already passed) is NOT dropped — it   *)
(* is admitted into its own (earlier) slot. Nothing is lost. No leader,     *)
(* no quorum, no vote.                                                      *)
(*                                                                          *)
(* The strict "one slot late => permanent reject" rule is NOT the default.  *)
(* It is re-introduced only as the OPT-IN --ttl window (bounded memory),    *)
(* which deliberately drops messages too far behind the frontier.          *)
(*                                                                          *)
(* Async hostile environment modeled:                                       *)
(*   - arbitrary message reordering (network is a SET),                     *)
(*   - unbounded delivery delay (Process is nondeterministic),              *)
(*   - node crashes and rejoins (state survives only via mmap snapshot),   *)
(*   - adversarial injection and replay: Send stamps any slot, any id.      *)
(*                                                                          *)
(* T_0 = 0 by normalization. We model integer slots directly: each ts is   *)
(* already the C_slot index of the message (i.e. ts = floor(T_hw/Delta_t)).*)
(* current_time IS the current slot index. Tick advances the slot by 1.    *)
(***************************************************************************)

EXTENDS Naturals, FiniteSets

CONSTANTS
    \* @type: Set(Str);
    Nodes,           \* finite set of node identifiers
    \* @type: Set(Str);
    MsgIDs           \* finite set of distinct message identifiers

ASSUME NodesAssumption  == IsFiniteSet(Nodes)  /\ Nodes  # {}
ASSUME MsgIDsAssumption == IsFiniteSet(MsgIDs)

\* Node liveness states, named rather than written as bare strings.
Up   == "up"
Down == "down"

VARIABLES
    \* @type: Int;
    current_slot,
    \* @type: Set({ id: Str, cslot: Int });
    network,             \* every message ever sent; nothing is discarded
    \* @type: Str -> Set(Str);
    processed,           \* processed[n] = msg ids node n has admitted
    \* @type: Str -> Set(Str);
    persisted,           \* persisted[n] = mmap snapshot (survives crash)
    \* @type: Str -> Str;
    node_state           \* node_state[n] \in {Up, Down}

vars == <<current_slot, network, processed, persisted, node_state>>

MsgRecord == [id: MsgIDs, cslot: Nat]

-------------------------------------------------------------------------------
(*                              INITIAL STATE                               *)

Init ==
    /\ current_slot = 0
    /\ network      = {}
    /\ processed    = [n \in Nodes |-> {}]
    /\ persisted    = [n \in Nodes |-> {}]
    /\ node_state   = [n \in Nodes |-> Up]

-------------------------------------------------------------------------------
(*                                ACTIONS                                   *)

\* Emission. A message enters the network carrying a slot stamp. An honest
\* sender stamps the slot it is currently in; an adversary stamps whatever it
\* likes, past or future, and may re-send an id it has already sent. There is
\* no separate honest action: Send(id, current_slot) is the honest case, and
\* singling it out would add nothing, since no fairness is assumed on it.
Send(id, cslot) ==
    /\ id \in MsgIDs
    /\ cslot \in Nat
    /\ network' = network \cup {[id |-> id, cslot |-> cslot]}
    /\ UNCHANGED <<current_slot, processed, persisted, node_state>>

\* C-SLOT ADMISSION (default build — late tolerated, nothing dropped).
\* Local, O(1) decision. The node admits m iff it has not already been
\* processed AND the slot the message belongs to has been reached
\* (m.cslot <= current_slot). The message keeps its own C_slot.
\* Late delivery (m.cslot < current_slot) is ADMITTED, not dropped: it is
\* placed into its own (earlier) slot. Nothing is lost.
\* Future-dated (m.cslot > current_slot) waits: it cannot be admitted
\* before the ticker reaches its slot (that slot has not happened yet).
Process(n, m) ==
    /\ n \in Nodes
    /\ m \in network
    /\ node_state[n] = Up
    /\ m.id \notin processed[n]              \* exactly-once guard (local)
    /\ m.cslot <= current_slot               \* admit present OR late (own slot)
    /\ processed' = [processed EXCEPT ![n] = @ \cup {m.id}]
    /\ UNCHANGED <<current_slot, network, persisted, node_state>>

\* CRASH: node loses RAM. mmap snapshot in `persisted` survives.
Crash(n) ==
    /\ n \in Nodes
    /\ node_state[n] = Up
    /\ persisted'  = [persisted  EXCEPT ![n] = processed[n]]
    /\ node_state' = [node_state EXCEPT ![n] = Down]
    /\ processed'  = [processed  EXCEPT ![n] = {}]
    /\ UNCHANGED <<current_slot, network>>

\* REJOIN: node recovers from mmap snapshot. processed = persisted.
Rejoin(n) ==
    /\ n \in Nodes
    /\ node_state[n] = Down
    /\ processed'  = [processed  EXCEPT ![n] = persisted[n]]
    /\ node_state' = [node_state EXCEPT ![n] = Up]
    /\ UNCHANGED <<current_slot, network, persisted>>

\* Slot ticker advances by 1.
Tick ==
    /\ current_slot' = current_slot + 1
    /\ UNCHANGED <<network, processed, persisted, node_state>>

Next ==
    \/ \E id \in MsgIDs, k \in Nat : Send(id, k)
    \/ \E n \in Nodes, m \in network : Process(n, m)
    \/ \E n \in Nodes : Crash(n)
    \/ \E n \in Nodes : Rejoin(n)
    \/ Tick

Spec == Init /\ [][Next]_vars

-------------------------------------------------------------------------------
(*                              TYPE INVARIANT                              *)

TypeInvariant ==
    /\ current_slot \in Nat
    /\ network      \subseteq MsgRecord
    /\ processed    \in [Nodes -> SUBSET MsgIDs]
    /\ persisted    \in [Nodes -> SUBSET MsgIDs]
    /\ node_state   \in [Nodes -> {Up, Down}]

-------------------------------------------------------------------------------
(*                       CORE SAFETY INVARIANTS                             *)
(*                                                                          *)
(* NoFutureAdmission is the property of interest. The three below it are    *)
(* consequences, kept because they are the statements a reader is likely to *)
(* look for and because they are cheap regression checks, not because they  *)
(* add strength.                                                            *)

\* THE HEADLINE PROPERTY.
\* A node never admits a message whose slot has not yet been reached. The
\* gate is m.cslot <= current_slot and current_slot is monotonic, so every
\* admitted id has a network record whose cslot lies in [0, current_slot]:
\* a real, present-or-past slot, never future-dated. Late messages (cslot <
\* current_slot) ARE admitted, into their own slot — that is intended; only
\* future-dated admission is barred.
NoFutureAdmission ==
    \A n \in Nodes : \A id \in processed[n] :
        \E m \in network : m.id = id /\ m.cslot <= current_slot

\* Corollary of NoFutureAdmission: only sent messages are processed.
NoPhantomProcess ==
    \A n \in Nodes : processed[n] \subseteq {m.id : m \in network}

\* Corollary of NoPhantomProcess.
DecisionLocalityOnly ==
    \A n1, n2 \in Nodes : \A id \in MsgIDs :
        (id \in processed[n1] /\ id \in processed[n2]) =>
            (\E m \in network : m.id = id)

\* Corollary of the type invariant, since processed[n] is a set of MsgIDs
\* and MsgIDs is finite.
ExactlyOncePerNode ==
    \A n \in Nodes : Cardinality(processed[n]) <= Cardinality(MsgIDs)

\* The crash snapshot never holds an id that was never sent. This holds at
\* all times, not only while the node is down.
PersistedReflectsReality ==
    \A n \in Nodes : persisted[n] \subseteq {m.id : m \in network}

-------------------------------------------------------------------------------
(*                              LIVENESS LAYER                              *)
(*                                                                          *)
(* DESIGN NOTE — fairness assignment is intentional:                        *)
(*                                                                          *)
(*  - WF(Tick): the slot ticker advances eventually. This is a physical-    *)
(*    hardware assumption (the ticker process does not stall forever).      *)
(*    Weak fairness suffices: Tick is unbounded here, so it is always       *)
(*    enabled and never intermittently disabled.                            *)
(*                                                                          *)
(*  - WF(Rejoin(n)) per node: a crashed node, given the chance, eventually  *)
(*    rejoins. This corresponds to operational recovery (operator restart). *)
(*                                                                          *)
(*  - SF(Process(n)): fairness ON Process. This matches the default code,   *)
(*    where a late message is NOT dropped but admitted into its own slot.   *)
(*    Strong fairness (not weak) because a crash intermittently disables    *)
(*    Process; SF guarantees that a message enabled infinitely often is     *)
(*    eventually admitted. This is what recovers VALIDITY: every TX that    *)
(*    reaches the network is eventually admitted by every up node.          *)
(*                                                                          *)
(*  - NO fairness on Send. Emission is a user or adversary action; neither  *)
(*    is required to happen.                                                *)
(***************************************************************************)

Fairness ==
    /\ WF_vars(Tick)
    /\ \A n \in Nodes : WF_vars(Rejoin(n))
    /\ \A n \in Nodes : SF_vars(\E m \in network : Process(n, m))

LiveSpec == Init /\ [][Next]_vars /\ Fairness

\* L1 TICK PROGRESS.
\* Under WF(Tick) the slot counter grows without bound: no slot index is
\* ever a ceiling. A model-checkable form, bounded by a horizon, is in
\* MC_Vortex_DSE_CSlot.
TickProgress == \A k \in Nat : <>(current_slot > k)

\* L2 EVENTUAL REJOIN.
\* Every crashed node eventually returns to Up, under WF(Rejoin(n)).
EventualRejoin ==
    \A n \in Nodes : (node_state[n] = Down) ~> (node_state[n] = Up)

\* L3 EVENTUAL ADMISSION (VALIDITY — the property the new rule recovers).
\* Once a message is in the network, every node eventually admits it.
\* Nothing is permanently dropped: late messages reach their own slot.
\* This is exactly what the strict drop-late spec could NOT claim.
EventualAdmission ==
    \A n \in Nodes : \A id \in MsgIDs :
        (\E m \in network : m.id = id) ~> (id \in processed[n])

=============================================================================
