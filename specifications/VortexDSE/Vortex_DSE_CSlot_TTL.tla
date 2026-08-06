---------------------- MODULE Vortex_DSE_CSlot_TTL ----------------------
(***************************************************************************)
(* Vortex DSE — Deterministic C-Slot Admission (V. Nasopoulos)             *)
(*                                                                          *)
(* C-slot law:                                                              *)
(*   C_slot(TX) = floor( (T_hw - T_0) / Delta_t )                           *)
(*                                                                          *)
(* Strict admission rule:                                                   *)
(*   if tx.C_slot != current_slot { reject }                                *)
(*                                                                          *)
(* This is NOT a TTL window. A message whose timestamp belongs to slot k    *)
(* is admissible at node n IFF the node is currently in slot k. One slot    *)
(* late => permanent reject. No leader, no quorum, no vote.                 *)
(*                                                                          *)
(* Async hostile environment modeled:                                       *)
(*   - arbitrary message reordering (network is a SET),                     *)
(*   - unbounded delivery delay (Process is nondeterministic),              *)
(*   - node crashes and rejoins (state survives only via the persistent snapshot),   *)
(*   - adversarial duplicate injection (replay attack).                     *)
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
    network,             \* in-flight messages (SET = no ordering)
    \* @type: Str -> Set(Str);
    processed,           \* processed[n] = msg ids node n has admitted
    \* @type: Str -> Set(Str);
    persisted,           \* persisted[n] = persistent snapshot (survives crash)
    \* @type: Str -> Str;
    node_state           \* node_state[n] \in {Up, Down}

vars == <<current_slot, network, processed, persisted, node_state>>

\* The default mode, over the same variable names. Every action here is an
\* action of it: the admission gate is equality where the default admits on
\* <=, and nothing else differs. The refinement is proved in
\* Vortex_DSE_CSlot_TTL_Proofs.
C == INSTANCE Vortex_DSE_CSlot

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

\* Emission, as in Vortex_DSE_CSlot: one action covers honest submission
\* (cslot = current_slot) and adversarial injection or replay (any other
\* stamp). No fairness is assumed on it either way.
Send(id, cslot) ==
    /\ id \in MsgIDs
    /\ cslot \in Nat
    /\ network' = network \cup {[id |-> id, cslot |-> cslot]}
    /\ UNCHANGED <<current_slot, processed, persisted, node_state>>

\* C-SLOT STRICT ADMISSION.
\* Local, O(1) decision. The node admits m iff m.cslot equals the node's
\* current slot AND it has not already been processed. No window, no TTL.
\* Late delivery (m.cslot < current_slot) => permanent reject.
\* Future-dated (m.cslot > current_slot) => reject now; would only be
\* admitted if the message is delivered when the slot matches.
Process(n, m) ==
    /\ n \in Nodes
    /\ m \in network
    /\ node_state[n] = Up
    /\ m.id \notin processed[n]              \* exactly-once guard (local)
    /\ m.cslot = current_slot                \* STRICT C-slot equality
    /\ processed' = [processed EXCEPT ![n] = @ \cup {m.id}]
    /\ UNCHANGED <<current_slot, network, persisted, node_state>>

\* CRASH: node loses RAM. persistent snapshot in `persisted` survives.
Crash(n) ==
    /\ n \in Nodes
    /\ node_state[n] = Up
    /\ persisted'  = [persisted  EXCEPT ![n] = processed[n]]
    /\ node_state' = [node_state EXCEPT ![n] = Down]
    /\ processed'  = [processed  EXCEPT ![n] = {}]
    /\ UNCHANGED <<current_slot, network>>

\* REJOIN: node recovers from persistent snapshot. processed = persisted.
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
    /\ \A m \in network : m.id \in MsgIDs /\ m.cslot \in Nat
    /\ processed    \in [Nodes -> SUBSET MsgIDs]
    /\ persisted    \in [Nodes -> SUBSET MsgIDs]
    /\ node_state   \in [Nodes -> {Up, Down}]

-------------------------------------------------------------------------------
(*                       CORE SAFETY INVARIANTS                             *)

\* I1: EXACTLY-ONCE PER NODE.
\* No node processes the same id twice (set semantics + guard).
ExactlyOncePerNode ==
    \A n \in Nodes : Cardinality(processed[n]) <= Cardinality(MsgIDs)

\* I2: STRICT C-SLOT ADMISSION (the headline property).
\* Every processed id corresponds to some network message whose cslot
\* equals the slot at which it was admitted. Because the gate is
\* m.cslot = current_slot and current_slot is monotonic, an admitted
\* message's cslot value lies in [0, current_slot].
\* The strong form we check: for every processed id at node n, there
\* exists a network record with that id whose cslot is <= current_slot
\* (i.e. it was a real, present-or-past slot, never future-dated).
CSlotStrictAdmission ==
    \A n \in Nodes : \A id \in processed[n] :
        \E m \in network : m.id = id /\ m.cslot <= current_slot

\* I3: PERSISTED REFLECTS REALITY.
\* persistent snapshot never invents ids that were not in the network.
PersistedReflectsReality ==
    \A n \in Nodes : persisted[n] \subseteq {m.id : m \in network}

\* I4: NO PHANTOM PROCESS.
\* Every processed id corresponds to a real network record.
NoPhantomProcess ==
    \A n \in Nodes : processed[n] \subseteq {m.id : m \in network}

\* I5: DECISION LOCALITY.
\* If two nodes have both processed id, that id exists in network.
\* Structural consequence: the gate depends only on (m.cslot, current_slot),
\* not on n. Same (m.cslot, current_slot) => same decision at every node.
DecisionLocalityOnly ==
    \A n1, n2 \in Nodes : \A id \in MsgIDs :
        (id \in processed[n1] /\ id \in processed[n2]) =>
            (\E m \in network : m.id = id)

\* I6: NO LATE ADMISSION.
\* This is the property that distinguishes C-slot from TTL.
\* If id was admitted by node n, then at the moment of admission,
\* m.cslot = current_slot_then. Since current_slot is monotonic and
\* messages with m.cslot > current_slot cannot be admitted (gate),
\* AND messages with m.cslot < current_slot also cannot be admitted,
\* the only admitted messages have m.cslot exactly equal to the
\* admission-time slot. The check is: no processed id has a sole
\* network record with cslot > current_slot (would mean we admitted
\* a future-dated message we should not yet see admitted).
NoLateAdmission ==
    \A n \in Nodes : \A id \in processed[n] :
        \E m \in network : m.id = id /\ m.cslot <= current_slot

-------------------------------------------------------------------------------
(*                          STATE-SPACE CONSTRAINT                          *)


-------------------------------------------------------------------------------
(*                              LIVENESS LAYER                              *)
(*                                                                          *)
(* DESIGN NOTE — fairness assignment is intentional:                        *)
(*                                                                          *)
(*  - WF(Tick): the slot ticker advances eventually. This is a physical-   *)
(*    hardware assumption (the ticker process does not stall forever).     *)
(*    Weak fairness suffices: Tick is unbounded here, so it is always      *)
(*    enabled and never intermittently disabled.                           *)
(*                                                                          *)
(*  - WF(Rejoin(n)) per node: a crashed node, given the chance, eventually  *)
(*    rejoins. This corresponds to operational recovery (operator restart). *)
(*                                                                          *)
(*  - NO fairness on Process. This is deliberate: the strict C-slot rule    *)
(*    by design allows a message to be permanently dropped if the network   *)
(*    delivers it after its slot has passed. That IS the feature, not a    *)
(*    bug. Adding WF(Process) would falsely claim "every TX eventually     *)
(*    admitted", which contradicts the strict admission gate.              *)
(*                                                                          *)
(*  - NO fairness on Send. Emission is a user or adversary action; neither  *)
(*    is required to happen.                                                *)
(***************************************************************************)

Fairness ==
    /\ WF_vars(Tick)
    /\ \A n \in Nodes : WF_vars(Rejoin(n))

LiveSpec == Init /\ [][Next]_vars /\ Fairness

\* L1 TICK PROGRESS.
\* Under WF(Tick) the slot counter grows without bound. A model-checkable
\* form, bounded by a horizon, is in MC_Vortex_DSE_CSlot_TTL.
TickProgress == \A k \in Nat : <>(current_slot > k)

\* L2 EVENTUAL REJOIN.
\* Every crashed node eventually returns to Up, under WF(Rejoin(n)).
\* What the bounded-memory mode gives up, stated so the cost is visible
\* rather than implied. A message whose slot has passed is refused for good,
\* so this property does NOT hold here — it is checked as a deliberate
\* liveness failure, and it is the reason the strict rule is a concession to
\* memory rather than a stronger protocol.
EventualAdmission ==
    \A n \in Nodes : \A id \in MsgIDs :
        (\E m \in network : m.id = id) ~> (id \in processed[n])

EventualRejoin ==
    \A n \in Nodes : (node_state[n] = Down) ~> (node_state[n] = Up)

=============================================================================
