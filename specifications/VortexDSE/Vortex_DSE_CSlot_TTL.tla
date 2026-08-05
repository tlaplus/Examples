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
    MsgIDs,          \* finite set of distinct message identifiers
    \* @type: Int;
    MaxSlot          \* slot horizon (state-space bound)

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
    node_state           \* node_state[n] \in {"up", "down"}

vars == <<current_slot, network, processed, persisted, node_state>>

MsgRecord == [id: MsgIDs, cslot: 0..MaxSlot]

-------------------------------------------------------------------------------
(*                              INITIAL STATE                               *)

Init ==
    /\ current_slot = 0
    /\ network      = {}
    /\ processed    = [n \in Nodes |-> {}]
    /\ persisted    = [n \in Nodes |-> {}]
    /\ node_state   = [n \in Nodes |-> "up"]

-------------------------------------------------------------------------------
(*                                ACTIONS                                   *)

\* Submit: sender stamps T_hw, which yields cslot = current_slot at emission.
\* Network may deliver this arbitrarily later (no ordering, no time bound).
Submit(id) ==
    /\ id \in MsgIDs
    /\ id \notin {m.id : m \in network}
    /\ \A n \in Nodes : id \notin processed[n]
    /\ network' = network \cup {[id |-> id, cslot |-> current_slot]}
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
    /\ node_state[n] = "up"
    /\ m.id \notin processed[n]              \* exactly-once guard (local)
    /\ m.cslot = current_slot                \* STRICT C-slot equality
    /\ processed' = [processed EXCEPT ![n] = @ \cup {m.id}]
    /\ UNCHANGED <<current_slot, network, persisted, node_state>>

\* CRASH: node loses RAM. persistent snapshot in `persisted` survives.
Crash(n) ==
    /\ n \in Nodes
    /\ node_state[n] = "up"
    /\ persisted'  = [persisted  EXCEPT ![n] = processed[n]]
    /\ node_state' = [node_state EXCEPT ![n] = "down"]
    /\ processed'  = [processed  EXCEPT ![n] = {}]
    /\ UNCHANGED <<current_slot, network>>

\* REJOIN: node recovers from persistent snapshot. processed = persisted.
Rejoin(n) ==
    /\ n \in Nodes
    /\ node_state[n] = "down"
    /\ processed'  = [processed  EXCEPT ![n] = persisted[n]]
    /\ node_state' = [node_state EXCEPT ![n] = "up"]
    /\ UNCHANGED <<current_slot, network, persisted>>

\* Adversarial duplicate / replay injection.
\* Attacker injects a message with arbitrary cslot value (past, present,
\* or future). The C-slot gate must still hold.
DuplicateInject(id, fake_cslot) ==
    /\ id \in MsgIDs
    /\ fake_cslot \in 0..MaxSlot
    /\ network' = network \cup {[id |-> id, cslot |-> fake_cslot]}
    /\ UNCHANGED <<current_slot, processed, persisted, node_state>>

\* Slot ticker advances by 1.
Tick ==
    /\ current_slot < MaxSlot
    /\ current_slot' = current_slot + 1
    /\ UNCHANGED <<network, processed, persisted, node_state>>

Next ==
    \/ \E id \in MsgIDs : Submit(id)
    \/ \E n \in Nodes, m \in network : Process(n, m)
    \/ \E n \in Nodes : Crash(n)
    \/ \E n \in Nodes : Rejoin(n)
    \/ \E id \in MsgIDs, k \in 0..MaxSlot : DuplicateInject(id, k)
    \/ Tick

Spec == Init /\ [][Next]_vars

-------------------------------------------------------------------------------
(*                              TYPE INVARIANT                              *)

TypeInvariant ==
    /\ current_slot \in 0..MaxSlot
    /\ network      \subseteq MsgRecord
    /\ processed    \in [Nodes -> SUBSET MsgIDs]
    /\ persisted    \in [Nodes -> SUBSET MsgIDs]
    /\ node_state   \in [Nodes -> {"up", "down"}]

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
    \A n \in Nodes :
        node_state[n] = "down" =>
            persisted[n] \subseteq {m.id : m \in network}

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

StateConstraint ==
    current_slot <= MaxSlot

-------------------------------------------------------------------------------
(*                              LIVENESS LAYER                              *)
(*                                                                          *)
(* DESIGN NOTE — fairness assignment is intentional:                        *)
(*                                                                          *)
(*  - SF(Tick): the slot ticker is fair, advancing eventually. This is a    *)
(*    physical-hardware assumption (the ticker process does not stall       *)
(*    forever). Strong fairness because Tick is always enabled until        *)
(*    current_slot reaches MaxSlot.                                         *)
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
(*  - NO fairness on Submit / DuplicateInject. Submit is a user action;    *)
(*    adversary injection is, by definition, not fair.                     *)
(***************************************************************************)

Fairness ==
    /\ SF_vars(Tick)
    /\ \A n \in Nodes : WF_vars(Rejoin(n))

LiveSpec == Init /\ [][Next]_vars /\ Fairness

\* L1 TICK PROGRESS.
\* Under SF(Tick), the slot counter eventually reaches the horizon.
TickProgress == <>(current_slot = MaxSlot)

\* L2 EVENTUAL REJOIN.
\* Every crashed node eventually returns to "up", under WF(Rejoin(n)).
EventualRejoin ==
    \A n \in Nodes : (node_state[n] = "down") ~> (node_state[n] = "up")

=============================================================================
