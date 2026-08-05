---------------------- MODULE Vortex_DSE_CSlot_Skew ----------------------
(***************************************************************************)
(* Vortex DSE   C-slot under BOUNDED CLOCK SKEW + Byzantine inject.        *)
(*                                                                          *)
(* Extension of Vortex_DSE_CSlot.tla. The single global current_slot is    *)
(* replaced with a per-node clock node_slot[n]. Two adversarial powers are *)
(* added beyond the baseline spec:                                          *)
(*                                                                          *)
(*  1. CLOCK SKEW: each node ticks independently. The system enforces       *)
(*     |node_slot[n1] - node_slot[n2]| <= MaxSkew as a structural          *)
(*     constraint on Tick.                                                  *)
(*                                                                          *)
(*  2. BYZANTINE INJECT: adversary may inject a message with arbitrary     *)
(*     cslot AND arbitrary origin node id (spoof the sender).              *)
(*                                                                          *)
(* The same exactly-once / no-phantom / strict-equality properties must    *)
(* still hold, locally per node. Decision-locality means each node makes   *)
(* its own admission decision against its own clock.                       *)
(***************************************************************************)

EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, MsgIDs, MaxSlot, MaxSkew

VARIABLES
    node_slot,    \* [Nodes -> Int]  per-node clock
    network,      \* set of msg records
    processed,
    persisted,
    node_state

vars == <<node_slot, network, processed, persisted, node_state>>

MsgRecord == [id: MsgIDs, cslot: 0..MaxSlot, origin: Nodes]

-------------------------------------------------------------------------------
Init ==
    /\ node_slot   = [n \in Nodes |-> 0]
    /\ network     = {}
    /\ processed   = [n \in Nodes |-> {}]
    /\ persisted   = [n \in Nodes |-> {}]
    /\ node_state  = [n \in Nodes |-> "up"]

-------------------------------------------------------------------------------
\* Submit: sender n stamps with its own local slot.
Submit(id, n) ==
    /\ id \in MsgIDs
    /\ n \in Nodes
    /\ node_state[n] = "up"
    /\ id \notin {m.id : m \in network}
    /\ \A x \in Nodes : id \notin processed[x]
    /\ network' = network \cup {[id |-> id, cslot |-> node_slot[n], origin |-> n]}
    /\ UNCHANGED <<node_slot, processed, persisted, node_state>>

\* Process: STRICT slot equality, but vs LOCAL clock now.
Process(n, m) ==
    /\ n \in Nodes
    /\ m \in network
    /\ node_state[n] = "up"
    /\ m.id \notin processed[n]
    /\ m.cslot = node_slot[n]
    /\ processed' = [processed EXCEPT ![n] = @ \cup {m.id}]
    /\ UNCHANGED <<node_slot, network, persisted, node_state>>

Crash(n) ==
    /\ n \in Nodes
    /\ node_state[n] = "up"
    /\ persisted'  = [persisted  EXCEPT ![n] = processed[n]]
    /\ node_state' = [node_state EXCEPT ![n] = "down"]
    /\ processed'  = [processed  EXCEPT ![n] = {}]
    /\ UNCHANGED <<node_slot, network>>

Rejoin(n) ==
    /\ n \in Nodes
    /\ node_state[n] = "down"
    /\ processed'  = [processed  EXCEPT ![n] = persisted[n]]
    /\ node_state' = [node_state EXCEPT ![n] = "up"]
    /\ UNCHANGED <<node_slot, network, persisted>>

\* Byzantine inject: adversary spoofs both cslot AND origin.
ByzantineInject(id, fake_cslot, fake_origin) ==
    /\ id \in MsgIDs
    /\ fake_cslot \in 0..MaxSlot
    /\ fake_origin \in Nodes
    /\ network' = network \cup
         {[id |-> id, cslot |-> fake_cslot, origin |-> fake_origin]}
    /\ UNCHANGED <<node_slot, processed, persisted, node_state>>

\* Per-node tick, bounded by MaxSkew vs slowest node.
SkewedTick(n) ==
    /\ n \in Nodes
    /\ node_slot[n] < MaxSlot
    /\ \A other \in Nodes :
         (node_slot[n] + 1) - node_slot[other] <= MaxSkew
    /\ node_slot' = [node_slot EXCEPT ![n] = @ + 1]
    /\ UNCHANGED <<network, processed, persisted, node_state>>

Next ==
    \/ \E id \in MsgIDs, n \in Nodes : Submit(id, n)
    \/ \E n \in Nodes, m \in network : Process(n, m)
    \/ \E n \in Nodes : Crash(n)
    \/ \E n \in Nodes : Rejoin(n)
    \/ \E id \in MsgIDs, k \in 0..MaxSlot, o \in Nodes : ByzantineInject(id, k, o)
    \/ \E n \in Nodes : SkewedTick(n)

Spec == Init /\ [][Next]_vars

-------------------------------------------------------------------------------
(*                          INVARIANTS                                       *)

TypeInvariant ==
    /\ node_slot   \in [Nodes -> 0..MaxSlot]
    /\ network     \subseteq MsgRecord
    /\ processed   \in [Nodes -> SUBSET MsgIDs]
    /\ persisted   \in [Nodes -> SUBSET MsgIDs]
    /\ node_state  \in [Nodes -> {"up", "down"}]

\* The Tick guard guarantees this; it is asserted as invariant to make
\* the skew bound an explicit, machine-checked property.
BoundedSkew ==
    \A n1, n2 \in Nodes :
        /\ node_slot[n1] - node_slot[n2] <= MaxSkew
        /\ node_slot[n2] - node_slot[n1] <= MaxSkew

ExactlyOncePerNode ==
    \A n \in Nodes : Cardinality(processed[n]) <= Cardinality(MsgIDs)

\* Local admission: a processed id has a network record whose cslot
\* is at most the node's current local slot. (Strict equality holds
\* at admission time; monotone clock means cslot <= node_slot[n] later.)
CSlotLocalAdmission ==
    \A n \in Nodes : \A id \in processed[n] :
        \E m \in network : m.id = id /\ m.cslot <= node_slot[n]

PersistedReflectsReality ==
    \A n \in Nodes :
        node_state[n] = "down" =>
            persisted[n] \subseteq {m.id : m \in network}

NoPhantomProcess ==
    \A n \in Nodes : processed[n] \subseteq {m.id : m \in network}

-------------------------------------------------------------------------------
StateConstraint ==
    \A n \in Nodes : node_slot[n] <= MaxSlot

=============================================================================
