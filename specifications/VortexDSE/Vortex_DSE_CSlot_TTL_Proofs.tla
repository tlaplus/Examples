------------------- MODULE Vortex_DSE_CSlot_TTL_Proofs -------------------
(***************************************************************************)
(* The bounded-memory mode refines the default one.                        *)
(*                                                                          *)
(* Its admission gate is m.cslot = current_slot where the default admits on *)
(* m.cslot <= current_slot, and no other action differs, so every behaviour *)
(* of this module is a behaviour of Vortex_DSE_CSlot under the identity     *)
(* mapping. Every safety property established for the default mode is       *)
(* therefore inherited here and does not need reproving.                    *)
(***************************************************************************)

EXTENDS Vortex_DSE_CSlot_TTL, TLAPS

LEMMA InitType == Init => TypeInvariant
  BY DEF Init, TypeInvariant, MsgRecord

LEMMA NextType == TypeInvariant /\ [Next]_vars => TypeInvariant'
  BY DEF TypeInvariant, MsgRecord, vars, Next, Send, Process, Crash, Rejoin, Tick

THEOREM TypeCorrect == Spec => []TypeInvariant
  BY InitType, NextType, PTL DEF Spec

\* The admission gate here is equality where the default admits on <=, so
\* the step needs to know that both are natural numbers: that is where the
\* type invariant is used, and nowhere else.
THEOREM Refinement == Spec => C!Spec
<1>1. Init => C!Init
  BY DEF Init, C!Init, Up, C!Up
<1>2. TypeInvariant /\ [Next]_vars => [C!Next]_C!vars
  <2> SUFFICES ASSUME TypeInvariant, Next PROVE [C!Next]_C!vars
    BY DEF vars, C!vars
  <2>1. CASE \E id \in MsgIDs, k \in Nat : Send(id, k)
    BY <2>1 DEF Send, C!Next, C!Send
  <2>2. CASE \E n \in Nodes, m \in network : Process(n, m)
    <3> PICK nn \in Nodes, mm \in network : Process(nn, mm)
      BY <2>2
    <3>1. mm.cslot \in Nat /\ current_slot \in Nat
      BY DEF TypeInvariant, MsgRecord
    <3>2. mm.cslot <= current_slot
      BY <3>1 DEF Process
    <3>. QED
      BY <3>2 DEF Process, C!Next, C!Process, Up, C!Up
  <2>3. CASE \E n \in Nodes : Crash(n)
    BY <2>3 DEF Crash, C!Next, C!Crash, Up, Down, C!Up, C!Down
  <2>4. CASE \E n \in Nodes : Rejoin(n)
    BY <2>4 DEF Rejoin, C!Next, C!Rejoin, Up, Down, C!Up, C!Down
  <2>5. CASE Tick
    BY <2>5 DEF Tick, C!Next, C!Tick
  <2>. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
<1>. QED
  BY <1>1, <1>2, TypeCorrect, PTL DEF Spec, C!Spec

=============================================================================
