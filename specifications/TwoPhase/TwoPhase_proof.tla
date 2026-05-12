------------------------ MODULE TwoPhase_proof -----------------------
(***************************************************************************)
(* TLAPS proof of                                                          *)
(*   THEOREM Implementation == Spec => A!Spec                              *)
(* stated in TwoPhase.tla.                                                 *)
(***************************************************************************)
EXTENDS TwoPhase, TLAPS

(***************************************************************************)
(* The following theorem is a standard proof that one specification        *)
(* implements (the safety part of) another specification under a           *)
(* refinement mapping.  In fact, the temporal leaf proofs will be exactly  *)
(* the same one-liners for every such proof.  In realistic example, the    *)
(* non-temporal leaf proofs will be replaced by fairly long structured     *)
(* proofs--especially the two substeps numbered <2>2.                      *)
(***************************************************************************)
THEOREM Implementation
<1>1. Spec => []Inv
  <2>1. Init => Inv
    BY DEF Init, Inv
  <2>2. Inv /\ [Next]_<<p, c, x>> => Inv'
    BY Z3 DEF Inv, Next, ProducerStep, ConsumerStep
  <2>. QED
    BY <2>1, <2>2, PTL DEF Spec
<1>2. QED
  <2>1. Init => A!Init
    BY Z3 DEF Init, A!Init, vBar
  <2>2. Inv /\ [Next]_<<p, c, x>>  => [A!Next]_<<vBar, x>>
    BY Z3 DEF Inv, Next, ProducerStep, ConsumerStep, A!Next, vBar
  <2>3. []Inv /\ [][Next]_<<p, c, x>>  => [][A!Next]_<<vBar, x>>
    BY <2>1, <2>2, PTL
  <2>. QED
    BY <2>1, <2>3, <1>1, PTL DEF Spec, A!Spec

==============================================================
