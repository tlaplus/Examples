--------------------------- MODULE ParReachProofs ---------------------------
(***************************************************************************)
(* This module contains TLAPS checked proofs of the safety properties      *)
(* asserted in module ParReach--namely, the invariance of Inv and that the *)
(* parallel algorithm implements the safety part of Misra's algorithm under *)
(* the refinement mapping defined there.                                   *)
(***************************************************************************)
EXTENDS ParReach, Integers, TLAPS

LEMMA TypeInvariant == Spec  => []Inv
<1>1. Init => Inv
    BY RootAssump DEF Init, Inv, ProcSet  
<1>2. Inv /\ [Next]_vars => Inv'
   BY SuccAssump DEF Inv, Next, Terminating, vars, ProcSet, p, a, b, c
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec
  
THEOREM Spec => R!Init /\ [][R!Next]_R!vars
<1>1. Init => R!Init
    BY ProcsAssump DEF Init, R!Init, pcBar, vrootBar, ProcSet  
<1>2. Inv /\ [Next]_vars => [R!Next]_R!vars
  <2> SUFFICES ASSUME Inv,
                      [Next]_vars
               PROVE  [R!Next]_R!vars
    OBVIOUS
  <2> USE DEF Inv, Next, Terminating, vars, R!Next, R!vars, vrootBar, pcBar
  <2>1. ASSUME NEW self \in Procs,
               a(self)
        PROVE  [R!Next]_R!vars
    <3>1. ASSUME vroot # {}
          PROVE  UNCHANGED R!vars
       BY <2>1, <3>1 DEF a
    <3>2. ASSUME vroot = {}
          PROVE  [R!Next]_R!vars
      <4>1. ASSUME vrootBar = {}
            PROVE  [R!Next]_R!vars
        BY <2>1, <3>2, <4>1 DEF a, R!a
      <4>2. ASSUME vrootBar # {}
            PROVE UNCHANGED R!vars
        <5>1.  \E q \in Procs \ {self} : pc[q] # "Done"
          BY <4>2, <3>2, <2>1 DEF a
        <5>2. pcBar' # "Done"
          BY <5>1, <3>2, <2>1 DEF a
        <5>. QED
          BY <5>2, <3>2, <2>1 DEF a
      <4>3. QED 
        BY <4>1, <4>2       
    <3>3. QED
      BY <3>1, <3>2 DEF R!Next
  <2>2. ASSUME NEW self \in Procs,
               b(self)
        PROVE [R!Next]_R!vars
    BY <2>2 DEF b, R!a
  <2>3. ASSUME NEW self \in Procs,
               c(self)
        PROVE  [R!Next]_R!vars
    BY <2>3 DEF c
  <2>4. CASE UNCHANGED vars
    BY <2>4
  <2>5. QED
    BY <2>1, <2>2, <2>3, <2>4 DEF Next, Terminating, p
<1>3. QED
  BY <1>1, <1>2, TypeInvariant, PTL DEF Spec



=============================================================================
\* Modification History
\* Last modified Sun Apr 14 16:55:36 PDT 2019 by lamport
\* Created Sat Apr 13 14:37:54 PDT 2019 by lamport
