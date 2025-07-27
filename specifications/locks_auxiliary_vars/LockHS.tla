-------------------------------- MODULE LockHS --------------------------------

(*****************************************************************************)
(* This module contains the specification of a lock with auxiliary variables.*)
(* 1. A history variable `h_turn` is needed to remember the assignement of   *)
(*    the turn variable used inside the Peterson specification.              *)
(* 2. A stuttering variable `s` is added to force the stuttering of the Lock *)
(*    specification to mimick the 3 steps taken by Peterson to enter the     *)
(*    critical section.                                                      *)
(* With these variables, one can finally refine LockHS to Peterson, giving   *)
(* an equivalence between the Lock and Peterson specifications.              *)
(*                                                                           *)
(* The stuttering is achieved using the Stuttering module created by Leslie  *)
(* Lamport and comes from to the paper "Auxiliary Variables in TLA+".        *)
(* The module used here has been modified, see explanations at the end of    *) 
(* the Stuttering module.                                                    *)
(*****************************************************************************)

EXTENDS Lock, NaturalsInduction

\* History variable to remember the turn variable
VARIABLE h_turn
NoHistoryChange(A) == A /\ UNCHANGED h_turn

\* Stuttering variable
VARIABLE s
INSTANCE Stuttering

THEOREM StutterConstantCondition(1..2, 1, LAMBDA j : j-1)
<1>. DEFINE InvD(S) == {sig \in (1..2) \ S : sig-1 \in S}
            R[n \in Nat] == IF n = 0 THEN {1}
                            ELSE R[n-1] \cup InvD(R[n-1])
<1>. SUFFICES (1..2) = UNION {R[n] : n \in Nat}
  BY Zenon DEF StutterConstantCondition
<1>. HIDE DEF R
<1>1. \A n \in Nat : R[n] = IF n = 0 THEN {1}
                            ELSE R[n-1] \cup InvD(R[n-1])
  <2>. DEFINE RDef(g,n) == g \cup InvD(g)
  <2>1. NatInductiveDefHypothesis(R, {1}, RDef)
    BY Zenon DEF R, NatInductiveDefHypothesis
  <2>2. NatInductiveDefConclusion(R, {1}, RDef)
    BY <2>1, NatInductiveDef, Zenon
  <2>. QED  BY <2>2 DEF NatInductiveDefConclusion
<1>2. ASSUME NEW n \in Nat
      PROVE  R[n] \subseteq 1 .. 2
  <2>. DEFINE P(_n) == R[_n] \subseteq 1 .. 2
  <2>1. P(0)
    BY <1>1
  <2>2. ASSUME NEW m \in Nat, P(m)
        PROVE  P(m+1)
    <3>1. \A S : InvD(S) \subseteq 1 .. 2
      OBVIOUS
    <3> DEFINE _m == m+1
    <3>2. _m \in Nat \ {0}
      OBVIOUS
    <3> HIDE DEF _m
    <3>3. R[_m] = R[_m-1] \cup InvD(R[_m-1])
      BY <1>1, <3>2, Isa
    <3> USE DEF _m
    <3>4. R[m+1] = R[m] \cup InvD(R[m])
      BY <3>3
    <3>. QED  BY <2>2, <3>1, <3>4
  <2>. HIDE DEF P
  <2>3. \A m \in Nat : P(m)
    BY <2>1, <2>2, NatInduction, Isa
  <2>. QED  BY <2>3 DEF P
<1>3. R[1] = 1 .. 2
  BY <1>1
<1>. QED  BY <1>2, <1>3

-------------------------------------------------------------------------------

Other(p) == IF p = 1 THEN 2 ELSE 1 

InitHS == Init /\ (h_turn = 1) /\ (s = top)

\* Adding 2 stuttering steps after an l1(self) transition
\* Updating the history variable during the right stutter step
l1HS(self) == 
  /\ PostStutter(l1(self), "l1", self, 1, 2, LAMBDA j : j-1)
  /\ h_turn' = IF s' # top THEN IF s'.val = 1 THEN Other(self)
                                              ELSE h_turn
                           ELSE h_turn

procHS(self) == 
  \/ NoStutter(NoHistoryChange(l0(self)))
  \/ l1HS(self)
  \/ NoStutter(NoHistoryChange(cs(self)))
  \/ NoStutter(NoHistoryChange(l2(self)))

NextHS == (\E self \in 1..2: procHS(self))

SpecHS == InitHS /\ [][NextHS]_<<vars, h_turn, s>>

-------------------------------------------------------------------------------

TypeOKHS == 
  /\ TypeOK
  /\ h_turn \in 1..2
  /\ s \in {top} \cup [id : {"l1"}, ctxt : {1, 2}, val : 1..2]

InvHS == 
  /\ \A p \in ProcSet : 
    /\ IF s # top THEN s.ctxt = p ELSE FALSE
    => pc[p] = "cs"
  /\ \A p \in ProcSet :
    \/ pc[p] = "l2"
    \/ pc[p] = "cs" /\ s = top
    \/ IF s # top THEN s.ctxt = p /\ s.val = 1 ELSE FALSE
    => h_turn = Other(p)

pc_translation(self, label, stutter) == 
  CASE (label = "l0") -> "a0"
    [] (label = "l1") -> "a1"
    [] (label = "l2") -> "a4"
    [] (label = "cs") -> IF stutter = top THEN "cs"
                         ELSE IF stutter.ctxt # self THEN "cs"
                         ELSE IF stutter.val = 2 THEN "a2"
                         ELSE IF stutter.val = 1 THEN "a3"
                         ELSE "error"
c_translation(alt_label) == 
  alt_label \in {"a2", "a3", "cs", "a4"}

P == INSTANCE Peterson WITH
      pc <- [p \in ProcSet |-> pc_translation(p, pc[p], s)],
      c <- [p \in ProcSet |-> c_translation(pc_translation(p, pc[p], s))],
      turn <- h_turn

-------------------------------------------------------------------------------

(*****************************************************************************)
(* Proofs using stuttering variables can be quite complicated as the backend *)
(* solvers can be quite overwhelmed by the different transitions made        *)
(* possible by the PostStutter clauses.                                      *)
(* The easiest way to complete such proofs seems to be the extraction of     *)
(* all relevant information in a first step and then refer to that step      *)
(* instead of the expanded PostStutter.                                      *)
(*****************************************************************************)

LEMMA TypingHS == SpecHS => []TypeOKHS
  <1> USE DEF TypeOKHS, TypeOK, Other
  <1>1. InitHS => TypeOKHS
    BY DEF InitHS, Init
  <1>2. [NextHS]_<<vars, h_turn, s>> /\ TypeOKHS => TypeOKHS'
    <2> USE DEF NoStutter, NoHistoryChange
    <2> SUFFICES ASSUME [NextHS]_<<vars, h_turn, s>>,
                        TypeOKHS
                 PROVE TypeOKHS'
      OBVIOUS
    <2>1. ASSUME NEW self \in 1..2, NoStutter(NoHistoryChange(l0(self)))
                 PROVE TypeOKHS'
      BY <2>1 DEF l0
    <2>2. ASSUME NEW self \in 1..2, l1HS(self)
                 PROVE TypeOKHS'
      BY <2>2 DEF l1HS, l1, PostStutter, vars
    <2>3. ASSUME NEW self \in 1..2, NoStutter(NoHistoryChange(cs(self)))
                 PROVE TypeOKHS'
      BY <2>3 DEF cs
    <2>4. ASSUME NEW self \in 1..2, NoStutter(NoHistoryChange(l2(self)))
                 PROVE TypeOKHS'
      BY <2>4 DEF l2
    <2>5. CASE UNCHANGED <<vars, h_turn, s>>
      BY <2>5 DEF vars
    <2>6. QED 
      BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF NextHS, procHS
  <1>3. QED 
    BY <1>1, <1>2, PTL DEF SpecHS

LEMMA AddingVariables == SpecHS => Spec
  <1> USE DEF Other
  <1>1. InitHS => Init
    BY DEF InitHS
  <1>2. [NextHS]_<<vars, h_turn, s>> /\ TypeOKHS => [Next]_vars
    <2> USE DEF Next, vars, proc, NoStutter, NoHistoryChange
    <2> SUFFICES ASSUME [NextHS]_<<vars, h_turn, s>>,
                        TypeOKHS
                 PROVE [Next]_vars
      OBVIOUS
    <2>1. ASSUME NEW self \in 1..2, NoStutter(NoHistoryChange(l0(self)))
                 PROVE [Next]_vars
      BY <2>1 DEF l0
    <2>2. ASSUME NEW self \in 1..2, l1HS(self)
                 PROVE [Next]_vars
      BY <2>2 DEF l1HS, l1, PostStutter, vars
    <2>3. ASSUME NEW self \in 1..2, NoStutter(NoHistoryChange(cs(self)))
                 PROVE [Next]_vars
      BY <2>3 DEF cs
    <2>4. ASSUME NEW self \in 1..2, NoStutter(NoHistoryChange(l2(self)))
                 PROVE [Next]_vars
      BY <2>4 DEF l2
    <2>5. CASE UNCHANGED <<vars, h_turn, s>>
      BY <2>5 DEF vars
    <2>6. QED 
      BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF NextHS, procHS
  <1>3. QED 
    BY <1>1, <1>2, TypingHS, PTL DEF SpecHS, Spec 

LEMMA MutualExclusionHS == SpecHS => []LockInv
  BY AddingVariables, MutualExclusion

LEMMA IndInvHS == SpecHS => []InvHS
  <1> USE DEF InvHS, Other
  <1>1. InitHS => InvHS
    BY DEF InitHS, Init
  <1>2. /\ [NextHS]_<<vars, h_turn, s>> 
        /\ TypeOKHS /\ TypeOKHS'
        /\ LockInv /\ LockInv'
        /\ InvHS
        => InvHS'
    <2> USE DEF NoStutter, NoHistoryChange
    <2> SUFFICES ASSUME [NextHS]_<<vars, h_turn, s>>, 
                        TypeOKHS, TypeOKHS',
                        LockInv, LockInv',
                        InvHS
                 PROVE InvHS'
      OBVIOUS 
    <2>1. ASSUME NEW self \in 1..2, NoStutter(NoHistoryChange(l0(self)))
                 PROVE InvHS'
      BY <2>1 DEF l0, ProcSet, TypeOKHS, TypeOK
    <2>2. ASSUME NEW self \in 1..2, l1HS(self)
                 PROVE InvHS'
      <3> USE DEF PostStutter
      <3>1. CASE s = top
        <4>1. s' # top /\ s' = [id|->"l1", ctxt |-> self, val |-> 2]
          BY <2>2, <3>1 DEF l1HS, l1, top
        <4>2. pc'[self] = "cs" /\ lockcs(self)'
          BY <2>2, <3>1 DEF l1HS, l1, ProcSet, TypeOKHS, TypeOK, lockcs
        <4>3. (\A p \in ProcSet \ {self} : pc[p] \in {"l0", "l1"})'
          BY <4>2 DEF ProcSet, TypeOKHS, TypeOK, lockcs, LockInv
        <4>4. QED 
          BY <4>1, <4>2, <4>3
      <3>2. ASSUME s # top /\ s.ctxt # self PROVE FALSE
        BY <2>2, <3>2 DEF l1HS
      <3>3. CASE s # top /\ s = [id|->"l1", ctxt |-> self, val |-> 2]
        <4>1. s' # top /\ s' = [id|->"l1", ctxt |-> self, val |-> 1]
          BY <2>2, <3>3 DEF l1HS, l1, top
        <4>2. h_turn' = Other(self)
          BY <2>2, <3>3, <4>1 DEF l1HS
        <4>3. pc[self] = "cs" /\ pc'[self] = "cs" /\ UNCHANGED pc
          BY <2>2, <3>3 DEF l1HS, ProcSet, vars
        <4>4. \A p \in ProcSet \ {self} : pc[p] \in {"l0", "l1"}
          BY <4>3 DEF ProcSet, LockInv, lockcs, TypeOKHS, TypeOK
        <4>5. (\A p \in ProcSet \ {self} : pc[p] \in {"l0", "l1"})'
          BY <4>3, <4>4
        <4>6. QED 
          BY <4>1, <4>2, <4>3, <4>5
      <3>4. CASE s # top /\ s = [id|->"l1", ctxt |-> self, val |-> 1]
        <4>1. s' = top
          BY <2>2, <3>4 DEF l1HS
        <4>2. h_turn = Other(self) /\ h_turn' = Other(self)
          BY <2>2, <3>4 DEF l1HS, ProcSet
        <4>3. pc[self] = "cs" /\ pc'[self] = "cs" /\ UNCHANGED pc
          BY <2>2, <3>4 DEF l1HS, ProcSet, vars
        <4>4. \A p \in ProcSet \ {self} : pc[p] \in {"l0", "l1"}
          BY <4>3 DEF ProcSet, LockInv, lockcs, TypeOKHS, TypeOK
        <4>5. (\A p \in ProcSet \ {self} : pc[p] \in {"l0", "l1"})'
          BY <4>3, <4>4
        <4>6. QED
          BY <4>1, <4>2, <4>3, <4>4
      <3>5. QED 
        BY <3>1, <3>2, <3>3, <3>4 DEF TypeOKHS
    <2>3. ASSUME NEW self \in 1..2, NoStutter(NoHistoryChange(cs(self)))
                 PROVE InvHS'
      BY <2>3 DEF cs, ProcSet, TypeOKHS, TypeOK
    <2>4. ASSUME NEW self \in 1..2, NoStutter(NoHistoryChange(l2(self)))
                 PROVE InvHS'
        BY <2>4 DEF l2, ProcSet, TypeOKHS, TypeOK
    <2>5. CASE UNCHANGED <<vars, h_turn, s>>
      BY <2>5 DEF vars
    <2>6. QED 
      BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF NextHS, procHS
  <1>3. QED
    BY <1>1, <1>2, TypingHS, MutualExclusionHS, PTL DEF SpecHS


THEOREM SpecHS => P!Spec
  <1> USE DEF pc_translation, c_translation, 
              ProcSet, P!ProcSet, Other, P!Other
  <1>1. InitHS => P!Init
    BY DEF P!Init, InitHS, Init
  <1>2. /\ [NextHS]_<<vars, h_turn, s>> 
        /\ TypeOKHS /\ TypeOKHS'
        /\ LockInv /\ LockInv'
        /\ InvHS /\ InvHS'
        => [P!Next]_P!vars
    <2> USE DEF P!Next, P!vars, P!proc, NoStutter, NoHistoryChange
    <2> SUFFICES ASSUME [NextHS]_<<vars, h_turn, s>>,
                        TypeOKHS, TypeOKHS',
                        LockInv, LockInv',
                        InvHS, InvHS'
                 PROVE [P!Next]_P!vars
      BY Zenon
    <2>1. ASSUME NEW self \in 1..2, NoStutter(NoHistoryChange(l0(self)))
                 PROVE P!a0(self)
      BY <2>1 DEF l0, P!a0, TypeOKHS, TypeOK, vars
    <2>2. ASSUME NEW self \in 1..2, l1HS(self)
                 PROVE P!a1(self) \/ P!a2(self) \/ P!a3(self)
      <3> USE DEF PostStutter
      <3>1. ASSUME s = top PROVE P!a1(self)
        \* extract relevant facts from premises
        <4>1. /\ pc[self] = "l1" /\ pc' = [pc EXCEPT ![self] = "cs"]
              /\ s' # top /\ s' = [id |-> "l1", ctxt |-> self, val |-> 2]
              /\ UNCHANGED h_turn
          BY <2>2, <3>1 DEF l1HS, l1, TypeOKHS, top
        \* Verify that P!pc[self] = "a1"
        <4>2. pc_translation(self, pc[self], s) = "a1"
          BY <4>1
        <4>3. pc_translation(self, pc[self], s)' = "a2"
          BY <4>1 DEF TypeOKHS, TypeOK
        <4>4. \A p \in ProcSet \ {self} : UNCHANGED pc[p]
          BY <4>1 DEF TypeOKHS, TypeOK
        <4>5. (\A p \in ProcSet \ {self} : pc[p] \in {"l0", "l1"})'
          BY <4>1 DEF TypeOKHS, TypeOK, lockcs, LockInv
        \* Verify that the P!pc is modified correctly
        <4>6. [p \in ProcSet |-> pc_translation(p, pc[p], s)]'
              = [[p \in ProcSet |-> pc_translation(p, pc[p], s)] 
                  EXCEPT ![self] = "a2" ]
          BY <4>2, <4>3, <4>4, <4>5 DEF TypeOKHS, TypeOK
        <4>7. QED
          BY <4>1, <4>2, <4>6 DEF P!a1, TypeOKHS, TypeOK
      <3>2. ASSUME s # top /\ s.ctxt # self PROVE FALSE
        BY <2>2, <3>2 DEF l1HS
      <3>3. ASSUME s # top /\ s = [id|->"l1", ctxt |-> self, val |-> 2]
            PROVE P!a2(self)
        \* extract relevant facts from premises
        <4>1. /\ pc[self] = "cs" /\ UNCHANGED pc
              /\ s' # top /\ s' = [id |-> "l1", ctxt |-> self, val |-> 1]
          BY <2>2, <3>3 DEF l1HS, top, vars, TypeOKHS, InvHS
        <4>2. h_turn' = Other(self)
          BY <2>2, <4>1 DEF l1HS
        \* Verify that P!pc[self] = "a2"
        <4>3. pc_translation(self, pc[self], s) = "a2"
          BY <3>3, <4>1
        <4>4. pc_translation(self, pc[self], s)' = "a3"
          BY <4>1 DEF TypeOKHS, TypeOK
        <4>5. \A p \in ProcSet \ {self} : UNCHANGED pc[p]
          BY <4>1 DEF TypeOKHS, TypeOK
        <4>6. (\A p \in ProcSet \ {self} : pc[p] \in {"l0", "l1"})'
          BY <4>1 DEF TypeOKHS, TypeOK, lockcs, LockInv
        \* Verify P!pc is modified correctly
        <4>7. [p \in ProcSet |-> pc_translation(p, pc[p], s)]'
              = [[p \in ProcSet |-> pc_translation(p, pc[p], s)] 
                  EXCEPT ![self] = "a3" ]
          BY <4>3, <4>4, <4>5, <4>6 DEF TypeOKHS, TypeOK
        <4>8. QED
          BY <4>2, <4>3, <4>7 DEF P!a2, TypeOKHS, TypeOK
      <3>4. ASSUME s # top /\ s = [id|->"l1", ctxt |-> self, val |-> 1]
            PROVE P!a3(self)
        \* extract relevant facts from premises
        <4>1. /\ pc[self] = "cs" /\ UNCHANGED pc
              /\ s' = top
              /\ UNCHANGED h_turn
          BY <2>2, <3>4 DEF l1HS, top, vars, TypeOKHS, TypeOK, InvHS
        \* Verify that P!pc[self] = "a1"
        <4>2. pc_translation(self, pc[self], s) = "a3"
          BY <3>4, <4>1
        <4>3. pc_translation(self, pc[self], s)' = "cs"
          BY <4>1 DEF TypeOKHS, TypeOK
        <4>4. \A p \in ProcSet \ {self} : UNCHANGED pc[p]
          BY <4>1 DEF TypeOKHS, TypeOK
        <4>5. (\A p \in ProcSet \ {self} : pc[p] \in {"l0", "l1"})'
          BY <4>1 DEF TypeOKHS, TypeOK, lockcs, LockInv
        \* Verify that the P!pc is modified correctly
        <4>6. [p \in ProcSet |-> pc_translation(p, pc[p], s)]'
              = [[p \in ProcSet |-> pc_translation(p, pc[p], s)] 
                  EXCEPT ![self] = "cs" ]
          BY <4>2, <4>3, <4>4, <4>5 DEF TypeOKHS, TypeOK
        \* Verify process can pass barrier
        <4>7. c_translation(pc_translation(Other(self), pc[Other(self)], s))' = FALSE
          BY <4>5
        <4>8. UNCHANGED c_translation(pc_translation(self, pc[self], s))
          BY <4>1, <4>2, <4>3
        <4>9. UNCHANGED c_translation(pc_translation(Other(self), pc[Other(self)], s))
          BY <4>4, <4>5
        <4>10. UNCHANGED [p \in ProcSet |-> c_translation(pc_translation(p, pc[p], s))]
          BY <4>8, <4>9 DEF TypeOKHS, TypeOK
        <4> HIDE DEF pc_translation, c_translation
        <4>x. QED
          BY <4>1, <4>2, <4>4, <4>6, <4>7, <4>10
          DEF P!a3, TypeOKHS, TypeOK
      <3>5. QED
        BY <3>1, <3>2, <3>3, <3>4 DEF TypeOKHS
    <2>3. ASSUME NEW self \in 1..2, NoStutter(NoHistoryChange(cs(self)))
                 PROVE P!cs(self) 
      BY <2>3 DEF cs, P!cs, TypeOKHS, TypeOK
    <2>4. ASSUME NEW self \in 1..2, NoStutter(NoHistoryChange(l2(self)))
                 PROVE P!a4(self)
      BY <2>4 DEF l2, P!a4, TypeOKHS, TypeOK
    <2>5. CASE UNCHANGED <<vars, h_turn, s>>
      BY <2>5, Isa DEF vars, P!vars
    <2>6. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, Zenon DEF NextHS, procHS, P!Next, P!proc
  <1>3. QED
    BY <1>1, <1>2, PTL,
       TypingHS, MutualExclusionHS, IndInvHS
    DEF SpecHS, P!Spec



===============================================================================