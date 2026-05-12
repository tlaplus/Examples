--------------------------- MODULE SimpleRegular_proof ------------------------
(***************************************************************************)
(* Wrapper theorems exposing TypeOK and Inv as named invariants of Spec.  *)
(* The inductive content is already in SimpleRegular.tla's Correctness.   *)
(***************************************************************************)
EXTENDS SimpleRegular, TLAPS

THEOREM TypeCorrect == Spec => []TypeOK
<1> USE NAssump DEF ProcSet
<1>1. Init => Inv
  <2>1. Init => 0 \in 0..(N-1) /\ pc[0] /= "Done"
    BY DEF Init
  <2>. QED  BY <2>1 DEF Init, Inv, TypeOK
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv, [Next]_vars  PROVE Inv'
    OBVIOUS
  <2>1. ASSUME NEW self \in 0..N-1, a1(self)
        PROVE  Inv'
    BY <2>1 DEF a1, Inv, TypeOK
  <2>2. ASSUME NEW self \in 0..N-1, a2(self)
        PROVE  Inv'
    BY <2>2 DEF a2, Inv, TypeOK
  <2>3. ASSUME NEW self \in 0..N-1, b(self)
        PROVE  Inv'
    <3> SUFFICES ASSUME NEW v \in x[(self-1) % N],
                        y' = [y EXCEPT ![self] = v]
                 PROVE  Inv'
      BY <2>3 DEF b
    <3>. QED  BY <2>3, Z3 DEF b, Inv, TypeOK
  <2>4. CASE UNCHANGED vars
    BY <2>4 DEF TypeOK, Inv, vars
  <2>. QED  BY <2>1, <2>2, <2>3, <2>4 DEF Next, Terminating, proc
<1>3. Inv => TypeOK
  BY DEF Inv
<1>. QED  BY <1>1, <1>2, <1>3, PTL DEF Spec

THEOREM InvInvariant == Spec => []Inv
<1> USE NAssump DEF ProcSet
<1>1. Init => Inv
  <2>1. Init => 0 \in 0..(N-1) /\ pc[0] /= "Done"
    BY DEF Init
  <2>. QED  BY <2>1 DEF Init, Inv, TypeOK
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv, [Next]_vars  PROVE Inv'
    OBVIOUS
  <2>1. ASSUME NEW self \in 0..N-1, a1(self)
        PROVE  Inv'
    BY <2>1 DEF a1, Inv, TypeOK
  <2>2. ASSUME NEW self \in 0..N-1, a2(self)
        PROVE  Inv'
    BY <2>2 DEF a2, Inv, TypeOK
  <2>3. ASSUME NEW self \in 0..N-1, b(self)
        PROVE  Inv'
    <3> SUFFICES ASSUME NEW v \in x[(self-1) % N],
                        y' = [y EXCEPT ![self] = v]
                 PROVE  Inv'
      BY <2>3 DEF b
    <3>. QED  BY <2>3, Z3 DEF b, Inv, TypeOK
  <2>4. CASE UNCHANGED vars
    BY <2>4 DEF TypeOK, Inv, vars
  <2>. QED  BY <2>1, <2>2, <2>3, <2>4 DEF Next, Terminating, proc
<1>. QED  BY <1>1, <1>2, PTL DEF Spec
============================================================================
