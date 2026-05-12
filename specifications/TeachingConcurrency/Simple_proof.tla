--------------------------- MODULE Simple_proof -------------------------------
(***************************************************************************)
(* Wrapper theorems exposing TypeOK and Inv as named invariants of Spec.  *)
(* The actual inductive content is already in Simple.tla's `Correctness`. *)
(***************************************************************************)
EXTENDS Simple

THEOREM TypeCorrect == Spec => []TypeOK
<1> USE NAssump DEF Inv, TypeOK, ProcSet
<1>1. Init => Inv
  BY DEF Init
<1>2. Inv /\ [Next]_vars => Inv'
  BY DEF Next, a, b, vars, Terminating, proc
<1>3. Inv => TypeOK
  OBVIOUS
<1>. QED  BY <1>1, <1>2, <1>3, PTL DEF Spec

THEOREM InvInvariant == Spec => []Inv
<1> USE NAssump DEF Inv, TypeOK, ProcSet
<1>1. Init => Inv
  BY DEF Init
<1>2. Inv /\ [Next]_vars => Inv'
  BY DEF Next, a, b, vars, Terminating, proc
<1>. QED  BY <1>1, <1>2, PTL DEF Spec
============================================================================
