---------------------- MODULE QuantumArithmeticAxioms_negative_A1 ----------------------
EXTENDS Naturals, Integers, TLC

(*
  NEGATIVE TEST for Inv_A1_NoZero.

  Writes b' = 0 directly, violating the A1 (No-Zero) axiom which says
  QA states live in {1..N}, never {0..N-1}. The Inv_A1_NoZero invariant
  from QuantumArithmeticAxioms.tla must fire with a ≤3-state
  counterexample.
*)

VARIABLES b, e, d, a, qtag, fail, lastMove, obs_float, obs_cross_count

vars == <<b, e, d, a, qtag, fail, lastMove, obs_float, obs_cross_count>>

\* Init: a legal A1-compliant state (b=1, e=1 ⇒ d=2, a=3)
Init ==
  /\ b = 1
  /\ e = 1
  /\ d = 2
  /\ a = 3
  /\ qtag = 24 * 3 + 3  \* duo-modular tag for a=3: Phi9(3)=3, Phi24(3)=3
  /\ fail = "OK"
  /\ lastMove = "NONE"
  /\ obs_float = 0
  /\ obs_cross_count = 1

\* BROKEN ACTION: writes b' = 0, violating A1 (b must be >= 1).
BrokenA1 ==
  /\ b' = 0      \* BAD: A1 says b \in 1..CAP, never 0
  /\ e' = 1
  /\ d' = 1
  /\ a' = 2
  /\ qtag' = qtag
  /\ fail' = "OK"
  /\ lastMove' = "σ"
  /\ UNCHANGED <<obs_float, obs_cross_count>>

Next == BrokenA1

Spec == Init /\ [][Next]_vars

\* Mirror of Inv_A1_NoZero from QuantumArithmeticAxioms.tla. Uses
\* CAP = 20 implicitly by asserting b \in 1..20 (negative test does not
\* take CONSTANTS; we hardwire the domain to match
\* QuantumArithmeticAxioms's bounded-model configuration).
Inv_A1_NoZero ==
  /\ b \in 1..20
  /\ e \in 1..20

================================================================================
