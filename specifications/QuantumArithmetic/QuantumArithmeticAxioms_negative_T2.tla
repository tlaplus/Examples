---------------------- MODULE QuantumArithmeticAxioms_negative_T2 ----------------------
EXTENDS Naturals, Integers, TLC

(*
  NEGATIVE TEST for Inv_T2_FirewallRespected.

  A pseudo-QA action modifies obs_float while obs_cross_count is still 1
  (i.e., Project has not yet fired). This violates the T2 Firewall:
  observer-layer variables must not be mutated by QA-layer actions;
  only the dedicated Project action may cross the output boundary.

  The direct state-level encoding of Inv_T2_FirewallRespected is:
    (obs_cross_count = 1) => (obs_float = 0)
  The broken action writes obs_float' = 42 while obs_cross_count remains 1,
  so the invariant must fire.

  Expected: ≤3-state counterexample.
*)

VARIABLES b, e, d, a, qtag, fail, lastMove, obs_float, obs_cross_count

vars == <<b, e, d, a, qtag, fail, lastMove, obs_float, obs_cross_count>>

Init ==
  /\ b = 1
  /\ e = 1
  /\ d = 2
  /\ a = 3
  /\ qtag = 24 * 3 + 3
  /\ fail = "OK"
  /\ lastMove = "NONE"
  /\ obs_float = 0           \* A1-compliant Init
  /\ obs_cross_count = 1     \* pre-Project

\* BROKEN ACTION: QA-layer pseudo-step that illegally modifies obs_float
\* without advancing obs_cross_count. Encodes a "continuous output leaks
\* back as QA state" violation.
BrokenT2 ==
  /\ b' = 1
  /\ e' = 2
  /\ d' = 3
  /\ a' = 5
  /\ qtag' = qtag
  /\ fail' = "OK"
  /\ lastMove' = "σ"
  /\ obs_float' = 42         \* BAD: T2 says QA actions UNCHANGED obs_float
  /\ obs_cross_count' = 1    \* unchanged: projection not declared

Next == BrokenT2

Spec == Init /\ [][Next]_vars

Inv_T2_FirewallRespected ==
  (obs_cross_count = 1) => (obs_float = 0)

================================================================================
