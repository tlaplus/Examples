---------------------- MODULE QuantumArithmeticAxioms_negative_A2 ----------------------
EXTENDS Naturals, Integers, TLC

(*
  NEGATIVE TEST for Inv_A2_DerivedCoords.

  Writes d' such that d' != b' + e', violating A2 (Derived Coords):
  d = b+e, a = b+2e must always be derived from (b,e), never assigned
  independently. The Inv_A2_DerivedCoords invariant must fire with a
  ≤3-state counterexample.
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
  /\ obs_float = 0
  /\ obs_cross_count = 1

\* BROKEN ACTION: writes d' = 99 while b' + e' = 4. Violates d = b + e.
BrokenA2 ==
  /\ b' = 2
  /\ e' = 2
  /\ d' = 99     \* BAD: should be b' + e' = 4
  /\ a' = 6      \* nominally b' + 2*e' = 6 (so a check passes; only d is broken)
  /\ qtag' = qtag
  /\ fail' = "OK"
  /\ lastMove' = "σ"
  /\ UNCHANGED <<obs_float, obs_cross_count>>

Next == BrokenA2

Spec == Init /\ [][Next]_vars

Inv_A2_DerivedCoords ==
  /\ d = b + e
  /\ a = b + 2 * e

================================================================================
