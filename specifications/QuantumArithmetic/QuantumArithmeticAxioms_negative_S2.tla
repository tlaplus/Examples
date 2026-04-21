---------------------- MODULE QuantumArithmeticAxioms_negative_S2 ----------------------
EXTENDS Naturals, Integers, TLC

(*
  NEGATIVE TEST for Inv_S2_IntegerState.

  Writes b' to a non-Nat value (a string), violating S2 (No float state):
  b, e, d, a must be Nat (int or Fraction). No np.zeros, no float.
  Since TLA+ has no native float type, the canonical S2 violation is
  writing a non-numeric value to a state variable; TLC's domain check
  for `\in Nat` fires on strings / tuples / functions alike.

  Expected: Inv_S2_IntegerState violated with a ≤3-state counterexample.
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

\* BROKEN ACTION: writes b' = "ghost", violating b \in Nat.
BrokenS2 ==
  /\ b' = "ghost"    \* BAD: S2 says b \in Nat
  /\ e' = 1
  /\ d' = 2
  /\ a' = 3
  /\ qtag' = qtag
  /\ fail' = "OK"
  /\ lastMove' = "σ"
  /\ UNCHANGED <<obs_float, obs_cross_count>>

Next == BrokenS2

Spec == Init /\ [][Next]_vars

Inv_S2_IntegerState ==
  /\ b \in Nat
  /\ e \in Nat
  /\ d \in Nat
  /\ a \in Nat
  /\ qtag \in Nat

================================================================================
