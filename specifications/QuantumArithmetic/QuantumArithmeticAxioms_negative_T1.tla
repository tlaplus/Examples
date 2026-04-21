---------------------- MODULE QuantumArithmeticAxioms_negative_T1 ----------------------
EXTENDS Naturals, Integers, TLC

(*
  NEGATIVE TEST for Inv_T1_IntegerPathTime.

  Writes lastMove' to a value OUTSIDE the finite generator alphabet
  {"NONE","σ","μ","λ"}, simulating the introduction of a continuous-
  time-like tag into the QA layer. This directly violates T1
  (Path Time): QA time is integer path length k; no continuous time
  variables in QA logic.

  Expected: Inv_T1_IntegerPathTime violated with a ≤3-state counterexample.
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

\* BROKEN ACTION: writes lastMove' = "t_continuous", violating T1.
BrokenT1 ==
  /\ b' = 1
  /\ e' = 2
  /\ d' = 3
  /\ a' = 5
  /\ qtag' = qtag
  /\ fail' = "OK"
  /\ lastMove' = "t_continuous"   \* BAD: T1 says finite generator alphabet only
  /\ UNCHANGED <<obs_float, obs_cross_count>>

Next == BrokenT1

Spec == Init /\ [][Next]_vars

Inv_T1_IntegerPathTime ==
  lastMove \in {"NONE","σ","μ","λ"}

================================================================================
