---------------------- MODULE QuantumArithmeticAxioms_negative_NT ----------------------
EXTENDS Naturals, Integers, TLC

(*
  NEGATIVE TEST for Inv_NT_NoObserverFeedback.

  Writes obs_cross_count' = 3, violating the Theorem NT bound that the
  observer-layer boundary is crossed EXACTLY TWICE per QA trace: once at
  Init (continuous input seed → discrete) and once at Project (discrete →
  continuous output). A third crossing represents feedback from observer
  output back into the QA layer — forbidden by Theorem NT.

  Expected: Inv_NT_NoObserverFeedback violated with a ≤3-state counterexample.
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
  /\ obs_float = 3           \* represents post-Project state (cross 2 done)
  /\ obs_cross_count = 2

\* BROKEN ACTION: attempts a THIRD boundary crossing (observer → QA feedback).
\* NT says the boundary is crossed at most twice; a third crossing means the
\* observer layer is feeding back into QA as a causal input.
BrokenNT ==
  /\ UNCHANGED <<b, e, d, a, qtag, fail, lastMove, obs_float>>
  /\ obs_cross_count' = 3    \* BAD: NT caps at 2

Next == BrokenNT

Spec == Init /\ [][Next]_vars

Inv_NT_NoObserverFeedback ==
  obs_cross_count \in {1, 2}

================================================================================
