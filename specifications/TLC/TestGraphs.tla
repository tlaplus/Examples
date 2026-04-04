----------------------------- MODULE TestGraphs -----------------------------
EXTENDS StateGraphs
(***************************************************************************)
(* Test harness for TLCMC using graphs defined in StateGraphs.             *)
(***************************************************************************)

CONSTANT null
VARIABLES S, C, state, successors, i, counterexample, T, L, pc

Workers == IF "K" \in DOMAIN IOEnv THEN atoi(IOEnv.K) ELSE 1

INSTANCE TLCMC WITH StateGraph <- TestCase.g, ViolationStates <- TestCase.v, K <- Workers, Constraint <- LAMBDA s, l : TRUE, Counterexamples <- TestCase.cx

=============================================================================

$ for g in 1 2 3 4 5 6 7 8 9 10 11 12 13; do for k in 1 2 3; do echo "=== Graph G$g, K=$k ==="; GRAPH=$g K=$k tlc -config TestGraphs.cfg TestGraphs.tla || break 2; done; done