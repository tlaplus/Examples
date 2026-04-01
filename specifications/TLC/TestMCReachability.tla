------------------------- MODULE TestMCReachability -------------------------
EXTENDS StateGraphs
(***************************************************************************)
(* Test harness for MCReachability using graphs defined in StateGraphs.    *)
(***************************************************************************)

VARIABLES S, C, successors, done, T, counterexample, L

INSTANCE MCReachability WITH
    StateGraph      <- TestCase.g,
    ViolationStates <- TestCase.v

=============================================================================
