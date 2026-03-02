Apalache configuration for DieHardest (Section 4, interleaved composition).

    $ apalache-mc check \
        --cinit=ConstInit  --next=NextInterleaved \
        --inv=NotSolved    --length=13 \
        APADieHardest.tla

Apalache finds the expected 12-state counterexample in about four hours
on a 2021 MacBook Pro (Apalache 0.52.2).

----------------------------- MODULE APADieHardest ------------------------------
(***************************************************************************)
(* Apalache-compatible model-checking wrapper for DieHardest.              *)
(*                                                                         *)
(* DieHardest's Sections 1-3 use TLC-specific operators (TLCGet, TLCSet)   *)
(* that Apalache does not support.  This module checks only Section 4      *)
(* (interleaved composition) by selecting NextInterleaved via --next.      *)
(*                                                                         *)
(* Adaptations for Apalache:                                               *)
(*  - Constants are initialized via ConstInit (--cinit) rather than a      *)
(*    TLC .cfg file.                                                       *)
(*  - Capacity functions use [s \in S |-> ...] instead of the TLC-module   *)
(*    operators :> and @@.                                                 *)
(***************************************************************************)

CONSTANT
    \* @type: Seq(Str -> Int);
    Capacities,
    \* @type: Int;
    Goal

VARIABLE
    \* @type: Str -> Int;
    c1,
    \* @type: Str -> Int;
    c2,
    \* @type: Int;
    s1,
    \* @type: Int;
    s2

INSTANCE DieHardest

MCGoal == 4

MCCapacity1 ==
    [ s \in {"j1", "j2"} |-> IF s = "j1" THEN 5 ELSE 3 ]

MCCapacity2 ==
    [ s \in {"j1", "j2", "j3"} |-> IF s = "j1" THEN 5 ELSE 3 ]

ConstInit ==
    /\ Capacities = <<MCCapacity1, MCCapacity2>>
    /\ Goal = MCGoal

=============================================================================
