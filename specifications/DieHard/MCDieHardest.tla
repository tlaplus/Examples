----------------------------- MODULE MCDieHardest ------------------------------
EXTENDS DieHardest

(***************************************************************************)
(* Compare the classic Die Hard configuration (5- and 3-gallon jugs) with  *)
(* the same configuration plus a duplicate 3-gallon jug.                   *)
(*                                                                         *)
(*   <<5, 3>>       needs 6 steps (the well-known Die Hard solution).      *)
(*   <<5, 3, 3>>    needs 5 steps: fill 5 → pour 5→3 → pour 5→3b →         *)
(*                  fill 5 → pour 5→3b, leaving 4 in the 5-gallon jug.     *)
(*                                                                         *)
(* TLC's counterexample will have s1 = 6, s2 = 5: configuration 2 "wins".  *)
(***************************************************************************)

MCGoal == 4

MCCapacity1 == "j1" :> 5 @@ "j2" :> 3

MCCapacity2 == "j1" :> 5 @@ "j2" :> 3 @@ "j3" :> 3

MCCapacities == <<MCCapacity1, MCCapacity2>>

=============================================================================
