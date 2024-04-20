------------------- MODULE Einstein ------------------------

(*********************************************************************************)
(* Literature/Source:                                                            *)
(*   https://udel.edu/~os/riddle.html                                            *)
(*                                                                               *)
(* Situation:                                                                    *)
(* - There are 5 houses in five different colors.                                *)
(* - In each house lives a person with a different nationality.                  *)
(* - These five owners drink a certain type of beverage, smoke a                 *)
(*   certain brand of cigar and keep a certain pet.                              *)
(* - No owners have the same pet, smoke the same brand of cigar, or              *)
(*   drink the same beverage.                                                    *)
(*                                                                               *)
(* Rules:                                                                        *)
(*  1 the Brit lives in the red house                                            *)
(*  2 the Swede keeps dogs as pets                                               *)
(*  3 the Dane drinks tea                                                        *)
(*  4 the green house is on the left of the white house                          *)
(*  5 the green house's owner drinks coffee                                      *)
(*  6 the person who smokes Pall Mall rears birds                                *)
(*  7 the owner of the yellow house smokes Dunhill                               *)
(*  8 the man living in the center house drinks mylk                             *)
(*  9 the Norwegian lives in the first house                                     *)
(* 10 the man who smokes blends lives next to the one who keeps cats             *)
(* 11 the man who keeps horses lives next to man who smokes Dunhill              *)
(* 12 the owner who smokes BlueMaster drinks beer                                *)
(* 13 the German smokes Prince                                                   *)
(* 14 the Norwegian lives next to the blue house                                 *)
(* 15 the man who smokes blend has a neighbor who drinks water                   *)
(*                                                                               *)
(* Question:                                                                     *)
(*  Who owns the fish?                                                           *)
(*                                                                               *)
(* Note that `^TLC^' takes a very long time to find the solution because it      *)
(* blindly enumerates all possible combinations of assignments to the variables; *)
(* in contrast, `^Apalache^' finds the solution easily using an `^SMT^' solver.  *)
(* Instructions to run `^Apalache^' appear at the end of the file.               *)
(*********************************************************************************)

EXTENDS Naturals, FiniteSets, Apalache

House == 1..5

\* Note that TLC!Permutations has a Java module override and, thus,
\* would be evaluated faster.  However, TLC!Permutations equals a
\* set of records whereas Permutation below equals a set of tuples/
\* sequences.  Also, Permutation expects Cardinality(S) = 5.
\* @type: Set(Str) => Set(Seq(Str));
Permutation(S) == {
  FunAsSeq(p, 5, 5) : p \in {
    p \in [ House -> S ] :
      /\ p[2] \in S \ {p[1]}
      /\ p[3] \in S \ {p[1], p[2]}
      /\ p[4] \in S \ {p[1], p[2], p[3]}
      /\ p[5] \in S \ {p[1], p[2], p[3], p[4]}
    }
  }

\* In most specs, the following parameterization would be defined as
\* constants.  Given that Einstein's riddle has only this
\* parameterization, the constants are replaced with constant-level
\* operators.  As a side-effect, TLC evaluates them eagerly at startup, 
\* and Apalache successfully determines their types.
NATIONALITIES == Permutation({ "brit", "swede", "dane", "norwegian", "german" })
DRINKS == Permutation({ "beer", "coffee", "mylk", "tea", "water" })
COLORS == Permutation({ "red", "white", "blue", "green", "yellow" })
PETS == Permutation({ "bird", "cat", "dog", "fish", "horse" })
CIGARS == Permutation({ "blend", "bm", "dh", "pm", "prince" })

VARIABLES
    \* @type: Seq(Str);
    nationality,    \* tuple of nationalities
    \* @type: Seq(Str);
    colors,         \* tuple of house colors
    \* @type: Seq(Str);
    pets,           \* tuple of pets
    \* @type: Seq(Str);
    cigars,         \* tuple of cigars
    \* @type: Seq(Str);
    drinks          \* tuple of drinks

------------------------------------------------------------

(*********)
(* Rules *)
(*********)

BritLivesInTheRedHouse == \E i \in 2..5 : nationality[i] = "brit" /\ colors[i] = "red"

SwedeKeepsDogs == \E i \in 2..5 : nationality[i] = "swede" /\ pets[i] = "dog"

DaneDrinksTea == \E i \in 2..5 : nationality[i] = "dane" /\ drinks[i] = "tea"

GreenLeftOfWhite == \E i \in 1..4 : colors[i] = "green" /\ colors[i + 1] = "white"

GreenOwnerDrinksCoffee == \E i \in 1..5 \ {3} : colors[i] = "green" /\ drinks[i] = "coffee"

SmokesPallmallRearsBirds == \E i \in 1..5 : cigars[i] = "pm" /\ pets[i] = "bird"

YellowOwnerSmokesDunhill == \E i \in 1..5 : colors[i] = "yellow" /\ cigars[i] = "dh"

CenterDrinksMylk == drinks[3] = "mylk"

NorwegianFirstHouse == nationality[1] = "norwegian"

BlendSmokerLivesNextToCatOwner ==
    \E i \in 1..4 :
        \/ cigars[i] = "blend" /\ pets[i + 1] = "cat"
        \/ pets[i] = "cat" /\ cigars[i + 1] = "blend"

HorseKeeperLivesNextToDunhillSmoker ==
    \E i \in 1..4 :
        \/ cigars[i] = "dh" /\ pets[i + 1] = "horse"
        \/ pets[i] = "horse" /\ cigars[i + 1] = "dh"

BluemasterSmokerDrinksBeer == \E i \in 1..5 : cigars[i] = "bm" /\ drinks[i] = "beer"

GermanSmokesPrince == \E i \in 2..5 : nationality[i] = "german" /\ cigars[i] = "prince"

NorwegianLivesNextToBlueHouse == colors[2] = "blue" \* since the norwegian lives in the first house

BlendSmokerHasWaterDrinkingNeighbor ==
    \E i \in 1..4 :
        \/ cigars[i] = "blend" /\ drinks[i + 1] = "water"
        \/ drinks[i] = "water" /\ cigars[i + 1] = "blend"

------------------------------------------------------------

(************)
(* Solution *)
(************)

Init ==
    /\ drinks \in { p \in DRINKS : p[3] = "mylk" }
    /\ nationality \in { p \in NATIONALITIES : p[1] = "norwegian" }
    /\ colors \in { p \in COLORS : p[2] = "blue" }
    /\ pets \in PETS
    /\ cigars \in CIGARS

\* Apalache cannot infer the type of `vars' because it could be a sequence or a tuple.
\* So we explicitely tell Apalache that it is a sequence by adding the following annotation:
\* @type: Seq(Seq(Str));
vars == <<nationality, colors, cigars, pets, drinks>>

Next ==
    UNCHANGED vars

Spec == Init /\ [][Next]_vars

Solution ==
    /\ BritLivesInTheRedHouse
    /\ SwedeKeepsDogs
    /\ DaneDrinksTea
    /\ GreenLeftOfWhite
    /\ GreenOwnerDrinksCoffee
    /\ SmokesPallmallRearsBirds
    /\ YellowOwnerSmokesDunhill
    /\ CenterDrinksMylk
    /\ NorwegianFirstHouse
    /\ BlendSmokerLivesNextToCatOwner
    /\ HorseKeeperLivesNextToDunhillSmoker
    /\ BluemasterSmokerDrinksBeer
    /\ GermanSmokesPrince
    /\ NorwegianLivesNextToBlueHouse
    /\ BlendSmokerHasWaterDrinkingNeighbor

FindSolution == ~Solution

\* To find the solution with the `^Apalache^' model-checker, run:
\* `^apalache-mc check --init=Init --inv=FindSolution --length=0 --run-dir=./outout Einstein.tla^'
\* You will then find the solution in `^./output/violation.tla^'.

============================================================
