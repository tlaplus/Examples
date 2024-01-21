------------------- MODULE Einstein ------------------------

(*********************************************************************)
(* Literature/Source:                                                *)
(*   https://udel.edu/~os/riddle.html                                *)
(*                                                                   *)
(* Situation:                                                        *)
(* - There are 5 houses in five different colors.                    *)
(* - In each house lives a person with a different nationality.      *)
(* - These five owners drink a certain type of beverage, smoke a     *)
(*   certain brand of cigar and keep a certain pet.                  *)
(* - No owners have the same pet, smoke the same brand of cigar, or  *)
(*   drink the same beverage.                                        *)
(*                                                                   *)
(* Rules:                                                            *)
(*  1 the Brit lives in the red house                                *)
(*  2 the Swede keeps dogs as pets                                   *)
(*  3 the Dane drinks tea                                            *)
(*  4 the green house is on the left of the white house              *)
(*  5 the green house's owner drinks coffee                          *)
(*  6 the person who smokes Pall Mall rears birds                    *)
(*  7 the owner of the yellow house smokes Dunhill                   *)
(*  8 the man living in the center house drinks mylk                 *)
(*  9 the Norwegian lives in the first house                         *)
(* 10 the man who smokes blends lives next to the one who keeps cats *)
(* 11 the man who keeps horses lives next to man who smokes Dunhill  *)
(* 12 the owner who smokes BlueMaster drinks beer                    *)
(* 13 the German smokes Prince                                       *)
(* 14 the Norwegian lives next to the blue house                     *)
(* 15 the man who smokes blend has a neighbor who drinks water       *)
(*                                                                   *)
(* Question:                                                         *)
(*  Who owns the fish?                                               *)
(*********************************************************************)

EXTENDS Naturals, FiniteSets

House == 1..5

\* Note that TLC!Permutations has a Java module override and, thus,
\* would be evaluated faster.  However, TLC!Permutations equals a
\* set of records whereas Permutation below equals a set of tuples/
\* sequences.  Also, Permutation expects Cardinality(S) = 5.
Permutation(S) == 
    { p \in [ House -> S ] :
        /\ p[2] \in S \ {p[1]}
        /\ p[3] \in S \ {p[1], p[2]}
        /\ p[4] \in S \ {p[1], p[2], p[3]}
        /\ p[5] \in S \ {p[1], p[2], p[3], p[4]} }
                
\* In most specs, the following parameterization would be defined as
\* constants.  Given that Einstein's riddle has only this
\* parameterization, the constants are replaced with constant-level
\* operators.  As a side-effect, TLC evaluates them eagerly at startup, 
\* and Apalache successfully determines their types.
NATIONALITIES == Permutation({ "brit_OF_NATIONALITY", "swede_OF_NATIONALITY", "dane_OF_NATIONALITY", "norwegian_OF_NATIONALITY", "german_OF_NATIONALITY" })
DRINKS == Permutation({ "beer_OF_DRINK", "coffee_OF_DRINK", "mylk_OF_DRINK", "tea_OF_DRINK", "water_OF_DRINK" })
COLORS == Permutation({ "red_OF_COLOR", "white_OF_COLOR", "blue_OF_COLOR", "green_OF_COLOR", "yellow_OF_COLOR" })
PETS == Permutation({ "bird_OF_PET", "cat_OF_PET", "dog_OF_PET", "fish_OF_PET", "horse_OF_PET" })
CIGARS == Permutation({ "blend_OF_CIGAR", "bm_OF_CIGAR", "dh_OF_CIGAR", "pm_OF_CIGAR", "prince_OF_CIGAR" })

VARIABLES
    \* @type: Int -> NATIONALITY;
    nationality,    \* tuple of nationalities
    \* @type: Int -> COLOR;
    colors,         \* tuple of house colors
    \* @type: Int -> PET;
    pets,           \* tuple of pets
    \* @type: Int -> CIGAR;
    cigars,         \* tuple of cigars
    \* @type: Int -> DRINK;
    drinks          \* tuple of drinks

------------------------------------------------------------

(*********)
(* Rules *)
(*********)

BritLivesInTheRedHouse == \E i \in 2..5 : nationality[i] = "brit_OF_NATIONALITY" /\ colors[i] = "red_OF_COLOR"

SwedeKeepsDogs == \E i \in 2..5 : nationality[i] = "swede_OF_NATIONALITY" /\ pets[i] = "dog_OF_PET"

DaneDrinksTea == \E i \in 2..5 : nationality[i] = "dane_OF_NATIONALITY" /\ drinks[i] = "tea_OF_DRINK"

GreenLeftOfWhite == \E i \in 1..4 : colors[i] = "green_OF_COLOR" /\ colors[i + 1] = "white_OF_COLOR"

GreenOwnerDrinksCoffee == \E i \in 1..5 \ {3} : colors[i] = "green_OF_COLOR" /\ drinks[i] = "coffee_OF_DRINK"

SmokesPallmallRearsBirds == \E i \in 1..5 : cigars[i] = "pm_OF_CIGAR" /\ pets[i] = "bird_OF_PET"

YellowOwnerSmokesDunhill == \E i \in 1..5 : colors[i] = "yellow_OF_COLOR" /\ cigars[i] = "dh_OF_CIGAR"

CenterDrinksMylk == drinks[3] = "mylk_OF_DRINK"

NorwegianFirstHouse == nationality[1] = "norwegian_OF_NATIONALITY"

BlendSmokerLivesNextToCatOwner ==
    \E i \in 1..4 :
        \/ cigars[i] = "blend_OF_CIGAR" /\ pets[i + 1] = "cat_OF_PET"
        \/ pets[i] = "cat_OF_PET" /\ cigars[i + 1] = "blend_OF_CIGAR"

HorseKeeperLivesNextToDunhillSmoker ==
    \E i \in 1..4 :
        \/ cigars[i] = "dh_OF_CIGAR" /\ pets[i + 1] = "horse_OF_PET"
        \/ pets[i] = "horse_OF_PET" /\ cigars[i + 1] = "dh_OF_CIGAR"

BluemasterSmokerDrinksBeer == \E i \in 1..5 : cigars[i] = "bm_OF_CIGAR" /\ drinks[i] = "beer_OF_DRINK"

GermanSmokesPrince == \E i \in 2..5 : nationality[i] = "german_OF_NATIONALITY" /\ cigars[i] = "prince_OF_CIGAR"

NorwegianLivesNextToBlueHouse == colors[2] = "blue_OF_COLOR" \* since the norwegian_OF_NATIONALITY lives in the first house

BlendSmokerHasWaterDrinkingNeighbor ==
    \E i \in 1..4 :
        \/ cigars[i] = "blend_OF_CIGAR" /\ drinks[i + 1] = "water_OF_DRINK"
        \/ drinks[i] = "water_OF_DRINK" /\ cigars[i + 1] = "blend_OF_CIGAR"

------------------------------------------------------------

(************)
(* Solution *)
(************)

Init ==
    /\ drinks \in { p \in DRINKS : p[3] = "mylk_OF_DRINK" }
    /\ nationality \in { p \in NATIONALITIES : p[1] = "norwegian_OF_NATIONALITY" }
    /\ colors \in { p \in COLORS : p[2] = "blue_OF_COLOR" }
    /\ pets \in PETS
    /\ cigars \in CIGARS

Next ==
    UNCHANGED <<nationality, colors, cigars, pets, drinks>>

Spec == Init /\ [][Next]_<<nationality, colors, cigars, pets, drinks>>

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
\* apalache-mc check --init=Init --inv=FindSolution --length=0 Einstein.tla
\* Then look for the file violation.tla in `^Apalache^' output directory.

============================================================
