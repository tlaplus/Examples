-------------------------- MODULE APCigaretteSmokers --------------------------
(* Apalache type annotations for CigaretteSmokers.tla, applied via INSTANCE
   so the original spec remains free of tool-specific idiosyncrasies. *)

EXTENDS Integers, FiniteSets

CONSTANT
  \* @type: Set(INGREDIENT);
  Ingredients,
  \* @type: Set(Set(INGREDIENT));
  Offers

VARIABLE
  \* @type: INGREDIENT -> { smoking: Bool };
  smokers,
  \* @type: Set(INGREDIENT);
  dealer

INSTANCE CigaretteSmokers

\* Concrete model values for the uninterpreted INGREDIENT type. Used by
\* APCigaretteSmokers.cfg via the `Const <- OpName` syntax.
IngredientsVal == {"matches_OF_INGREDIENT", "paper_OF_INGREDIENT", "tobacco_OF_INGREDIENT"}
OffersVal == { IngredientsVal \ {i} : i \in IngredientsVal }

==============================================================================
