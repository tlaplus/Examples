---- MODULE APCat ----
(* Apalache type annotations for Cat.tla, applied via INSTANCE so the
   original spec remains free of tool-specific idiosyncrasies. *)

EXTENDS Naturals

CONSTANTS
  \* @type: Int;
  Number_Of_Boxes

VARIABLES
  \* @type: Int;
  cat_box,
  \* @type: Int;
  observed_box,
  \* @type: Str;
  direction

INSTANCE Cat

====
