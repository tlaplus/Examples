----------------------------- MODULE APDieHarder -----------------------------
(* Apalache type annotations for DieHarder.tla, applied via INSTANCE so the
   original spec remains free of tool-specific idiosyncrasies. *)

EXTENDS Naturals

CONSTANT
  \* @type: Set(JUG);
  Jug,
  \* @type: JUG -> Int;
  Capacity,
  \* @type: Int;
  Goal

VARIABLE
  \* @type: JUG -> Int;
  contents

INSTANCE DieHarder

\* Concrete values for the constants used by APDieHarder.cfg.
JugVal == { "small_OF_JUG", "big_OF_JUG" }
\* @type: JUG -> Int;
CapacityVal == [ j \in JugVal |-> IF j = "small_OF_JUG" THEN 3 ELSE 5 ]

==============================================================================
