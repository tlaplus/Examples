------------------------------- MODULE APBarrier -------------------------------
(* Apalache type annotations for Barrier.tla, applied via INSTANCE so the
   original spec remains free of tool-specific idiosyncrasies. The locally
   redefined `vars` provides the missing annotation that disambiguates the
   1-tuple in `Barrier!vars`. *)

EXTENDS Integers

CONSTANTS
  \* @type: Int;
  N

VARIABLES
  \* @type: Int -> Str;
  pc

\* @type: <<Int -> Str>>;
vars == << pc >>

INSTANCE Barrier

================================================================================
