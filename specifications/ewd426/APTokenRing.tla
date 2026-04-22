--------------------------- MODULE APTokenRing ---------------------------
(* Apalache type annotations for TokenRing.tla, applied via INSTANCE so the
   original spec remains free of tool-specific idiosyncrasies. *)

EXTENDS Naturals, FiniteSets

CONSTANTS
  \* @type: Int;
  N,
  \* @type: Int;
  M

VARIABLES
  \* @type: Int -> Int;
  c

\* @type: <<Int -> Int>>;
vars == << c >>

INSTANCE TokenRing

==========================================================================
