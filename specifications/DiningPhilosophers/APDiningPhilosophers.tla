---- MODULE APDiningPhilosophers ----
(* Apalache type annotations for DiningPhilosophers.tla, applied via
   INSTANCE so the original spec remains free of tool-specific
   idiosyncrasies. *)

EXTENDS Integers, TLC

CONSTANTS
  \* @type: Int;
  NP

VARIABLES
  \* @type: Int -> { holder: Int, clean: Bool };
  forks,
  \* @type: Int -> Str;
  pc,
  \* @type: Int -> Bool;
  hungry

INSTANCE DiningPhilosophers

====
