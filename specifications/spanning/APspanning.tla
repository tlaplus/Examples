------------------------------ MODULE APspanning ------------------------------
(* Apalache type annotations for spanning.tla, applied via INSTANCE so the
   original spec remains free of tool-specific idiosyncrasies. *)

EXTENDS Integers

CONSTANTS
  \* @type: Set(PROC);
  Proc,
  \* @type: PROC;
  NoPrnt,
  \* @type: PROC;
  root,
  \* @type: Set(<<PROC, PROC>>);
  nbrs

VARIABLES
  \* @type: PROC -> PROC;
  prnt,
  \* @type: PROC -> Bool;
  rpt,
  \* @type: Set(<<PROC, PROC>>);
  msg

INSTANCE spanning

\* Concrete values for the constants used by APspanning.cfg.
ProcVal == { "p1_OF_PROC", "p2_OF_PROC", "p3_OF_PROC" }
NoPrntVal == "noprnt_OF_PROC"
rootVal == "p1_OF_PROC"
\* @type: Set(<<PROC, PROC>>);
nbrsVal == { <<"p1_OF_PROC", "p2_OF_PROC">>, <<"p2_OF_PROC", "p1_OF_PROC">>,
             <<"p2_OF_PROC", "p3_OF_PROC">>, <<"p3_OF_PROC", "p2_OF_PROC">> }

==============================================================================
