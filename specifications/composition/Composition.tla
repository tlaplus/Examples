---------------------------- MODULE Composition ----------------------------
(**************************************************************************)
(* Background reading: Conjoining Specifications by Abadi and Lamport     *)
(* https://lamport.azurewebsites.net/pubs/abadi-conjoining.pdf            *)
(*                                                                        *)
(* Spec A and B are two components that together are composed into a      *)
(* larger system.  It's toy example in the sense that minimize            *)
(* interaction of A and B to behaviors where first A takes its steps      *)
(* followed by B.  Variable y in A and B represents the control wire      *)
(* that A and B use to synchronize.                                       *)
(* Variable z has been added to make the example more interesting--it     *)
(* only appears in spec A but *not* B.                                    *)
(*                                                                        *)
(**************************************************************************)
EXTENDS Naturals, Sequences

(* COMPONENT Spec A *)
------------ MODULE A ------------
VARIABLES x, \* Abstract/very high-level representation of the overall computation.
             \* Think of it as some computation going on.  At a certain state
             \* of the computation, the composed system transitions into the
             \* next phase.
          y, \* Represents the phase that the composed system is in.
             \* This toy example has three phases: <<"A", "B", "C">>.
          z  \* z is the variable that is only going to be present in spec A.
varsA == <<x, y, z>>

InitA ==
  /\ x = 0
  /\ y = "A"
  /\ z = TRUE
  
NextA == 
  /\ y = "A"
  /\ x' = x + 1
  /\ IF x' = 5 
     THEN y' = "B"
     ELSE UNCHANGED y
  /\ z' = ~ z

==================================

(* COMPONENT Spec B *)
VARIABLES x,
          y
varsB == <<x, y>>

\* ++Observation: This is most likely not the original Init predicate of a 
\*                standalone B component, unless perhaps we consider spec A 
\*                the environment of spec B.  In this particular example, 
\*                InitB is superfluouos anyway.  However, if one would want
\*                to prove something about spec B, we probably need an init
\*                predicate (=> Conjoining Specifications).
InitB == 
  /\ x \in Nat          \* Spec B may starts with x being any natural number,
                        \* which is where A left off.
  /\ y \in {"A", "B"}   \* Phase A or B, otherwise InitA /\ InitB in Spec 
                        \* below will equal FALSE.

NextB ==
  /\ y = "B"
  /\ x' = x + 1
  /\ IF x' = 10    \* (Make sure values is greater than in spec A)
     THEN y' = "C" \* Phase C of the composed system (or ultimate termination).
     ELSE UNCHANGED y

-----------------------------------------------------------------------------

(* This *extends* component spec B to defines what happens to the variables
   in spec A, which are not defined in B, when B takes a step. *) 
VARIABLES restOfTheUniverse

\* Note that TLC doesn't complain about restOfTheUniverse
\* not appearing in InitB.
OpenNextB ==
  /\ NextB
  /\ UNCHANGED <<restOfTheUniverse>>

vars ==
  <<x,y,restOfTheUniverse>>

(* Composition of A and B (A /\ B)        *)
(* Down here we know about the internals  *)
(* of spec A and B (whitebox component).  *)

INSTANCE A WITH z <- restOfTheUniverse

Spec == InitA /\ InitB /\ [][ \/ [NextA]_vars
                              \/ [OpenNextB]_vars
                            ]_vars

Inv == y \in {"A","B","C"}
THEOREM Spec => Inv

=============================================================================
\* Modification History
\* Last modified Fri Jun 12 16:30:33 PDT 2020 by markus
\* Last modified Fri Jun 12 16:30:19 PDT 2020 by Markus Kuppe
\* Created Fri Jun 12 10:30:09 PDT 2020 by Leslie Lamport
