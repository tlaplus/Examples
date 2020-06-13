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
          z  \* z is the variable that is only going to be present in spec A.
varsA == <<x, z>>

InitA ==
  /\ x = 0
  /\ z = TRUE
  
NextA == 
  /\ x < 6
  /\ x' = x + 1
  /\ z' = ~ z

==================================

(* COMPONENT Spec B *)
VARIABLES x
varsB == <<x>>

\* ++Observation: This is most likely not the original Init predicate of a 
\*                standalone B component, unless perhaps we consider spec A 
\*                the environment of spec B.  In this particular example, 
\*                InitB is superfluouos anyway.  However, if one would want
\*                to prove something about spec B, we probably need an init
\*                predicate (=> Conjoining Specifications).
InitB == 
  /\ x \in Nat          \* Spec B may starts with x being any natural number,
                        \* which is where A left off.

NextB ==
  /\ x < 10
  /\ x' = x + 1

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
  <<x,restOfTheUniverse>>

(* Composition of A and B (A /\ B)        *)
(* Down here we know about the internals  *)
(* of spec A and B (whitebox component).  *)

INSTANCE A WITH z <- restOfTheUniverse

Spec == InitA /\ InitB /\ [][ IF ENABLED NextA THEN [NextA]_vars
                              ELSE [OpenNextB]_vars
                            ]_vars

Inv == x \in 0..10
THEOREM Spec => Inv

\* Not a theorem due to no fairness constraint.
Live ==
  <>[](x = 10)
=============================================================================
\* Modification History
\* Last modified Fri Jun 12 17:34:09 PDT 2020 by markus
\* Last modified Fri Jun 12 16:30:19 PDT 2020 by Markus Kuppe
\* Created Fri Jun 12 10:30:09 PDT 2020 by Leslie Lamport
