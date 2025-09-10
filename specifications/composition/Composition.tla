---------------------------- MODULE Composition ----------------------------
(**************************************************************************)
(* Background reading: Conjoining Specifications by Abadi and Lamport     *)
(* https://lamport.azurewebsites.net/pubs/abadi-conjoining.pdf            *)
(**************************************************************************)
EXTENDS Integers, Sequences

Nodes == 1..3 \* Fixed to 1..3 here but should be a constant.

(* COMPONENT Spec A (Computation) *)
------ MODULE A --------
VARIABLES x,      \* Private to this component.
          active  \* Shared with component spec B.
vars == <<x,active>>

Type ==
  /\ x \in 0..10
  /\ active \in [ Nodes -> BOOLEAN ]

Init ==
  /\ x = 0
  /\ active \in [ Nodes -> BOOLEAN ]

Next ==
  \* Not all nodes are inactive.
  /\ \E i \in DOMAIN active : active[i] = TRUE
  \* Mimic some computation.
  /\ x' \in 1..10
  \* Computation changed the activation of 0 to N nodes.
  /\ active' \in [ Nodes -> BOOLEAN ]

==================================

(* COMPONENT Spec B (Safra's termination detection) *)
------------ MODULE B ------------
VARIABLES active,    \* Shared with component A.
          inactive   \* Shared with component C.
vars == <<inactive, active>>

Type ==
  /\ inactive \subseteq Nodes
  /\ active \in [ Nodes -> BOOLEAN ]

Init ==
  /\ inactive = {}
  /\ active \in [ Nodes -> BOOLEAN ]
  
Next == 
  \* Since this high-level composition abstracts away communication,
  \* we could abstract termination detection into a single step: 
  \*   /\ \A i \in DOMAIN active : active[i] = FALSE 
  \*   /\ inactive' = Nodes
  \* However, we want to model the possible interleavings of the
  \* A and B spec.
  /\ \E i \in DOMAIN active: 
                    active[i] = FALSE /\ i \notin inactive
  /\ inactive' = inactive \cup { 
                 CHOOSE i \in DOMAIN active: 
                    active[i] = FALSE /\ i \notin inactive
                               }  
  /\ UNCHANGED active
  
==================================

(* COMPONENT Spec C (orderly/graceful shutdown) *)
------------ MODULE C ------------
VARIABLES inactive \* Shared with component spec B. 
vars == <<inactive>>

Type ==
  /\ inactive \subseteq Nodes

Init == 
  /\ inactive \subseteq Nodes

IOExit == TRUE \* Shutdown via sys.exit

Next ==
  /\ inactive = Nodes
  /\ UNCHANGED inactive
  /\ IOExit
==================================

-----------------------------------------------------------------------------

(* Component specification. *)
VARIABLES x, active, inactive
vars ==
  <<inactive, x, active>>

A == INSTANCE A
B == INSTANCE B
C == INSTANCE C

TypeOK ==
  /\ A!Type
  /\ B!Type
  /\ C!Type

Init == 
  /\ A!Init
  /\ B!Init
  /\ C!Init

\* PlusPy will most certainly not be able to evaluate this 
\* Next formula. Might have to introduce an auxiliary variable
\* that represents the phase/stage of composed system.
Next ==
  \/ /\ ENABLED A!Next
     /\ [A!Next]_vars
     /\ UNCHANGED <<inactive>>
  \/ /\ ENABLED B!Next
     /\ [B!Next]_vars
     /\ UNCHANGED <<x>>
  \/ /\ [C!Next]_vars
     /\ UNCHANGED <<x, active>>
     
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

THEOREM Spec => []TypeOK

(* The system eventually converges to shutdown. This, however, does 
   *not* hold because component spec A could keep computing forever. *)
AlwaysShutdown ==
  <>[][C!Next]_vars

(* Unless all nodes are inactive at startup, some computation will occur. *)
ComputationIfSomeActive == 
  [n \in Nodes |-> FALSE] # active => <>[](x \in 1..10)
THEOREM Spec => ComputationIfSomeActive

(* Iff - from some point onward - all nodes will become
   inactive, the composed system will eventually shutdown. *)
ShutdownIfNoComputation ==
  <>[][~ A!Next]_vars => <>[][C!Next]_vars
THEOREM Spec => ShutdownIfNoComputation

=============================================================================
\* Modification History
\* Last modified Mon Jun 15 17:37:21 PDT 2020 by markus
\* Last modified Fri Jun 12 16:30:19 PDT 2020 by Markus Kuppe
\* Created Fri Jun 12 10:30:09 PDT 2020 by Leslie Lamport
