----------------------------- MODULE TLCSailfish1 -----------------------------

(**************************************************************************************)
(* In this configuartion, we have 3 nodes among which one is Byzantine. Quorums       *)
(* are chosen such that every two quorums have a correct node in common, and each     *)
(* blocking set intersects all quorums and contains a correct node. This allows to    *)
(* exercise the protocol with some Byzantine behavior while limiting state-space      *)
(* explosion.                                                                         *)
(**************************************************************************************)

EXTENDS Integers, FiniteSets

VARIABLES vs, es, round, log

CONSTANTS
    n1,n2,n3

N == {n1,n2,n3}
F == {n1}
R == 1..5
IsQuorum(Q) == Q \in {{n1,n3},{n2,n3},{n1,n2,n3}}
IsBlocking(B) == B \in {{n3},{n1,n3},{n2,n3},{n1,n2,n3}}
LeaderSchedule == <<n1,n2,n3>>
Leader(r) == LeaderSchedule[((r-1) % Cardinality(N))+1]
GST == 3

INSTANCE Sailfish

(**************************************************************************************)
(* Next we define a constraint to stop the model-checker.                             *)
(**************************************************************************************)
StateConstraint == \A n \in N \ F : round[n] \in 0..Max(R)

Done == \A n \in N \ F : round[n] = Max(R)
Terminate == Done /\ UNCHANGED <<vs, es, round, log>>
TerminatingSpec == Init /\ [][Next \/ Terminate]_<<vs, es, round, log>>

(**************************************************************************************)
(* Finally, we give some properties we expect to be violated (useful to get the       *)
(* model-checker to print interesting executions).                                    *)
(**************************************************************************************)

Falsy1 == \neg (
    \A n \in N \ F : round[n] = Max(R)
)

Falsy2 == \neg (
    \E n \in N \ F : Len(log[n]) > 1
)

\* can be used to stop the model-checker when the leader vertex of round 2 is committed
Falsy3 == \neg (
    \E n \in N \ F : \E i \in DOMAIN log[n] : log[n][i] = <<n2,2>>
)

===========================================================================
