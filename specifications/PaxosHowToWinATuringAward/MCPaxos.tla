---- MODULE MCPaxos ----
EXTENDS Paxos, TLC

CONSTANT MaxBallot

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a1, a2, a3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2
----

\* MV CONSTANT definitions Acceptor
const_1560336937634605000 == 
{a1, a2, a3}
----

\* MV CONSTANT definitions Value
const_1560336937634606000 == 
{v1, v2}
----

\* CONSTANT definitions @modelParameterConstants:1Quorum
const_1560336937634607000 == 
{{a1, a2}, {a1, a3}, {a2, a3}}
----

\* CONSTANT definition @modelParameterDefinitions:1
def_ov_1560336937634609000 ==
0..MaxBallot
----
\* CONSTANT definition @modelParameterDefinitions:2
def_ov_1560336937634610000 ==
0..MaxBallot
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1560336937635612000 ==
V!Spec
----
=============================================================================
\* Modification History
\* Created Wed Jun 12 03:55:37 PDT 2019 by lamport
