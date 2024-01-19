---- MODULE MC ----
EXTENDS Paxos, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a1, a2, a3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2
----

\* MV CONSTANT definitions Acceptor
const_1560353114150701000 == 
{a1, a2, a3}
----

\* MV CONSTANT definitions Value
const_1560353114150702000 == 
{v1, v2}
----

\* CONSTANT definitions @modelParameterConstants:1Quorum
const_1560353114150703000 == 
{{a1, a2}, {a1, a3}, {a2, a3}}
----

\* CONSTANT definition @modelParameterDefinitions:1
def_ov_1560353114150705000 ==
0..2
----
\* CONSTANT definition @modelParameterDefinitions:2
def_ov_1560353114150706000 ==
0..2
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1560353114151708000 ==
V!Spec
----
=============================================================================
\* Modification History
\* Created Wed Jun 12 08:25:14 PDT 2019 by lamport
