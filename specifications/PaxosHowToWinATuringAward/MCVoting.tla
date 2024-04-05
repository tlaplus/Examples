---- MODULE MCVoting ----
EXTENDS Voting, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a1, a2, a3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2
----

\* MV CONSTANT definitions Acceptor
const_156180051387243000 == 
{a1, a2, a3}
----

\* MV CONSTANT definitions Value
const_156180051387244000 == 
{v1, v2}
----

\* CONSTANT definitions @modelParameterConstants:2Quorum
const_156180051387245000 == 
{{a1, a2}, {a1, a3}, {a2, a3}}
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_156180051387246000 ==
0..2
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_156180051387248000 ==
C!Spec
----
=============================================================================
\* Modification History
\* Created Sat Jun 29 02:28:33 PDT 2019 by lamport
