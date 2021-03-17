---- MODULE MC ----
EXTENDS paxos, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
m1, m2, m3
----

\* MV CONSTANT definitions Value_set
const_1616001027183131000 == 
{v1, v2}
----

\* MV CONSTANT definitions Monitors
const_1616001027183132000 == 
{m1, m2, m3}
----

\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1616001027183134000 ==
Inv_diam(53)
----
=============================================================================
\* Modification History
\* Created Wed Mar 17 17:10:27 WET 2021 by afonsonf
