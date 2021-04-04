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
const_161756307870972000 == 
{v1, v2}
----

\* MV CONSTANT definitions Monitors
const_161756307870973000 == 
{m1, m2, m3}
----

\* INVARIANT definition @modelCorrectnessInvariants:1
inv_161756307870975000 ==
Inv_diam(53)
----
=============================================================================
\* Modification History
\* Created Sun Apr 04 20:04:38 WEST 2021 by afonsonf
