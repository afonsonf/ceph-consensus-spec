---- MODULE MC ----
EXTENDS paxos, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
m1, m2, m3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1
----

\* MV CONSTANT definitions Monitors
const_1614960247456165000 == 
{m1, m2, m3}
----

\* MV CONSTANT definitions Value_set
const_1614960247456166000 == 
{v1}
----

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1614960247456167000 ==
Inv_diam(59) \/ number_refreshes # 1
----
=============================================================================
\* Modification History
\* Created Fri Mar 05 16:04:07 WET 2021 by afonsonf
