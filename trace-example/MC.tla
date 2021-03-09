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
const_161530561528321000 == 
{m1, m2, m3}
----

\* MV CONSTANT definitions Value_set
const_161530561528322000 == 
{v1}
----

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_161530561528423000 ==
Inv_diam(44) \/ number_refreshes<2
----
=============================================================================
\* Modification History
\* Created Tue Mar 09 16:00:15 WET 2021 by afonsonf
