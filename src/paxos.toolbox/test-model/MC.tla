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
const_1614962295605180000 == 
{m1, m2, m3}
----

\* MV CONSTANT definitions Value_set
const_1614962295605181000 == 
{v1}
----

=============================================================================
\* Modification History
\* Created Fri Mar 05 16:38:15 WET 2021 by afonsonf
