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
const_161756550139779000 == 
{v1, v2}
----

\* MV CONSTANT definitions Monitors
const_161756550139780000 == 
{m1, m2, m3}
----

=============================================================================
\* Modification History
\* Created Sun Apr 04 20:45:01 WEST 2021 by afonsonf
