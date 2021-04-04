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
const_161746067761338000 == 
{v1, v2}
----

\* MV CONSTANT definitions Monitors
const_161746067761339000 == 
{m1, m2, m3}
----

=============================================================================
\* Modification History
\* Created Sat Apr 03 15:37:57 WEST 2021 by afonsonf
