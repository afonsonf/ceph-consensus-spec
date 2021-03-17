---- MODULE MC ----
EXTENDS paxos, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
m1, m2, m3
----

\* MV CONSTANT definitions Value_set
const_1616001439707138000 == 
{v1}
----

\* MV CONSTANT definitions Monitors
const_1616001439707139000 == 
{m1, m2, m3}
----

=============================================================================
\* Modification History
\* Created Wed Mar 17 17:17:19 WET 2021 by afonsonf
