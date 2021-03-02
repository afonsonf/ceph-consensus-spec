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
const_161460287544057000 == 
{m1, m2, m3}
----

\* MV CONSTANT definitions Value_set
const_161460287544058000 == 
{v1}
----

=============================================================================
\* Modification History
\* Created Mon Mar 01 12:47:55 WET 2021 by afonsonf
