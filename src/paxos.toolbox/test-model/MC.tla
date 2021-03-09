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
const_161530623056328000 == 
{m1, m2, m3}
----

\* MV CONSTANT definitions Value_set
const_161530623056329000 == 
{v1}
----

=============================================================================
\* Modification History
\* Created Tue Mar 09 16:10:30 WET 2021 by afonsonf
