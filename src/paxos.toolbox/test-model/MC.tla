---- MODULE MC ----
EXTENDS paxos, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
m1, m2, m3, m4, m5
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1
----

\* MV CONSTANT definitions Monitors
const_16146788319165000 == 
{m1, m2, m3, m4, m5}
----

\* MV CONSTANT definitions Value_set
const_16146788319166000 == 
{v1}
----

\* SYMMETRY definition
symm_16146788319167000 == 
Permutations(const_16146788319165000)
----

=============================================================================
\* Modification History
\* Created Tue Mar 02 09:53:51 WET 2021 by afonsonf
