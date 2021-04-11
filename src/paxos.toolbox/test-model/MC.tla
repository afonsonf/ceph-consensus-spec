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
const_16181442516046000 == 
{v1, v2}
----

\* MV CONSTANT definitions Monitors
const_16181442516047000 == 
{m1, m2, m3}
----

\* SYMMETRY definition
symm_16181442516048000 == 
Permutations(const_16181442516046000) \union Permutations(const_16181442516047000)
----

=============================================================================
\* Modification History
\* Created Sun Apr 11 13:30:51 WEST 2021 by afonsonf
