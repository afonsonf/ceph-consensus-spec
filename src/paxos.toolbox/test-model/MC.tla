---- MODULE MC ----
EXTENDS paxos, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
m1, m2, m3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2
----

\* MV CONSTANT definitions Monitors
const_161850101388650000 == 
{m1, m2, m3}
----

\* MV CONSTANT definitions Value_set
const_161850101388651000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_161850101388652000 == 
Permutations(const_161850101388650000) \union Permutations(const_161850101388651000)
----

=============================================================================
\* Modification History
\* Created Thu Apr 15 16:36:53 WEST 2021 by afonsonf
