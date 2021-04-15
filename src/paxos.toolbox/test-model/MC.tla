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
const_161849102795542000 == 
{m1, m2, m3}
----

\* MV CONSTANT definitions Value_set
const_161849102795543000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_161849102795544000 == 
Permutations(const_161849102795542000) \union Permutations(const_161849102795543000)
----

=============================================================================
\* Modification History
\* Created Thu Apr 15 13:50:27 WEST 2021 by afonsonf
