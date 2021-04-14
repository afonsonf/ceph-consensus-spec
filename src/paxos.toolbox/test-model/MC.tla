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
const_1618414109221203000 == 
{m1, m2, m3}
----

\* MV CONSTANT definitions Value_set
const_1618414109221204000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_1618414109221205000 == 
Permutations(const_1618414109221203000) \union Permutations(const_1618414109221204000)
----

=============================================================================
\* Modification History
\* Created Wed Apr 14 16:28:29 WEST 2021 by afonsonf
