---- MODULE MC ----
EXTENDS paxos, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
m1, m2, m3, m4
----

\* MV CONSTANT definitions Value_set
const_1615734982193363000 == 
{v1}
----

\* MV CONSTANT definitions Monitors
const_1615734982193364000 == 
{m1, m2, m3, m4}
----

\* SYMMETRY definition
symm_1615734982193365000 == 
Permutations(const_1615734982193364000)
----

=============================================================================
\* Modification History
\* Created Sun Mar 14 15:16:22 WET 2021 by afonsonf
