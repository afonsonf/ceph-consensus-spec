---- MODULE MC ----
EXTENDS ceph, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
m1, m2, m3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2
----

\* MV CONSTANT definitions Monitors
const_16187828978286000 == 
{m1, m2, m3}
----

\* MV CONSTANT definitions Value_set
const_16187828978287000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_16187828978288000 == 
Permutations(const_16187828978286000) \union Permutations(const_16187828978287000)
----

=============================================================================
\* Modification History
\* Created Sun Apr 18 22:54:57 WEST 2021 by afonsonf
