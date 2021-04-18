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
const_161850589177195000 ==
{m1, m2, m3}
----

\* MV CONSTANT definitions Value_set
const_161850589177196000 ==
{v1, v2}
----

\* SYMMETRY definition
symm_161850589177197000 ==
Permutations(const_161850589177195000) \union Permutations(const_161850589177196000)
----

\* INVARIANT definition @modelCorrectnessInvariants:1
inv_161850589177199000 ==
Inv_diam(53)
----
=============================================================================
\* Modification History
\* Created Thu Apr 15 17:58:11 WEST 2021 by afonsonf
