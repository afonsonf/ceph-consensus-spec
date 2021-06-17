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
const_162393434718242000 == 
{m1, m2, m3}
----

\* MV CONSTANT definitions Value_set
const_162393434718243000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_162393434718244000 == 
Permutations(const_162393434718242000) \union Permutations(const_162393434718243000)
----

\* VIEW definition @modelParameterView
view_162393434718245000 == 
view
----

=============================================================================
\* Modification History
\* Created Thu Jun 17 13:52:27 WEST 2021 by afonsonf
