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
const_162334693645957000 == 
{m1, m2, m3}
----

\* MV CONSTANT definitions Value_set
const_162334693646058000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_162334693646059000 == 
Permutations(const_162334693645957000) \union Permutations(const_162334693646058000)
----

=============================================================================
\* Modification History
\* Created Thu Jun 10 18:42:16 WEST 2021 by afonsonf
