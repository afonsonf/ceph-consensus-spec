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
const_161894924371742000 == 
{m1, m2, m3}
----

\* MV CONSTANT definitions Value_set
const_161894924371743000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_161894924371744000 == 
Permutations(const_161894924371742000) \union Permutations(const_161894924371743000)
----

=============================================================================
\* Modification History
\* Created Tue Apr 20 21:07:23 WEST 2021 by afonsonf
