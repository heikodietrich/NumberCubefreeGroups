This is the pre-release GAP code accompanying the paper 

  "The number of groups of cubefree order"  (https://arxiv.org/abs/2608.18815)

by Heiko Dietrich and David Jefferies.

Eventually this code will be distributed with a future release of the GAP package Cubefree https://gap-packages.github.io/cubefree/

**Main file:** cubefree-enum.gap

Once loaded, the code provides the function `NumberCubefreeGroup(n)` that determines the number of isomorphism types of group of cubefree order n. It works faster for n odd for various reasons.

The code also provides functions `NumberCubefreeSolvableGroups(n)` and `NumberCubefreeSupersolvableGroups(n)` which only count solvable and supersolvable groups, respectively. The function `NumberCubefreeCGroups(n)` only counts the number of cubefree C-groups (groups all whose Sylow subgroups are cyclic), this is mainly for cross-checking against https://github.com/heikodietrich/cgroups

This implementation is built on the algorithm described in the above paper. Several optimisations have been introduced with the help of the LLM Claude Opus 5; the LLM has also streamlined and improved the final implementation that is provided here. The validity of the implementation has been thoroughly cross-checked, see Section 6.3.

**Test files:** cubefree-enum-test.gap and cf_db.g

Reading cube-enum-test.gap will load cf_db.g (which contains a list of cross checked pairs [n,gnu(n)], including for all cubefree n<10^6) and provide the function `cubefree_test_against_DB( bound )` that will test NumberCubefreeGroups for the first 'bound' entries in cf_db.g
