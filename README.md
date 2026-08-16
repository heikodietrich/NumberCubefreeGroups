This is just the pre-release GAP code accompanying the paper "The number of groups of cubefree order" by Heiko Dietrich and David Jefferies (arxiv link to follow).
Eventually this code will be distributed with a future release of the GAP package Cubefree https://gap-packages.github.io/cubefree/

The code provides the function NumberCubefreeGroup(n) that determines the number of isomorphism types of group of cubefree order n. It works faster for n odd for various reasons.

The code also provides functions NumberCubefreeSolvableGroups(n) and NumberCubefreeSupersolvableGroups(n) which only count solvable and supersolvable groups, respectively.

This implementation is built on the algorithm described in the above paper. Several optimisations have been introduced with the help of the LLM Claude Opus 5; the LLM has also streamlined and improved the final implementation that is provided here. The validity of the implementation has been thoroughly cross-checked, see Section 5.2.
