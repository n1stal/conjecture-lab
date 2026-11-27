# Exact weighted terminal distances for up to five packed vertices or four terminals

Jaime Nistal is the responsible author. Codex (OpenAI) is credited for material AI-assisted mathematical reasoning, certificate construction and Lean formalization.

Take any finite number of distinct specified terminals in a finite simple connected graph. A distance-k packing has mutual distances strictly greater than k. If the largest such packing has p vertices, the exact maximum weighted distance sum is **kM + (k+1)(p−1)C** in either of these complementary regimes:

- Any finite number of terminals, with 1≤p≤5.
- Exactly four terminals, with any positive p.

Here M sums the products of the nonnegative integer terminal weights over unordered terminal pairs; C is the largest product of the two side weights of a terminal bipartition. The theorem proves the universal upper bound and certifies attainment by an actual graph.

This answers the packing branch of [Hak–Kozerenko, *Triameter, distance packings, and vertex connectivity*, §7 Question 3](https://arxiv.org/html/2611.17259v1#S7) in the two stated regimes, not for unrestricted terminal count and packing number simultaneously, nor for the separate disjoint-separator part. Their Theorem 1.1 is credited and its numerical cap is derived inside the proof. [Chung's 1988 result](https://doi.org/10.1002/jgt.3190120213) already implies the unweighted k=1 special case for even terminal counts, and for odd terminal counts when p≤2 by rounding; these cases are not claimed as new. [Galli–Letchford](https://doi.org/10.1016/j.orl.2010.05.004), §2 and Table 1, supply the preexisting five-point bipartite hull characterization. This project verifies a standalone exact integer elimination certificate for that characterization, without assuming it.

[EXACT-PROOF.md](EXACT-PROOF.md) gives the mathematical proof. The formal proof compresses weights onto positively separated terminals without decreasing the clipped distance objective, proves every five-point graph facet, and checks a finite Fourier–Motzkin projection certificate. Back-substitution scales the current integer values together and inserts a maximal lower numerator, producing exact integer cut masses with a common positive denominator. Actual shortest-walk witnesses and attained packing numbers are part of the graph model. An independent trunk-and-arms graph construction attains the bound.

The Challenge names a witnessed maximum cut value C rather than assuming one as a premise. The independent Solution and comparator cover both declarations:

- TriameterQ3Public.weighted_extremum_up_to_five
- TriameterQ3Public.weighted_extremum_four_terminals_all_p

Both use the exact Lean 4.35.0-rc2 toolchain and bundled Std only. The two files do not import each other. The intentional Challenge holes are not dependencies of Solution.
