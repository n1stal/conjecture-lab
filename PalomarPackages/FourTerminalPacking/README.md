# Sharp distance packing for four prescribed terminals

Jaime Nistal is the responsible author. Codex (OpenAI) is credited for material AI-assisted proof development and formalization.

Fix positive integers k and p. Consider finite simple connected graphs where the largest set of vertices at pairwise distance strictly greater than k has p elements. Then the largest possible sum of the six pairwise shortest distances on four distinct vertices is

**6k + 4(k+1)(p−1).**

For nonnegative integer terminal weights, let M be the sum of products of weights over the six pairs, and C the largest such sum crossing any bipartition. The exact maximum weighted distance sum is **kM + (k+1)(p−1)C**. Both Lean theorems prove a universal upper bound and attainment by an explicit graph with exact packing number p.

This proves the four-terminal packing branch in [Hak–Kozerenko, *Triameter, distance packings, and vertex connectivity*, §7, Question 3](https://arxiv.org/html/2611.17259v1#S7). It does not prove the exact finite extremum for five or more terminals or the separate disjoint-separator branch. [Chung's 1988 theorem](https://doi.org/10.1002/jgt.3190120213) already implies the unweighted k=1 upper bound for any even terminal count by replacing each terminal with a clique of true twins; this includes four terminals. That case is not claimed as new. Hak and Kozerenko's Theorem 1.1 is credited and its numerical bound is derived within the Lean proof using geodesic arms.

[EXACT-FOUR-PROOF.md](EXACT-FOUR-PROOF.md) gives the full mathematical argument, including prior-work details. The native graph model uses symmetric, irreflexive adjacency, exact shortest unit-edge walks, and the actual maximum packing. The upper bound clips the six excess distances and dominates them by a mixture of cuts. For attainment, attach four arms to the ends of a path in a maximum-weight bipartition, with first-layer edges for odd k. Two end caps and consecutive interior blocks certify the packing upper bound; equally spaced vertices on a geodesic certify the lower bound.

The frozen Challenge contains the two exact statements and their definitions and imports only bundled Lean/Std. The independent Solution contains the complete proof, does not import Challenge, and uses only propext, Classical.choice and Quot.sound. Run the Solution with the pinned Lean 4.35.0-rc2 toolchain using lake build. This repository needs no Mathlib or external dependencies. The deliberately unproved Challenge declarations are not dependencies of the Solution.

Compared declarations:
- TriameterQ3Attainment.four_terminal_unweighted_exact
- TriameterQ3Attainment.weighted_four_terminal_exact
