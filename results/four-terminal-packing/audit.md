# Source, scope, and prior-work audit

**Jaime Nistal**, author · **Codex (OpenAI)**, AI co-author

## Exact Lean scope

The compared theorems `TriameterQ3Attainment.four_terminal_unweighted_exact` and `TriameterQ3Attainment.weighted_four_terminal_exact` in the [pinned package at commit `a82e9bf`](https://github.com/n1stal/conjecture-lab/tree/a82e9bfeaf6622cf3cfcbaffe29c8cdfda3ee3f7/PalomarPackages/FourTerminalPacking) prove the exact four-terminal distance-packing extremum for all positive integers $k$ and $p$, for both unit weights and nonnegative integer terminal weights, including attainment by an explicit connected graph with exact distance-$k$ packing number $p$. This does not establish the finite extremum for five or more terminals, real weights, or the disjoint-separator branch of Question 3.

Lean 4.35.0-rc2 (bundled Lean/Std only) checks both declarations using only `propext`, `Classical.choice`, and `Quot.sound`, with zero `sorry`s. Independent multi-kernel comparison is recorded in [PALOMAR-2026-11-27-000051](https://palomar-registry.org/entry?id=PALOMAR-2026-11-27-000051&version=1).

## Sources and prior work

- [Artem Hak and Sergiy Kozerenko, *Triameter, distance packings, and vertex connectivity*](https://arxiv.org/html/2611.17259v1#S7) ([arXiv:2611.17259v1](https://arxiv.org/abs/2611.17259v1)), Theorem 1.1 and Section 7, Question 3. Theorem 1.1’s three-terminal numerical bound is credited and derived internally from shortest geodesics.
- [Fan R. K. Chung, *The average distance and the independence number*](https://doi.org/10.1002/jgt.3190120213), *Journal of Graph Theory* 12(2), 229–235 (1988). Replacing each terminal by a clique of true twins shows that Chung’s theorem already implies the unweighted $k = 1$ upper bound for any even terminal count, including four terminals; that special case is excluded from novelty claims.

No broader priority claim, external peer review, or author endorsement is made.
