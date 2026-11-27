# Sharp distance packing for four prescribed terminals

**Jaime Nistal**, author · **Codex (OpenAI)**, AI co-author

Fix positive integers $k$ and $p$. Among finite simple connected graphs whose distance-$k$ packing number is $p$ (meaning the largest vertex subset at pairwise distance strictly greater than $k$ has size $p$), the maximum sum of the six pairwise shortest distances on four distinct vertices is

$$6k + 4(k + 1)(p - 1).$$

More generally, for nonnegative integer terminal weights, letting $M$ be the sum of weight products over the six pairs and $C$ the largest such sum crossing any bipartition of the four terminals, the exact maximum weighted distance sum is

$$kM + (k + 1)(p - 1)C.$$

Both theorems prove the universal upper bound and construct an attaining connected graph with exact packing number $p$. This settles the four-terminal packing branch of [Hak–Kozerenko, *Triameter, distance packings, and vertex connectivity*, §7, Question 3](https://arxiv.org/html/2611.17259v1#S7). Five or more terminals and the separate disjoint-separator branch remain open. The unweighted $k = 1$ special case follows from [Chung (1988)](https://doi.org/10.1002/jgt.3190120213) and is excluded from novelty claims.

## Files and verification

- [Written proof](EXACT-FOUR-PROOF.md)
- [Source, scope, and prior-work audit](audit.md)
- [Pinned Lean 4 package (`a82e9bf`)](https://github.com/n1stal/conjecture-lab/tree/a82e9bfeaf6622cf3cfcbaffe29c8cdfda3ee3f7/PalomarPackages/FourTerminalPacking) · [Lean solution (`Solution.lean`)](https://github.com/n1stal/conjecture-lab/blob/a82e9bfeaf6622cf3cfcbaffe29c8cdfda3ee3f7/PalomarPackages/FourTerminalPacking/Palomar/FourTerminalPacking/Solution.lean)
- [Palomar registration (`PALOMAR-2026-11-27-000051`)](https://palomar-registry.org/entry?id=PALOMAR-2026-11-27-000051&version=1) · [Lean status](../../docs/lean-status.md#four-terminal-packing) · [Verification guide](../../docs/verification.md)

The compared Lean declarations are `TriameterQ3Attainment.four_terminal_unweighted_exact` and `TriameterQ3Attainment.weighted_four_terminal_exact`, verified on Lean 4.35.0-rc2 (bundled Std only, no Mathlib dependency) with axioms `propext`, `Classical.choice`, and `Quot.sound`. Externally unrefereed.
