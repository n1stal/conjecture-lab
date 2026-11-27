# Chen’s δ-complement total-domination conjecture

**Jaime Nistal**, author · **Codex (OpenAI)**, AI co-author

For every finite simple graph $G$ such that neither $G$ nor its $\delta$-complement $G_\delta$ has an isolated vertex, the sum of their total-domination numbers satisfies

$$\gamma_t(G) + \gamma_t(G_\delta) \le n + 2k,$$

where $n$ is the order of $G$ and $k$ is the number of distinct vertex degrees of $G$. This proves [Pinhe Chen’s Conjecture 4, *Mathematics* 14(11):1797 (2026), §6.2](https://doi.org/10.3390/math14111797), removing the per-degree-class nonisolation hypothesis of Chen’s Theorem 6.

## Files and verification

- [Written proof](PROOF.md)
- [Source, scope, and prior-work audit](audit.md)
- [Pinned Lean 4 package (`519eaf6`)](https://github.com/n1stal/conjecture-lab/tree/519eaf69d1aa38f53663759817c66aee8f105698/results/delta-complement-total-domination) · [Lean solution (`DeltaConjecture4.lean`)](https://github.com/n1stal/conjecture-lab/blob/519eaf69d1aa38f53663759817c66aee8f105698/results/delta-complement-total-domination/DeltaConjecture4.lean)
- [Palomar registration (`PALOMAR-2026-11-27-000025`)](https://palomar-registry.org/entry?id=PALOMAR-2026-11-27-000025&version=1) · [Lean status](../../docs/lean-status.md#chen-delta-complement-total-domination) · [Verification guide](../../docs/verification.md)

The compared Lean declaration is `DeltaNordhaus.conjecture4`, verified on Lean 4.35.0-rc2 (Mathlib `0653561`) with axioms `propext`, `Classical.choice`, and `Quot.sound`. The proof establishes a stronger partition bound internally and reproves the classical ordinary-complement bound of [Cockayne, Dawes, and Hedetniemi (1980)](https://doi.org/10.1002/net.3230100304); Chen’s Example 3 already gives sharpness. Externally unrefereed.
