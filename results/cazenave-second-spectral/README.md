# Cazenave’s second spectral graph conjecture

**Jaime Nistal**, author · **Codex (OpenAI)**, AI co-author

Two copies of $K_4$ minus an edge, joined at degree-two tips by a path with three new internal vertices, form a connected simple 11-vertex graph satisfying

$$\lambda_2(A) > \frac{21}{8} \qquad \text{and} \qquad \mu_1(D - A) \le \frac{37}{8},$$

so $\lambda_2(A) > \mu_1(D - A) - 2$. This refutes [Tristan Cazenave’s Conjecture 2 (#20829), arXiv:2611.03879v1, §7](https://arxiv.org/html/2611.03879v1#S7).

## Files and verification

- [Written proof](PROOF.md) (including an infinite-order extension not in the compared Lean target)
- [Source, scope, and prior-work audit](audit.md)
- [Pinned Lean 4 package (`2a5b608`)](https://github.com/n1stal/conjecture-lab/tree/2a5b608164c4579d7816f2fc9e15332b0321527f/PalomarPackages/CazenaveC2) · [Lean solution (`Solution.lean`)](https://github.com/n1stal/conjecture-lab/blob/2a5b608164c4579d7816f2fc9e15332b0321527f/PalomarPackages/CazenaveC2/Palomar/CazenaveC2/Solution.lean)
- [Palomar registration (`PALOMAR-2026-11-27-000045`)](https://palomar-registry.org/entry?id=PALOMAR-2026-11-27-000045&version=1) · [Lean status](../../docs/lean-status.md#cazenave-second-spectral) · [Verification guide](../../docs/verification.md)

The compared Lean declaration is `CazenaveRegistry.cazenave_conjecture_2_false`, using native Mathlib graph matrices, exact real polynomial sign changes, and an exact rational sum-of-squares certificate (no floating-point eigenvalues). Verified on Lean 4.35.0-rc2 (Mathlib `0653561`) with axioms `propext`, `Classical.choice`, and `Quot.sound`. No order-minimality claim is made. Externally unrefereed.
