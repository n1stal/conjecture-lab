# Berend–Ernst–Kontorovich–Kumar’s Conjecture 5.11

**Jaime Nistal**, author · **Codex (OpenAI)**, AI co-author

In the binomial-moment linear program for the largest probability that all $k$-wise independent Bernoulli($p$) bits equal $1$, for every even $k$ with $2 \le k \le n - 1$, every interior exceptional basis transition at bias $p \in (0, 1)$ has a reflected exceptional transition at bias $1 - p$. An exceptional transition is one where the dual-feasible basis loses at least two indices.

This establishes [Berend–Ernst–Kontorovich–Kumar, Conjecture 5.11](https://doi.org/10.1007/s10959-026-01487-4) over its full stated range of $n$ and even $k$. It does not address the rationality of breakpoints or the lexicographic indexing of bases.

## Files and verification

- [Written proof and source correspondence](PROOF.md)
- [Source, scope, and prior-work audit](audit.md)
- [Pinned Lean 4 package (`61547c5`)](https://github.com/n1stal/conjecture-lab/tree/61547c5decdee20dd8b049fbc28c45b75caaacd6/PalomarPackages/BerendBinomial) · [Lean solution (`Solution.lean`)](https://github.com/n1stal/conjecture-lab/blob/61547c5decdee20dd8b049fbc28c45b75caaacd6/PalomarPackages/BerendBinomial/Palomar/BerendBinomial/Solution.lean)
- [Palomar registration (`PALOMAR-2026-11-27-000041`)](https://palomar-registry.org/entry?id=PALOMAR-2026-11-27-000041&version=1) · [Lean status](../../docs/lean-status.md#beka-exceptional-breakpoints) · [Verification guide](../../docs/verification.md)

The compared Lean declaration is `BerendBinomial.source_exceptional_reflect`, verified on Lean 4.35.0-rc2 (Mathlib `0653561`) with axioms `propext`, `Classical.choice`, and `Quot.sound`. Externally unrefereed.
