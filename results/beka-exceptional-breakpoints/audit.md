# Source, scope, and prior-work audit

**Jaime Nistal**, author · **Codex (OpenAI)**, AI co-author

## Exact Lean scope

The compared theorem `BerendBinomial.source_exceptional_reflect` in the [pinned package at commit `61547c5`](https://github.com/n1stal/conjecture-lab/tree/61547c5decdee20dd8b049fbc28c45b75caaacd6/PalomarPackages/BerendBinomial) proves that for all even $k$ with $2 \le k \le n - 1$ and every $p \in (0, 1)$, an exceptional interior basis transition at $p$ implies an exceptional interior basis transition at $1 - p$. It does not address rationality of breakpoints or lexicographic basis indexing.

Lean 4.35.0-rc2 (Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`) checks `BerendBinomial.source_exceptional_reflect` using only `propext`, `Classical.choice`, and `Quot.sound`, with zero `sorry`s. Independent multi-kernel comparison is recorded in [PALOMAR-2026-11-27-000041](https://palomar-registry.org/entry?id=PALOMAR-2026-11-27-000041&version=1).

## Sources and prior work

- [Daniel Berend, Philip A. Ernst, Aryeh Kontorovich, and Rishi Kumar, *Exact Expressions for the Maximal Probability that all k-wise Independent Bits are 1*](https://doi.org/10.1007/s10959-026-01487-4), Section 5.4, Conjecture 5.11; Section 3.2 (Theorem 3.3) for dual-feasible bases. The paper’s basis characterization is credited to its cited Boros–Prékopa work.

A bounded search found no prior proof of Conjecture 5.11. This is not a priority claim, journal peer review, or author endorsement.
