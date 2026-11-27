# Source, scope, and prior-work audit

**Jaime Nistal**, author · **Codex (OpenAI)**, AI co-author

## Exact Lean scope

The compared theorem `CazenaveRegistry.cazenave_conjecture_2_false` in the [pinned package at commit `2a5b608`](https://github.com/n1stal/conjecture-lab/tree/2a5b608164c4579d7816f2fc9e15332b0321527f/PalomarPackages/CazenaveC2) proves the full negation of Cazenave’s Conjecture 2 (#20829) via an explicit connected simple 11-vertex graph with $\lambda_2(A) > \mu_1(D - A) - 2$. No order-minimality is claimed. The separate infinite-family construction for every order at least 11 in [PROOF.md](PROOF.md) is not part of the compared Lean target.

Lean 4.35.0-rc2 (Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`) checks `CazenaveRegistry.cazenave_conjecture_2_false` using only `propext`, `Classical.choice`, and `Quot.sound`, with zero `sorry`s. Independent multi-kernel comparison is recorded in [PALOMAR-2026-11-27-000045](https://palomar-registry.org/entry?id=PALOMAR-2026-11-27-000045&version=1).

## Sources and prior work

- [Tristan Cazenave, *Lemmas and Conjectures in Spectral Graph Theory*](https://arxiv.org/abs/2611.03879v1) ([§7 HTML](https://arxiv.org/html/2611.03879v1#S7)), Section 7, Conjecture 2 (#20829); definitions and domain in Section 1. The preprint labels this conjecture unrefuted and gives a weaker known bound.

A bounded search found no prior refutation of Conjecture 2 (#20829). This is not a priority claim, journal peer review, or author endorsement.
