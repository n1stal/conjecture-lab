# Source, scope, and prior-work audit

**Jaime Nistal**, author · **Codex (OpenAI)**, AI co-author

## Exact Lean scope

The compared theorem `DeltaNordhaus.conjecture4` in the [pinned package at commit `519eaf6`](https://github.com/n1stal/conjecture-lab/tree/519eaf69d1aa38f53663759817c66aee8f105698/results/delta-complement-total-domination) proves Pinhe Chen’s Conjecture 4 for every finite undirected loopless graph whose graph and $\delta$-complement have no isolated vertices. No per-class nonisolation, connectedness, regularity, or order cutoff is assumed. The minimum in the definition of total domination is both achieved and certified to be no larger than the size of any total dominating set. The internal arbitrary-partition theorem is a proof ingredient, not a separate registry claim.

Lean 4.35.0-rc2 (Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`) checks `DeltaNordhaus.conjecture4` using only `propext`, `Classical.choice`, and `Quot.sound`, with zero `sorry`s. Independent multi-kernel comparison is recorded in [PALOMAR-2026-11-27-000025](https://palomar-registry.org/entry?id=PALOMAR-2026-11-27-000025&version=1).

## Sources and prior work

- [Pinhe Chen, *Refined Nordhaus–Gaddum-Type Bounds for Roman and Total Domination on δ-Complement Graphs*](https://doi.org/10.3390/math14111797), *Mathematics* 14(11), 1797 (2026), Section 6.2, Conjecture 4. Theorem 6 covers the special case where every induced degree-class pair is isolate-free, and Example 3 establishes sharpness of the bound.
- [E. J. Cockayne, R. M. Dawes, and S. T. Hedetniemi, *Total domination in graphs*](https://doi.org/10.1002/net.3230100304), *Networks* 10(3), 211–219 (1980). The classical ordinary-complement upper bound is reproved internally; no equality classification is claimed.

Targeted searches for Chen’s title, DOI, and conjecture statement located no prior full proof removing the per-class nonisolation condition. This is a bounded search, not a priority claim, external peer review, or author endorsement.
