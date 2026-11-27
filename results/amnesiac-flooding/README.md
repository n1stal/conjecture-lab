# A counterexample to Turau’s amnesiac flooding conjecture

**Jaime Nistal**, author · **Codex (OpenAI)**, AI co-author

A connected, non-bipartite graph on 24 vertices floods in three rounds from four simultaneous sources. Its radius is 10, so the left side of [Turau’s conjectured inequality, arXiv:2002.10752v4 §8](https://arxiv.org/html/2002.10752v4#S8) is at most \(4\cdot3=12\), while the right side is \(10+4-1=13\). **\(12<13\)** is the counterexample.

## The graph

Split a 20-vertex path into four blocks of five. Add one vertex per block, adjacent to that block's middle three path vertices. Start at the four block centers. The first three rounds carry 12, 24, and 26 directed transmissions; the fourth is empty, so it is not counted. Repeating the construction gives a counterexample for every number of sources \(k\ge4\).

The result refutes the stated conjecture for the original synchronous protocol. It does **not** refute Turau’s weaker proved bound in Theorem 4 or establish the optimal flooding time of every graph in the family.

## Proof and verification

- [The exact 24-vertex Lean witness](../../Proofs/Amnesiac.lean): Flooding.turau_false and Flooding.round_counts.
- [The Lean family proof](../../Proofs/AmnesiacFamily.lean): FloodFamily.refutes_turau_for_each.
- [Proof notes and prior-work audit](audit.md), including the radius argument, the round convention, and related distributed-computing literature.
- [Passing hosted CI receipt](https://github.com/n1stal/conjecture-lab/actions/runs/45875325915): Publication gate #9, 26 November 2026, for the [proof commit a282890](https://github.com/n1stal/conjecture-lab/commit/a282890470a9900a0eb3822227b7c49d31a42d45). This is a historical receipt for the Turau proof, not a CI claim about later repository changes. [Reproduce the Lean check locally](../../docs/verification.md).

Lean verification is not external mathematical or journal review. The prior-work search is bounded; no priority claim or endorsement by the original author is made.

[Standalone Palomar statement package](../../Palomar/Turau/README.md) and local verification instructions.

[Written proof](PROOF.md) · [Palomar registration](https://palomar-registry.org/entry?id=PALOMAR-2026-11-26-000065&version=1)
