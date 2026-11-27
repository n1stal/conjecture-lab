# Conjecture Lab

Mathematical proofs, counterexamples, and partial results in combinatorics, graph theory, discrete geometry, and spectral graph theory. Includes Lean 4 formalizations and independent kernel-checked registrations.

Curated by [Jaime Nistal](https://github.com/n1stal) and Codex (OpenAI).

[Full catalogue](CONTENTS.md) · [Verification](docs/verification.md) · [Lean status](docs/lean-status.md) · [Palomar registrations](docs/palomar-registrations.md)

<!-- BEGIN GENERATED RESULTS -->

## Results

| Problem | Lean verification status | Problem | Lean verification status |
| :--- | :---: | :--- | :---: |
| **1.** [Turau’s amnesiac flooding conjecture ★](results/amnesiac-flooding/) | ✅ | **4.** [Berend–Ernst–Kontorovich–Kumar’s Conjecture 5.11 ★](results/beka-exceptional-breakpoints/) | ✅ |
| **2.** [Pinhe Chen’s δ-complement total-domination conjecture ★](results/chen-delta-complement-total-domination/) | ✅ | **4.** [Van Cott–Zhang’s coin-system conjectures 5.2(1) and (3) ★](results/van-cott-zhang-521/) | ✅ |
| **2.** [Jovanović–Sedlar–Škrekovski spectral-rank problem (Problem 21) ★](results/spectral-rank-problem-21/) | ✅ | **6.** [Cazenave’s second spectral graph conjecture ★](results/cazenave-second-spectral/) | ✅ |

Read down the left pair of columns, then down the right pair. Numbers are approximate editorial importance ranks based on mathematical significance, breadth, and consequences, not recency or Lean status. Equal numbers indicate no clear distinction in importance; tied ranks use competition ranking (1, 2, 2, 4).

- ✅ Fully Lean-verified.
- 🟢 Partially Lean-verified, with a computer-assisted proof.
- 🟡 Partially Lean-verified.
- ⬜ No Lean verification.
- ★ Registered in [Palomar](docs/palomar-registrations.md): exact statement, pinned source commit, and independent multi-kernel verification report recorded publicly. This is separate from journal peer review.

For Van Cott–Zhang’s coin-system conjectures, the prefix pattern is realized at every length $n \ge 11$, refuting the general $3r+1$ ban in part (1) for $r \ge 4$ and the two-family classification in part (3) at lengths $14, 17, 20, \dots$; a separate Palomar-registered proof establishes the ban at length $7$. Length $10$ and part (2) at length $9$ remain open. [Proofs and scope](results/van-cott-zhang-521/)

Turau’s conjecture, Problem 21, and the Van Cott–Zhang family proof (together with the inverse Z partial theorems and the Property P baseline) compile in the default `main` Lean build. Chen’s Conjecture 4, Berend–Ernst–Kontorovich–Kumar’s Conjecture 5.11, Cazenave’s Conjecture 2, the length-7 Van Cott–Zhang theorem, and the four-terminal distance-packing theorem are verified in standalone Lean 4 packages at their pinned commits and registered in Palomar. See [Lean status](docs/lean-status.md) for declarations, commits, and replay details.

## Partial results on open problems

This section is ordered by the significance of the partial contributions.

- [Gao–Ruan–Xie’s inverse Z-polynomial conjecture (rank at most four) ★](results/inverse-z-rank-four/). Positivity through the rank and log-concavity hold for every finite matroid of rank at most four. Ranks five and above remain open. [Lean status](docs/lean-status.md#inverse-z-rank-four)
- [Hak–Kozerenko’s distance-packing question for four prescribed terminals ★](results/four-terminal-packing/). For all positive integers k and p, the exact maximum pairwise distance sum on four terminals with distance-k packing number p is 6k + 4(k + 1)(p − 1), with weighted generalization kM + (k + 1)(p − 1)C (the unweighted k = 1 case follows from Chung 1988). Five or more terminals and the disjoint-separator branch remain open. [Lean status](docs/lean-status.md#four-terminal-packing)
- [Gao–Ruan–Xie’s inverse Z-polynomial conjecture (line-preserving projective restrictions)](results/inverse-z-projective/). Strict log-concavity holds in every rank for finite projective geometries restricted to subsets retaining at least two points on every line (overlapping projective and deletion prior work is credited in the audit). The unrestricted conjecture remains open. [Lean status](docs/lean-status.md#inverse-z-projective)

<!-- END GENERATED RESULTS -->

## Current research

Open preflights, exploratory proof packages, and earlier snapshots are indexed on [research branches](docs/research-branches.md), and active registry intake is tracked in the [Palomar filing queue](docs/palomar-queue.md). Each result page states the exact scope of the claim, its Lean verification, and its prior-work audit. All results are externally unrefereed.

## Layout

- `results/`: individual results, written proofs, and prior-work audits.
- `Proofs/`, `InverseZProofs/`, `InverseZProjective/`, `SpectralRank/`, `Palomar/`: Lean 4 formalizations and pinned dependencies.
- `docs/`: verification instructions, Lean status, Palomar registrations, and research policy.
- `scripts/`: repository-wide publication gate and index sync tools.

## How to cite

GitHub's **Cite this repository** control reads [`CITATION.cff`](CITATION.cff).
The repository-level authors are Jaime Nistal and Codex (OpenAI), in that order.

Suggested BibTeX for the repository:

```bibtex
@misc{nistal2026conjecturelab,
  author       = {Jaime Nistal and {Codex (OpenAI)}},
  title        = {Conjecture Lab},
  year         = {2026},
  howpublished = {GitHub repository},
  url          = {https://github.com/n1stal/conjecture-lab},
  note         = {Unrefereed mathematical notes and Lean 4 formalizations}
}
```

For an individual result, cite its author, result title, directory, and commit or Palomar registration.
Cite the original conjecture's publication separately (see [the catalogue](CONTENTS.md#primary-sources)).
These notes have no DOI or peer-reviewed publication. See also [provenance and citation](docs/provenance.md) and [prior-work policy](docs/research-process.md).

## Verification

The [verification guide](docs/verification.md) gives commands, toolchain pins, and the scope of each Lean and kernel check.

## Precise scope

See [the scope notes](CONTENTS.md#precise-scope) and each result's proof and audit for hypotheses and limitations.

## Primary sources

Sources are linked in the [catalogue](CONTENTS.md#primary-sources) and individual result audits.
