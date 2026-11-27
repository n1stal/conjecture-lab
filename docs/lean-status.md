# Lean verification status

[Home](../README.md) · [Full catalogue](../CONTENTS.md) · [Verification](verification.md) · [Palomar registrations](palomar-registrations.md)

Pinned repository toolchain: `leanprover/lean4:v4.35.0-rc2`. Approved axioms across all verified declarations: `propext`, `Classical.choice`, `Quot.sound` (zero `sorry`s).

| Result | Section | Lean status | Build scope | Palomar |
| :--- | :--- | :---: | :--- | :--- |
| [Turau’s amnesiac flooding conjecture](#amnesiac-flooding) | Solved | ✅ | `main` default build | [PALOMAR-2026-11-26-000065](https://palomar-registry.org/entry?id=PALOMAR-2026-11-26-000065&version=1) |
| [Pinhe Chen’s δ-complement total-domination conjecture](#chen-delta-complement-total-domination) | Solved | ✅ | pinned `519eaf6` | [PALOMAR-2026-11-27-000025](https://palomar-registry.org/entry?id=PALOMAR-2026-11-27-000025&version=1) |
| [Jovanović–Sedlar–Škrekovski spectral-rank problem (Problem 21)](#spectral-rank-problem-21) | Solved | ✅ | `main` default build | [PALOMAR-2026-11-27-000004](https://palomar-registry.org/entry?id=PALOMAR-2026-11-27-000004&version=1) |
| [Berend–Ernst–Kontorovich–Kumar’s Conjecture 5.11](#beka-exceptional-breakpoints) | Solved | ✅ | pinned `61547c5` | [PALOMAR-2026-11-27-000041](https://palomar-registry.org/entry?id=PALOMAR-2026-11-27-000041&version=1) |
| [Van Cott–Zhang’s coin-system conjectures 5.2(1) and (3)](#van-cott-zhang-521) | Solved | ✅ | `main` default build | [PALOMAR-2026-11-27-000001](https://palomar-registry.org/entry?id=PALOMAR-2026-11-27-000001&version=1), [PALOMAR-2026-11-27-000034](https://palomar-registry.org/entry?id=PALOMAR-2026-11-27-000034&version=1) |
| [Cazenave’s second spectral graph conjecture](#cazenave-second-spectral) | Solved | ✅ | pinned `2a5b608` | [PALOMAR-2026-11-27-000045](https://palomar-registry.org/entry?id=PALOMAR-2026-11-27-000045&version=1) |
| [Gao–Ruan–Xie’s inverse Z-polynomial conjecture (rank at most four)](#inverse-z-rank-four) | Partial | ✅ | `main` default build | [PALOMAR-2026-11-26-000061](https://palomar-registry.org/entry?id=PALOMAR-2026-11-26-000061&version=1) |
| [Hak–Kozerenko’s distance-packing question for four prescribed terminals](#four-terminal-packing) | Partial | ✅ | pinned `a82e9bf` | [PALOMAR-2026-11-27-000051](https://palomar-registry.org/entry?id=PALOMAR-2026-11-27-000051&version=1) |
| [Gao–Ruan–Xie’s inverse Z-polynomial conjecture (line-preserving projective restrictions)](#inverse-z-projective) | Partial | ✅ | `main` default build | — |
| [Property P finite witness {1, 2}](#property-p-baseline) | Baseline | ✅ | `main` default build | — |

<a id="amnesiac-flooding"></a>

## A counterexample to Turau’s amnesiac flooding conjecture

- **Result page:** [Turau’s amnesiac flooding conjecture](../results/amnesiac-flooding/) · [Audit](../results/amnesiac-flooding/audit.md)
- **Lean status:** ✅ Complete
- **Build scope:** Compiled by `lake build --wfail` and axiom-checked by `python3 scripts/check_publication.py` on `main`.
- **Checked declarations:** `Flooding.turau_false`, `Flooding.round_counts`, `FloodFamily.refutes_turau_for_each`
- **Palomar registration:** [PALOMAR-2026-11-26-000065](https://palomar-registry.org/entry?id=PALOMAR-2026-11-26-000065&version=1) (commit `d77d114`)
- **Scope:** For each k ≥ 4, a connected non-bipartite graph on 6k vertices with radius floor(5k/2) floods in at most three rounds from k sources, violating Turau’s conjectured lower bound. Does not refute Turau’s weaker proved bound in Theorem 4.

<a id="chen-delta-complement-total-domination"></a>

## Chen’s total-domination conjecture for the delta complement

- **Result page:** [Pinhe Chen’s δ-complement total-domination conjecture](../results/chen-delta-complement-total-domination/) · [Audit](../results/chen-delta-complement-total-domination/audit.md)
- **Lean status:** ✅ Complete
- **Build scope:** Standalone Lean 4 package at pinned commit [`519eaf6`](https://github.com/n1stal/conjecture-lab/tree/519eaf69d1aa38f53663759817c66aee8f105698/results/delta-complement-total-domination) (`results/delta-complement-total-domination`).
- **Checked declarations:** `DeltaNordhaus.conjecture4`
- **Palomar registration:** [PALOMAR-2026-11-27-000025](https://palomar-registry.org/entry?id=PALOMAR-2026-11-27-000025&version=1) (commit `519eaf6`)
- **Scope:** Full Pinhe Chen Conjecture 4 for all finite undirected loopless graphs whose graph and δ-complement are isolate-free, removing the per-degree-class nonisolation condition of Chen’s Theorem 6. Sharpness is already established by Chen’s Example 3.

<a id="spectral-rank-problem-21"></a>

## Ordered spectral proximity forces adjacency rank at most five

- **Result page:** [Jovanović–Sedlar–Škrekovski spectral-rank problem (Problem 21)](../results/spectral-rank-problem-21/) · [Audit](../results/spectral-rank-problem-21/audit.md)
- **Lean status:** ✅ Complete
- **Build scope:** Compiled by `lake build --wfail` and axiom-checked by `python3 scripts/check_publication.py` on `main`.
- **Checked declarations:** `SpectralRank.problem_21`
- **Palomar registration:** [PALOMAR-2026-11-27-000004](https://palomar-registry.org/entry?id=PALOMAR-2026-11-27-000004&version=1) (commit `7846ef8`)
- **Scope:** For any simple graph on 3n vertices, n ≥ 3, squared distance of its ordered adjacency spectrum to (2n, 0, …, 0, −n, −n) strictly below 2/3 forces real adjacency rank at most five. Answers Problem 21, not Conjecture 20.

<a id="beka-exceptional-breakpoints"></a>

## Reflection of exceptional breakpoints for k-wise independent bits

- **Result page:** [Berend–Ernst–Kontorovich–Kumar’s Conjecture 5.11](../results/beka-exceptional-breakpoints/) · [Audit](../results/beka-exceptional-breakpoints/audit.md)
- **Lean status:** ✅ Complete
- **Build scope:** Standalone Lean 4 package at pinned commit [`61547c5`](https://github.com/n1stal/conjecture-lab/tree/61547c5decdee20dd8b049fbc28c45b75caaacd6/PalomarPackages/BerendBinomial) (`PalomarPackages/BerendBinomial`).
- **Checked declarations:** `BerendBinomial.source_exceptional_reflect`
- **Palomar registration:** [PALOMAR-2026-11-27-000041](https://palomar-registry.org/entry?id=PALOMAR-2026-11-27-000041&version=1) (commit `61547c5`)
- **Scope:** Establishes Conjecture 5.11 of Berend, Ernst, Kontorovich, and Kumar over its full stated range of n and even k with 2 ≤ k ≤ n − 1. Does not address rationality of breakpoints or lexicographic indexing of bases.

<a id="van-cott-zhang-521"></a>

## Counterexamples to Van Cott–Zhang Conjecture 5.2(1) and (3)

- **Result page:** [Van Cott–Zhang’s coin-system conjectures 5.2(1) and (3)](../results/van-cott-zhang-521/) · [Audit](../results/van-cott-zhang-521/audit.md)
- **Lean status:** ✅ Complete
- **Build scope:** Compiled by `lake build --wfail` and axiom-checked by `python3 scripts/check_publication.py` on `main`.
- **Checked declarations:** `CoinOrder.vanCottZhangConjecture521_false`, `CoinOrder.Family.every_length_ge_eleven`, `CoinOrder.Family.general_prohibition_fails`, `CoinOrder.Family.classification_fails`, `CoinOrder.Family.conjecture523_false`
- **Palomar registration:** [PALOMAR-2026-11-27-000001](https://palomar-registry.org/entry?id=PALOMAR-2026-11-27-000001&version=1) (commit `9f89113`) — length ≥ 11 family and counterexamples to 5.2(1) and (3); [PALOMAR-2026-11-27-000034](https://palomar-registry.org/entry?id=PALOMAR-2026-11-27-000034&version=1) (commit `65752dd`) — seven-denomination prohibition in 5.2(1) (CoinOrder.SevenRegistry.seven_denominations_no_pattern)
- **Scope:** The prefix pattern exists at every length at least 11. Counterexamples to the general prohibition in 5.2(1) occur at every length 13, 16, 19, …, and to the D/G classification in 5.2(3) at every length 14, 17, 20, …. A companion Palomar-registered proof establishes the length-7 ban in 5.2(1). Length 10 and part (2) at length 9 remain open.

<a id="cazenave-second-spectral"></a>

## Counterexample to Cazenave’s second spectral graph conjecture

- **Result page:** [Cazenave’s second spectral graph conjecture](../results/cazenave-second-spectral/) · [Audit](../results/cazenave-second-spectral/audit.md)
- **Lean status:** ✅ Complete
- **Build scope:** Standalone Lean 4 package at pinned commit [`2a5b608`](https://github.com/n1stal/conjecture-lab/tree/2a5b608164c4579d7816f2fc9e15332b0321527f/PalomarPackages/CazenaveC2) (`PalomarPackages/CazenaveC2`).
- **Checked declarations:** `CazenaveRegistry.cazenave_conjecture_2_false`
- **Palomar registration:** [PALOMAR-2026-11-27-000045](https://palomar-registry.org/entry?id=PALOMAR-2026-11-27-000045&version=1) (commit `2a5b608`)
- **Scope:** Full negation of Cazenave’s Conjecture 2 (#20829) via an explicit 11-vertex connected simple graph using exact algebraic and rational certificates. No order-minimality claim; the written infinite-order extension is outside the Lean comparison target.

<a id="inverse-z-rank-four"></a>

## Inverse Z-polynomials through rank four

- **Result page:** [Gao–Ruan–Xie’s inverse Z-polynomial conjecture (rank at most four)](../results/inverse-z-rank-four/) · [Audit](../results/inverse-z-rank-four/audit.md)
- **Lean status:** ✅ Complete
- **Build scope:** Compiled by `lake build --wfail` and axiom-checked by `python3 scripts/check_publication.py` on `main`.
- **Checked declarations:** `ConjectureLab.Submission.inverse_z_rank_at_most_four`, `InverseZ.matroidInverseZ_rank_at_most_four`
- **Palomar registration:** [PALOMAR-2026-11-26-000061](https://palomar-registry.org/entry?id=PALOMAR-2026-11-26-000061&version=1) (commit `fba1c28`)
- **Scope:** Positive coefficients through the rank and log-concavity for matroids on finite ambient types of rank at most four. The unrestricted conjecture (ranks ≥ 5) remains open here.

<a id="four-terminal-packing"></a>

## Sharp distance packing for four prescribed terminals

- **Result page:** [Hak–Kozerenko’s distance-packing question for four prescribed terminals](../results/four-terminal-packing/) · [Audit](../results/four-terminal-packing/audit.md)
- **Lean status:** ✅ Complete
- **Build scope:** Standalone Lean 4 package at pinned commit [`a82e9bf`](https://github.com/n1stal/conjecture-lab/tree/a82e9bfeaf6622cf3cfcbaffe29c8cdfda3ee3f7/PalomarPackages/FourTerminalPacking) (`PalomarPackages/FourTerminalPacking`).
- **Checked declarations:** `TriameterQ3Attainment.four_terminal_unweighted_exact`, `TriameterQ3Attainment.weighted_four_terminal_exact`
- **Palomar registration:** [PALOMAR-2026-11-27-000051](https://palomar-registry.org/entry?id=PALOMAR-2026-11-27-000051&version=1) (commit `a82e9bf`)
- **Scope:** Exact four-terminal distance-packing extremum for all positive integers k and p, with unweighted and nonnegative integer-weighted objectives and explicit attaining connected graphs. Excludes Chung’s (1988) unweighted k = 1 special case from novelty; five or more terminals, real weights, and the disjoint-separator branch of Question 3 remain open.

<a id="inverse-z-projective"></a>

## Strict inverse Z log-concavity for line-preserving projective restrictions

- **Result page:** [Gao–Ruan–Xie’s inverse Z-polynomial conjecture (line-preserving projective restrictions)](../results/inverse-z-projective/) · [Audit](../results/inverse-z-projective/audit.md)
- **Lean status:** ✅ Complete
- **Build scope:** Compiled by `lake build --wfail` and axiom-checked by `python3 scripts/check_publication.py` on `main`.
- **Checked declarations:** `InverseZProjective.GaussianIncidence.represented_inverseZ_strict_logConcave`
- **Scope:** In every rank, the inverse Z-polynomial of a finite projective geometry restricted to points retaining at least two on every line has positive coefficients through rank and strict log-concavity at every interior degree. Prior projective-geometry formulas and overlapping deletion methods are credited; the unrestricted conjecture is not settled.

<a id="property-p-baseline"></a>

## Property P: the finite witness {1, 2}

- **Audit:** [Property P finite witness {1, 2}](../results/property-p-baseline/audit.md)
- **Lean status:** ✅ Complete
- **Build scope:** Compiled by `lake build --wfail` and axiom-checked by `python3 scripts/check_publication.py` on `main`.
- **Checked declarations:** `ConjectureLab.baseline_valid`, `ConjectureLab.baseline_weight`
- **Scope:** The set {1, 2} has Property P and its reciprocal sum is 3/2. This is a known baseline, not a search certificate, upper bound, or resolution of Erdős Problem 12.
