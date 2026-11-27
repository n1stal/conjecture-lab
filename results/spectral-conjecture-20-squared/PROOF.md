# The unique nearest graph in squared spectral distance

**Jaime Nistal**, with OpenAI Codex assistance in proof development and verification.

## Result

For every integer `n ≥ 3`, among **all simple undirected graphs on `3n` vertices not isomorphic to `Kₙ,ₙ,ₙ`**, the unique minimizer up to isomorphism of the sum of squared differences between the ordered adjacency eigenvalues is
**Hₙ = join((n−1)K₁, K₁ ∪ Kₙ,ₙ).**
Equivalently, start with `Kₙ₋₁,ₙ,ₙ` and add one new vertex adjacent exactly to the `n−1` vertices in the smallest part. This is the squared-distance minimizer assertion in [Conjecture 20 of Irena M. Jovanović, Jelena Sedlar, and Riste Škrekovski](https://arxiv.org/html/2610.18636v2#S5).

The authors already identified the case `n = 3`; the proof here is uniform in `n`. The minimum squared score also tends to **1/2** as n grows. This is the p = 2 limit for the optimum over all nonisomorphic competitors, not simply for a proposed sequence of candidates. This package does not claim the Manhattan assertion, historical priority, or peer review.

## Proof outline

1. Verify the balanced target's ordered spectrum (`(2n, 0, …, 0, −n, −n)`) and the proposed competitor's graph realization. The squared score of `Hₙ` is strictly positive and below `16/27`. Thus it is a nonisomorphic competitor and any equal or better graph is below the same threshold.
2. For a graph below that threshold, the rank theorem for [Problem 21](https://arxiv.org/html/2610.18636v2#S5) bounds the adjacency rank by five, since `16/27 < 2/3`. A spectral bound excludes rank below two. The rank-two-through-five classification represents the graph as a positive-weight blow-up of a small catalogue template, with isolated vertices accounted for explicitly.
3. The checked matrix and arithmetic inequalities on the templates leave only balanced tripartite and the specified `Hₙ`. The finite catalogue checks verify the catalogue and local template cases, not a finite search over graph orders. The triangle and Paw cases reduce the arbitrary positive weights to the indicated classes and exclude isolates when needed.
4. Relabeling preserves the ordered spectrum. A candidate isomorphic to `Kₙ,ₙ,ₙ` is outside the minimization domain; all remaining graphs below the threshold are isomorphic to `Hₙ`. Above the threshold they have strictly greater score. This proves existence and uniqueness up to isomorphism, including disconnected graphs in the comparison.

## Limiting value

The checked minimizer identity reduces the global minimum to the actual score of Hₙ. For n ≥ 5 that score differs from 1/2 by at most 7/n. The proof bounds deviations of the candidate's nonzero eigenvalues via exact evaluations of its cubic and uses the zero-trace identity. The original paper already gave sharper asymptotics for the candidate in [Theorem 17(ii), §3.3](https://arxiv.org/html/2610.18636v2#S3.SS3). We credit that result and establish in Lean that the limit is the limit of the actual minimum.

## Lean source and replay

Download the [complete checked source package and receipts](LEAN-SOURCES.tar.gz) and unpack it. It contains 16 source modules, their SHA-256 manifest, and a replay script. The exact unconditional theorem is `Conjecture20Squared.squared_unique_nearest` in `C20Classify.lean`; the threshold theorem is `Conjecture20Squared.close_graph_is_balanced_or_hub`, and the exact limit theorem is `C20Rate.conjecture_20_squared_limit` in `C20Limit.lean`.

The archive SHA-256 is `c14457b69d92fe2afba4ff907aa16810b4e257b829e22091667aa653f2e1daaa`. See the archive README for its exact [base checkout](https://github.com/n1stal/conjecture-lab/tree/8673a57d26ea1c8d2752635bd2dae5fe8665a171), Lean and Mathlib pin, and the strict replay sequence. These declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.
