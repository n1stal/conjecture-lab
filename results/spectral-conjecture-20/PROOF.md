# The nearest graphs to the balanced complete tripartite graph

Jaime Nistal, with Codex assistance.

We prove [Conjecture 20 of Irena M. Jovanović, Jelena Sedlar, and Riste Škrekovski](https://arxiv.org/html/2610.18636v2#S5) in Lean. For every integer n ≥ 3, among all simple graphs on 3n vertices not isomorphic to Kₙ,ₙ,ₙ, the unique nearest graph up to isomorphism is Hₙ under **both** sums of ordered adjacency eigenvalue differences: the sum of absolute differences and the sum of squared differences. The respective minimum values tend to **1** and **1/2**.

Hₙ is obtained by starting with Kₙ₋₁,ₙ,ₙ and adding one vertex adjacent to every vertex in the smallest part and to no other vertex. The search domain includes disconnected graphs and excludes only the isomorphism class of Kₙ,ₙ,ₙ, not all cospectral graphs.

## Proof

**1. A spectral benchmark.** The target has ordered eigenvalues 2n, then 3n−3 zeros, then −n twice. For Hₙ, group vertices into four classes of sizes n−1, n, n, and 1. Its four nonzero eigenvalues come from the symmetric weighted adjacency matrix on these classes, with entries √(wᵢwⱼ) between adjacent classes. The remaining eigenvalues are zero. This compression preserves the spectrum with multiplicities after the extra zeros are restored. The four eigenvalues are −n and the three roots of an explicit cubic. Exact root brackets give scores below 16/27 for squared distance and 11/9 for Manhattan distance, with a tighter Manhattan bound of 17/15 for n ≥ 5. The formal proof constructs an actual eligible representative of Hₙ.

**2. Squared distance.** The checked rank bound from Problem 21 and the finite catalogue of small adjacency-rank templates restrict any graph of squared score below 16/27 to a short list of weighted graphs, with isolated vertices considered explicitly. Exact inequalities on the weights leave only the target and Hₙ. Hence any eligible graph at or below the score of Hₙ is isomorphic to Hₙ. The rank-template catalogues are finite, but the inequalities on their weights are uniform in n.

**3. Manhattan distance.** The ordered eigenvalue differences sum to zero. Thus Manhattan distance below 11/9 bounds the second eigenvalue by 11/18. Interlacing excludes induced P₄ and 2K₂; bounds on the two smallest eigenvalues also exclude K₄. The triangle count, obtained from the third spectral moment, excludes the triangle-free case. The formal graph reduction leaves triangle and paw templates with positive vertex-class weights and possibly isolates. For n ≥ 5 the sharper 17/15 bound gives squared distance below 2/3, again because the signed eigenvalue differences sum to zero: if their absolute sum is D, the squares sum to at most D²/2. The weighted inequalities then force the balanced graph or Hₙ (including exclusion of isolates in the surviving case). For n = 3,4, a finite certificate over admissible vertex-class weights checks the same classification with exact polynomial sign bounds rather than floating-point eigenvalues. These two arguments cover all n ≥ 3.

**4. Limits of the minima.** Since Hₙ wins, its scores are the actual optima. Exact evaluations of the cubic and its root brackets give error bounds 4/n for the Manhattan score relative to 1 and 7/n for the squared score relative to 1/2, for n ≥ 5. The original paper already derived sharper asymptotics for the proposed graph in Theorem 17. The new point is that those limiting values are for the global minima over all eligible graphs.

## Lean source and replay

The end-to-end statement is [`Conjecture20.conjecture20`](lean/Conjecture20Complete.lean). It combines the [two uniqueness statements](lean/Conjecture20Nearest.lean) and proves both limits. It was checked by Lean 4.35.0-rc2 with warnings as errors. Its only dependencies on axioms are `propext`, `Classical.choice`, and `Quot.sound`.

Use the [pinned base checkout](https://github.com/n1stal/conjecture-lab/tree/8673a57d26ea1c8d2752635bd2dae5fe8665a171), Lean 4.35.0-rc2, and Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55. Download and unpack the [complete 34-module source archive](LEAN-SOURCES.tar.gz), then run `bash lean/replay.sh /absolute/path/to/base-checkout` from this result directory. This checks the source hashes, builds the Problem 21 dependencies, and compiles each of the 34 modules in dependency order.

## Prior work and scope

Abdollahi and Zakeri originally proposed a different nearest graph for n ≥ 4. Jovanović, Sedlar, and Škrekovski disproved that proposal, identified Hₙ, credited the known case n = 3 (and discussed an error in the earlier drawing), and proposed the all-orders statement proved here. Their paper also suggested the second-eigenvalue and low-rank approaches used in the proof. A targeted search on 27 November 2026 did not identify another resolution of this exact all-orders statement. This is a machine-checked result, not a claim of priority or peer review.
