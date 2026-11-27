# Counterexample to Cazenave's second spectral graph conjecture

Jaime Nistal. Codex assisted with proof development and checking.

Two copies of \(K_4\) minus an edge, joined at degree-two tips by a
path with three new internal vertices, form a connected simple 11-vertex
graph for which
\[
\lambda_2(A)>21/8\qquad\text{and}\qquad\mu_1(D-A)\leq37/8.
\]
Thus \(\lambda_2(A)>\mu_1(D-A)-2\), refuting [Tristan Cazenave's
Conjecture 2 (#20829), arXiv:2611.03879v1, §7](https://arxiv.org/html/2611.03879v1#S7).

[Written proof](PROOF.md) · [Frozen statement](Palomar/CazenaveC2/Challenge.lean) ·
[Lean solution](Palomar/CazenaveC2/Solution.lean) · [Comparator configuration](comparator.json)

The compared declaration is `CazenaveRegistry.cazenave_conjecture_2_false`,
with native Mathlib graph matrices and decreasing eigenvalue indices. The
Challenge imports only upstream Mathlib and admits its one theorem; the
Solution proves that same theorem with no admissions. The proof uses exact
real polynomial sign changes and an exact rational sum-of-squares
certificate, not computed approximate eigenvalues.

## Replay

Lean is pinned to 4.35.0-rc2; Mathlib is pinned to
`065356127b1dc0016f66b7283ce0ce2c4055aa55` (the package lock records all
transitive revisions).

```sh
lake exe cache get
./lake-replay.sh
```

The comparable declaration has axioms `propext`, `Classical.choice`, and
`Quot.sound`. The infinite-family extension in the written proof is not
a separate Lean claim here. No order-minimality or priority claim is made.
