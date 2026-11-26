# Ordered spectral proximity forces adjacency rank at most five

The verified Lean theorem is
`SpectralRank.problem_21` in [SpectralTop.lean](../../SpectralRank/SpectralTop.lean).

For a finite simple graph H on 3n vertices, n≥3, put its real adjacency
eigenvalues in decreasing order. If the sum of the squared differences
from the ordered sequence (2n,0,…,0,−n,−n) is strictly less than 2/3,
then its real adjacency matrix has rank at most five.

This is an affirmative answer to Problem 21 of Jovanović, Sedlar and
Škrekovski, arXiv:2610.18636v2, and does not need H to be connected.
The target sequence and squared distance are exactly their displayed
formula immediately before Problem 21. This does not settle their
separate minimizer and uniqueness Conjecture 20.
Source: https://arxiv.org/html/2610.18636v2#S5

## Proof summary

Place the three-supported target sequence diagonally in an orthonormal
ordered eigenbasis for H. This gives a real rank-at-most-three comparator C
whose squared Frobenius error is the squared spectral distance. A symmetric
matrix of rank at least six has a nonsingular principal submatrix of order
six or seven by successively adjoining a one- or two-pivot Schur complement.
Restricting to that minor cannot increase the rank of C or the error.

Lean verifies complete coverage of simple graphs on six and seven
vertices from vertex-augmentation relabeling witnesses: 209 rows cover
11,291 augmentations over the successive orders, including 9,984 at
order seven. In the covered 1,200 representatives it checks either a
nonzero integer null vector, or exact integer Gram certificates selecting
real subspaces whose squared gains exceed specified rational thresholds.
The dimensions guarantee orthonormal directions in the kernel of any
rank-at-most-three comparator. Bessel's inequality bounds their errors by
the full squared Frobenius norm. The smallest certificate sums are 69/100
and 130/100 for orders six and seven, respectively, both exceeding 2/3.
The final Lean theorem instantiates both fully checked finite corpora,
not hypotheses or floating-point tests.

## Reproduce

Use [the repository verification instructions](../../docs/verification.md).
The default build compiles the ten SpectralRank modules; the publication gate
audits the exact top declaration using the pinned Lean toolchain. The finite
inputs are embedded in the Lean modules and checked by proofs; no Python
program, external graph database, or numerical library is trusted. The
top-level axiom audit is propext, Classical.choice, and Quot.sound only.

See the [dated source and overlap audit](audit.md) for citations and scope.
