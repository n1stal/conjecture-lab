# Counterexample to Cazenave Conjecture 2 (#20829)

Jaime Nistal. Codex assisted with proof development and checking.

The 11-vertex graph formally refutes the full original claim. The argument below also gives an infinite family on paper. The first family member is not claimed to be an order-minimal counterexample.

## Target

[Tristan Cazenave, Lemmas and Conjectures in Spectral Graph Theory, arXiv:2611.03879v1, §7 Conjecture 2 #20829](https://arxiv.org/html/2611.03879v1#S7) proposes \(\lambda_2(G)\leq\mu_1(G)-2\) for finite connected simple graphs with at least two vertices. Eigenvalues are ordered decreasingly with multiplicity; \(\lambda_2\) is for the ordinary adjacency matrix \(A\), and \(\mu_1\) is the largest eigenvalue of the ordinary combinatorial Laplacian \(L=D-A\). Neither \(D+A\) nor the normalized Laplacian is used below. This is a refutation of that universal conjecture, not a claim about optimizing a finite order or about Cazenave 6(ii)/(iii).

## Graphs

For each integer \(k\geq3\) take two disjoint copies of the diamond \(K_4\) minus an edge. In each copy label \(a,b,c,d\), with the missing edge \(ad\). Join the two \(a\) vertices by a path with \(k\) **new internal vertices** \(p_1,\ldots,p_k\). Thus the path has \(k+1\) edges, the graph is connected and simple, and has \(8+k\) vertices, maximum degree three and \(11+k\) edges. The first actual example, for \(k=3\), has vertices \(0,\ldots,10\) and these fourteen edges:

    01 02 12 13 23   45 46 56 57 67   08 89 9–10 10–4

Both diamonds have a tip \(a\) with full-graph degree 3, two middle vertices with degree 3, and unused tip \(d\) of degree 2. Path internal degrees are all 2.

## 1. An exact 2-dimensional spectral lower bound

Let \(u\) be supported on the left diamond and \(p_1\), with entries \((10,11,11,8,4)\) at \((a,b,c,d,p_1)\). Define \(v\) by reflection, supported on the right diamond and \(p_k\), in the analogous order. For \(k\geq3\) the supports are disjoint and anticomplete: the two outside support path vertices are not adjacent, even at \(k=3\). Consequently \(u^T v=u^TA v=0\). Directly,
\[
u^Tu=v^Tv=422,\qquad
u^TAu=v^TAv=2(110+110+121+88+88+40)=1114.
\]
Every nonzero vector in their two-dimensional span has adjacency Rayleigh quotient \(557/211\). The max–min principle therefore gives \(\lambda_2(G)\ge557/211>21/8\), with exact gap \(25/1688\) to the rational threshold.

## 2. An exact uniform Laplacian upper bound

We show \(B=(37/8)I-L\) is positive definite. On either diamond its principal block \(C\), in order \(a,b,c,d\), is
\[
8C=\begin{pmatrix}
13&8&8&0\\
8&13&8&8\\
8&8&13&8\\
0&8&8&21
\end{pmatrix}.
\]
The leading principal minors of \(8C\) are \(13,105,725,6905\), and deleting row/column \(a\) gives determinant \(1565\). Thus \(C\) is positive definite and its inverse has
\[
(C^{-1})_{aa}=8(1565)/6905=2504/1381.
\]
Each diamond block has only one coupling to the path, a unit entry at its \(a\) and the neighboring path vertex. Completing the square on both four-dimensional diamond blocks leaves the tridiagonal Schur complement on the path. Its two endpoint diagonal entries are \(x=21/8-2504/1381=8969/11048\), all other diagonal entries are \(y=21/8\), and consecutive off-diagonals are \(+1\). Exactly \(0<x<1\) and
\[
xy-2=11581/88384>0.
\]

Complete the square also on the two path endpoints, using \(x>0\). If \(k=3\) the middle vertex is common to both endpoint neighbors; the remaining scalar is \(y-2/x>0\). If \(k\geq4\), the remaining path has at least two vertices. Its endpoint diagonals are \(y-1/x>1/x>1\), and any interior diagonal is \(y>2\). It is positive definite, because applying \(2z_i z_j\geq-(z_i^2+z_j^2)\) to each off-diagonal edge gives a positive coefficient on every squared coordinate. Adding back the positive eliminated blocks proves \(B\succ0\), hence \(\mu_1(G)<37/8\).

Combining the bounds yields \(\lambda_2(G)\geq557/211>21/8>\mu_1(G)-2\) for every \(k\geq3\). No dimension cutoff or approximate eigenvalue evaluation enters the universal refutation.

## What the Lean proof checks

For the 11-vertex witness, the file `DiamondGraph.lean` works directly with
Mathlib's adjacency matrix and ordinary Laplacian of the listed connected
simple graph. It checks the exact degree ledger and evaluates the
Laplacian quadratic form. `RationalArithmetic.lean` rewrites that shift
as a sum of squares. The actual top Laplacian eigenvector then gives
\(\mu_1\le37/8\), enough for the strict violation.

For the adjacency bound, the independent Lean proof uses the intermediate
value theorem on the polynomials
\[
p(t)=t^4-t^3-5t^2+t+2,\qquad q(t)=t^3-3t^2-t+5.
\]
The verified evaluations give a root of \(p\) in \((21/8,8/3)\)
and a root of \(q\) in \((8/3,11/4)\).
`SpectralAdapter.lean` checks an explicit nonzero adjacency eigenvector
for each respective root. They are distinct and both exceed \(21/8\);
hence the second-largest eigenvalue exceeds \(21/8\). Its theorem
`CazenaveC2.source_conjecture_false` and the comparable wrapper
`CazenaveRegistry.cazenave_conjecture_2_false` use only the axioms
`propext`, `Classical.choice` and `Quot.sound` on the pinned toolchain.

The all-orders family argument in §§1–2 is a written extension and is
not itself claimed as a Lean theorem. The checked Python Fraction audit
in `exact-check.py` independently verifies the rational arithmetic
for the first 30 members.

## Prior-art boundary

The author's v1 still explicitly calls #20829 unrefuted. Their reported exhaustive cutoff for this specific item is connected graphs through \(n=9\); only items 1 and 7 were extended to connected graphs at \(n=10\). Their tested structured family examples are not a certificate for the present two-diamond construction. The §8 author archive link was checked but the ZIP could not be retrieved in the environment's bounded request, so the raw row was not independently inspected. Focused exact ID, source ID plus wording, and diamond-with-path queries across primary arXiv, trureturing result source, Hexagon preprints, and public GitHub/SCOPE discovery turned up no matching resolution at the time of this bounded search. This is not proof no earlier or unindexed result exists.

Do not conflate it with [trureturing Cazenave 4](https://www.trureturing.org/research/op-cazenave2611c4/), [trureturing Cazenave 5](https://www.trureturing.org/research/op-cazenave2611c5/), [Kramer's 6(ii)](https://hexagonmath.org/2611.00232v1), or [Coba Bruges's proposed 6(iii)](https://hexagonmath.org/2611.01102v1). The original author labels C2 #20829; those are distinct inequalities. Further, C3 #501193 is an immediate consequence of [Gerardo and Octavio Arizmendi, Energy of a graph and Randić index](https://arxiv.org/abs/2009.08041), since their \(2R\leq\mathcal E(A)\) and the trivial nuclear norm bound \(\mathcal E(A)\leq\mathrm{rank}(A)\lambda_1\) imply it; do not count that as a second novel result. The sufficiently strong old fixed-edge lower bound on \(R\) also implies C6(i) and the edge-size clause of C6(iv), not C2.
