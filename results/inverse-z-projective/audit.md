# Strict inverse Z log-concavity for line-preserving projective restrictions

**Jaime Nistal**, author · **Codex (OpenAI)**, AI co-author

## What Lean proves

Start with a finite-dimensional vector space over a finite field and choose a set of retained vector representatives. Each two-dimensional subspace must contain two retained nonparallel vectors. For the represented matroid on these vectors, the inverse Z-polynomial has positive coefficients in every degree through its rank. Its coefficients satisfy \(a_i a_{i+2}<a_{i+1}^2\) whenever \(i+2\) is at most its rank. The strict inequality is vacuous in ranks zero and one. In a binary projective geometry of rank at least two, a line has three points, so any two deletions would violate the hypothesis. Multi-point deletions occur for fields of size at least three.

Choosing one nonzero vector per retained point gives the equivalent projective formulation: restrict a projective geometry to a set retaining at least two points on every line. The exact Lean statement also permits repeated projective directions represented by different vectors, and a zero vector. It neither assumes log-concavity nor supplies numerical evidence as a proof premise. It does not settle unrestricted rank five or the general inverse Z conjecture.

- [Exact Lean theorem](../../InverseZProjective/ProjectiveMain.lean): InverseZProjective.GaussianIncidence.represented_inverseZ_strict_logConcave.
- [Mathematical proof and coefficient formula](proof.md).
- [Published definition of inverse Z](../../InverseZProofs/Algebra.lean), reused without alteration.
- [Repository verification instructions](../../docs/verification.md). The result is in the default kernel and catalogue gate. It is not part of the rank-four Palomar Challenge/Solution comparison.

The proof constructs the actual vector matroid and recovers its ranked flat lattice, transports the upper Möbius weights and accounts for deleted atoms in the bottom weight, and evaluates the resulting candidate inverse Z sums. A Gaussian-binomial factor is strictly log-concave; the deletion factor is positive and log-concave. The proof formalizes the factorization and their product.

## Sources and overlap audit (2026-11-26)

- [Gao, Ruan and Xie, arXiv:2507.01332v1](https://arxiv.org/html/2507.01332v1): Conjecture 1.5 states the broader inverse Z log-concavity problem. Theorem 1.6 already proves the sparse paving case and has priority where those classes overlap.
- [Braden, Ferroni, Matherne and Nepal, arXiv:2510.01086v2](https://arxiv.org/html/2510.01086v2): Theorem 2.2 gives the inverse Z characterization. Section 4.3 and Proposition 4.4 compute the inverse KL polynomial for a single-point deletion from a projective geometry, overlapping the one-deletion candidate here. Their Theorem 1.4 inverse Z deletion formula and §4.3 give an existing route to the affine-in-deletion-count identity: telescope over the deleted points. Every intermediate restriction still retains two points per line, so each deletion sees the same upper quotient geometries and the same contributions in the deletion formula. We credit that prior recipe. The Lean proof instead identifies the coefficient factors directly using the filtered flat lattice and the degree/symmetry criterion; it makes no new deletion-formula or priority claim.
- [Gao, Li and Xie, arXiv:2601.17314](https://arxiv.org/abs/2601.17314): explicit equivariant inverse Z formulas and strong inductive log-concavity for uniform and q-uniform matroids are prior work, including the full (unrestricted) projective-geometry overlap. Their stated q-uniform result is not a result about arbitrary deletions retaining two points per line.
- [Cheng and Liu, arXiv:2607.24186v2](https://arxiv.org/html/2607.24186v2): Theorem 1.1 also studies projective deletions, but describes the ordinary Kazhdan–Lusztig polynomial \(P\) and ordinary \(Z\)-polynomial under their half-rank condition. It does not identify the inverse \(Y\) checked here.
- [Badalov, arXiv:2609.13417v1](https://arxiv.org/abs/2609.13417v1): the deletion constructions and counterexamples concern log-concavity of the inverse Kazhdan–Lusztig polynomial \(Q\), not the inverse Z-polynomial \(Y\) checked here. We do not use them as evidence for or against this theorem.

This source comparison is bounded. It credits overlapping results and techniques rather than asserting a first proof or a first formalization. A separate AI review compared the literal Lean scope and the written proof; this is not outside human refereeing or author endorsement.
