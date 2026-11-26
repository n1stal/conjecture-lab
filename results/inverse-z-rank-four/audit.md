# Inverse Z-polynomial log-concavity through rank four

**Jaime Nistal**, author · **Codex (OpenAI)**, AI co-author

## What Lean proves

For every Mathlib matroid on a finite ambient type of rank at most four, the
inverse Z-polynomial has strictly positive coefficients in degrees zero through
the rank. If its coefficients are \(a_i\), counting absent terms as zero, then
\(a_i a_{i+2} \le a_{i+1}^2\) for every \(i\ge 0\). This covers finite matroids
by taking their ground set as the ambient type, and does not assume simplicity
or representability. The proof also establishes that the coefficients above
the rank vanish. The unrestricted conjecture is not settled here.

- [Exact statement and proof](../../Solution.lean):
  `ConjectureLab.Submission.inverse_z_rank_at_most_four`.
- [Main development](../../InverseZProofs/Main.lean):
  `InverseZ.matroidInverseZ_rank_at_most_four`.
- [Polynomial definition](../../InverseZProofs/Algebra.lean): the signed
  Möbius recurrence on the genuine ranked lattice of flats, using the
  degree and palindromicity characterization of the inverse Z-polynomial.
- [Registry comparison statement](../../Challenge.lean): an intentional
  statement-only copy. It is not part of the proof or the default build.

The rank-four argument writes the sequence as \((A,B,C,B,A)\). It proves
\(C-B\ge 0\) by the point–line inequality and proves
\((B-A)-(C-B)\ge W_1-3\) by rank-preserving deletion, where \(W_1\) counts the
points of the simplification. Endpoint positivity and these two bounds imply
log-concavity. None of the numerical searches are premises of the proof.

## Sources and prior work (checked 2026-11-26)

- [Gao, Ruan and Xie, arXiv:2507.01332v1](https://arxiv.org/html/2507.01332v1):
  Conjecture 1.5 is the target. Theorem 1.6 already proves the sparse paving
  case; it has priority on that overlapping class. The [journal
  version](https://www.sciencedirect.com/science/article/pii/S0097316526000634)
  also reports the sparse paving result.
- [Braden, Ferroni, Matherne and Nepal, arXiv:2510.01086v2](https://arxiv.org/html/2510.01086v2):
  Theorem 2.2 gives the inverse Z characterization used here. Their
  corank-two computations and counterexample to a related real-rootedness
  property do not establish or refute this rank-bounded theorem.
- [Gao, Li and Xie, arXiv:2601.17314](https://arxiv.org/abs/2601.17314):
  equivariant results for uniform and q-uniform matroids cover further
  special families, not all matroids of rank at most four.
- [RealRooted issue #1405](https://github.com/PerAlexandersson/RealRooted/issues/1405)
  tracks the broader log-concavity conjecture. Also checked the Formal
  Conjectures tree and issue searches for inverse Z and the source arXiv ID.

Searches combined “inverse Z-polynomial,” “log-concavity,” “rank 4,”
“rank four,” and author names. No matching all-matroid rank-at-most-four
proof or Lean formalization was located in these sources. This is a bounded
search, not a priority claim. The written and formal statements were compared
in a separate AI review; no external human refereeing or author endorsement
is claimed.

The signs agree with Gao–Ruan–Xie's normalization. Their loop convention
deletes the loops; all flats contain the bottom flat (the loop set), and
removing that set preserves the ranked flat lattice. The Lean definition
therefore agrees with that convention without excluding looped matroids.
