module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.Matrix.Rank
public import SpectralRank.SpectralTop

@[expose] public section

namespace ConjectureLab.SpectralProblem21Submission

open Matrix
open scoped BigOperators

/-- The real 0–1 adjacency matrix of a Boolean adjacency relation. -/
def adjacency {V : Type*} (A : V → V → Bool) : Matrix V V ℝ :=
  fun i j => if A i j then 1 else 0

theorem adjacency_isHermitian {V : Type*} (A : V → V → Bool)
    (hsymm : ∀ i j, A i j = A j i) : (adjacency A).IsHermitian := by
  change (adjacency A)ᴴ = adjacency A
  ext i j
  simp [adjacency, hsymm j i]

/-- The decreasing ordered adjacency spectrum of the balanced complete
tripartite graph: one entry 2n, then 3n−3 zeroes, then two entries −n. -/
noncomputable def tripartiteSpectrum (n : ℕ)
    (i : Fin (Fintype.card (Fin (3*n)))) : ℝ :=
  if i.val = 0 then 2*(n : ℝ) else if 3*n ≤ i.val+2 then -(n : ℝ) else 0

/-- Jovanović–Sedlar–Škrekovski, arXiv:2610.18636v2, Problem 21.
For a finite simple undirected graph of order 3n, n≥3, if the sum of
squared differences between its decreasing ordered real adjacency
eigenvalues and the displayed tripartite spectrum is strictly below 2/3,
then its real adjacency matrix has rank at most five.
Connectedness is not needed; this does not address Conjecture 20. -/
theorem problem_21 (n : ℕ) (hn : 3 ≤ n) (A : Fin (3*n) → Fin (3*n) → Bool)
    (hdiag : ∀ i, A i i = false) (hsymm : ∀ i j, A i j = A j i)
    (hClose : ∑ i, ((adjacency_isHermitian A hsymm).eigenvalues₀ i -
      tripartiteSpectrum n i)^2 < (2/3 : ℝ)) :
    (adjacency A).rank ≤ 5 := by
  exact SpectralRank.problem_21 n hn A hdiag hsymm hClose

#print axioms problem_21

end ConjectureLab.SpectralProblem21Submission
