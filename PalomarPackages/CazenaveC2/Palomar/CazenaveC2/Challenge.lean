module

public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.Analysis.Matrix.Spectrum

@[expose] public section

/-! Exact formal target for Tristan Cazenave, arXiv:2611.03879v1, §7,
Conjecture 2 (#20829). No candidate-local notation, definitions or imports
occur in the shared theorem type. -/
namespace CazenaveRegistry

/-- The second largest adjacency eigenvalue is not always bounded by the
largest ordinary combinatorial Laplacian eigenvalue minus two. -/
theorem cazenave_conjecture_2_false :
    ¬ (∀ (n : ℕ) (hn : 2 ≤ n) (H : SimpleGraph (Fin n)) (d : DecidableRel H.Adj),
      letI := d
      H.Connected →
      (H.isHermitian_adjMatrix ℝ).eigenvalues₀
          ⟨1, Eq.mpr (congrArg (fun k : ℕ => 1 < k) (Fintype.card_fin n)) (Nat.lt_of_succ_le hn)⟩ ≤
      (H.isHermitian_lapMatrix ℝ).eigenvalues₀
          ⟨0, Eq.mpr (congrArg (fun k : ℕ => 0 < k) (Fintype.card_fin n))
            (Nat.zero_lt_of_lt (Nat.lt_of_succ_le hn))⟩ - 2) := by
  sorry

end CazenaveRegistry
