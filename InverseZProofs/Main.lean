module

public import InverseZProofs.Integrated
public import InverseZProofs.Invariance
public import InverseZProofs.Lookup

@[expose] public section

set_option autoImplicit false
namespace InverseZ
open Set Matroid
open InverseZ.Algebra

variable {α : Type*} [Finite α]

private theorem list_result (M : Matroid α) (hr : M.eRank ≤ 4) :
    LogConcave (coefficients M) ∧ Positive (coefficients M) := by
  let N := M ↾ simplGround M
  have hRank : N.eRank = M.eRank := simpl_rank_eq M
  have hPolynomial : matroidInverseZ N = matroidInverseZ M :=
    matroidInverseZ_simplification M
  have hCoefficients : coefficients N = coefficients M := by
    unfold coefficients
    rw [hRank,hPolynomial]
  have hR : N.eRank ≤ 4 := hRank ▸ hr
  have h := rank_at_most_four_pairs_logconcave N (simpl_pairs_indep M) hR
  rwa [hCoefficients] at h

/-- Gao–Ruan–Xie's inverse Z conjecture in ranks at most four.
    Every coefficient in the full rank range is strictly positive, and each
    adjacent triple, including triples past the support, satisfies log-concavity.
    No assumptions of simplicity or representability are imposed. -/
theorem matroidInverseZ_rank_at_most_four (M : Matroid α) (hr : M.eRank ≤ 4) :
    (∀ i : ℕ, i ≤ M.eRank.toNat → 0 < (matroidInverseZ M).coeff i) ∧
    (∀ i : ℕ, (matroidInverseZ M).coeff i * (matroidInverseZ M).coeff (i+2) ≤
      (matroidInverseZ M).coeff (i+1) * (matroidInverseZ M).coeff (i+1)) := by
  obtain ⟨hl,hp⟩ := list_result M hr
  have hlength : (coefficients M).length = M.eRank.toNat+1 := by simp [coefficients]
  constructor
  · intro i hi
    have hh := positive_lookup hp i (by rw [hlength]; omega)
    simpa only [coefficients,List.getElem_map,List.getElem_range] using hh
  · intro i
    by_cases hi : i+2 ≤ M.eRank.toNat
    · have hh := logconcave_lookup hl i (by rw [hlength]; omega)
      simpa only [coefficients,List.getElem_map,List.getElem_range] using hh
    · rw [matroidInverseZ_support M (i+2) (by omega), mul_zero]
      exact mul_self_nonneg _

#print axioms matroidInverseZ_rank_at_most_four

end InverseZ
