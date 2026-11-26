module

public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
public import Mathlib.Combinatorics.Matroid.Rank.ENat

@[expose] public section

namespace ConjectureLab.Submission
open Finset Polynomial
open scoped BigOperators ENat

section Ranked
variable {L : Type*} [PartialOrder L] [LocallyFiniteOrder L] [DecidableEq L]
variable (rk : L → ℕ)

noncomputable def signedMu (a b : L) : ℤ := by
  classical
  exact (-1) ^ (rk b - rk a) * IncidenceAlgebra.mu ℤ a b

noncomputable def lowCorrection (d : ℕ) (p : ℤ[X]) : ℤ[X] :=
  ∑ i ∈ range ((d+1)/2), monomial i (p.coeff (d-i) - p.coeff i)

noncomputable def inverseKL (strict : StrictMono rk) (a b : L) : ℤ[X] :=
  if a = b then 1
  else lowCorrection (rk b-rk a)
    ((Ico a b).attach.sum fun x =>
      C (signedMu rk x.val b) * (X ^ (rk b-rk x.val) * inverseKL strict a x.val))
termination_by rk b
decreasing_by exact strict (mem_Ico.mp x.property).2

noncomputable def inverseZ (q : L → L → ℤ[X]) (a b : L) : ℤ[X] :=
  ∑ x ∈ Icc a b, C (signedMu rk x b) * (X ^ (rk b-rk x) * q a x)

end Ranked

section Matroid
open Set Matroid
variable {α : Type*} [Finite α]
variable (M : Matroid α)

abbrev Flats := {F : Set α // M.IsFlat F}

noncomputable instance flatLocallyFinite : LocallyFiniteOrder (Flats M) :=
  LocallyFiniteOrder.ofFiniteIcc fun _ _ => Set.toFinite _

noncomputable def flatRank (F : Flats M) : ℕ := (M.eRk F.val).toNat

theorem flatRank_strict : StrictMono (flatRank M) := by
  classical
  intro F G hFG
  have hsub : F.val ⊆ G.val := le_of_lt hFG
  obtain ⟨u, huG, huF⟩ := Set.exists_of_ssubset hFG
  obtain ⟨I, J, hI, hJ, hIJ⟩ := M.exists_isBasis_subset_isBasis hsub G.property.subset_ground
  have hIJ' : I ⊂ J := by
    refine lt_of_le_of_ne hIJ ?_
    intro e
    have huCF : u ∈ M.closure F.val := by
      rw [← hI.closure_eq_closure, e, hJ.closure_eq_closure]
      exact M.mem_closure_of_mem huG G.property.subset_ground
    rw [F.property.closure] at huCF
    exact huF huCF
  rw [flatRank, flatRank, ← ENat.natCast_lt_natCast,
    ENat.natCast_toNat ((M.eRk_le_encard F.val).trans_lt (Set.toFinite F.val).encard_lt_top).ne,
    ENat.natCast_toNat ((M.eRk_le_encard G.val).trans_lt (Set.toFinite G.val).encard_lt_top).ne,
    ← hI.encard_eq_eRk, ← hJ.encard_eq_eRk]
  exact (Set.toFinite I).encard_lt_encard hIJ'

def bottomFlat : Flats M := ⟨M.closure ∅, M.isFlat_closure _⟩
def topFlat : Flats M := ⟨M.E, M.ground_isFlat⟩

noncomputable def matroidInverseKL (a b : Flats M) : ℤ[X] := by
  classical
  exact inverseKL (flatRank M) (flatRank_strict M) a b

/-- Inverse Z of a finite matroid, defined on its actual flat lattice. -/
noncomputable def matroidInverseZ : ℤ[X] := by
  classical
  exact inverseZ (flatRank M) (matroidInverseKL M) (bottomFlat M) (topFlat M)

end Matroid

/-- The coefficients of the inverse Z-polynomial are positive through rank
and log-concave for every matroid on a finite ambient type of rank at most four.
No simplicity or representability restriction is imposed. Higher ranks are
not covered. -/
theorem inverse_z_rank_at_most_four {α : Type*} [Finite α]
    (M : Matroid α) (hr : M.eRank ≤ 4) :
    (∀ i : ℕ, i ≤ M.eRank.toNat → 0 < (matroidInverseZ M).coeff i) ∧
    (∀ i : ℕ, (matroidInverseZ M).coeff i * (matroidInverseZ M).coeff (i+2) ≤
      (matroidInverseZ M).coeff (i+1) * (matroidInverseZ M).coeff (i+1)) := by
  sorry

end ConjectureLab.Submission
