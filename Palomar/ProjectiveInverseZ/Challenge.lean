module

public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
public import Mathlib.Combinatorics.Matroid.Rank.ENat
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

namespace ConjectureLab.ProjectiveSubmission
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


section ProjectiveModel
open Module Submodule Matroid
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V] [Finite V]

def LinePreserving (S : Set V) : Prop :=
  ∀ U : Submodule K V, finrank K U = 2 →
    ∃ x ∈ S, ∃ y ∈ S, x ∈ U ∧ y ∈ U ∧ x ≠ 0 ∧ y ∉ span K ({x} : Set V)
omit [FiniteDimensional K V] in
private theorem span_finrank_of_indep {I : Set V} (hI : LinearIndepOn K id I) :
    finrank K (span K I) = I.ncard := by
  classical
  let : Fintype I := Fintype.ofFinite I
  have he : Set.range (fun x : I => (x : V)) = I := Subtype.range_coe
  have hli : LinearIndependent K (fun x : I => (x : V)) := hI
  rw [← he, finrank_span_eq_card hli, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, he]
private theorem linear_augment {I J : Set V}
    (hI : LinearIndepOn K id I) (hJ : LinearIndepOn K id J) (h : I.ncard < J.ncard) :
    ∃ e ∈ J, e ∉ I ∧ LinearIndepOn K id (insert e I) := by
  have hn : ¬ J ⊆ (span K I : Set V) := by
    intro hJI
    have hd := Submodule.finrank_mono (span_le.mpr hJI)
    rw [span_finrank_of_indep hI, span_finrank_of_indep hJ] at hd
    omega
  obtain ⟨e, heJ, heI⟩ := Set.not_subset.mp hn
  have he : e ∉ I := fun h => heI (subset_span h)
  exact ⟨e, heJ, he, (linearIndepOn_id_insert he).2 ⟨hI, heI⟩⟩
def representedMatroid (S : Set V) : Matroid V :=
  (IndepMatroid.ofFinite (Set.toFinite S)
    (fun I => I ⊆ S ∧ LinearIndepOn K id I)
    ⟨Set.empty_subset _, linearIndepOn_empty K id⟩
    (by intro I J h hIJ; exact ⟨hIJ.trans h.1, h.2.mono hIJ⟩)
    (by
      intro I J hI hJ hIJ
      obtain ⟨e, heJ, heI, h⟩ := linear_augment hI.2 hJ.2 hIJ
      exact ⟨e, heJ, heI, Set.insert_subset (hJ.1 heJ) hI.1, h⟩)
    (by intro I h; exact h.1)).matroid
end ProjectiveModel

section Main
variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V] [Finite V]
theorem projective_inverse_z (S : Set V) (hS : LinePreserving (K:=K) S) :
    (∀ i, i ≤ (representedMatroid (K:=K) S).eRank.toNat →
      0 < (matroidInverseZ (representedMatroid (K:=K) S)).coeff i) ∧
    (∀ i, i+2 ≤ (representedMatroid (K:=K) S).eRank.toNat →
      (matroidInverseZ (representedMatroid (K:=K) S)).coeff i *
        (matroidInverseZ (representedMatroid (K:=K) S)).coeff (i+2) <
      (matroidInverseZ (representedMatroid (K:=K) S)).coeff (i+1) *
        (matroidInverseZ (representedMatroid (K:=K) S)).coeff (i+1)) := by sorry

end Main
end ConjectureLab.ProjectiveSubmission
