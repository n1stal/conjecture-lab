module
public import InverseZProjective.RepresentedRank
public import InverseZProjective.SubspaceMobius
@[expose] public section
set_option autoImplicit false
namespace InverseZProjective.GaussianIncidence
open Module Submodule Finset InverseZ.Algebra InverseZProjective.ProjectiveTrace
section Transport
variable {A B : Type*}
variable [PartialOrder A] [LocallyFiniteOrder A] [PartialOrder B] [LocallyFiniteOrder B]
variable [DecidableEq A] [DecidableEq B]
variable (e : A ↪o B) (rk : A → ℕ) (strict : StrictMono rk)
include strict
theorem mu_eq_of_interval_embedding (a b : A)
    (cover : ∀ y, e a ≤ y → y ≤ e b → ∃ x, e x = y) :
    IncidenceAlgebra.mu ℤ (e a) (e b) = IncidenceAlgebra.mu ℤ a b := by
  classical
  generalize he : rk b = n
  induction n using Nat.strong_induction_on generalizing b with
  | h n ih =>
    rw [IncidenceAlgebra.mu_apply (e a) (e b), IncidenceAlgebra.mu_apply a b]
    by_cases hEq : a = b
    · simp [hEq]
    · rw [ite_eq_right hEq, ite_eq_right (fun h => hEq (e.injective h))]
      congr 1
      symm
      refine sum_bij (fun x _ => e x) ?_ ?_ ?_ ?_
      · intro x hx
        obtain ⟨ha,hb⟩ := mem_Ico.mp hx
        exact mem_Ico.mpr ⟨e.monotone ha,e.strictMono hb⟩
      · intro x _ y _ h
        exact e.injective h
      · intro y hy
        obtain ⟨ha,hb⟩ := mem_Ico.mp hy
        obtain ⟨x,rfl⟩ := cover y ha hb.le
        exact ⟨x, mem_Ico.mpr ⟨e.le_iff_le.mp ha,e.lt_iff_lt.mp hb⟩, rfl⟩
      · intro x hx
        have hxb := (mem_Ico.mp hx).2
        have hlt := strict hxb
        rw [he] at hlt
        symm
        apply ih (rk x) hlt x ?_ rfl
        intro y hy₁ hy₂
        exact cover y hy₁ (hy₂.trans (e.monotone hxb.le))
end Transport
section Actual
variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V] [Finite V]
variable [LocallyFiniteOrder (Submodule K V)]
def flatSubspaceEmbedding (S : Set V) :
    Flats (representedMatroid (K:=K) S) ↪o Submodule K V :=
  (representedFlatIso (K:=K) S).symm.toOrderEmbedding.trans (OrderEmbedding.subtype _)
omit [Finite K] [LocallyFiniteOrder (Submodule K V)] in
theorem flatSubspaceEmbedding_rank (S : Set V) (a : Flats (representedMatroid (K:=K) S)) :
    flatRank (representedMatroid (K:=K) S) a = finrank K (flatSubspaceEmbedding S a) := by
  have h := representedFlatIso_rank S ((representedFlatIso (K:=K) S).symm a)
  rw [OrderIso.apply_symm_apply] at h
  exact h
omit [Finite K] [LocallyFiniteOrder (Submodule K V)] in
theorem interval_survives (S : Set V) (hS : LinePreserving (K:=K) S)
    (a : Flats (representedMatroid (K:=K) S)) (ha : 0 < flatRank (representedMatroid (K:=K) S) a)
    (y : Submodule K V) (hay : flatSubspaceEmbedding S a ≤ y) :
    ∃ x, flatSubspaceEmbedding S x = y := by
  let e := representedFlatIso (K:=K) S
  have ha' : 0 < finrank K (flatSubspaceEmbedding S a) := by
    rwa [← flatSubspaceEmbedding_rank]
  have hy := Submodule.finrank_mono hay
  by_cases h₂ : 2 ≤ finrank K y
  · let Y : Surviving (K:=K) S := ⟨y, span_trace_eq_of_linePreserving S hS y h₂⟩
    refine ⟨e Y, ?_⟩
    change (e.symm (e Y)).val = y
    rw [OrderIso.symm_apply_apply]
  · have hh : flatSubspaceEmbedding S a = y := eq_of_le_of_finrank_le hay (by omega)
    exact ⟨a,hh⟩
theorem represented_signedMu_nonzero (S : Set V) (hS : LinePreserving (K:=K) S)
    (a b : Flats (representedMatroid (K:=K) S)) (hab : a ≤ b)
    (ha : 0 < flatRank (representedMatroid (K:=K) S) a) :
    matroidSignedMu (representedMatroid (K:=K) S) a b =
      (Nat.card K : ℤ)^((flatRank (representedMatroid (K:=K) S) b -
        flatRank (representedMatroid (K:=K) S) a).choose 2) := by
  classical
  let M := representedMatroid (K:=K) S
  let e := flatSubspaceEmbedding (K:=K) S
  have h := mu_eq_of_interval_embedding e (flatRank M) (flatRank_strict M) a b
    (fun y hy _ => interval_survives S hS a ha y hy)
  have hmu := subspace_signedMu_closed (e a) (e b) (e.monotone hab)
  change (-1 : ℤ)^(finrank K (e b)-finrank K (e a)) *
    IncidenceAlgebra.mu ℤ (e a) (e b) = _ at hmu
  rw [h, ← flatSubspaceEmbedding_rank S a, ← flatSubspaceEmbedding_rank S b] at hmu
  exact hmu
end Actual
#print axioms represented_signedMu_nonzero
end InverseZProjective.GaussianIncidence
