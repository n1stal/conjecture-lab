module
public import InverseZProjective.ProjectiveProfile
@[expose] public section
set_option autoImplicit false
namespace InverseZProjective.GaussianIncidence
open Module Submodule Finset InverseZ.Algebra InverseZProjective.ProjectiveTrace InverseZProjective.ProjectiveBridge
variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V] [Finite V] [LocallyFiniteOrder (Submodule K V)]
variable (S : Set V)
open scoped Classical
local notation "M" => representedMatroid (K:=K) S
local notation "r" => flatRank M
local notation "O" => bottomFlat M
local notation "q" => (Nat.card K : ℤ)

noncomputable def projA (f : Flats M) : ℤ := matroidSignedMu M O f
noncomputable def projB (f : Flats M) : ℤ :=
  ((deletedInFlat S f).card : ℤ) * qInteger (Nat.card K) (r f-2) * q^((r f-2).choose 2)

omit [Finite K] [LocallyFiniteOrder (Submodule K V)] in
theorem projA_bottom : projA S O = 1 := by
  delta projA matroidSignedMu
  exact signedMu_self _ _

omit [Finite K] in
theorem projB_small (f : Flats M) (hf : r f ≤ 2) : projB S f = 0 := by
  simp [projB, Nat.sub_eq_zero_of_le hf, qInteger]

omit [Finite K] [LocallyFiniteOrder (Submodule K V)] in
private theorem layer_rank {b f : Flats M} {j : ℕ} (hf : f ∈ layer r O b j) :
    r f = j := by
  have hh := ((mem_layer r).mp hf).2
  simpa only [flatRank_bottom,Nat.sub_zero] using hh

private theorem on_layer_upper (hS : LinePreserving (K:=K) S)
    {b f : Flats M} {j : ℕ} (hj : 0 < j) (hf : f ∈ layer r O b j) :
    matroidSignedMu M f b = q^((r b-j).choose 2) := by
  rw [represented_signedMu_nonzero S hS f b ((mem_layer r).mp hf).1.2
    (by rw [layer_rank S hf]; exact hj),layer_rank S hf]

private theorem on_layer_A (hS : LinePreserving (K:=K) S)
    {b f : Flats M} {j : ℕ} (hj : 0 < j) (hf : f ∈ layer r O b j) :
    projA S f = q^(j.choose 2) - ((deletedInFlat S f).card : ℤ) * q^((j-1).choose 2) := by
  have h := represented_signedMu_bottom S hS f (j-1)
    ((layer_rank S hf).trans (by omega))
  exact h.trans (by rw [show j-1+1=j by omega])

omit [Finite K] in
private theorem on_layer_B {b f : Flats M} {j : ℕ} (hf : f ∈ layer r O b j) :
    projB S f = ((deletedInFlat S f).card : ℤ) * qInteger (Nat.card K) (j-2) * q^((j-2).choose 2) := by
  rw [projB,layer_rank S hf]

/-- The constant-degree bucket at every positive absolute rank. The exceptional
    atom layer is treated by subtracting missing atoms rather than their incidences. -/
theorem projective_constant_bucket (hS : LinePreserving (K:=K) S) (b : Flats M)
    (j : ℕ) (hj : 0 < j) :
    (∑ f ∈ layer r O b j, matroidSignedMu M f b * projA S f) =
      q^((r b-j).choose 2) *
        ((gaussianCount K (r b) j : ℤ)*q^(j.choose 2) -
          ((deletedInFlat S b).card : ℤ) * gaussianCount K (r b-1) (j-1) * q^((j-1).choose 2)) := by
  classical
  by_cases h₁ : j = 1
  · subst j
    have hc := card_layer_one_add_deleted S hS b
    have hi := congrArg (fun t : ℕ => (t : ℤ)) hc
    simp only [Nat.cast_add] at hi
    calc
      _ = ∑ _f ∈ layer r O b 1, q^((r b-1).choose 2) := by
        apply sum_congr rfl
        intro f hf
        rw [on_layer_upper S hS (by omega) hf, projA,
          represented_signedMu_bottom S hS f 0 (layer_rank S hf)]
        have hz : deletedInFlat S f = ∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro p hp
          have h₁p := deleted_mem_rank_one S hS f p hp
          have hle : p ≤ flatSubspaceEmbedding S f := (mem_Ioc.mp (mem_filter.mp hp).1).2
          have he := eq_of_le_of_finrank_le hle (by
            rw [← flatSubspaceEmbedding_rank S f,layer_rank S hf,h₁p])
          exact (mem_filter.mp hp).2 ⟨f,he.symm⟩
        norm_num [hz]
      _ = _ := by
        norm_num [gaussianCount_zero]
        have he : (((layer r O b 1).card : ℕ) : ℤ) = (gaussianCount K (r b) 1 : ℤ) - ((deletedInFlat S b).card : ℤ) := by omega
        rw [he]
        ring
  · have hj' : 2 ≤ j := by omega
    calc
      _ = ∑ f ∈ layer r O b j, q^((r b-j).choose 2) *
          (q^(j.choose 2)-((deletedInFlat S f).card : ℤ)*q^((j-1).choose 2)) := by
        exact sum_congr rfl (fun f hf => by rw [on_layer_upper S hS hj hf,on_layer_A S hS hj hf])
      _ = _ := by
        rw [← mul_sum, sum_sub_distrib, ← sum_mul, deleted_incidence_mass S hS b j hj']
        simp [card_layer_high S hS b j hj']

theorem projective_linear_bucket (hS : LinePreserving (K:=K) S) (b : Flats M)
    (j : ℕ) (hj : 2 ≤ j) :
    (∑ f ∈ layer r O b j, matroidSignedMu M f b * projB S f) =
      q^((r b-j).choose 2) *
        (((deletedInFlat S b).card : ℤ)*gaussianCount K (r b-1) (j-1)*qInteger (Nat.card K) (j-2)*q^((j-2).choose 2)) := by
  calc
    _ = ∑ f ∈ layer r O b j, q^((r b-j).choose 2) *
        (((deletedInFlat S f).card : ℤ)*qInteger (Nat.card K) (j-2)*q^((j-2).choose 2)) := by
      exact sum_congr rfl (fun f hf => by rw [on_layer_upper S hS (by omega) hf,on_layer_B S hf])
    _ = _ := by rw [← mul_sum, ← sum_mul, ← sum_mul, deleted_incidence_mass S hS b j hj]

#print axioms projective_constant_bucket
#print axioms projective_linear_bucket
end InverseZProjective.GaussianIncidence
