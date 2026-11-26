module
public import InverseZProjective.ProjectiveWeighted
@[expose] public section
set_option autoImplicit false
namespace InverseZProjective.GaussianIncidence
open Module Finset InverseZ.Algebra InverseZProjective.ProjectiveTrace InverseZProjective.ProjectiveBridge
variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V] [Finite V] [LocallyFiniteOrder (Submodule K V)]
variable (S : Set V)
open scoped Classical
local notation "M" => representedMatroid (K:=K) S
local notation "r" => flatRank M
local notation "O" => bottomFlat M
local notation "q" => (Nat.card K : ℤ)
local notation "L" => matroidLayerCoefficient M (projA S) (projB S)

omit [Finite K] [LocallyFiniteOrder (Submodule K V)] in
private theorem constant_filter (b : Flats M) (i : ℕ) (hi : i ≤ r b) :
    (Icc O b).filter (fun f => r b-r f = i) = layer r O b (r b-i) := by
  ext f
  simp only [mem_filter, mem_layer, mem_Icc, flatRank_bottom, Nat.sub_zero]
  constructor
  · intro h
    have hh := (flatRank_strict M).monotone h.1.2
    exact ⟨h.1,by omega⟩
  · intro h
    exact ⟨h.1,by omega⟩

omit [Finite K] [LocallyFiniteOrder (Submodule K V)] in
private theorem linear_filter (b : Flats M) (i : ℕ) (hi₀ : 0 < i) (hi : i ≤ r b) :
    (Icc O b).filter (fun f => r b-r f+1 = i) = layer r O b (r b-i+1) := by
  ext f
  simp only [mem_filter, mem_layer, mem_Icc, flatRank_bottom, Nat.sub_zero]
  constructor
  · intro h
    have hh := (flatRank_strict M).monotone h.1.2
    exact ⟨h.1,by omega⟩
  · intro h
    exact ⟨h.1,by omega⟩

omit [Finite K] in
/-- The true candidate flat sum evaluated at degree zero. -/
theorem projective_layer_zero (b : Flats M) : L b 0 = projA S b := by
  classical
  delta matroidLayerCoefficient layerCoefficient
  rw [constant_filter S b 0 (by omega),Nat.sub_zero]
  have hh := layer_top r (flatRank_strict M) (bottomFlat_le M b)
  rw [flatRank_bottom,Nat.sub_zero] at hh
  rw [hh, sum_singleton]
  have he : (Icc O b).filter (fun f => r b-r f+1 = 0) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro f hf
    have := (mem_filter.mp hf).2
    omega
  rw [he,sum_empty,add_zero]
  change matroidSignedMu M b b * projA S b = _
  rw [show matroidSignedMu M b b = 1 by delta matroidSignedMu; exact signedMu_self _ _,one_mul]

omit [Finite K] in
/-- At degree equal to rank the bottom term is the signed Möbius weight and
    the only possible linear bucket is rank one, where the candidate vanishes. -/
theorem projective_layer_top (b : Flats M) :
    L b (r b) = projA S b := by
  by_cases hb : r b = 0
  · rw [hb,projective_layer_zero S b]
  classical
  delta matroidLayerCoefficient layerCoefficient
  rw [constant_filter S b (r b) le_rfl,Nat.sub_self,
    layer_zero r (flatRank_strict M) (bottomFlat_le M b),sum_singleton,
    linear_filter S b (r b) (by omega) le_rfl,Nat.sub_self,zero_add,projA_bottom S,mul_one]
  have hz : ∑ f ∈ layer r O b 1, signedMu r f b * projB S f = 0 := by
    apply sum_eq_zero
    intro f hf
    have hh := ((mem_layer r).mp hf).2
    rw [flatRank_bottom,Nat.sub_zero] at hh
    rw [projB_small S f (by omega),mul_zero]
  rw [hz,add_zero]
  rfl

/-- Evaluate both candidate rank buckets at an interior degree. -/
theorem projective_layer_interior (hS : LinePreserving (K:=K) S) (b : Flats M)
    (i : ℕ) (hi₀ : 0 < i) (hi : i < r b) :
    L b i =
      q^(i.choose 2) *
        ((gaussianCount K (r b) (r b-i) : ℤ)*q^((r b-i).choose 2) -
          ((deletedInFlat S b).card : ℤ)*gaussianCount K (r b-1) (r b-i-1)*q^((r b-i-1).choose 2)) +
      q^((i-1).choose 2) *
        (((deletedInFlat S b).card : ℤ)*gaussianCount K (r b-1) (r b-i)*
          qInteger (Nat.card K) (r b-i-1)*q^((r b-i-1).choose 2)) := by
  classical
  delta matroidLayerCoefficient layerCoefficient
  rw [constant_filter S b i hi.le,linear_filter S b i hi₀ hi.le]
  change (∑ f ∈ layer r O b (r b-i), matroidSignedMu M f b * projA S f) +
    (∑ f ∈ layer r O b (r b-i+1), matroidSignedMu M f b * projB S f) = _
  rw [projective_constant_bucket S hS b _ (by omega),projective_linear_bucket S hS b _ (by omega),
    show r b-(r b-i)=i by omega,show r b-(r b-i+1)=i-1 by omega,
    show r b-i+1-1=r b-i by omega,show r b-i+1-2=r b-i-1 by omega]
#print axioms projective_layer_top
#print axioms projective_layer_interior
end InverseZProjective.GaussianIncidence
