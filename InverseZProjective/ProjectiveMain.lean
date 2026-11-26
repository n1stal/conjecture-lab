module
public import InverseZProjective.ProjectiveAnalytic
public import InverseZProofs.MobiusPositive
@[expose] public section
set_option autoImplicit false
namespace InverseZProjective.GaussianIncidence
open Module Submodule InverseZ.Algebra InverseZProjective.ProjectiveTrace
variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V] [Finite V]

private theorem product_strict (a b c x y z : ℤ)
    (hx : 0 < x) (hz : 0 < z) (h1 : a*c < b*b) (h2 : x*z ≤ y*y) :
    (a*x)*(c*z) < (b*y)*(b*y) := by
  have hp := Int.mul_pos hx hz
  have hm := Int.mul_lt_mul_of_pos_right h1 hp
  have hr := Int.mul_le_mul_of_nonneg_left h2 (show 0 ≤ b*b by simpa only [pow_two] using sq_nonneg b)
  have swap (u v w x : ℤ) : (u*v)*(w*x) = (u*w)*(v*x) := by ac_rfl
  rw [swap a x c z, swap b y b y]
  exact Int.lt_of_lt_of_le hm hr

/-- On a finite vector space, keep a set of representatives containing two
    nonparallel vectors in every two-dimensional subspace. The inverse Z
    polynomial of the actual represented matroid has positive coefficients
    throughout its rank and is strictly log-concave at every interior degree.
    For one nonzero representative per retained projective point this is
    exactly the line-preserving projective restriction theorem. -/
theorem represented_inverseZ_strict_logConcave (S : Set V) (hS : LinePreserving (K:=K) S) :
    (∀ i, i ≤ (representedMatroid (K:=K) S).eRank.toNat →
      0 < (matroidInverseZ (representedMatroid (K:=K) S)).coeff i) ∧
    (∀ i, i+2 ≤ (representedMatroid (K:=K) S).eRank.toNat →
      (matroidInverseZ (representedMatroid (K:=K) S)).coeff i *
        (matroidInverseZ (representedMatroid (K:=K) S)).coeff (i+2) <
      (matroidInverseZ (representedMatroid (K:=K) S)).coeff (i+1) *
        (matroidInverseZ (representedMatroid (K:=K) S)).coeff (i+1)) := by
  classical
  let : Finite (Submodule K V) := Finite.of_injective (fun U : Submodule K V => (U : Set V))
    SetLike.coe_injective
  let : LocallyFiniteOrder (Submodule K V) := LocallyFiniteOrder.ofFiniteIcc fun _ _ => Set.toFinite _
  let M := representedMatroid (K:=K) S
  let b := topFlat M
  let n := flatRank M b
  let P := matroidInverseZ M
  let s := profileScale K n
  let D : ℤ := (deletedInFlat S b).card
  let A := gaussianA K n
  let F := projectiveFactor K n D
  change (∀ i, i ≤ M.eRank.toNat → 0 < P.coeff i) ∧ _
  have hr : n = M.eRank.toNat := flatRank_top M
  by_cases hn : 0 < n
  · have hs : 0 < s := profileScale_pos K n hn
    have heq (i : ℕ) (hi : i ≤ n) : s * P.coeff i = A i * F i :=
      projective_source_coefficient S hS i hi hn
    have hd : 0 ≤ D := Int.natCast_nonneg _
    have hk : 0 < profileEndpoint K n D := by
      have hp := InverseZ.matroid_signed_mobius_positive M b
      have hh := projective_scaled_zero S hS b hn
      rw [projective_layer_zero S b,projA] at hh
      change s * matroidSignedMu M (bottomFlat M) b =
        A 0 * projectiveFactor K n D 0 at hh
      have hf : projectiveFactor K n D 0 = profileEndpoint K n D := by simp [projectiveFactor]
      rw [hf] at hh
      have hpos := mul_pos hs hp
      rw [hh] at hpos
      exact pos_of_mul_pos_right hpos (gaussianA_pos K n 0 (Nat.zero_le _)).le
    have hf (i : ℕ) : 0 < F i := projectiveFactor_pos K n D i hd hk
    constructor
    · intro i hi
      have hi' : i ≤ n := by omega
      have hp := mul_pos (gaussianA_pos K n i hi') (hf i)
      rw [← heq i hi'] at hp
      exact pos_of_mul_pos_right hp hs.le
    · intro i hi
      change i+2 ≤ M.eRank.toNat at hi
      have hi' : i+2 ≤ n := by omega
      have hA := gaussianA_strict K n i hi'
      have hF := projectiveFactor_logConcave K n D i hi' hd hk
      have h := product_strict _ _ _ _ _ _ (hf i) (hf (i+2)) hA hF
      change (A i * F i)*(A (i+2)*F (i+2)) < (A (i+1)*F (i+1))*(A (i+1)*F (i+1)) at h
      rw [← heq i (by omega),← heq (i+2) hi',← heq (i+1) (by omega)] at h
      have swap (x y : ℤ) : (s*x)*(s*y) = (s*s)*(x*y) := by ac_rfl
      rw [swap,swap] at h
      exact lt_of_mul_lt_mul_left h (show 0 ≤ s*s by simpa only [pow_two] using sq_nonneg s)
  · constructor
    · intro i hi
      have hz : i = M.eRank.toNat := by omega
      subst i
      rw [matroidInverseZ_top_coeff]
      exact InverseZ.matroid_signed_mobius_positive M b
    · intro i hi
      change i+2 ≤ M.eRank.toNat at hi
      omega

#print axioms represented_inverseZ_strict_logConcave
end InverseZProjective.GaussianIncidence
