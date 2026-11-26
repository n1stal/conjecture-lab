module
public import InverseZProjective.GaussianMobius
@[expose] public section
set_option autoImplicit false
namespace InverseZProjective.GaussianIncidence
open Module Submodule Finset InverseZ.Algebra
theorem mobiusWeight_closed (q : ℤ) (n : ℕ) :
    mobiusWeight q n = (-1)^n * q^(n.choose 2) := by
  induction n with
  | zero => simp [mobiusWeight]
  | succ n ih =>
    have he : (n+1).choose 2 = n.choose 2+n := by
      have h := Nat.choose_succ_succ' n 1
      rw [Nat.choose_one_right] at h
      exact h.trans (Nat.add_comm _ _)
    calc
      _ = -(q^n*((-1 : ℤ)^n * q^(n.choose 2))) := by rw [mobiusWeight_succ, ih]
      _ = ((-1 : ℤ)^n * (-1)) * (q^(n.choose 2) * q^n) := by ring
      _ = _ := by rw [← pow_succ, ← pow_add, ← he]
section
variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V]
variable [LocallyFiniteOrder (Submodule K V)] [DecidableEq (Submodule K V)]
omit [Finite K] in
private theorem layer_card_subspace (U W : Submodule K V) (hUW : U ≤ W) (i : ℕ) :
    (layer (fun X : Submodule K V => finrank K X) U W i).card =
      gaussianCount K (finrank K W-finrank K U) i := by
  classical
  let F := layer (fun X : Submodule K V => finrank K X) U W i
  let e : F ≃ {X : Set.Icc U W // finrank K X.val-finrank K U=i} :=
    { toFun := fun x =>
        let h := (mem_layer (fun X : Submodule K V => finrank K X)).mp x.property
        ⟨⟨x.val,h.1⟩,h.2⟩
      invFun := fun x => ⟨x.val.val,(mem_layer (fun X : Submodule K V => finrank K X)).mpr
        ⟨x.val.property,x.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hh := Nat.card_congr e
  rw [Nat.card_eq_fintype_card, Fintype.card_coe, card_subspace_interval_layer U W hUW] at hh
  exact hh
theorem subspace_mu_closed (U W : Submodule K V) (hUW : U ≤ W) :
    IncidenceAlgebra.mu ℤ U W =
      (-1 : ℤ)^(finrank K W-finrank K U) *
        (Nat.card K : ℤ)^((finrank K W-finrank K U).choose 2) := by
  rw [← mobiusWeight_closed]
  exact mu_eq_of_gaussian_layer_card (fun X : Submodule K V => finrank K X)
    (fun _ _ h => Submodule.finrank_lt_finrank_of_lt h) layer_card_subspace hUW
theorem subspace_signedMu_closed (U W : Submodule K V) (hUW : U ≤ W) :
    signedMu (fun X : Submodule K V => finrank K X) U W =
      (Nat.card K : ℤ)^((finrank K W-finrank K U).choose 2) := by
  unfold signedMu
  rw [subspace_mu_closed U W hUW, ← mul_assoc, ← mul_pow]
  norm_num
end
#print axioms subspace_signedMu_closed
end InverseZProjective.GaussianIncidence
