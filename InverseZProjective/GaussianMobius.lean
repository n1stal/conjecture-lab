module
public import InverseZProjective.GaussianPascal
public import InverseZProofs.Coefficients
@[expose] public section
set_option autoImplicit false
namespace InverseZProjective.GaussianIncidence
open Module Submodule Finset InverseZ.Algebra
section Interval
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
theorem card_subspace_interval_layer (U W : Submodule K V) (hUW : U ≤ W) (i : ℕ) :
    Nat.card {X : Set.Icc U W // finrank K X.val - finrank K U = i} =
      gaussianCount K (finrank K W - finrank K U) i := by
  let U' := U.comap W.subtype
  have hU' : finrank K U' = finrank K U := (comapSubtypeEquivOfLe hUW).finrank_eq
  let e : Set.Ici U' ≃ Set.Icc U W :=
    { toFun := fun X =>
        let Y := W.mapIic X.val
        ⟨Y.val, by
          change U ≤ X.val.map W.subtype
          have hh : (U.comap W.subtype).map W.subtype = U := by
            rw [Submodule.map_comap_subtype, inf_eq_right.mpr hUW]
          exact hh ▸ Submodule.map_mono (f:=W.subtype) X.property, Y.property⟩
      invFun := fun Y => ⟨Y.val.comap W.subtype, Submodule.comap_mono Y.property.1⟩
      left_inv := fun X => by
        apply Subtype.ext
        exact W.mapIic.symm_apply_apply X.val
      right_inv := fun Y => by
        apply Subtype.ext
        change (Y.val.comap W.subtype).map W.subtype = Y.val
        rw [Submodule.map_comap_subtype, inf_eq_right.mpr Y.property.2] }
  let e' := e.subtypeEquiv (p := fun X => finrank K X.val = i+finrank K U')
    (q := fun X => finrank K X.val - finrank K U = i) (fun X => by
      change _ ↔ finrank K (X.val.map W.subtype) - finrank K U = i
      rw [Submodule.finrank_map_subtype_eq,hU']
      have hle := Submodule.finrank_mono X.property
      rw [hU'] at hle
      omega)
  rw [Nat.card_congr e'.symm, card_rankSubspaces_above, hU']
end Interval
section Ranked
variable {K L : Type*} [Field K] [Finite K]
variable [PartialOrder L] [LocallyFiniteOrder L] [DecidableEq L]
variable (rk : L → ℕ) (strict : StrictMono rk)
include strict
theorem mu_eq_of_gaussian_layer_card
    (hc : ∀ a b, a ≤ b → ∀ i, (layer rk a b i).card = gaussianCount K (rk b-rk a) i)
    {a b : L} (hab : a ≤ b) :
    IncidenceAlgebra.mu ℤ a b = mobiusWeight (Nat.card K) (rk b-rk a) := by
  classical
  by_cases e : a = b
  · subst b
    simp [mobiusWeight]
  have hlt : a < b := lt_of_le_of_ne hab e
  obtain ⟨n, hn⟩ : ∃ n : ℕ, rk b-rk a = n+1 :=
    ⟨rk b-rk a-1, by have hh := strict hlt; omega⟩
  have hwt :
      ∑ x ∈ Icc a b, mobiusWeight (Nat.card K) (rk x-rk a) = 0 := by
    rw [closed_sum_layers rk strict (fun x => mobiusWeight (Nat.card K) (rk x-rk a)) hn]
    calc
      _ = ∑ i ∈ range (n+2), (gaussianCount K (n+1) i : ℤ)*mobiusWeight (Nat.card K) i := by
        apply sum_congr rfl
        intro i _
        have hx : ∀ x ∈ layer rk a b i, rk x-rk a = i := fun _ h => ((mem_layer rk).mp h).2
        rw [sum_congr rfl (fun x h => congrArg (mobiusWeight (Nat.card K)) (hx x h))]
        simp [hc a b hab i, hn]
      _ = 0 := gaussian_mobius_sum K n
  have hmu := IncidenceAlgebra.sum_Icc_mu_right (𝕜:=ℤ) a b
  have hcut : Icc a b = insert b (Ico a b) := by
    ext x
    simp only [mem_Icc,mem_Ico,mem_insert]
    constructor
    · intro hx
      exact (eq_or_lt_of_le hx.2).elim Or.inl (fun hh => Or.inr ⟨hx.1,hh⟩)
    · rintro (rfl|hx)
      · exact ⟨hab,le_rfl⟩
      · exact ⟨hx.1,hx.2.le⟩
  rw [hcut, sum_insert (by simp : b ∉ Ico a b), ite_eq_right e] at hmu
  rw [hcut, sum_insert (by simp : b ∉ Ico a b)] at hwt
  have hsame : ∑ x ∈ Ico a b, IncidenceAlgebra.mu ℤ a x =
      ∑ x ∈ Ico a b, mobiusWeight (Nat.card K) (rk x-rk a) := by
    apply sum_congr rfl
    intro x hx
    exact mu_eq_of_gaussian_layer_card hc (mem_Ico.mp hx).1
  rw [hsame] at hmu
  omega
termination_by rk b
decreasing_by all_goals exact strict (mem_Ico.mp hx).2
end Ranked
#print axioms card_subspace_interval_layer
#print axioms mu_eq_of_gaussian_layer_card
end InverseZProjective.GaussianIncidence
