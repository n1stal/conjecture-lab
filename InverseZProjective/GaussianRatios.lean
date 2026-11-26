module
public import InverseZProjective.GaussianIncidence
public import Mathlib.LinearAlgebra.Projectivization.Cardinality
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Data.Fintype.BigOperators
@[expose] public section
set_option autoImplicit false
namespace InverseZProjective.GaussianIncidence
open Module Submodule
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V]
theorem gaussianCount_symm (k : ℕ) (hk : k ≤ finrank K V) :
    gaussianCount K (finrank K V) k = gaussianCount K (finrank K V) (finrank K V-k) := by
  let e : Submodule K V ≃ Submodule K (Module.Dual K V) :=
    (Subspace.orderIsoFiniteDimensional (K:=K) (V:=V)).toEquiv
  let f : RankSubspaces K V k ≃ RankSubspaces K (Module.Dual K V) (finrank K V-k) :=
    e.subtypeEquiv (fun U => by
      change finrank K U = k ↔ finrank K U.dualAnnihilator = finrank K V-k
      have h := Subspace.finrank_add_finrank_dualAnnihilator_eq U
      omega)
  have H := Nat.card_congr f
  rw [card_rankSubspaces, card_rankSubspaces, Subspace.dual_finrank_eq] at H
  exact H
def rankSubspacesBelowEquiv (U : Submodule K V) (k : ℕ) :
    RankSubspaces K U k ≃ {X : Set.Iic U // finrank K X.val = k} :=
  U.mapIic.toEquiv.subtypeEquiv (fun X => by
    change finrank K X = k ↔ finrank K (X.map U.subtype) = k
    rw [Submodule.finrank_map_subtype_eq])
private theorem card_sigma_uniform {A : Type*} {B : A → Type*} [Finite A] [∀ x, Finite (B x)]
    (m : ℕ) (h : ∀ a, Nat.card (B a) = m) :
    Nat.card (Sigma B) = Nat.card A * m := by
  classical
  let : Fintype A := Fintype.ofFinite A
  let : ∀ a, Fintype (B a) := fun _ => Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma, Nat.card_eq_fintype_card]
  simp only [Fintype.card_eq_nat_card, h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rfl
theorem gaussianCount_one [Finite K] :
    gaussianCount K (finrank K V) 1 = ∑ i ∈ Finset.range (finrank K V), Nat.card K ^ i := by
  rw [← card_rankSubspaces (K:=K) (V:=V) 1,
    ← Nat.card_congr (Projectivization.equivSubmodule K V)]
  exact Projectivization.card_of_finrank K V rfl
theorem gaussian_point_ratio [Finite V] (k : ℕ) :
    gaussianCount K (finrank K V) (k+1) * gaussianCount K (k+1) 1 =
      gaussianCount K (finrank K V) 1 * gaussianCount K (finrank K V-1) k := by
  classical
  let : Finite (Submodule K V) := Finite.of_injective (fun U : Submodule K V => (U : Set V))
    SetLike.coe_injective
  let A := RankSubspaces K V (k+1)
  let P := RankSubspaces K V 1
  let L := Σ a : A, {p : P // p.val ≤ a.val}
  let R := Σ p : P, {a : A // p.val ≤ a.val}
  let e : L ≃ R :=
    ⟨fun l => ⟨l.2.val, l.1, l.2.property⟩,
      fun r => ⟨r.2.val, r.1, r.2.property⟩,
      fun _ => rfl, fun _ => rfl⟩
  have hL (a : A) : Nat.card {p : P // p.val ≤ a.val} = gaussianCount K (k+1) 1 := by
    let g : {p : P // p.val ≤ a.val} ≃ {p : Set.Iic a.val // finrank K p.val = 1} :=
      ⟨fun p => ⟨⟨p.val.val, p.property⟩,p.val.property⟩,
        fun p => ⟨⟨p.val.val, p.property⟩,p.val.property⟩,fun _ => rfl,fun _ => rfl⟩
    rw [Nat.card_congr g, Nat.card_congr (rankSubspacesBelowEquiv a.val 1).symm, card_rankSubspaces, a.property]
  have hR (p : P) : Nat.card {a : A // p.val ≤ a.val} = gaussianCount K (finrank K V-1) k := by
    let g : {a : A // p.val ≤ a.val} ≃ {a : Set.Ici p.val // finrank K a.val = k+1} :=
      ⟨fun a => ⟨⟨a.val.val, a.property⟩,a.val.property⟩,
        fun a => ⟨⟨a.val.val, a.property⟩,a.val.property⟩,fun _ => rfl,fun _ => rfl⟩
    rw [Nat.card_congr g, card_rankSubspaces_above_point p.val p.property]
  have hl := card_sigma_uniform _ hL
  have hr := card_sigma_uniform _ hR
  have h := Nat.card_congr e
  change Nat.card L = _ at hl
  change Nat.card R = _ at hr
  rw [hl, hr] at h
  unfold A P at h
  simpa only [card_rankSubspaces] using h
theorem gaussianCount_symm_canonical (K : Type*) [Field K] (n k : ℕ) (hk : k ≤ n) :
    gaussianCount K n k = gaussianCount K n (n-k) := by
  have h : k ≤ finrank K (Fin n → K) := by rwa [Module.finrank_fin_fun]
  simpa only [Module.finrank_fin_fun] using gaussianCount_symm (K:=K) (V:=Fin n → K) k h
theorem gaussianCount_one_canonical (K : Type*) [Field K] [Finite K] (n : ℕ) :
    gaussianCount K n 1 = ∑ i ∈ Finset.range n, Nat.card K ^ i := by
  simpa only [Module.finrank_fin_fun] using gaussianCount_one (K:=K) (V:=Fin n → K)
theorem gaussian_point_ratio_canonical (K : Type*) [Field K] [Finite K] (n k : ℕ) :
    gaussianCount K n (k+1) * gaussianCount K (k+1) 1 =
      gaussianCount K n 1 * gaussianCount K (n-1) k := by
  simpa only [Module.finrank_fin_fun] using gaussian_point_ratio (K:=K) (V:=Fin n → K) k
theorem gaussian_codim_ratio_canonical (K : Type*) [Field K] [Finite K] (n i : ℕ) (hi : i < n) :
    gaussianCount K n i * gaussianCount K (n-i) 1 =
      gaussianCount K n 1 * gaussianCount K (n-1) i := by
  have h := gaussian_point_ratio_canonical K n (n-i-1)
  rw [show n-i-1+1 = n-i by omega,
    ← gaussianCount_symm_canonical K n i (by omega),
    gaussianCount_symm_canonical K (n-1) (n-i-1) (by omega),
    show n-1-(n-i-1)=i by omega] at h
  exact h
theorem gaussian_adjacent_ratio_canonical (K : Type*) [Field K] [Finite K] (n i : ℕ) (hi : i < n) :
    gaussianCount K n (i+1) * gaussianCount K (i+1) 1 =
      gaussianCount K n i * gaussianCount K (n-i) 1 :=
  (gaussian_point_ratio_canonical K n i).trans (gaussian_codim_ratio_canonical K n i hi).symm
#print axioms gaussian_adjacent_ratio_canonical
end InverseZProjective.GaussianIncidence
