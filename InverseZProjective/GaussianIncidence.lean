module
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
@[expose] public section
set_option autoImplicit false
namespace InverseZProjective.GaussianIncidence
open Module Submodule
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]
abbrev RankSubspaces (K V : Type*) [Field K] [AddCommGroup V] [Module K V] (k : ℕ) :=
  {U : Submodule K V // finrank K U = k}
noncomputable def gaussianCount (K : Type*) [Field K] (n k : ℕ) : ℕ :=
  Nat.card (RankSubspaces K (Fin n → K) k)
def rankSubspaceEquiv (e : V ≃ₗ[K] W) (k : ℕ) :
    RankSubspaces K V k ≃ RankSubspaces K W k :=
  (orderIsoMapComap e).toEquiv.subtypeEquiv (fun U => by
    change finrank K U = k ↔ finrank K (U.map e.toLinearMap) = k
    rw [e.finrank_map_eq])
variable [FiniteDimensional K V]
theorem card_rankSubspaces (k : ℕ) :
    Nat.card (RankSubspaces K V k) = gaussianCount K (finrank K V) k :=
  Nat.card_congr (rankSubspaceEquiv (Module.finBasis K V).equivFun k)
private theorem rank_mkQ_map_add (U X : Submodule K V) (hUX : U ≤ X) :
    finrank K (X.map U.mkQ) + finrank K U = finrank K X := by
  let f := U.mkQ.domRestrict X
  have hr := f.finrank_range_add_finrank_ker
  have hker : f.ker = U.comap X.subtype := by
    ext x
    change U.mkQ x.val = 0 ↔ x.val ∈ U
    exact Quotient.mk_eq_zero U
  have hRange : f.range = X.map U.mkQ := LinearMap.range_domRestrict _ _
  rw [hRange, hker, (Submodule.comapSubtypeEquivOfLe hUX).finrank_eq] at hr
  exact hr
theorem rank_comapMkQRelIso_add (U : Submodule K V) (X : Submodule K (V ⧸ U)) :
    finrank K X + finrank K U = finrank K ((comapMkQRelIso U X).val) := by
  let Y := comapMkQRelIso U X
  have h := rank_mkQ_map_add U Y.val Y.property
  change finrank K ((comapMkQRelIso U).symm Y) + finrank K U = _ at h
  rw [(comapMkQRelIso U).symm_apply_apply] at h
  exact h
def rankSubspacesAboveEquiv (U : Submodule K V) (k : ℕ) :
    RankSubspaces K (V ⧸ U) k ≃
      {X : Set.Ici U // finrank K X.val = k + finrank K U} :=
  (comapMkQRelIso U).toEquiv.subtypeEquiv (fun X => by
    change finrank K X = k ↔ finrank K ((comapMkQRelIso U X).val) = k + finrank K U
    have h := rank_comapMkQRelIso_add U X
    omega)
theorem card_rankSubspaces_above (U : Submodule K V) (k : ℕ) :
    Nat.card {X : Set.Ici U // finrank K X.val = k + finrank K U} =
      gaussianCount K (finrank K V-finrank K U) k := by
  rw [Nat.card_congr (rankSubspacesAboveEquiv U k).symm, card_rankSubspaces,
    Submodule.finrank_quotient]
theorem card_rankSubspaces_above_point (U : Submodule K V) (hU : finrank K U = 1) (k : ℕ) :
    Nat.card {X : Set.Ici U // finrank K X.val = k+1} =
      gaussianCount K (finrank K V-1) k := by
  simpa only [hU] using card_rankSubspaces_above U k
#print axioms card_rankSubspaces_above_point
end InverseZProjective.GaussianIncidence
