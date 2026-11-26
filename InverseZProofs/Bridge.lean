module

public import InverseZProofs.Central
public import InverseZProofs.BooleanBase
public import InverseZProofs.MatroidPointLine
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace InverseZ.Algebra
open Finset Polynomial Matroid
open scoped BigOperators ENat

variable {α : Type*} [Finite α] (M : Matroid α)

theorem coe_flatRank (F : Flats M) : (flatRank M F : ℕ∞) = M.eRk F.val :=
  ENat.natCast_toNat ((M.eRk_le_encard F.val).trans_lt (Set.toFinite F.val).encard_lt_top).ne

theorem layer_rank_iff {F G : Flats M} {k : ℕ} :
    F ∈ layer (flatRank M) (bottomFlat M) G k ↔ M.eRk F.val = k ∧ F ≤ G := by
  classical
  rw [mem_layer, flatRank_bottom, Nat.sub_zero, and_comm]
  rw [← ENat.natCast_inj, coe_flatRank]
  exact and_congr_right (fun _ => and_iff_right (bottomFlat_le M F))

noncomputable def layerEquiv (G : Flats M) (k : ℕ) :
    (layer (flatRank M) (bottomFlat M) G k) ≃
      {F : FlatAt M (k : ℕ∞) // F.val ⊆ G.val} where
  toFun F := ⟨⟨F.val, F.val.property, ((layer_rank_iff M).mp F.property).1⟩,
    ((layer_rank_iff M).mp F.property).2⟩
  invFun F := ⟨⟨F.val.val,F.val.property.1⟩,
    (layer_rank_iff M).mpr ⟨F.val.property.2, F.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def topLayerEquiv (k : ℕ) :
    (layer (flatRank M) (bottomFlat M) (topFlat M) k) ≃ FlatAt M (k : ℕ∞) where
  toFun F := (layerEquiv M (topFlat M) k F).val
  invFun F := (layerEquiv M (topFlat M) k).symm ⟨F, F.property.1.subset_ground⟩
  left_inv F := by
    change (layerEquiv M (topFlat M) k).symm (layerEquiv M (topFlat M) k F) = F
    exact Equiv.symm_apply_apply _ _
  right_inv F := by
    change ((layerEquiv M (topFlat M) k)
      ((layerEquiv M (topFlat M) k).symm ⟨F, F.property.1.subset_ground⟩)).val = F
    rw [Equiv.apply_symm_apply]

theorem W_eq_card (k : ℕ) :
    W (flatRank M) (bottomFlat M) (topFlat M) k = Nat.card (FlatAt M (k : ℕ∞)) := by
  rw [← Nat.card_congr (topLayerEquiv M k), Nat.card_eq_fintype_card, Fintype.card_coe]
  rfl

abbrev IncidentAt (i j : ℕ) :=
  {p : FlatAt M (i : ℕ∞) × FlatAt M (j : ℕ∞) // p.1.val ⊆ p.2.val}

abbrev IncidentSigma (i j : ℕ) :=
  Σ G : layer (flatRank M) (bottomFlat M) (topFlat M) j,
    layer (flatRank M) (bottomFlat M) G.val i

noncomputable def incidentEquiv (i j : ℕ) :
    IncidentSigma M i j ≃ IncidentAt M i j where
  toFun v := ⟨((layerEquiv M v.1.val i v.2).val, topLayerEquiv M j v.1),
    (layerEquiv M v.1.val i v.2).property⟩
  invFun v := by
    let G := (topLayerEquiv M j).symm v.val.2
    refine ⟨G,(layerEquiv M G.val i).symm ⟨v.val.1, ?_⟩⟩
    exact v.property
  left_inv v := by
    rcases v with ⟨G,F⟩
    rfl
  right_inv v := by
    rcases v with ⟨⟨F,G⟩,h⟩
    rfl

theorem I_eq_card (i j : ℕ) :
    I (flatRank M) (bottomFlat M) (topFlat M) i j = Nat.card (IncidentAt M i j) := by
  classical
  rw [← Nat.card_congr (incidentEquiv M i j), Nat.card_eq_fintype_card]
  unfold IncidentSigma
  rw [Fintype.card_sigma]
  simp only [Fintype.card_coe, Nat.cast_sum, I, W]
  exact (Finset.sum_coe_sort (layer (flatRank M) (bottomFlat M) (topFlat M) j)
    (fun F => ((layer (flatRank M) (bottomFlat M) F i).card : ℤ))).symm

theorem singleton_indep_of_pairs
    (pairs : ∀ p ∈ M.E, ∀ q ∈ M.E, p ≠ q → M.Indep ({p,q} : Set α))
    (hg : 1 < M.E.encard) (p : M.E) : M.Indep ({p.val} : Set α) := by
  obtain ⟨q,hq,hne⟩ := Set.exists_ne_of_one_lt_encard hg p.val
  exact (pairs p.val p.property q hq (Ne.symm hne)).subset (by simp)

theorem singleton_flat_of_pairs
    (pairs : ∀ p ∈ M.E, ∀ q ∈ M.E, p ≠ q → M.Indep ({p,q} : Set α))
    (p : M.E) : M.IsFlat ({p.val} : Set α) := by
  apply Matroid.isFlat_iff_closure_eq.mpr
  apply Set.Subset.antisymm _ (M.subset_closure _ (Set.singleton_subset_iff.mpr p.property))
  intro q hq
  by_contra hne
  have epq : p.val ≠ q := fun e => hne (Set.mem_singleton_iff.mpr e.symm)
  have hI := pairs p.val p.property q (M.closure_subset_ground _ hq) epq
  have hcl := hI.closure_inter_eq_self_of_subset
    (show ({p.val} : Set α) ⊆ ({p.val,q} : Set α) by simp)
  exact hne (hcl ▸ Set.mem_inter hq (by simp : q ∈ ({p.val,q} : Set α)))

/-- For a simple matroid of ground size at least two, its points are exactly the
    singleton rank-one flats. -/
noncomputable def pointEquiv
    (pairs : ∀ p ∈ M.E, ∀ q ∈ M.E, p ≠ q → M.Indep ({p,q} : Set α))
    (hg : 1 < M.E.encard) : M.E ≃ FlatAt M 1 := by
  classical
  let f (p : M.E) : FlatAt M 1 := ⟨{p.val}, singleton_flat_of_pairs M pairs p, by
    rw [(singleton_indep_of_pairs M pairs hg p).eRk_eq_encard, Set.encard_singleton]⟩
  apply Equiv.ofBijective f
  constructor
  · intro p q he
    exact Subtype.ext (Set.singleton_eq_singleton_iff.mp (congrArg Subtype.val he))
  · intro F
    obtain ⟨B,hB⟩ := M.exists_isBasis F.val F.property.1.subset_ground
    obtain ⟨p,hp⟩ := Set.encard_eq_one.mp (hB.encard_eq_eRk.trans F.property.2)
    have hpF : p ∈ F.val := hB.subset (hp.symm ▸ Set.mem_singleton p)
    let q : M.E := ⟨p,F.property.1.subset_ground hpF⟩
    refine ⟨q,Subtype.ext ?_⟩
    change ({p} : Set α) = F.val
    calc
      {p} = M.closure {p} := (singleton_flat_of_pairs M pairs q).closure.symm
      _ = M.closure F.val := by simpa [hp] using hB.closure_eq_closure
      _ = F.val := F.property.1.closure

theorem W_one_eq_ground_card
    (pairs : ∀ p ∈ M.E, ∀ q ∈ M.E, p ≠ q → M.Indep ({p,q} : Set α))
    (hg : 1 < M.E.encard) :
    W (flatRank M) (bottomFlat M) (topFlat M) 1 = Nat.card M.E := by
  rw [W_eq_card]
  exact congrArg (fun n : ℕ => (n : ℤ)) (Nat.card_congr (pointEquiv M pairs hg)).symm

#print axioms W_eq_card
#print axioms I_eq_card
#print axioms pointEquiv
#print axioms W_one_eq_ground_card
end InverseZ.Algebra
