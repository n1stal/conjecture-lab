module

public import InverseZProofs.CountedDeletion
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

set_option autoImplicit false
namespace InverseZ
open Set Matroid

abbrev IdxSubset (k : ℕ) := {s : Finset (Fin 4) // s.card = k}
abbrev IdxInc :=
  {i : IdxSubset 2 × IdxSubset 3 // i.1.val ⊆ i.2.val}

theorem idx_line_count : Nat.card (IdxSubset 2) = 6 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem idx_plane_count : Nat.card (IdxSubset 3) = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem idx_inc_count : Nat.card IdxInc = 12 := by
  rw [Nat.card_eq_fintype_card]
  decide

variable {α : Type*} [Finite α] (M : Matroid α)

theorem indep_ground_four_card (hI : M.Indep M.E) (hr : M.eRank = 4) :
    Nat.card M.E = 4 := by
  rw [Nat.card_coe_set_eq]
  have hh := (Set.toFinite M.E).cast_ncard_eq
  rw [← hI.eRk_eq_encard, M.eRk_ground, hr] at hh
  exact (Nat.cast_inj (R := ℕ∞)).mp hh

noncomputable def groundIndex (hI : M.Indep M.E) (hr : M.eRank = 4) : Fin 4 ↪ α := by
  classical
  letI : Fintype M.E := Fintype.ofFinite M.E
  have hc : Fintype.card M.E = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact indep_ground_four_card M hI hr
  exact (Fintype.equivFinOfCardEq hc).symm.toEmbedding.trans (Function.Embedding.subtype _)

theorem groundIndex_range (hI : M.Indep M.E) (hr : M.eRank = 4) :
    Set.range (groundIndex M hI hr) = M.E := by
  classical
  let : Fintype M.E := Fintype.ofFinite M.E
  dsimp only [groundIndex,Function.Embedding.trans,Equiv.toEmbedding,
    Function.Embedding.subtype]
  ext x
  constructor
  · rintro ⟨i,rfl⟩
    exact Subtype.property _
  · intro hx
    have hc : Fintype.card M.E = 4 := (Nat.card_eq_fintype_card).symm.trans (indep_ground_four_card M hI hr)
    refine ⟨(Fintype.equivFinOfCardEq hc : M.E ≃ Fin 4) ⟨x,hx⟩, ?_⟩
    change ((Fintype.equivFinOfCardEq hc).symm ((Fintype.equivFinOfCardEq hc) ⟨x,hx⟩)).val = x
    rw [Equiv.symm_apply_apply]

noncomputable def booleanFlatIndex (hI : M.Indep M.E) (hr : M.eRank = 4) (k : ℕ) :
    IdxSubset k ≃ FlatAt M (k : ℕ∞) := by
  classical
  let f := groundIndex M hI hr
  have hrange : Set.range f = M.E := groundIndex_range M hI hr
  let fIdx (s : IdxSubset k) : FlatAt M (k : ℕ∞) := by
    refine ⟨f '' (s.val : Set (Fin 4)), ?_, ?_⟩
    · have hsub : f '' (s.val : Set (Fin 4)) ⊆ M.E :=
        hrange ▸ Set.image_subset_range _ _
      apply Matroid.isFlat_iff_closure_eq.mpr
      have hcl := hI.closure_inter_eq_self_of_subset hsub
      rw [Set.inter_eq_left.mpr (M.closure_subset_ground _)] at hcl
      exact hcl
    · have hsub : f '' (s.val : Set (Fin 4)) ⊆ M.E :=
        hrange ▸ Set.image_subset_range _ _
      rw [(hI.subset hsub).eRk_eq_encard, f.injective.encard_image,
        Set.encard_coe_eq_coe_finsetCard, s.2]
  apply Equiv.ofBijective fIdx
  constructor
  · intro a b hab
    apply Subtype.ext
    apply Finset.coe_injective
    exact Set.image_injective.mpr f.injective (congrArg Subtype.val hab)
  · intro F
    let s := (Set.toFinite (f ⁻¹' F.val)).toFinset
    have hs : (s : Set (Fin 4)) = f ⁻¹' F.val := (Set.toFinite _).coe_toFinset
    have hS : f '' (s : Set (Fin 4)) = F.val := by
      rw [hs]
      apply Set.image_preimage_eq_of_subset
      rw [hrange]
      exact F.2.1.subset_ground
    have hcard : s.card = k := by
      apply (Nat.cast_inj (R := ℕ∞)).mp
      rw [← Set.encard_coe_eq_coe_finsetCard, ← f.injective.encard_image, hS,
        ← (hI.subset F.2.1.subset_ground).eRk_eq_encard, F.2.2]
    exact ⟨⟨s,hcard⟩,Subtype.ext hS⟩

theorem booleanFlatIndex_coe (hI : M.Indep M.E) (hr : M.eRank = 4) (k : ℕ)
    (s : IdxSubset k) :
    (booleanFlatIndex M hI hr k s).val = groundIndex M hI hr '' (s.val : Set (Fin 4)) :=
  rfl

noncomputable def booleanIncIndex (hI : M.Indep M.E) (hr : M.eRank = 4) :
    IdxInc ≃ Incidence M := by
  classical
  let f := booleanFlatIndex M hI hr 2
  let g := booleanFlatIndex M hI hr 3
  have hsub (L : IdxSubset 2) (P : IdxSubset 3) :
      (f L).val ⊆ (g P).val ↔ L.val ⊆ P.val := by
    simp only [f,g,booleanFlatIndex_coe]
    exact Set.image_subset_image_iff (groundIndex M hI hr).injective
  refine
    { toFun := fun i => ⟨(f i.val.1,g i.val.2),(hsub _ _).2 i.2⟩
      invFun := fun i => ⟨(f.symm i.val.1,g.symm i.val.2),(hsub _ _).1 ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · simpa only [Equiv.apply_symm_apply] using i.2
  · intro i
    apply Subtype.ext
    exact Prod.ext (f.symm_apply_apply _) (g.symm_apply_apply _)
  · intro i
    apply Subtype.ext
    exact Prod.ext (f.apply_symm_apply _) (g.apply_symm_apply _)

theorem geom_curvature_boolean_base (hI : M.Indep M.E) (hr : M.eRank = 4) :
    geomCurvature M = 1 := by
  have h2 := (Nat.card_congr (booleanFlatIndex M hI hr 2)).symm.trans idx_line_count
  have h3 := (Nat.card_congr (booleanFlatIndex M hI hr 3)).symm.trans idx_plane_count
  have h23 := (Nat.card_congr (booleanIncIndex M hI hr)).symm.trans idx_inc_count
  have h1 := indep_ground_four_card M hI hr
  change Nat.card (FlatAt M 2) = 6 at h2
  change Nat.card (FlatAt M 3) = 4 at h3
  unfold geomCurvature
  omega

/-- The global curvature bound for actual finite rank-four matroids. -/
theorem geom_curvature_bound (hr : M.eRank = 4) :
    geomCurvature M ≥ (Nat.card M.E : Int) - 3 := by
  generalize hn : Nat.card M.E = n
  induction n using Nat.strong_induction_on generalizing M with
  | h n ih =>
    by_cases hfree : M.Indep M.E
    · have hcard := indep_ground_four_card M hfree hr
      rw [geom_curvature_boolean_base M hfree hr]
      omega
    obtain ⟨B,hB⟩ := M.exists_isBase
    have hnot : ¬ M.E ⊆ B := fun hs => hfree (hB.indep.subset hs)
    obtain ⟨e,he,heB⟩ := Set.not_subset.mp hnot
    have hRank : (M ＼ {e}).eRank = 4 := by
      change (M ↾ (M.E \ {e})).eRank = 4
      rw [M.eRank_restrict]
      apply le_antisymm
      · rw [←hr]
        exact M.eRk_le_eRank _
      have hle := M.eRk_mono (show B ⊆ M.E \ {e} from
        fun _ h => ⟨hB.subset_ground h,fun hx => heB (Set.mem_singleton_iff.mp hx ▸ h)⟩)
      rwa [hB.eRk_eq_eRank,hr] at hle
    have hcard : Nat.card (M ＼ {e}).E + 1 = Nat.card M.E := by
      simpa only [Matroid.delete_ground,Nat.card_coe_set_eq] using
        Set.ncard_sdiff_singleton_add_one he (Set.toFinite _)
    have hstep := geom_curvature_deletion M e hr he
    have hSmall := ih (Nat.card (M ＼ {e}).E) (by omega) (M ＼ {e}) hRank rfl
    omega

#print axioms geom_curvature_boolean_base
#print axioms geom_curvature_bound

end InverseZ
