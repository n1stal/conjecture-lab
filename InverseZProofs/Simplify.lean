module

public import InverseZProofs.Algebra
public import InverseZProofs.CountedDeletion

@[expose] public section

set_option autoImplicit false
namespace InverseZ
open Set Matroid
open InverseZ.Algebra

variable {α : Type*} [Finite α] (M : Matroid α)

omit [Finite α] in
theorem rank_one_flat_has_representative (F : FlatAt M 1) :
    ∃ x ∈ F.val, M.closure ({x} : Set α) = F.val ∧ M.Indep ({x} : Set α) := by
  obtain ⟨I,hI⟩ := M.exists_isBasis F.val F.2.1.subset_ground
  have hc := hI.encard_eq_eRk.trans F.2.2
  obtain ⟨x,hx⟩ := Set.encard_eq_one.mp hc
  refine ⟨x,hI.subset (hx.symm ▸ Set.mem_singleton x), ?_, hx ▸ hI.indep⟩
  rw [← hx,hI.closure_eq_closure,F.2.1.closure]

noncomputable def rankOneRep (F : FlatAt M 1) : α :=
  Classical.choose (rank_one_flat_has_representative M F)

omit [Finite α] in
theorem rankOneRep_properties (F : FlatAt M 1) :
    rankOneRep M F ∈ F.val ∧
      M.closure ({rankOneRep M F} : Set α) = F.val ∧
      M.Indep ({rankOneRep M F} : Set α) :=
  Classical.choose_spec (rank_one_flat_has_representative M F)

noncomputable def simplGround : Set α := Set.range (rankOneRep M)

omit [Finite α] in
theorem simpl_ground_subset : simplGround M ⊆ M.E := by
  rintro _ ⟨F,rfl⟩
  exact F.2.1.subset_ground (rankOneRep_properties M F).1

omit [Finite α] in
theorem simpl_spans_flat (F : Flats M) : M.closure (F.val ∩ simplGround M) = F.val := by
  apply Set.Subset.antisymm
  · simpa only [F.property.closure] using M.closure_subset_closure
      (Set.inter_subset_left : F.val ∩ simplGround M ⊆ F.val)
  · intro x hx
    by_cases hx0 : x ∈ M.closure (∅ : Set α)
    · exact M.closure_subset_closure (Set.empty_subset _) hx0
    have hEx := F.property.subset_ground hx
    have hI : M.Indep ({x} : Set α) := by
      have hIns : insert x (∅ : Set α) = {x} := by ext z; simp
      rw [←hIns]
      exact M.empty_indep.insert_indep_iff.mpr (Or.inl ⟨hEx,hx0⟩)
    let P : FlatAt M 1 := ⟨M.closure ({x} : Set α),M.isFlat_closure _,by
      rw [M.eRk_closure_eq,hI.eRk_eq_encard,Set.encard_singleton]⟩
    have hPF : P.val ⊆ F.val := by
      change M.closure ({x} : Set α) ⊆ F.val
      simpa only [F.property.closure] using M.closure_subset_closure
        (Set.singleton_subset_iff.mpr hx)
    have hProp := rankOneRep_properties M P
    have hRS : ({rankOneRep M P} : Set α) ⊆ F.val ∩ simplGround M :=
      Set.singleton_subset_iff.mpr ⟨hPF hProp.1,⟨P,rfl⟩⟩
    apply M.closure_subset_closure hRS
    rw [hProp.2.1]
    exact M.mem_closure_self x hEx

theorem simpl_pairs_indep :
    ∀ p ∈ (M ↾ simplGround M).E, ∀ q ∈ (M ↾ simplGround M).E,
      p ≠ q → (M ↾ simplGround M).Indep ({p,q} : Set α) := by
  rintro p ⟨F,rfl⟩ q ⟨G,rfl⟩ hpq
  apply Matroid.restrict_indep_iff.mpr
  have hF := rankOneRep_properties M F
  have hG := rankOneRep_properties M G
  constructor
  · apply hG.2.2.insert_indep_iff.mpr
    left
    refine ⟨F.2.1.subset_ground hF.1, ?_⟩
    rw [hG.2.1]
    intro hpG
    have hFG : F.val ⊆ G.val := by
      rw [← hF.2.1,← G.2.1.closure]
      exact M.closure_subset_closure (Set.singleton_subset_iff.mpr hpG)
    have heq : (⟨F.val,F.2.1⟩ : Flats M) = ⟨G.val,G.2.1⟩ := by
      by_contra hn
      have hr := flatRank_strict M (lt_of_le_of_ne hFG hn)
      simp only [flatRank,F.2.2,G.2.2] at hr
      omega
    exact hpq (congrArg (rankOneRep M) (Subtype.ext (congrArg (fun K : Flats M => K.val) heq)))
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    exact hx.elim (fun h => h ▸ ⟨F,rfl⟩) (fun h => h ▸ ⟨G,rfl⟩)

omit [Finite α] in
theorem simpl_rank_eq : (M ↾ simplGround M).eRank = M.eRank := by
  rw [M.eRank_restrict, ← M.eRk_ground]
  nth_rw 1 [← M.eRk_closure_eq]
  have h := simpl_spans_flat M (topFlat M)
  change M.closure (M.E ∩ simplGround M) = M.E at h
  rw [Set.inter_eq_right.mpr (simpl_ground_subset M)] at h
  rw [h]

omit [Finite α] in
noncomputable def simplFlatOrderIso : Flats (M ↾ simplGround M) ≃o Flats M := by
  refine
    { toFun := fun F => ⟨M.closure F.val,M.isFlat_closure _⟩
      invFun := fun G => ⟨G.val ∩ simplGround M,?_⟩
      left_inv := ?_
      right_inv := ?_
      map_rel_iff' := ?_ }
  · apply Matroid.isFlat_iff_closure_eq.mpr
    rw [M.restrict_closure_eq Set.inter_subset_right (simpl_ground_subset M),
      simpl_spans_flat M G]
  · intro F
    apply Subtype.ext
    exact (M.restrict_closure_eq F.2.subset_ground (simpl_ground_subset M)).symm.trans F.2.closure
  · intro G
    exact Subtype.ext (simpl_spans_flat M G)
  · intro F G
    constructor
    · intro h x hx
      have hc := M.mem_closure_of_mem hx (F.2.subset_ground.trans (simpl_ground_subset M))
      have hEq := M.restrict_closure_eq G.2.subset_ground (simpl_ground_subset M)
      have hF := F.2.subset_ground hx
      have hG : x ∈ M.closure G.val ∩ simplGround M := ⟨h hc,hF⟩
      have hnew := hEq.symm ▸ hG
      exact G.2.closure ▸ hnew
    · exact M.closure_subset_closure

omit [Finite α] in
theorem simplFlatOrderIso_rank (F : Flats (M ↾ simplGround M)) :
    flatRank M (simplFlatOrderIso M F) = flatRank (M ↾ simplGround M) F := by
  simp only [flatRank]
  change (M.eRk (M.closure F.val)).toNat = ((M ↾ simplGround M).eRk F.val).toNat
  rw [M.eRk_closure_eq, M.restrict_eRk_eq (show F.val ⊆ simplGround M from F.2.subset_ground)]

#print axioms simpl_pairs_indep
#print axioms simplFlatOrderIso
#print axioms simplFlatOrderIso_rank

end InverseZ
