module

public import InverseZProofs.Algebra
public import InverseZProofs.Structural
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

set_option autoImplicit false
namespace InverseZ
open Set Matroid Finset
open InverseZ.Algebra

variable {α : Type*} [Finite α] (M : Matroid α)
noncomputable def rawMu (a b : Flats M) : Int := by
  classical
  exact IncidenceAlgebra.mu ℤ a b

def addPoint (e : α) (F : Flats M) : Flats M :=
  ⟨M.closure (insert e F.val), M.isFlat_closure _⟩

omit [Finite α] in
theorem le_addPoint (e : α) (F : Flats M) : F ≤ addPoint M e F :=
  M.subset_closure_of_subset' (Set.subset_insert _ _) F.property.subset_ground

omit [Finite α] in
theorem addPoint_le (e : α) {F G : Flats M} (hf : F ≤ G) (he : e ∈ G.val) :
    addPoint M e F ≤ G := by
  change M.closure (insert e F.val) ⊆ G.val
  rw [← G.property.closure]
  exact M.closure_subset_closure (Set.insert_subset he hf)

omit [Finite α] in
theorem mem_addPoint {e : α} (he : e ∈ M.E) (F : Flats M) :
    e ∈ (addPoint M e F).val :=
  M.mem_closure_of_mem (Set.mem_insert _ _)
    (Set.insert_subset he F.property.subset_ground)

noncomputable def joinFiber (e : α) (G : Flats M) : Finset (Flats M) := by
  classical
  exact (Finset.Icc (bottomFlat M) G).filter (fun F => addPoint M e F = G)

theorem mem_joinFiber (e : α) (F G : Flats M) :
    F ∈ joinFiber M e G ↔ F ≤ G ∧ addPoint M e F = G := by
  classical
  simp [joinFiber, bottomFlat_le]

/-- Weisner-type cancellation, proved by partitioning a Möbius sum by
    the flat spanned after adjoining a fixed point. -/
theorem mobius_joinFiber_zero (e : α) (he₀ : e ∉ (bottomFlat M).val)
    (G : Flats M) (heG : e ∈ G.val) :
    (∑ F ∈ joinFiber M e G, rawMu M (bottomFlat M) F) = 0 := by
  classical
  generalize hrG : flatRank M G = n
  induction n using Nat.strong_induction_on generalizing G with
  | h n ih =>
    let all := Finset.Icc (bottomFlat M) G
    let contain := all.filter (fun H => e ∈ H.val)
    have heE : e ∈ M.E := G.property.subset_ground heG
    have hmaps (F : Flats M) (hF : F ∈ all) : addPoint M e F ∈ contain :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨bottomFlat_le M _,addPoint_le M e (Finset.mem_Icc.mp hF).2 heG⟩,
        mem_addPoint M heE F⟩
    have hsum := Finset.sum_fiberwise_of_maps_to hmaps
      (fun F => rawMu M (bottomFlat M) F)
    have hsame (H : Flats M) (hH : H ∈ contain) :
        all.filter (fun F => addPoint M e F = H) = joinFiber M e H := by
      have hHG : H ≤ G := (Finset.mem_Icc.mp (Finset.mem_filter.mp hH).1).2
      ext F
      rw [mem_joinFiber]
      simp only [Finset.mem_filter, all, Finset.mem_Icc, bottomFlat_le, true_and]
      constructor
      · rintro ⟨_,heq⟩
        exact ⟨heq ▸ le_addPoint M e F, heq⟩
      · rintro ⟨hle,heq⟩
        exact ⟨hle.trans hHG,heq⟩
    have heq : (∑ H ∈ contain,
        ∑ F ∈ joinFiber M e H, rawMu M (bottomFlat M) F) =
        ∑ F ∈ all, rawMu M (bottomFlat M) F := by
      rw [← hsum]
      apply Finset.sum_congr rfl
      intro H hH
      rw [hsame H hH]
    have hhead : G ∈ contain := Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨bottomFlat_le M _,le_rfl⟩,heG⟩
    rw [Finset.sum_eq_single G] at heq
    · simp only [rawMu] at heq
      rw [IncidenceAlgebra.sum_Icc_mu_right] at heq
      have hne : bottomFlat M ≠ G := fun hh => he₀ (hh.symm ▸ heG)
      unfold rawMu
      simpa only [hne,ite_false] using heq
    · intro H hH hne
      have hHG := (Finset.mem_Icc.mp (Finset.mem_filter.mp hH).1).2
      have hlt : flatRank M H < n := by
        rw [← hrG]
        exact flatRank_strict M (lt_of_le_of_ne hHG hne)
      exact ih _ hlt H (Finset.mem_filter.mp hH).2 rfl
    · intro h
      exact (h hhead).elim

theorem joinFiber_rank_succ (e : α) (F G : Flats M)
    (hf : F ∈ joinFiber M e G) (hproper : F ≠ G) (heG : e ∈ G.val) :
    flatRank M G = flatRank M F + 1 := by
  have hf' := (mem_joinFiber M e F G).mp hf
  have hOut : e ∉ F.val := by
    intro he
    have heq : addPoint M e F = F := Subtype.ext (by
      change M.closure (insert e F.val) = F.val
      rw [Set.insert_eq_of_mem he,F.property.closure])
    exact hproper (heq.symm.trans hf'.2)
  have hIn : M.eRk G.val = M.eRk F.val + 1 := by
    rw [← hf'.2]
    dsimp only [addPoint]
    rw [M.eRk_closure_eq,increment_rank_of_insert M e F.property.subset_ground
      (G.property.subset_ground heG)]
    simpa only [F.property.closure] using hOut
  rw [flatRank,flatRank,hIn, ENat.toNat_add
    (M.isRkFinite_of_finite (Set.toFinite F.val)).eRk_lt_top.ne (by simp : (1:ℕ∞) ≠ ⊤)]
  rfl

theorem joinFiber_has_proper (e : α) (G : Flats M)
    (heG : e ∈ G.val) (he₀ : e ∉ (bottomFlat M).val) :
    ∃ F ∈ joinFiber M e G, F ≠ G := by
  have heE := G.property.subset_ground heG
  have hIndep : M.Indep ({e} : Set α) := by
    have hIns : insert e (∅ : Set α) = {e} := by ext x; simp
    rw [← hIns]
    exact M.empty_indep.insert_indep_iff.mpr (Or.inl ⟨heE,he₀⟩)
  obtain ⟨B,hB,heB⟩ := hIndep.subset_isBasis_of_subset (Set.singleton_subset_iff.mpr heG)
    G.property.subset_ground
  have heB' : e ∈ B := heB (Set.mem_singleton e)
  let F : Flats M := ⟨M.closure (B \ {e}), M.isFlat_closure _⟩
  have heF : e ∉ F.val := hB.indep.notMem_closure_sdiff_of_mem heB'
  have hFG : F ≤ G := by
    change M.closure (B \ {e}) ⊆ G.val
    rw [← G.property.closure]
    exact M.closure_subset_closure (Set.sdiff_subset.trans hB.subset)
  have hJoin : addPoint M e F = G := by
    apply Subtype.ext
    change M.closure (insert e (M.closure (B \ {e}))) = G.val
    rw [M.closure_insert_closure_eq_closure_insert,Set.insert_sdiff_singleton,
      Set.insert_eq_of_mem heB',hB.closure_eq_closure,G.property.closure]
  exact ⟨F,(mem_joinFiber M e F G).mpr ⟨hFG,hJoin⟩,fun h => heF (h.symm ▸ heG)⟩

/-- The signed Möbius number from the bottom to every flat is positive
    for every matroid on a finite ambient type. -/
theorem matroid_signed_mobius_positive (G : Flats M) :
    0 < matroidSignedMu M (bottomFlat M) G := by
  classical
  generalize hrG : flatRank M G = n
  induction n using Nat.strong_induction_on generalizing G with
  | h n ih =>
    by_cases hG : G = bottomFlat M
    · subst G
      simp [matroidSignedMu, signedMu]
    have hlt : bottomFlat M < G :=
      lt_of_le_of_ne (bottomFlat_le M G) (Ne.symm hG)
    obtain ⟨e,heG,he₀⟩ := Set.exists_of_ssubset hlt
    let s := (joinFiber M e G).erase G
    have hNon : s.Nonempty := by
      obtain ⟨F,hF,hne⟩ := joinFiber_has_proper M e G heG he₀
      exact ⟨F,Finset.mem_erase.mpr ⟨hne,hF⟩⟩
    have hGG : G ∈ joinFiber M e G := by
      apply (mem_joinFiber M e G G).mpr
      refine ⟨le_rfl,Subtype.ext ?_⟩
      change M.closure (insert e G.val) = G.val
      rw [Set.insert_eq_of_mem heG,G.property.closure]
    have hsum := mobius_joinFiber_zero M e he₀ G heG
    have hh := Finset.sum_erase_add _ (fun F => rawMu M (bottomFlat M) F) hGG
    change (∑ F ∈ s, rawMu M (bottomFlat M) F) +
      rawMu M (bottomFlat M) G = _ at hh
    rw [hsum] at hh
    have hmu : rawMu M (bottomFlat M) G =
      -(∑ F ∈ s, rawMu M (bottomFlat M) F) := by omega
    have hTransform : matroidSignedMu M (bottomFlat M) G =
        ∑ F ∈ s, matroidSignedMu M (bottomFlat M) F := by
      have hraw (F : Flats M) :
          matroidSignedMu M (bottomFlat M) F =
            (-1)^flatRank M F * rawMu M (bottomFlat M) F := by
        simp [matroidSignedMu,signedMu,rawMu]
      simp only [hraw]
      rw [hmu, mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro F hf
      have hj := Finset.mem_erase.mp hf
      rw [joinFiber_rank_succ M e F G hj.2 hj.1 heG,pow_succ]
      simp
    rw [hTransform]
    apply Finset.sum_pos _ hNon
    intro F hf
    have hj := Finset.mem_erase.mp hf
    have hRank : flatRank M F < n := by
      rw [← hrG, joinFiber_rank_succ M e F G hj.2 hj.1 heG]
      omega
    exact ih _ hRank F rfl

#print axioms matroid_signed_mobius_positive

end InverseZ
