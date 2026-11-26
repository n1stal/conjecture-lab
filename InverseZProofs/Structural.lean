module

public import Mathlib.Combinatorics.Matroid.Minor.Delete
public import Mathlib.Combinatorics.Matroid.Rank.ENat

@[expose] public section

set_option autoImplicit false
namespace InverseZ
open Set Matroid

variable {α : Type*} (M : Matroid α) (e : α)

def OldFlat (F : Set α) : Prop :=
  M.IsFlat F ∧ M.closure (F \ {e}) = F

theorem deletion_flat_closure_trace {U : Set α} (hU : (M ＼ {e}).IsFlat U) :
    M.closure U \ {e} = U := by
  have hd : Disjoint U ({e} : Set α) :=
    Set.disjoint_left.mpr fun _ hu he => (hU.subset_ground hu).2 he
  simpa only [M.delete_closure_eq_of_disjoint hd] using hU.closure

theorem old_flat_trace_flat {F : Set α} (hF : OldFlat M e F) :
    (M ＼ {e}).IsFlat (F \ {e}) := by
  rw [Matroid.isFlat_iff_closure_eq, M.delete_closure_eq]
  have heq : (F \ {e}) \ {e} = F \ {e} := by
    ext x
    simp only [mem_sdiff, mem_singleton_iff]
    tauto
  rw [heq, hF.2]

theorem deletion_flat_closure_old {U : Set α} (hU : (M ＼ {e}).IsFlat U) :
    OldFlat M e (M.closure U) :=
  ⟨M.isFlat_closure U, by rw [deletion_flat_closure_trace M e hU]⟩

theorem preserve_old_incidences {F G : Set α} (hF : OldFlat M e F) (hG : OldFlat M e G) :
    F \ {e} ⊆ G \ {e} ↔ F ⊆ G := by
  constructor
  · intro hh
    simpa only [hF.2, hG.2] using M.closure_subset_closure hh
  · intro hh _ hx
    exact ⟨hh hx.1, hx.2⟩

theorem old_flat_rank {F : Set α} (hF : OldFlat M e F) :
    M.eRk (F \ {e}) = M.eRk F := by
  rw [← M.eRk_closure_eq (F \ {e}), hF.2]

theorem deletion_flat_rank {U : Set α} (hU : (M ＼ {e}).IsFlat U) :
    (M ＼ {e}).eRk U = M.eRk (M.closure U) := by
  rw [M.eRk_closure_eq]
  exact M.restrict_eRk_eq hU.subset_ground

theorem new_flat_trace_eq {F : Set α}
    (hF : M.IsFlat F) (hnew : ¬ OldFlat M e F) : M.closure (F \ {e}) = F \ {e} := by
  have hne : e ∉ M.closure (F \ {e}) :=
    fun he => hnew ⟨hF, (M.closure_sdiff_singleton_eq_closure he).trans hF.closure⟩
  apply Set.Subset.antisymm
  · intro x hx
    refine ⟨?_, ?_⟩
    · have hsub := M.closure_subset_closure (show F \ {e} ⊆ F from Set.sdiff_subset)
      exact hF.closure ▸ hsub hx
    · intro hxe
      exact hne (Set.mem_singleton_iff.mp hxe ▸ hx)
  · exact M.subset_closure _ (Set.sdiff_subset.trans hF.subset_ground)

theorem new_flat_contains_deleted {F : Set α}
    (hF : M.IsFlat F) (hnew : ¬ OldFlat M e F) : e ∈ F := by
  by_contra he
  have hDiff : F \ {e} = F := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_singleton_iff]
    exact ⟨And.left, fun hx => ⟨hx, fun hxe => he (hxe ▸ hx)⟩⟩
  exact hnew ⟨hF, by rw [hDiff]; exact hF.closure⟩

theorem increment_rank_of_insert {S : Set α}
    (hS : S ⊆ M.E) (he : e ∈ M.E) (hnot : e ∉ M.closure S) :
    M.eRk (insert e S) = M.eRk S + 1 := by
  obtain ⟨I, hI⟩ := M.exists_isBasis S hS
  have hnotI : e ∉ M.closure I := by rw [hI.closure_eq_closure]; exact hnot
  have hnotMemI : e ∉ I :=
    fun heI => hnotI (M.mem_closure_of_mem heI hI.indep.subset_ground)
  have hB := hI.insert_isBasis_insert_of_notMem_closure hnotI he
  rw [hB.eRk_eq_encard, Set.encard_insert_of_notMem hnotMemI, hI.encard_eq_eRk]

theorem new_flat_trace_rank_succ {F : Set α}
    (hF : M.IsFlat F) (hnew : ¬ OldFlat M e F) :
    M.eRk F = M.eRk (F \ {e}) + 1 := by
  have heF := new_flat_contains_deleted M e hF hnew
  have hIn : insert e (F \ {e}) = F := by
    rw [Set.insert_sdiff_singleton, Set.insert_eq_of_mem heF]
  have heNot : e ∉ M.closure (F \ {e}) := by
    rw [new_flat_trace_eq M e hF hnew]
    simp
  rw [← hIn] at ⊢
  simpa only [hIn] using increment_rank_of_insert M e
    (Set.sdiff_subset.trans hF.subset_ground : F \ {e} ⊆ M.E)
    (hF.subset_ground heF) heNot

/-- Two rank-two flats with one contained in the other must coincide. -/
theorem rank_two_flat_unique_of_subset {F G : Set α}
    (hF : M.IsFlat F) (hG : M.IsFlat G)
    (rankF : M.eRk F = 2) (rankG : M.eRk G = 2) (hFG : F ⊆ G) :
    F = G := by
  apply Set.Subset.antisymm hFG
  intro u hu
  by_contra hn
  have hinc := increment_rank_of_insert M u hF.subset_ground
    (hG.subset_ground hu) (hF.closure.symm ▸ hn)
  have hle := M.eRk_mono (Set.insert_subset hu hFG)
  rw [hinc,rankF,rankG] at hle
  exact (by decide : ¬ ((2:ℕ∞)+1 ≤ 2)) hle

/-- A new plane has exactly one old line, namely its trace. -/
theorem new_plane_unique_old_line {H : Set α}
    (hH : M.IsFlat H) (rankH : M.eRk H = 3)
    (hnew : ¬ OldFlat M e H) :
    ∃! L : Set α, OldFlat M e L ∧ M.eRk L = 2 ∧ L ⊆ H := by
  have hcl := new_flat_trace_eq M e hH hnew
  have hFlat : M.IsFlat (H \ {e}) := Matroid.isFlat_iff_closure_eq.mpr hcl
  have hr := (new_flat_trace_rank_succ M e hH hnew).symm
  rw [rankH] at hr
  have hrank : M.eRk (H \ {e}) = 2 :=
    ENat.add_left_injective_of_ne_top (by simp : (1:ℕ∞) ≠ ⊤)
      (hr.trans (by decide : (3:ℕ∞)=2+1))
  have hDiff : (H \ {e}) \ {e} = H \ {e} := by
    ext x
    simp only [mem_sdiff, mem_singleton_iff]
    tauto
  refine ⟨H \ {e}, ⟨⟨hFlat, by rw [hDiff, hcl]⟩, hrank, Set.sdiff_subset⟩, ?_⟩
  intro L hL
  have hSub : L \ {e} ⊆ H \ {e} := fun _ hx => ⟨hL.2.2 hx.1, hx.2⟩
  have hC := M.closure_subset_closure hSub
  rw [hL.1.2,hcl] at hC
  exact rank_two_flat_unique_of_subset M hL.1.1 hFlat hL.2.1 hrank hC

/-- In a rank-four matroid, every line lies in at least two distinct planes. -/
theorem line_has_two_planes {L : Set α} (hL : M.IsFlat L)
    (rankL : M.eRk L = 2) (rankM : M.eRank = 4) :
    ∃ P Q : Set α, M.IsFlat P ∧ M.IsFlat Q ∧
      M.eRk P = 3 ∧ M.eRk Q = 3 ∧ L ⊆ P ∧ L ⊆ Q ∧ P ≠ Q := by
  obtain ⟨I,hI⟩ := M.exists_isBasis L hL.subset_ground
  obtain ⟨B,hB,hIB⟩ := hI.indep.exists_isBase_superset
  have hs := Set.encard_sdiff_add_encard_of_subset hIB
  rw [hI.encard_eq_eRk,rankL,hB.encard_eq_eRank,rankM] at hs
  have ht : (B \ I).encard = 2 :=
    ENat.add_left_injective_of_ne_top (by simp : (2:ℕ∞) ≠ ⊤)
      (hs.trans (by decide : (4:ℕ∞)=2+2))
  have hgt : 1 < (B \ I).encard := by rw [ht]; decide
  obtain ⟨u,v,hu,hv,huv⟩ := Set.one_lt_encard_iff.mp hgt
  have hOutside (x : α) (hx : x ∈ B \ I) : x ∉ M.closure I := by
    intro hxi
    have hsub : I ⊆ B \ {x} := fun y hy => ⟨hIB hy, by
      intro h
      exact hx.2 (Set.mem_singleton_iff.mp h ▸ hy)⟩
    exact (hB.indep.notMem_closure_sdiff_of_mem hx.1)
      (M.closure_subset_closure hsub hxi)
  let P := M.closure (insert u I)
  let Q := M.closure (insert v I)
  have hp (x : α) (hx : x ∈ B \ I) : M.eRk (M.closure (insert x I)) = 3 := by
    rw [M.eRk_closure_eq, increment_rank_of_insert M x hI.indep.subset_ground
      (hB.subset_ground hx.1) (hOutside x hx), hI.eRk_eq_eRk,rankL]
    decide
  have hClose : M.closure I = L := hI.closure_eq_closure.trans hL.closure
  have hContain (x : α) : L ⊆ M.closure (insert x I) := by
    rw [← hClose]
    exact M.closure_subset_closure (Set.subset_insert x I)
  have huP : u ∈ P := M.mem_closure_of_mem (Set.mem_insert u I)
    (Set.insert_subset (hB.subset_ground hu.1) hI.indep.subset_ground)
  have huQ : u ∉ Q := by
    intro hMem
    have hsub : insert v I ⊆ B \ {u} := by
      apply Set.insert_subset
      · exact ⟨hv.1, by simpa only [Set.mem_singleton_iff] using huv.symm⟩
      · intro z hz
        exact ⟨hIB hz, by intro h; exact hu.2 (Set.mem_singleton_iff.mp h ▸ hz)⟩
    exact (hB.indep.notMem_closure_sdiff_of_mem hu.1)
      (M.closure_subset_closure hsub hMem)
  exact ⟨P,Q,M.isFlat_closure _,M.isFlat_closure _,hp u hu,hp v hv,hContain u,hContain v,
    fun h => huQ (h ▸ huP)⟩

#print axioms deletion_flat_closure_old
#print axioms preserve_old_incidences
#print axioms new_flat_trace_rank_succ
#print axioms new_plane_unique_old_line
#print axioms line_has_two_planes

end InverseZ
