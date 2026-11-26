module

public import InverseZProofs.Structural
public import Mathlib.Data.Fintype.Card

@[expose] public section

set_option autoImplicit false
namespace InverseZ
open Set Matroid

variable {α : Type*} (M : Matroid α) (e : α)

abbrev FlatAt (k : ℕ∞) := {F : Set α // M.IsFlat F ∧ M.eRk F = k}
abbrev OldAt (k : ℕ∞) := {F : FlatAt M k // OldFlat M e F.val}
abbrev NewAt (k : ℕ∞) := {F : FlatAt M k // ¬ OldFlat M e F.val}
abbrev Incidence :=
  {i : FlatAt M 2 × FlatAt M 3 // i.1.val ⊆ i.2.val}
abbrev OldLineInc :=
  {i : Incidence M // OldFlat M e i.val.1.val}
abbrev NewLineInc :=
  {i : Incidence M // ¬ OldFlat M e i.val.1.val}
abbrev OldBothInc :=
  {i : OldLineInc M e // OldFlat M e i.val.val.2.val}
abbrev OldLineNewPlaneInc :=
  {i : OldLineInc M e // ¬ OldFlat M e i.val.val.2.val}

noncomputable def oldFlatsOfDeletion (k : ℕ∞) :
    FlatAt (M ＼ {e}) k ≃ OldAt M e k where
  toFun U := ⟨⟨M.closure U.val, M.isFlat_closure U.val,
    (deletion_flat_rank M e U.2.1).symm.trans U.2.2⟩, deletion_flat_closure_old M e U.2.1⟩
  invFun F := ⟨F.val.val \ {e}, old_flat_trace_flat M e F.2, by
    have hs : F.val.val \ {e} ⊆ (M ＼ {e}).E :=
      fun _ hx => ⟨F.2.1.subset_ground hx.1,hx.2⟩
    exact (M.restrict_eRk_eq hs).trans ((old_flat_rank M e F.2).trans F.val.2.2)⟩
  left_inv U := Subtype.ext (deletion_flat_closure_trace M e U.2.1)
  right_inv F := Subtype.ext (Subtype.ext F.2.2)

noncomputable def oldIncidencesOfDeletion :
    Incidence (M ＼ {e}) ≃ OldBothInc M e := by
  let f := oldFlatsOfDeletion M e 2
  let g := oldFlatsOfDeletion M e 3
  refine
    { toFun := fun U => ⟨⟨⟨((f U.val.1).val,(g U.val.2).val),
          M.closure_subset_closure U.2⟩,(f U.val.1).2⟩,(g U.val.2).2⟩
      invFun := fun H => ⟨(f.symm ⟨H.val.val.val.1,H.val.2⟩,
          g.symm ⟨H.val.val.val.2,H.2⟩),fun _ hx => ⟨H.val.val.2 hx.1,hx.2⟩⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro U
    apply Subtype.ext
    apply Prod.ext
    · exact f.symm_apply_apply U.val.1
    · exact g.symm_apply_apply U.val.2
  · intro H
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val (f.apply_symm_apply ⟨H.val.val.val.1,H.val.2⟩)
    · exact congrArg Subtype.val (g.apply_symm_apply ⟨H.val.val.val.2,H.2⟩)

noncomputable def oldLineNewPlaneEquiv :
    OldLineNewPlaneInc M e ≃ NewAt M e 3 := by
  let f : OldLineNewPlaneInc M e → NewAt M e 3 :=
    fun H => ⟨H.val.val.val.2,H.2⟩
  apply Equiv.ofBijective f
  constructor
  · intro a b hab
    have hv : a.val.val.val.2 = b.val.val.val.2 := congrArg Subtype.val hab
    have hp := new_plane_unique_old_line M e a.val.val.val.2.2.1 a.val.val.val.2.2.2 a.2
    obtain ⟨C,_,hh⟩ := hp
    have hae := hh a.val.val.val.1.val ⟨a.val.2,a.val.val.val.1.2.2,a.val.val.2⟩
    have hbe := hh b.val.val.val.1.val ⟨b.val.2,b.val.val.val.1.2.2,
      fun _ hx => hv.symm ▸ b.val.val.2 hx⟩
    exact Subtype.ext (Subtype.ext (Subtype.ext (Prod.ext
      (Subtype.ext (hae.trans hbe.symm)) hv)))
  · intro H
    obtain ⟨L,hL,_⟩ := new_plane_unique_old_line M e H.val.2.1 H.val.2.2 H.2
    exact ⟨⟨⟨⟨(⟨L,hL.1.1,hL.2.1⟩,H.val),hL.2.2⟩,hL.1⟩,H.2⟩,rfl⟩

variable [Finite α]

theorem partition_card {β : Type*} [Finite β] (p : β → Prop) :
    Nat.card β = Nat.card {b // p b} + Nat.card {b // ¬ p b} := by
  classical
  exact (Nat.card_congr (Equiv.Set.sumCompl {b | p b}).symm).trans Nat.card_sum

theorem flat_count_deletion (k : ℕ∞) :
    Nat.card (FlatAt M k) =
      Nat.card (FlatAt (M ＼ {e}) k) + Nat.card (NewAt M e k) := by
  rw [partition_card (fun F : FlatAt M k => OldFlat M e F.val),
    ← Nat.card_congr (oldFlatsOfDeletion M e k)]

theorem incidence_count_deletion :
    Nat.card (Incidence M) =
      Nat.card (Incidence (M ＼ {e})) +
        Nat.card (NewAt M e 3) + Nat.card (NewLineInc M e) := by
  rw [partition_card (fun i : Incidence M => OldFlat M e i.val.1.val),
    partition_card (fun i : OldLineInc M e => OldFlat M e i.val.val.2.val),
    ← Nat.card_congr (oldIncidencesOfDeletion M e),
    Nat.card_congr (oldLineNewPlaneEquiv M e)]

theorem incidence_new_line_count (rankM : M.eRank = 4) :
    2 * Nat.card (NewAt M e 2) ≤ Nat.card (NewLineInc M e) := by
  classical
  have hs (L : NewAt M e 2) : ∃ P Q : FlatAt M 3,
      L.val.val ⊆ P.val ∧ L.val.val ⊆ Q.val ∧ P ≠ Q := by
    obtain ⟨P,Q,hP,hQ,rP,rQ,iP,iQ,hne⟩ :=
      line_has_two_planes M L.val.2.1 L.val.2.2 rankM
    exact ⟨⟨P,hP,rP⟩,⟨Q,hQ,rQ⟩,iP,iQ,fun hh => hne (congrArg Subtype.val hh)⟩
  choose P Q hP hQ hne using hs
  let f (a : Bool × NewAt M e 2) : NewLineInc M e :=
    if a.1 then ⟨⟨(a.2.val,P a.2),hP a.2⟩,a.2.2⟩
    else ⟨⟨(a.2.val,Q a.2),hQ a.2⟩,a.2.2⟩
  have inj : Function.Injective f := by
    rintro ⟨a,L⟩ ⟨b,K⟩ hh
    have hsame : L = K := by
      have hh' := congrArg (fun i : NewLineInc M e => i.val.val.1) hh
      cases a <;> cases b <;> exact Subtype.ext hh'
    subst K
    cases a <;> cases b
    · rfl
    · have hsame' := congrArg (fun i : NewLineInc M e => i.val.val.2) hh
      exact (hne L hsame'.symm).elim
    · have hsame' := congrArg (fun i : NewLineInc M e => i.val.val.2) hh
      exact (hne L hsame').elim
    · rfl
  let := Fintype.ofFinite (Bool × NewAt M e 2)
  let := Fintype.ofFinite (NewLineInc M e)
  have hh : Nat.card (Bool × NewAt M e 2) ≤ Nat.card (NewLineInc M e) := by
    simpa only [Nat.card_eq_fintype_card] using Fintype.card_le_of_injective f inj
  rw [Nat.card_prod] at hh
  have hBool : Nat.card Bool = 2 := by rw [Nat.card_eq_fintype_card]; decide
  simpa only [hBool] using hh

noncomputable def geomCurvature : Int :=
  (Nat.card (Incidence M) : Int) - 2 * (Nat.card (FlatAt M 2) : Int) -
    (Nat.card (FlatAt M 3) : Int) + (Nat.card M.E : Int) + 1

theorem geom_curvature_deletion (rankM : M.eRank = 4) (he : e ∈ M.E) :
    geomCurvature M ≥ geomCurvature (M ＼ {e}) + 1 := by
  have h2 := flat_count_deletion M e 2
  have h3 := flat_count_deletion M e 3
  have h23 := incidence_count_deletion M e
  have hn := incidence_new_line_count M e rankM
  have hp : Nat.card M.E = Nat.card (M ＼ {e}).E + 1 := by
    simpa only [Matroid.delete_ground,Nat.card_coe_set_eq] using
      (Set.ncard_sdiff_singleton_add_one he (Set.toFinite _)).symm
  unfold geomCurvature
  omega

#print axioms oldIncidencesOfDeletion
#print axioms incidence_count_deletion
#print axioms incidence_new_line_count
#print axioms geom_curvature_deletion

end InverseZ
