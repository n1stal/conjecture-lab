module
public import InverseZProjective.ProjectiveBottomMobius
public import InverseZProjective.ProjectiveFlatCounts
public import InverseZProjective.ProjectiveBridge
@[expose] public section
set_option autoImplicit false
namespace InverseZProjective.GaussianIncidence
open Module Submodule Finset InverseZ.Algebra InverseZProjective.ProjectiveTrace InverseZProjective.ProjectiveBridge
variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V] [Finite V]
variable [LocallyFiniteOrder (Submodule K V)]
variable (S : Set V)
local notation "M" => representedMatroid (K:=K) S
local notation "e" => flatSubspaceEmbedding (K:=K) S
local notation "r" => flatRank M
local notation "O" => bottomFlat M
open scoped Classical

omit [Finite K] in
theorem deleted_subset_layer {a b : Flats M} (hab : a ≤ b) :
    deletedInFlat S a = (deletedInFlat S b).filter (fun p => p ≤ e a) := by
  classical
  ext x
  unfold deletedInFlat
  simp only [mem_filter, mem_Ioc]
  constructor
  · rintro ⟨⟨h₀,ha⟩,hne⟩
    exact ⟨⟨⟨h₀,ha.trans ((flatSubspaceEmbedding (K:=K) S).monotone hab)⟩,hne⟩,ha⟩
  · rintro ⟨⟨⟨h₀,_⟩,hne⟩,ha⟩
    exact ⟨⟨h₀,ha⟩,hne⟩

omit [Finite K] in
theorem deleted_mem_rank_one (hS : LinePreserving (K:=K) S) (b : Flats M)
    (p : Submodule K V) (hp : p ∈ deletedInFlat S b) : finrank K p = 1 := by
  classical
  unfold deletedInFlat at hp
  obtain ⟨h₀,hnot⟩ := mem_filter.mp hp
  have hpos : 0 < finrank K p := by
    have hh := Submodule.finrank_lt_finrank_of_lt (mem_Ioc.mp h₀).1
    rwa [finrank_bot] at hh
  by_contra hn
  let P : Surviving (K:=K) S := ⟨p, span_trace_eq_of_linePreserving S hS p (by omega)⟩
  apply hnot
  refine ⟨representedFlatIso S P, ?_⟩
  change ((representedFlatIso (K:=K) S).symm (representedFlatIso S P)).val = _
  rw [OrderIso.symm_apply_apply]

omit [Finite K] [LocallyFiniteOrder (Submodule K V)] in
theorem card_layer_above (hS : LinePreserving (K:=K) S) (b : Flats M)
    (j : ℕ) (hj : 2 ≤ j) (p : Submodule K V) (hp : p ≤ e b) (hjp : finrank K p ≤ j) :
    ((layer r O b j).filter (fun f => p ≤ e f)).card =
      gaussianCount K (r b - finrank K p) (j - finrank K p) := by
  classical
  let F := (layer r O b j).filter (fun f => p ≤ e f)
  let E : F ≃ {x : Set.Iic b // r x.val = j ∧ p ≤ e x.val} :=
    { toFun := fun x => by
        obtain ⟨hx,hp⟩ := mem_filter.mp x.property
        obtain ⟨⟨_,hxb⟩,hr⟩ := (mem_layer r).mp hx
        exact ⟨⟨x.val,hxb⟩,(by simpa only [flatRank_bottom,Nat.sub_zero] using hr),hp⟩
      invFun := fun x => ⟨x.val.val, mem_filter.mpr ⟨(mem_layer r).mpr
        ⟨⟨bottomFlat_le M _,x.val.property⟩,by simpa only [flatRank_bottom,Nat.sub_zero] using x.property.1⟩,
        x.property.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h := Nat.card_congr E
  rw [Nat.card_eq_fintype_card,Fintype.card_coe,
    card_actualFlats_above_subspace S hS b p hp j hj hjp] at h
  exact h

omit [Finite K] [LocallyFiniteOrder (Submodule K V)] in
theorem card_layer_high (hS : LinePreserving (K:=K) S) (b : Flats M)
    (j : ℕ) (hj : 2 ≤ j) :
    (layer r O b j).card = gaussianCount K (r b) j := by
  classical
  simpa only [bot_le, filter_true, finrank_bot, Nat.sub_zero] using
    card_layer_above S hS b j hj ⊥ bot_le (by simp)

omit [Finite K] in
theorem deleted_incidence_mass (hS : LinePreserving (K:=K) S) (b : Flats M)
    (j : ℕ) (hj : 2 ≤ j) :
    (∑ f ∈ layer r O b j, ((deletedInFlat S f).card : ℤ)) =
      ((deletedInFlat S b).card : ℤ) * gaussianCount K (r b-1) (j-1) := by
  classical
  let D := deletedInFlat S b
  let F := layer r O b j
  have hsum : (∑ f ∈ F, ((D.filter (fun p => p ≤ e f)).card : ℤ)) =
      ∑ p ∈ D, ((F.filter (fun f => p ≤ e f)).card : ℤ) := by
    simp only [card_eq_sum_ones, Nat.cast_sum, sum_filter]
    exact sum_comm
  calc
    _ = ∑ f ∈ F, ((D.filter (fun p => p ≤ e f)).card : ℤ) := by
      apply sum_congr rfl
      intro f hf
      rw [deleted_subset_layer S ((mem_layer r).mp hf).1.2]
    _ = _ := hsum
    _ = _ := by
      have hw (p : Submodule K V) (hp : p ∈ D) :
          (F.filter (fun f => p ≤ e f)).card = gaussianCount K (r b-1) (j-1) := by
        have h₁ := deleted_mem_rank_one S hS b p hp
        have h₂ : p ≤ e b := (mem_Ioc.mp (mem_filter.mp hp).1).2
        rw [card_layer_above S hS b j hj p h₂ (by omega),h₁]
      rw [sum_congr rfl (fun p hp => congrArg (fun t : ℕ => (t : ℤ)) (hw p hp))]
      simp [D]
omit [Finite K] in
theorem card_layer_one_add_deleted (hS : LinePreserving (K:=K) S) (b : Flats M) :
    (layer r O b 1).card + (deletedInFlat S b).card = gaussianCount K (r b) 1 := by
  classical
  let T : Finset (Submodule K V) := (Ioc (⊥ : Submodule K V) (e b)).filter (fun p : Submodule K V => finrank K p = 1)
  let R := T.filter (fun p => ∃ f, e f = p)
  have hD : T.filter (fun p => ¬ ∃ f, e f = p) = deletedInFlat S b := by
    ext p
    simp only [mem_filter, T, deletedInFlat]
    constructor
    · rintro ⟨⟨h₁,_⟩,h₂⟩
      exact ⟨h₁,h₂⟩
    · intro hp
      exact ⟨⟨hp.1,deleted_mem_rank_one S hS b p (mem_filter.mpr hp)⟩,hp.2⟩
  have hR : (layer r O b 1).card = R.card := by
    refine card_bij (fun f _ => e f) ?_ ?_ ?_
    · intro f hf
      obtain ⟨⟨_,hf₁⟩,hf₂⟩ := (mem_layer r).mp hf
      have hr : r f = 1 := by simpa only [flatRank_bottom,Nat.sub_zero] using hf₂
      have hdim : finrank K (e f) = 1 := (flatSubspaceEmbedding_rank S f).symm.trans hr
      have hne : (⊥ : Submodule K V) ≠ e f := by
        intro he
        rw [← he,finrank_bot] at hdim
        omega
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Ioc.mpr ⟨bot_lt_iff_ne_bot.mpr hne.symm,(flatSubspaceEmbedding (K:=K) S).monotone hf₁⟩,
        hdim⟩,⟨f,rfl⟩⟩
    · intro f _ g _ hg
      exact (flatSubspaceEmbedding (K:=K) S).injective hg
    · intro p hp
      obtain ⟨hp',⟨f,rfl⟩⟩ := mem_filter.mp hp
      obtain ⟨hI,hdim⟩ := mem_filter.mp hp'
      refine ⟨f,(mem_layer r).mpr ⟨⟨bottomFlat_le M _,(flatSubspaceEmbedding (K:=K) S).le_iff_le.mp (mem_Ioc.mp hI).2⟩,?_⟩,rfl⟩
      rw [flatRank_bottom,Nat.sub_zero,flatSubspaceEmbedding_rank S f,hdim]
  have hT : T.card = gaussianCount K (r b) 1 := by
    let E : T ≃ {x : Set.Icc (⊥ : Submodule K V) (e b) //
        finrank K x.val - finrank K (⊥ : Submodule K V) = 1} :=
      { toFun := fun x => by
          obtain ⟨hx,hr⟩ := mem_filter.mp x.property
          obtain ⟨h₁,h₂⟩ := mem_Ioc.mp hx
          exact ⟨⟨x.val,h₁.le,h₂⟩,by simpa only [finrank_bot,Nat.sub_zero] using hr⟩
        invFun := fun x => by
          have hd : finrank K x.val.val = 1 := by
            simpa only [finrank_bot,Nat.sub_zero] using x.property
          have hne : (⊥ : Submodule K V) ≠ x.val.val := by
            intro he
            rw [← he,finrank_bot] at hd
            omega
          exact ⟨x.val.val,mem_filter.mpr ⟨mem_Ioc.mpr ⟨bot_lt_iff_ne_bot.mpr hne.symm,x.val.property.2⟩,hd⟩⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hh := Nat.card_congr E
    rw [Nat.card_eq_fintype_card,Fintype.card_coe,card_subspace_interval_layer _ _ bot_le,
      finrank_bot,Nat.sub_zero,← flatSubspaceEmbedding_rank S b] at hh
    exact hh
  rw [hR,← hD, card_filter_add_card_filter_not, hT]

#print axioms card_layer_high
#print axioms deleted_incidence_mass
end InverseZProjective.GaussianIncidence
