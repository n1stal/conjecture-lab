module

public import InverseZProofs.PointLine
public import InverseZProofs.Structural

@[expose] public section

set_option autoImplicit false
namespace InverseZ
open Set Matroid

abbrev MatroidLine {α : Type*} (M : Matroid α) :=
  {F : Set α // M.IsFlat F ∧ M.eRk F = 2}

noncomputable def lineOfDistinct {α : Type*} (M : Matroid α)
    (pairs : ∀ p ∈ M.E, ∀ q ∈ M.E, p ≠ q → M.Indep ({p,q} : Set α))
    (p q : M.E) (h : p ≠ q) : MatroidLine M := by
  have h' : (p : α) ≠ (q : α) := fun he => h (Subtype.ext he)
  refine ⟨M.closure ({↑p,↑q} : Set α), M.isFlat_closure _, ?_⟩
  rw [M.eRk_closure_eq, (pairs _ p.2 _ q.2 h').eRk_eq_encard, Set.encard_pair h']

/-- Every finite simple matroid of rank at least three has at least as many
    lines as points. Simplicity is expressed as independence of each
    pair of distinct ground elements. -/
theorem matroid_point_line {α : Type*} [Finite α] (M : Matroid α)
    (pairs : ∀ p ∈ M.E, ∀ q ∈ M.E, p ≠ q → M.Indep ({p,q} : Set α))
    (rankM : 3 ≤ M.eRank) :
    Nat.card M.E ≤ Nat.card (MatroidLine M) := by
  classical
  let : Fintype M.E := Fintype.ofFinite M.E
  unfold MatroidLine
  let : Fintype {F : Set α // M.IsFlat F ∧ M.eRk F = 2} := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card]
  have hTwo : 1 < M.E.encard :=
    (by decide : (1:ℕ∞) < 3).trans_le (rankM.trans M.eRank_le_encard_ground)
  obtain ⟨x,y,hx,hy,hxy⟩ := Set.one_lt_encard_iff.mp hTwo
  let default : MatroidLine M := lineOfDistinct M pairs ⟨x,hx⟩ ⟨y,hy⟩
    (fun h => hxy (congrArg Subtype.val h))
  let J (p q : M.E) : MatroidLine M :=
    if h : p=q then default else lineOfDistinct M pairs p q h
  let I (p : M.E) (L : MatroidLine M) := (p : α) ∈ (L : Set α)
  have hGround (p q : M.E) : ({↑p,↑q} : Set α) ⊆ M.E := by
    intro z hz
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
    exact hz.elim (fun he => he ▸ p.2) (fun he => he ▸ q.2)
  have hp (p q : M.E) (h : p ≠ q) : I p (J p q) := by
    dsimp only [I]
    simp only [J, dite_eq_right h, lineOfDistinct]
    exact M.mem_closure_of_mem (by simp) (hGround p q)
  have hq (p q : M.E) (h : p ≠ q) : I q (J p q) := by
    dsimp only [I]
    simp only [J,dite_eq_right h,lineOfDistinct]
    exact M.mem_closure_of_mem (by simp) (hGround p q)
  have hUnique (p q : M.E) (L : MatroidLine M) (h : p ≠ q)
      (hpL : I p L) (hqL : I q L) : L = J p q := by
    apply Subtype.ext
    apply Eq.symm
    apply rank_two_flat_unique_of_subset M (J p q).2.1 L.2.1 (J p q).2.2 L.2.2
    simp only [J,dite_eq_right h,lineOfDistinct]
    have hsub : ({↑p,↑q} : Set α) ⊆ (L : Set α) := by
      intro z hz
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
      exact hz.elim (fun he => he ▸ hpL) (fun he => he ▸ hqL)
    simpa only [L.2.1.closure] using M.closure_subset_closure hsub
  have hSome (p : M.E) : ∃ L, I p L := by
    obtain ⟨z,hz,hn⟩ := Set.exists_ne_of_one_lt_encard hTwo (p : α)
    exact ⟨J p ⟨z,hz⟩, hp p ⟨z,hz⟩ (fun h => hn (congrArg Subtype.val h).symm)⟩
  have hOutside (L : MatroidLine M) : ∃ p, ¬ I p L := by
    by_contra hF
    have hsub : M.E ⊆ (L : Set α) := by
      intro z hz
      by_contra hn
      exact hF ⟨⟨z,hz⟩,hn⟩
    have hle := M.eRk_mono hsub
    rw [M.eRk_ground,L.2.2] at hle
    exact (by decide : ¬ ((3:ℕ∞) ≤ 2)) (rankM.trans hle)
  exact point_line_inequality I J hp hq hUnique hSome hOutside

#print axioms matroid_point_line

end InverseZ
