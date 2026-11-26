module

public import Mathlib.Combinatorics.Hall.Finite
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

@[expose] public section

set_option autoImplicit false
namespace InverseZ
open Finset

/-- The combinatorial point–line inequality, proved with Hall's theorem. -/
theorem point_line_inequality {P L : Type*} [Fintype P] [Fintype L]
    (inc : P → L → Prop)
    (join : P → P → L)
    (join_mem₁ : ∀ p q, p ≠ q → inc p (join p q))
    (join_mem₂ : ∀ p q, p ≠ q → inc q (join p q))
    (join_unique : ∀ p q l, p ≠ q → inc p l → inc q l → l = join p q)
    (some_line : ∀ p, ∃ l, inc p l)
    (some_outside : ∀ l, ∃ p, ¬ inc p l) :
    Fintype.card P ≤ Fintype.card L := by
  classical
  by_contra h
  have hlt : Fintype.card L < Fintype.card P := Nat.lt_of_not_ge h
  let t : L → Finset P := fun l => univ.filter (fun p => ¬ inc p l)
  have hall : ∀ s : Finset L, s.card ≤ (s.biUnion t).card := by
    intro s
    by_cases hsmall : s.card ≤ 1
    · by_cases hs : s = ∅
      · simp [hs]
      obtain ⟨l, hl⟩ := Finset.nonempty_iff_ne_empty.mpr hs
      obtain ⟨p, hp⟩ := some_outside l
      have hm : p ∈ s.biUnion t := Finset.mem_biUnion.mpr ⟨l, hl, by simp [t,hp]⟩
      have hpos := Finset.card_pos.mpr ⟨p, hm⟩
      omega
    · obtain ⟨l,hl,m,hm,hlm⟩ := Finset.one_lt_card.mp (by omega : 1 < s.card)
      have hcommon (p : P) (hp : p ∈ (univ : Finset P) \ s.biUnion t) :
          inc p l ∧ inc p m := by
        have hnot := (Finset.mem_sdiff.mp hp).2
        constructor
        · by_contra hpl
          exact hnot (Finset.mem_biUnion.mpr ⟨l, hl, by simp [t,hpl]⟩)
        · by_contra hpm
          exact hnot (Finset.mem_biUnion.mpr ⟨m, hm, by simp [t,hpm]⟩)
      have hc : ((univ : Finset P) \ s.biUnion t).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro p hp q hq
        by_contra hpq
        obtain ⟨hpl, hpm⟩ := hcommon p hp
        obtain ⟨hql, hqm⟩ := hcommon q hq
        exact hlm ((join_unique p q l hpq hpl hql).trans
          (join_unique p q m hpq hpm hqm).symm)
      have hadd := Finset.card_sdiff_add_card_eq_card
        (Finset.subset_univ (s.biUnion t))
      have hsc := Finset.card_le_univ s
      rw [Finset.card_univ] at hadd
      omega
  obtain ⟨f,hfinj,hf⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hall
  let size (l : L) := ((univ : Finset P).filter (fun p => inc p l)).card
  let degree (p : P) := ((univ : Finset L).filter (inc p)).card
  have hne (l : L) : ¬ inc (f l) l := (Finset.mem_filter.mp (hf l)).2
  have hdeg (p : P) : 0 < degree p := by
    obtain ⟨l,hl⟩ := some_line p
    exact Finset.card_pos.mpr ⟨l, by simp [hl]⟩
  have hsize (l : L) : size l ≤ degree (f l) := by
    apply Finset.card_le_card_of_injOn (join (f l))
    · intro q hq
      have hi := (Finset.mem_filter.mp hq).2
      have hpq : f l ≠ q := fun hq' => hne l (hq' ▸ hi)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, join_mem₁ _ _ hpq⟩
    · intro q₁ hq₁ q₂ hq₂ hEq
      have hi₁ := (Finset.mem_filter.mp hq₁).2
      have hi₂ := (Finset.mem_filter.mp hq₂).2
      by_contra hnq
      have hp₁ : f l ≠ q₁ := fun hq' => hne l (hq' ▸ hi₁)
      have hp₂ : f l ≠ q₂ := fun hq' => hne l (hq' ▸ hi₂)
      have he := (join_unique q₁ q₂ l hnq hi₁ hi₂).trans
        (join_unique q₁ q₂ (join (f l) q₁) hnq (join_mem₂ _ _ hp₁)
          (hEq.symm ▸ join_mem₂ _ _ hp₂)).symm
      have hi := join_mem₁ _ _ hp₁
      rw [← he] at hi
      exact hne l hi
  have hedge : (∑ l, size l) = ∑ p, degree p := by
    simp only [size, degree, Finset.card_filter]
    rw [Finset.sum_comm]
  let image := (univ : Finset L).image f
  have hcard : image.card < Fintype.card P := by
    simpa only [image, Finset.card_image_of_injective _ hfinj, Finset.card_univ] using hlt
  have hdiff : ((univ : Finset P) \ image).Nonempty := by
    apply Finset.card_pos.mp
    have hsum := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ image)
    rw [Finset.card_univ] at hsum
    omega
  obtain ⟨p,hpdiff⟩ := hdiff
  have hp := (Finset.mem_sdiff.mp hpdiff).2
  have hproper : (∑ p ∈ image, degree p) < ∑ p, degree p :=
    Finset.sum_lt_sum_of_subset (Finset.subset_univ _) (Finset.mem_univ p) hp (hdeg p)
      (fun _ _ _ => Nat.zero_le _)
  have hle : (∑ l, size l) ≤ ∑ p ∈ image, degree p := by
    rw [Finset.sum_image (fun a _ b _ hab => hfinj hab)]
    exact Finset.sum_le_sum (fun l _ => hsize l)
  omega

#print axioms point_line_inequality

end InverseZ
