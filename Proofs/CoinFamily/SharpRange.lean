module

public import Proofs.CoinFamily.FamilyExclusivity
public import Proofs.CoinFamily.VanCottZhangSmall

@[expose] public section

set_option autoImplicit false
namespace CoinOrder.Family

theorem hasPrefixPattern_ge11 (n : Nat) (hn : 11 ≤ n) :
    HasPrefixPattern n := by
  by_cases hh : n ≤ 14
  · exact every_small_length_family n hn hh
  · exact hasPrefixPattern_ge15 n (by omega)

private theorem C14_not_D : ¬ IsD 4 C14 := by
  rintro ⟨_,a,_,ha⟩
  have h3 := ha 2 (by decide)
  have h8 := ha 7 (by decide)
  rw [d_third 4 a (by decide)] at h3
  rw [d_eighth 4 a (by decide)] at h8
  simp [C14] at h3 h8
  omega

private theorem C14_not_G : ¬ IsG 4 C14 := by
  rintro ⟨_,_,ha⟩
  have h6 := ha 5 (by decide)
  rw [g_sixth 4 (by decide)] at h6
  simp [C14] at h6

theorem part3_exclusivity_refuted_ge4 (r : Nat) (hr : 4 ≤ r) :
    ∃ C : List Nat, C.length = 3*r+2 ∧ C.head? = some 1 ∧ C.Pairwise (· < ·) ∧
      (∀ i, 1 ≤ i → i ≤ 3 → Orderly (coinPrefix C i)) ∧
      (∀ i, 4 ≤ i → i < C.length → ¬ Orderly (coinPrefix C i)) ∧
      Orderly C.reverse ∧ ¬ IsD r C ∧ ¬ IsG r C := by
  by_cases hh : r = 4
  · subst r
    exact ⟨C14, prefix_pattern_14.1, prefix_pattern_14.2.1,
      prefix_pattern_14.2.2.1, prefix_pattern_14.2.2.2.1,
      prefix_pattern_14.2.2.2.2.1, prefix_pattern_14.2.2.2.2.2, C14_not_D,C14_not_G⟩
  · exact part3_exclusivity_refuted r (by omega)

/-- Conjecture 5.2(3), with D and G according to the paper. -/
def Conjecture523 : Prop :=
  ∀ (r : Nat) (C : List Nat), 1 ≤ r → C.length = 3*r+2 →
    C.head? = some 1 → C.Pairwise (· < ·) →
    (((∀ i, 1 ≤ i → i ≤ 3 → Orderly (coinPrefix C i)) ∧
      (∀ i, 4 ≤ i → i < C.length → ¬ Orderly (coinPrefix C i)) ∧
      Orderly C.reverse) ↔ (IsD r C ∨ IsG r C))

theorem vanCottZhangConjecture523_false : ¬ Conjecture523 := by
  intro h
  obtain ⟨C,hl,h1,hp,hi,hm,ho,hd,hg⟩ := part3_exclusivity_refuted_ge4 4 (by decide)
  exact (not_or_intro hd hg) ((h 4 C (by decide) hl h1 hp).mp ⟨hi,hm,ho⟩)

#print axioms vanCottZhangConjecture523_false
#print axioms hasPrefixPattern_ge11
#print axioms part3_exclusivity_refuted_ge4

end CoinOrder.Family
