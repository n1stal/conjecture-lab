module

public import Std

@[expose] public section

namespace CoinFamilyResidue

/-- A denomination strictly below the closing coin L+6. -/
def LowerCoin (L x : Nat) : Prop :=
  (x ≤ L ∧ x % 3 = 1) ∨ x = 2 ∨ x = 5 ∨ x = 8 ∨ x = 14

instance (L x : Nat) : Decidable (LowerCoin L x) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _ ∨ _))

def count (L x : Nat) : Nat :=
  if x = 0 then 0 else if LowerCoin L x then 1 else if x = L+3 then 3 else 2

theorem lower_range {L x : Nat} (hL : 22 ≤ L) (h : LowerCoin L x) :
    0 < x ∧ x ≤ L := by
  unfold LowerCoin at h
  omega

theorem count_pos {L x : Nat} (hx : 0 < x) : 1 ≤ count L x := by
  unfold count
  split <;> try omega
  split <;> try omega
  split <;> omega

theorem count_of_coin {L x : Nat} (hL : 22 ≤ L) (hx : LowerCoin L x) :
    count L x = 1 := by
  have hp := (lower_range hL hx).1
  simp [count, hx, Nat.ne_of_gt hp]

theorem count_le_two_of_ne {L x : Nat} (hx : x ≠ L+3) :
    count L x ≤ 2 := by
  by_cases hz : x = 0 <;> by_cases hc : LowerCoin L x <;> simp [count, hz, hc, hx]

theorem count_le_three (L x : Nat) : count L x ≤ 3 := by
  unfold count
  split <;> try omega
  split <;> try omega
  split <;> omega

theorem count_ge_two_of_not_coin {L x : Nat} (hz : x ≠ 0) (hc : ¬ LowerCoin L x) :
    2 ≤ count L x := by
  rw [count, ite_eq_right hz, ite_eq_right hc]
  split <;> omega

theorem not_sum_two_at_exception {L c r : Nat} (hL : L = 22 ∨ 28 ≤ L)
    (hm : L % 3 = 1) (hc : LowerCoin L c) (hr : LowerCoin L r) : c+r ≠ L+3 := by
  unfold LowerCoin at hc hr
  omega

theorem wrap_zero_or_coin {L c r : Nat} (hL : 22 ≤ L) (hm : L % 3 = 1)
    (hc : LowerCoin L c) (hr : LowerCoin L r) (hw : L+6 ≤ c+r) :
    c+r-(L+6) = 0 ∨ LowerCoin L (c+r-(L+6)) := by
  unfold LowerCoin at hc hr ⊢
  omega

theorem unwrapped {L c r : Nat} (hL : L = 22 ∨ 28 ≤ L)
    (hm : L % 3 = 1) (hc : LowerCoin L c) :
    count L (c+r) ≤ 1+count L r := by
  have hmin : 22 ≤ L := by omega
  by_cases hz : r = 0
  · subst r
    rw [Nat.add_zero, count_of_coin hmin hc]
    have h0 : count L 0 = 0 := by simp [count]
    simp [h0]
  · by_cases hr : LowerCoin L r
    · have hne := not_sum_two_at_exception hL hm hc hr
      have hu := count_le_two_of_ne hne
      have heq := count_of_coin hmin hr
      omega
    · have hb := count_ge_two_of_not_coin hz hr
      have hu := count_le_three L (c+r)
      omega

theorem wrapped {L c r : Nat} (hL : 22 ≤ L)
    (hm : L % 3 = 1) (hc : LowerCoin L c)
    (hr : r < L+6) (hw : L+6 ≤ c+r) :
    count L (c+r-(L+6)) ≤ count L r := by
  have hcr := lower_range hL hc
  have hz : r ≠ 0 := by omega
  by_cases hrc : LowerCoin L r
  · have heq := count_of_coin hL hrc
    rcases wrap_zero_or_coin hL hm hc hrc hw with h | h
    · simp [h, count]
    · simpa only [count_of_coin hL h, heq] using Nat.le_refl 1
  · have hb := count_ge_two_of_not_coin hz hrc
    have hne : c+r-(L+6) ≠ L+3 := by omega
    have hu := count_le_two_of_ne hne
    omega

#print axioms unwrapped
#print axioms wrapped

end CoinFamilyResidue
