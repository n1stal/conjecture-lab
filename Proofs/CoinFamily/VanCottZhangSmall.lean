module

public import Proofs.VanCottZhang
public import Proofs.CoinFamily.Prefixes

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 4096

namespace CoinOrder

/-- A system realizes the prefix pattern at a specified length. -/
def SmallPrefixPattern (n : Nat) (C : List Nat) : Prop :=
  C.length = n ∧ C.head? = some 1 ∧ C.Pairwise (· < ·) ∧
  (∀ i : Nat, 1 ≤ i → i ≤ 3 → Orderly (coinPrefix C i)) ∧
  (∀ i : Nat, 4 ≤ i → i < C.length → ¬ Orderly (coinPrefix C i)) ∧
  Orderly C.reverse


def C11 : List Nat := [1,2,4,5,7,9,12,14,17,22,27]

set_option maxHeartbeats 3000000 in
theorem final11_orderly : Orderly C11.reverse := by
  apply orderly_of_check 27 [22,17,14,12,9,7,5,4,2,1] <;> decide

theorem first_three_11_orderly (i : Nat) (h1 : 1 ≤ i) (h3 : i ≤ 3) :
    Orderly (coinPrefix C11 i) := by
  have hi : i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hi with rfl | rfl | rfl
  · exact orderly_of_check 1 [] (by decide) (by decide) (by decide)
  · exact orderly_of_check 2 [1] (by decide) (by decide) (by decide)
  · exact orderly_of_check 4 [2,1] (by decide) (by decide) (by decide)

theorem middle11_nonorderly (i : Nat) (h4 : 4 ≤ i) (hn : i < C11.length) :
    ¬ Orderly (coinPrefix C11 i) := by
  have hi : i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 := by
    change i < 11 at hn
    omega
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact not_orderly_of_better _ 8 [4,4] (by decide) (by decide) (by decide)
  · exact not_orderly_of_better _ 10 [5,5] (by decide) (by decide) (by decide)
  · exact not_orderly_of_better _ 12 [5,7] (by decide) (by decide) (by decide)
  · exact not_orderly_of_better _ 18 [9,9] (by decide) (by decide) (by decide)
  · exact not_orderly_of_better _ 17 [5,12] (by decide) (by decide) (by decide)
  · exact not_orderly_of_better _ 23 [9,14] (by decide) (by decide) (by decide)
  · exact not_orderly_of_better _ 28 [14,14] (by decide) (by decide) (by decide)

theorem prefix_pattern_11 : SmallPrefixPattern 11 C11 :=
  ⟨by decide, by decide, by decide, first_three_11_orderly, middle11_nonorderly, final11_orderly⟩


def C12 : List Nat := [1,2,4,5,7,8,10,11,13,16,19,22]

set_option maxHeartbeats 3000000 in
theorem final12_orderly : Orderly C12.reverse := by
  apply orderly_of_check 22 [19,16,13,11,10,8,7,5,4,2,1] <;> decide

theorem first_three_12_orderly (i : Nat) (h1 : 1 ≤ i) (h3 : i ≤ 3) :
    Orderly (coinPrefix C12 i) := by
  have hi : i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hi with rfl | rfl | rfl
  · exact orderly_of_check 1 [] (by decide) (by decide) (by decide)
  · exact orderly_of_check 2 [1] (by decide) (by decide) (by decide)
  · exact orderly_of_check 4 [2,1] (by decide) (by decide) (by decide)

theorem middle12_nonorderly (i : Nat) (h4 : 4 ≤ i) (hn : i < C12.length) :
    ¬ Orderly (coinPrefix C12 i) := by
  have hi : i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 := by
    change i < 12 at hn
    omega
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact not_orderly_of_better _ 8 [4,4] (by decide) (by decide) (by decide)
  · exact not_orderly_of_better _ 10 [5,5] (by decide) (by decide) (by decide)
  · exact not_orderly_of_better _ 11 [4,7] (by decide) (by decide) (by decide)
  · exact not_orderly_of_better _ 13 [5,8] (by decide) (by decide) (by decide)
  · exact not_orderly_of_better _ 14 [4,10] (by decide) (by decide) (by decide)
  · exact not_orderly_of_better _ 16 [5,11] (by decide) (by decide) (by decide)
  · exact not_orderly_of_better _ 19 [8,11] (by decide) (by decide) (by decide)
  · exact not_orderly_of_better _ 22 [11,11] (by decide) (by decide) (by decide)

theorem prefix_pattern_12 : SmallPrefixPattern 12 C12 :=
  ⟨by decide, by decide, by decide, first_three_12_orderly, middle12_nonorderly, final12_orderly⟩


def C14 : List Nat := [1,2,4,5,7,8,10,13,15,18,21,26,29,37]

set_option maxHeartbeats 3000000 in
theorem final14_orderly : Orderly C14.reverse := by
  apply orderly_of_check 37 [29,26,21,18,15,13,10,8,7,5,4,2,1] <;> decide

theorem first_three_14_orderly (i : Nat) (h1 : 1 ≤ i) (h3 : i ≤ 3) :
    Orderly (coinPrefix C14 i) := by
  have hi : i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hi with rfl | rfl | rfl
  · exact orderly_of_check 1 [] (by decide) (by decide) (by decide)
  · exact orderly_of_check 2 [1] (by decide) (by decide) (by decide)
  · exact orderly_of_check 4 [2,1] (by decide) (by decide) (by decide)

theorem middle14_nonorderly (i : Nat) (h4 : 4 ≤ i) (hn : i < C14.length) :
    ¬ Orderly (coinPrefix C14 i) := by
  have hi : i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 := by
    change i < 14 at hn
    omega
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact not_orderly_of_better _ 8 [4,4] (by decide) (by decide) (by decide)
  · exact not_orderly_of_better _ 10 [5,5] (by decide) (by decide) (by decide)
  · exact not_orderly_of_better _ 11 [4,7] (by decide) (by decide) (by decide)
  · exact not_orderly_of_better _ 13 [5,8] (by decide) (by decide) (by decide)
  · exact not_orderly_of_better _ 16 [8,8] (by decide) (by decide) (by decide)
  · exact not_orderly_of_better _ 18 [5,13] (by decide) (by decide) (by decide)
  · exact not_orderly_of_better _ 21 [8,13] (by decide) (by decide) (by decide)
  · exact not_orderly_of_better _ 30 [15,15] (by decide) (by decide) (by decide)
  · exact not_orderly_of_better _ 29 [8,21] (by decide) (by decide) (by decide)
  · exact not_orderly_of_better _ 41 [15,26] (by decide) (by decide) (by decide)

theorem prefix_pattern_14 : SmallPrefixPattern 14 C14 :=
  ⟨by decide, by decide, by decide, first_three_14_orderly, middle14_nonorderly, final14_orderly⟩


theorem prefix_pattern_13 : SmallPrefixPattern 13 C13 :=
  ⟨by decide, by decide, by decide, first_three_orderly, all_middle_nonorderly, final_orderly⟩

/-- Source: Theorem 4.3 and Definition 5.1, at r=4. -/
def dPrefix8 (a : Nat) : List Nat :=
  [1,2,2+a,3+a,3+2*a,4+2*a,4+3*a,5+3*a]

def gPrefix6 : List Nat := [1,2,4,5,7,9]

theorem not_D_prefix (a : Nat) : C14.take 8 ≠ dPrefix8 a := by
  intro h
  have hc4 := congrArg (fun L : List Nat => L[2]!) h
  change 4 = 2+a at hc4
  have ha : a = 2 := by omega
  subst a
  revert h
  decide

theorem not_G_prefix : C14.take 6 ≠ gPrefix6 := by decide

theorem length14_counterexample_to_D_or_G :
    ∃ C : List Nat, SmallPrefixPattern 14 C ∧
      (∀ a : Nat, C.take 8 ≠ dPrefix8 a) ∧ C.take 6 ≠ gPrefix6 :=
  ⟨C14, prefix_pattern_14, not_D_prefix, not_G_prefix⟩

theorem every_small_length (n : Nat) (hlo : 11 ≤ n) (hhi : n ≤ 14) :
    ∃ C : List Nat, SmallPrefixPattern n C := by
  have hn : n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 := by omega
  rcases hn with rfl | rfl | rfl | rfl
  · exact ⟨C11, prefix_pattern_11⟩
  · exact ⟨C12, prefix_pattern_12⟩
  · exact ⟨C13, prefix_pattern_13⟩
  · exact ⟨C14, prefix_pattern_14⟩

theorem every_small_length_family (n : Nat) (hlo : 11 ≤ n) (hhi : n ≤ 14) :
    Family.HasPrefixPattern n := every_small_length n hlo hhi

#print axioms every_small_length
#print axioms every_small_length_family
#print axioms length14_counterexample_to_D_or_G

end CoinOrder
