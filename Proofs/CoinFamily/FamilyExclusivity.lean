module

public import Proofs.CoinFamily.PrefixTheorems

@[expose] public section

set_option autoImplicit false
namespace CoinOrder.Family

/-- The denominations of D, Theorem 4.3. The index starts at 1. -/
def dValue (r a : Nat) : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | k+3 => dValue r a (k+2) +
      if 2*r+2 < k+3 then a+1 else if (k+3)%2=0 then 1 else a

/-- The denominations of G, Definition 5.1. The index starts at 1. -/
def gValue (r : Nat) : Nat → Nat
  | 0 => 0
  | 1 => 1
  | k+2 => gValue r (k+1) +
      if 2*r+4 ≤ k+2 then 5 else
      if k+2 ≤ 5 then (if (k+2)%2=0 then 1 else 2)
      else (if (k+2)%2=0 then 2 else 3)

def IsD (r : Nat) (C : List Nat) : Prop :=
  C.length=3*r+2 ∧ ∃ a, 2 ≤ a ∧
    ∀ i < 3*r+2, C[i]? = some (dValue r a (i+1))

def IsG (r : Nat) (C : List Nat) : Prop :=
  C.length=3*r+2 ∧ 2 ≤ r ∧
    ∀ i < 3*r+2, C[i]? = some (gValue r (i+1))

private theorem tail_initial (k : Nat) : (tail k).reverse.take 8 =
    [1,2,4,5,7,8,10,13] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [tail,List.reverse_cons,List.take_append_of_le_length (by simp),ih]

theorem initial (k : Nat) : (full k).reverse.take 8 = [1,2,4,5,7,8,10,13] := by
  rw [full,List.reverse_cons,List.take_append_of_le_length (by simp),tail_initial]

private theorem head_values (k : Nat) :
    (full k).reverse[2]? = some 4 ∧
    (full k).reverse[5]? = some 8 ∧
    (full k).reverse[7]? = some 13 := by
  have h := initial k
  have atIndex (i v : Nat) (hi : i < 8)
      (hv : ([1,2,4,5,7,8,10,13] : List Nat)[i]? = some v) :
      (full k).reverse[i]? = some v := by
    rw [← hv,← h,List.getElem?_take,ite_eq_left hi]
  exact ⟨atIndex 2 4 (by decide) rfl,atIndex 5 8 (by decide) rfl,atIndex 7 13 (by decide) rfl⟩

theorem full_not_D (k r : Nat) (hr : 3 ≤ r) : ¬ IsD r (full k).reverse := by
  rintro ⟨_,a,_,ha⟩
  have h3 := ha 2 (by omega)
  have h8 := ha 7 (by omega)
  rw [(head_values k).1] at h3
  rw [(head_values k).2.2] at h8
  have hsmall (i : Nat) (hi : i ≤ 8) : ¬ 2*r+2 < i := by omega
  simp [dValue,hsmall] at h3 h8
  omega

theorem full_not_G (k r : Nat) (hr : 2 ≤ r) : ¬ IsG r (full k).reverse := by
  rintro ⟨_,_,ha⟩
  have h6 := ha 5 (by omega)
  rw [(head_values k).2.1] at h6
  have hsmall (i : Nat) (hi : i ≤ 6) : ¬ 2*r+4 ≤ i := by omega
  simp [gValue,hsmall] at h6

theorem part3_exclusivity_refuted (r : Nat) (hr : 5 ≤ r) :
    ∃ C : List Nat, C.length = 3*r+2 ∧ C.head? = some 1 ∧ C.Pairwise (· < ·) ∧
      (∀ i, 1 ≤ i → i ≤ 3 → Orderly (coinPrefix C i)) ∧
      (∀ i, 4 ≤ i → i < C.length → ¬ Orderly (coinPrefix C i)) ∧
      Orderly C.reverse ∧ ¬ IsD r C ∧ ¬ IsG r C := by
  let k := 3*r+2-13
  have hk : k ≠ 1 := by dsimp [k]; omega
  refine ⟨(full k).reverse,?_,full_unit k,full_strict k,first k,?_,?_,full_not_D k r (by omega),full_not_G k r (by omega)⟩
  · simp only [List.length_reverse,full_length]
    dsimp [k]; omega
  · intro i h4 hi
    exact middle k i h4 (by simpa using hi)
  · simpa using full_orderly k hk

#print axioms part3_exclusivity_refuted

end CoinOrder.Family
