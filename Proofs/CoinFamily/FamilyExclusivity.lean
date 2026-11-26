module

public import Proofs.CoinFamily.PrefixTheorems

@[expose] public section

set_option autoImplicit false
namespace CoinOrder.Family

/-- The denominations of D, Theorem 4.3. The index starts at 1. -/
def dValue (r a : Nat) : Nat → Nat :=
  Nat.rec 0 (fun k prev =>
    if k = 0 then 1 else if k = 1 then 2 else
      prev + if 2*r+2 < k+1 then a+1 else if (k+1)%2=0 then 1 else a)

/-- The denominations of G, Definition 5.1. The index starts at 1. -/
def gValue (r : Nat) : Nat → Nat :=
  Nat.rec 0 (fun k prev =>
    if k = 0 then 1 else
      prev + if 2*r+4 ≤ k+1 then 5 else
        if k+1 ≤ 5 then (if (k+1)%2=0 then 1 else 2)
        else (if (k+1)%2=0 then 2 else 3))

def IsD (r : Nat) (C : List Nat) : Prop :=
  C.length=3*r+2 ∧ ∃ a, 2 ≤ a ∧
    ∀ i < 3*r+2, C[i]? = some (dValue r a (i+1))

def IsG (r : Nat) (C : List Nat) : Prop :=
  C.length=3*r+2 ∧ 2 ≤ r ∧
    ∀ i < 3*r+2, C[i]? = some (gValue r (i+1))

theorem d_step (r a k : Nat) :
    dValue r a (k+1) = if k = 0 then 1 else if k = 1 then 2 else
      dValue r a k + if 2*r+2 < k+1 then a+1 else if (k+1)%2=0 then 1 else a := rfl

theorem g_step (r k : Nat) : gValue r (k+1) = if k = 0 then 1 else
    gValue r k + if 2*r+4 ≤ k+1 then 5 else
      if k+1 ≤ 5 then (if (k+1)%2=0 then 1 else 2)
      else (if (k+1)%2=0 then 2 else 3) := rfl

theorem d_third (r a : Nat) (hr : 3 ≤ r) : dValue r a 3 = 2+a := by
  rw [d_step r a 2, show dValue r a 2 = 2 from rfl]
  split <;> try omega
  split <;> try omega
  split <;> try omega
  split <;> omega

theorem d_eighth (r a : Nat) (hr : 3 ≤ r) : dValue r a 8 = 5+3*a := by
  rw [d_step r a 7, d_step r a 6, d_step r a 5, d_step r a 4, d_step r a 3, d_third r a hr]
  have h (j : Nat) (hj : j ≤ 8) : ¬ 2*r+2 < j := by omega
  simp [h]
  omega

theorem g_sixth (r : Nat) (hr : 2 ≤ r) : gValue r 6 = 9 := by
  rw [g_step r 5, g_step r 4, g_step r 3, g_step r 2, g_step r 1, show gValue r 1 = 1 from rfl]
  have h (j : Nat) (hj : j ≤ 6) : ¬ 2*r+4 ≤ j := by omega
  simp [h]

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
  rw [d_third r a hr] at h3
  rw [d_eighth r a hr] at h8
  simp at h3 h8
  omega

theorem full_not_G (k r : Nat) (hr : 2 ≤ r) : ¬ IsG r (full k).reverse := by
  rintro ⟨_,_,ha⟩
  have h6 := ha 5 (by omega)
  rw [(head_values k).2.1] at h6
  rw [g_sixth r hr] at h6
  contradiction

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
