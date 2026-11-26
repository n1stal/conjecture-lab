module

public import Std

@[expose] public section

set_option autoImplicit false

namespace CoinOrder
noncomputable def greedyCoins : List Nat → Nat → List Nat :=
  List.rec (fun _ => [])
    (fun d _ rec v => List.replicate (v / d) d ++ rec (v % d))

def Represents (C : List Nat) (v : Nat) (R : List Nat) : Prop :=
  (∀ x ∈ R, x ∈ C) ∧ R.sum = v

/-- The greedy representation is valid and uses at most as many coins
    as every other representation, for every amount. -/
def Orderly (C : List Nat) : Prop :=
  ∀ v, Represents C v (greedyCoins C v) ∧
    ∀ R, Represents C v R → (greedyCoins C v).length ≤ R.length

def coinPrefix (C : List Nat) (n : Nat) : List Nat := (C.take n).reverse
end CoinOrder

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

/-- Exact Van Cott–Zhang prefix pattern at length n. -/
def HasPrefixPattern (n : Nat) : Prop :=
  ∃ C : List Nat, C.length = n ∧ C.head? = some 1 ∧ C.Pairwise (· < ·) ∧
    (∀ i, 1 ≤ i → i ≤ 3 → Orderly (coinPrefix C i)) ∧
    (∀ i, 4 ≤ i → i < C.length → ¬ Orderly (coinPrefix C i)) ∧
    Orderly C.reverse

/-- Conjecture 5.2(3), with D and G according to the paper. -/
def Conjecture523 : Prop :=
  ∀ (r : Nat) (C : List Nat), 1 ≤ r → C.length = 3*r+2 →
    C.head? = some 1 → C.Pairwise (· < ·) →
    (((∀ i, 1 ≤ i → i ≤ 3 → Orderly (coinPrefix C i)) ∧
      (∀ i, 4 ≤ i → i < C.length → ¬ Orderly (coinPrefix C i)) ∧
      Orderly C.reverse) ↔ (IsD r C ∨ IsG r C))
end CoinOrder.Family

namespace CoinOrder.Family

theorem every_length_ge_eleven (n : Nat) (h : 11 ≤ n) :
    HasPrefixPattern n := by sorry

theorem general_prohibition_fails (r : Nat) (h : 4 ≤ r) :
    HasPrefixPattern (3*r+1) := by sorry

theorem classification_fails (r : Nat) (h : 4 ≤ r) :
    ∃ C : List Nat, C.length = 3*r+2 ∧ C.head? = some 1 ∧ C.Pairwise (· < ·) ∧
      (∀ i, 1 ≤ i → i ≤ 3 → Orderly (coinPrefix C i)) ∧
      (∀ i, 4 ≤ i → i < C.length → ¬ Orderly (coinPrefix C i)) ∧
      Orderly C.reverse ∧ ¬ IsD r C ∧ ¬ IsG r C := by sorry

theorem conjecture523_false : ¬ Conjecture523 := by sorry


end CoinOrder.Family
