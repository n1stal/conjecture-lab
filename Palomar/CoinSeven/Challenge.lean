module

public import Std

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 4096
namespace CoinOrder

/-- Greedy processes the denominations in decreasing order. -/
def greedyCount : List Nat → Nat → Nat
  | [], _ => 0
  | d :: ds, v => v / d + greedyCount ds (v % d)

def greedyCoins : List Nat → Nat → List Nat
  | [], _ => []
  | d :: ds, v => List.replicate (v / d) d ++ greedyCoins ds (v % d)

def Represents (C : List Nat) (v : Nat) (R : List Nat) : Prop :=
  (∀ x ∈ R, x ∈ C) ∧ R.sum = v

/-- The greedy representation is valid and uses at most as many coins
    as every other representation, for every amount. -/
def Orderly (C : List Nat) : Prop :=
  ∀ v, Represents C v (greedyCoins C v) ∧
    ∀ R, Represents C v R → (greedyCoins C v).length ≤ R.length

def coinPrefix (C : List Nat) (n : Nat) : List Nat := (C.take n).reverse

namespace SevenRegistry

theorem seven_denominations_no_pattern
    {C : List Nat} (len : C.length = 7) (first : C.head? = some 1)
    (strict : C.Pairwise (· < ·))
    (initial : ∀ i, 1 ≤ i → i ≤ 3 → Orderly (coinPrefix C i))
    (middle : ∀ i, 4 ≤ i → i < C.length → ¬ Orderly (coinPrefix C i))
    (full : Orderly C.reverse) : False := by sorry

end SevenRegistry
end CoinOrder
