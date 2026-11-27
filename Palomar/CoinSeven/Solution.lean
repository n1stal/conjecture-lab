module

public import Proofs.CoinSeven.NoSeven

@[expose] public section

namespace CoinOrder
namespace SevenRegistry

theorem seven_denominations_no_pattern
    {C : List Nat} (len : C.length = 7) (first : C.head? = some 1)
    (strict : C.Pairwise (· < ·))
    (initial : ∀ i, 1 ≤ i → i ≤ 3 → Orderly (coinPrefix C i))
    (middle : ∀ i, 4 ≤ i → i < C.length → ¬ Orderly (coinPrefix C i))
    (full : Orderly C.reverse) : False :=
  vanCottZhang_no_seven len first strict initial middle full

#print axioms seven_denominations_no_pattern

end SevenRegistry
end CoinOrder
