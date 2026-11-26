module

public import Proofs.CoinFamily.Prefixes
public import Proofs.CoinFamily.FamilyOrderly

@[expose] public section

set_option autoImplicit false
namespace CoinOrder.Family

theorem hasPrefixPattern_13 : HasPrefixPattern 13 := by
  exact hasPrefixPattern_at 0 (full_orderly 0 (by decide))

theorem hasPrefixPattern_ge15 (n : Nat) (hn : 15 ≤ n) : HasPrefixPattern n := by
  apply hasPrefixPattern_at_length n (by omega)
  exact full_orderly _ (by omega)

theorem part1_refuted_at_every_large_parameter (r : Nat) (hr : 4 ≤ r) :
    HasPrefixPattern (3*r+1) := by
  by_cases h : r=4
  · subst r
    exact hasPrefixPattern_13
  · exact hasPrefixPattern_ge15 _ (by omega)

#print axioms hasPrefixPattern_13
#print axioms hasPrefixPattern_ge15
#print axioms part1_refuted_at_every_large_parameter

end CoinOrder.Family
