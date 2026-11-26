module

public import Proofs.CoinFamily.SharpRange

@[expose] public section

set_option autoImplicit false

namespace CoinOrder.Family

theorem every_length_ge_eleven (n : Nat) (h : 11 ≤ n) :
    HasPrefixPattern n := hasPrefixPattern_ge11 n h

theorem general_prohibition_fails (r : Nat) (h : 4 ≤ r) :
    HasPrefixPattern (3*r+1) := part1_refuted_at_every_large_parameter r h

theorem classification_fails (r : Nat) (h : 4 ≤ r) :
    ∃ C : List Nat, C.length = 3*r+2 ∧ C.head? = some 1 ∧ C.Pairwise (· < ·) ∧
      (∀ i, 1 ≤ i → i ≤ 3 → Orderly (coinPrefix C i)) ∧
      (∀ i, 4 ≤ i → i < C.length → ¬ Orderly (coinPrefix C i)) ∧
      Orderly C.reverse ∧ ¬ IsD r C ∧ ¬ IsG r C := part3_exclusivity_refuted_ge4 r h

theorem conjecture523_false : ¬ Conjecture523 := vanCottZhangConjecture523_false

#print axioms every_length_ge_eleven
#print axioms general_prohibition_fails
#print axioms classification_fails
#print axioms conjecture523_false

end CoinOrder.Family
