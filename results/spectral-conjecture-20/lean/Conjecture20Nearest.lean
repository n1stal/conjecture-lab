import ManhattanWinner
import ManhattanSmallFinal
import C20Classify

namespace Conjecture20
open Matrix Conjecture20Squared

/-- Comparison is over every simple graph of the same order except the
isomorphism class of the reference graph. The matrix form of isomorphism is
simultaneous relabeling by an equivalence of vertex types. -/
def IsNearest (n : Nat)
    (cost : (B : Matrix (Fin (3*n)) (Fin (3*n)) ℝ) → B.IsHermitian → ℝ)
    (A : Fin (3*n) → Fin (3*n) → Bool) (hs : ∀ i j, A i j=A j i) : Prop :=
  (¬ RelabelAs (realAdj A) (balanced n)) ∧
    ∀ (B : Fin (3*n) → Fin (3*n) → Bool) (hb : ∀ i j, B i j=B j i),
      (∀ i, B i i=false) → (¬ RelabelAs (realAdj B) (balanced n)) →
      cost _ (realAdjHerm A hs) ≤ cost _ (realAdjHerm B hb)

/-- The complete nearest-graph assertion for both of the source's scores. -/
theorem nearest_both (n : Nat) (hn : 3≤n)
    (A : Fin (3*n) → Fin (3*n) → Bool) (hs : ∀ i j, A i j=A j i)
    (hd : ∀ i, A i i=false) :
    (IsNearest n (ManhattanLarge.l1 n) A hs ↔ RelabelAs (realAdj A) (hub n)) ∧
    (IsNearest n (score n) A hs ↔ RelabelAs (realAdj A) (hub n)) := by
  constructor
  · by_cases h5 : 5≤n
    · exact ManhattanLarge.manhattan_unique_minimizer_large n h5 A hs hd
    · exact ManhattanSmallFinal.manhattan_unique_minimizer_small n (by omega) A hs hd
  · exact squared_unique_nearest n hn A hs hd

#print axioms nearest_both
end Conjecture20
