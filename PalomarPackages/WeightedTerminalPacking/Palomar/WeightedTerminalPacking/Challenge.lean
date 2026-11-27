module

public import Std
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# Exact weighted distance packing with at most five packed vertices

For every finite number of distinct prescribed terminal vertices,
every positive k, and every packing number p between one and five,
the largest weighted distance sum is k times the total pair weight plus
(k+1)(p−1) times the largest terminal cut product. The sum is over
unordered endpoint pairs with product weights. Packing uses distance
strictly greater than k. The theorem certifies both upper bound and
attainment in finite simple connected graphs.
-/
namespace TriameterQ3Graph

universe u

/-- Symmetric, irreflexive adjacency. -/
structure SimpleGraph (V : Type u) where
  adj : V → V → Prop
  symm : ∀ {a b}, adj a b → adj b a
  loopless : ∀ a, ¬ adj a a

/-- A native walk of length n, with values outside [0,n] ignored. -/
structure Walk {V : Type u} (G : SimpleGraph V) (a b : V) (n : Nat) where
  point : Nat → V
  first : point 0 = a
  last : point n = b
  step : ∀ i, i < n → G.adj (point i) (point (i+1))

variable {V : Type u}

/-- Connectivity expressed using actual unweighted-edge walks. -/
def Connected (G : SimpleGraph V) : Prop :=
  ∀ a b : V, ∃ n : Nat, Nonempty (Walk G a b n)

/-- Shortest-walk distances plus an exact finite-length witness for every pair. -/
structure ShortestDistances (G : SimpleGraph V) where
  dist : V → V → Nat
  geodesic : ∀ a b, Walk G a b (dist a b)
  minimal : ∀ a b n, Walk G a b n → dist a b ≤ n

/-- An actual k-packing, with one index per selected vertex. -/
def IsPacking {G : SimpleGraph V} (M : ShortestDistances G)
    (k : Nat) {p : Nat} (f : Fin p → V) : Prop :=
  ∀ i j, i ≠ j → k < M.dist (f i) (f j)

/-- Exact packing number: a certified attaining packing and a universal cap. -/
structure ExactPacking {G : SimpleGraph V} (M : ShortestDistances G)
    (k p : Nat) : Prop where
  attained : ∃ f : Fin p → V, IsPacking M k f
  upper : ∀ n (f : Fin n → V), IsPacking M k f → n ≤ p

end TriameterQ3Graph

namespace TriameterQ3SmallPacking
open TriameterQ3Graph

/-- Sum over one finite index. -/
def vsum : (n : Nat) → (Fin n → Nat) → Nat
  | 0, _ => 0
  | n+1, f => f 0 + vsum n (fun i => f i.succ)

/-- Sum over the unordered pairs, each appearing exactly once. -/
def psum : (n : Nat) → (Fin n → Fin n → Nat) → Nat
  | 0, _ => 0
  | n+1, f => vsum n (fun i => f 0 i.succ) + psum n (fun i j => f i.succ j.succ)

/-- Weight of a specified side of a terminal cut. -/
def partWeight {n : Nat} (w : Fin n → Nat) (s : Fin n → Bool) (a : Bool) : Nat :=
  vsum n (fun i => if s i = a then w i else 0)

/-- Product of the two side weights. -/
def cutWeight {n : Nat} (w : Fin n → Nat) (s : Fin n → Bool) : Nat :=
  partWeight w s true * partWeight w s false

/-- Six no longer plays a special role: sum once over each unordered pair
of terminal labels, with the product of its two natural-valued weights. -/
def terminalScore {V : Type} {G : SimpleGraph V} (M : ShortestDistances G)
    {r : Nat} (T : Fin r → V) (w : Fin r → Nat) : Nat :=
  psum r (fun i j => w i*w j*M.dist (T i) (T j))

/-- Total product weight of all unordered terminal pairs. -/
def pairWeight {r : Nat} (w : Fin r → Nat) : Nat :=
  psum r (fun i j => w i*w j)

/-- Length budget above the base distance k. -/
def packingRadius (k p : Nat) : Nat := (k+1)*(p-1)

end TriameterQ3SmallPacking

namespace TriameterQ3Public
open TriameterQ3Graph TriameterQ3SmallPacking

/-- C is the largest product of side weights over all terminal cuts,
with an attaining cut supplied rather than hidden in a choice definition. -/
def IsCutMaximum {r : Nat} (w : Fin r → Nat) (C : Nat) : Prop :=
  (∀ s : Fin r → Bool, cutWeight w s ≤ C) ∧ ∃ s : Fin r → Bool, cutWeight w s = C

/-- All finite simple connected graphs attaining exact packing number p
are compared with the stated value, and a graph attaining that value is
certified. ShortestDistances has an actual walk per pair and proves
shortness among all unit-edge walks. ExactPacking supplies an attained
packing and an upper bound on every actual packing. -/
def ExactWeightedValue {r : Nat} (w : Fin r → Nat) (k p S : Nat) : Prop :=
  (∀ (n : Nat) (G : SimpleGraph (Fin n)) (_ : Connected G) (M : ShortestDistances G)
      (T : Fin r → Fin n), Function.Injective T → ExactPacking M k p →
      terminalScore M T w ≤ S) ∧
  (∃ (n : Nat) (G : SimpleGraph (Fin n)) (_ : Connected G) (M : ShortestDistances G)
      (T : Fin r → Fin n), Function.Injective T ∧ ExactPacking M k p ∧
      terminalScore M T w = S)

/-- Exact weighted distance sum for arbitrary prescribed terminal count
and packing number at most five. -/
theorem weighted_extremum_up_to_five {r : Nat} (w : Fin r → Nat) (k p : Nat)
    (hk : 0 < k) (hp : 0 < p) (hbound : p ≤ 5) :
    ∃ C : Nat, IsCutMaximum w C ∧
      ExactWeightedValue w k p (k*pairWeight w+packingRadius k p*C) := by
  sorry

end TriameterQ3Public

namespace TriameterQ3Public
open TriameterQ3Graph TriameterQ3SmallPacking

/-- Complementary scope: four prescribed terminals and every positive
packing number, in the same Nat-weight graph model as the p≤5 result. -/
theorem weighted_extremum_four_terminals_all_p (w : Fin 4 → Nat) (k p : Nat)
    (hk : 0 < k) (hp : 0 < p) :
    ∃ C : Nat, IsCutMaximum w C ∧
      ExactWeightedValue w k p (k*pairWeight w+packingRadius k p*C) := by
  sorry

end TriameterQ3Public
