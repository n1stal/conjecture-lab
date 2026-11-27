module

public import Std
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# Sharp distance packing for four prescribed terminals

Let k,p be positive integers. In a finite simple connected graph whose maximum
k-packing has p vertices, the largest possible sum of the six unordered
distances on four distinct prescribed vertices is 6k+4(k+1)(p−1).
A k-packing requires pairwise distance strictly greater than k.

More generally, for nonnegative integer terminal weights the sum weighted by
products attains exactly k times the total pair weight plus (k+1)(p−1) times
the maximum bipartition cut weight. Both targets include universal optimality
and actual graph attainment. These are the four-terminal packing statements
from the setting of Hak–Kozerenko §7 Question 3, not the separation statement
or a claim about the finite extremum for more than four terminals.
-/
namespace TriameterQ3Four

/-- A scalar value for each of the six unordered terminal pairs. -/
structure Edges where
  ab : Int
  ac : Int
  ad : Int
  bc : Int
  bd : Int
  cd : Int

/-- Values indexed by the eight cuts with the a-terminal on the first side. -/
structure Atoms where
  p000 : Int
  p001 : Int
  p010 : Int
  p011 : Int
  p100 : Int
  p101 : Int
  p110 : Int
  p111 : Int

/-- Inner product over the six unordered pairs. -/
def dot (x c : Edges) : Int :=
  x.ab*c.ab + x.ac*c.ac + x.ad*c.ad + x.bc*c.bc + x.bd*c.bd + x.cd*c.cd

/-- Total weight of the six pairs. -/
def coefficientSum (c : Edges) : Int :=
  c.ab + c.ac + c.ad + c.bc + c.bd + c.cd

/-- Weight crossing each cut, with a in the first side and bits for b,c,d. -/
def cutCosts (c : Edges) : Atoms :=
  ⟨0,
   c.ad + c.bd + c.cd,
   c.ac + c.bc + c.cd,
   c.ac + c.ad + c.bc + c.bd,
   c.ab + c.bc + c.bd,
   c.ab + c.ad + c.bc + c.cd,
   c.ab + c.ac + c.bd + c.cd,
   c.ab + c.ac + c.ad⟩

/-- Largest weight across any terminal bipartition. -/
def maxCut (c : Edges) : Int :=
  max (cutCosts c).p111 (max (cutCosts c).p110 (max (cutCosts c).p101 (max (cutCosts c).p100 (max (cutCosts c).p011 (max (cutCosts c).p010 (max (cutCosts c).p001 (0)))))))

/-- Pair coefficients are the products of terminal weights. -/
def terminalCoefficients (a b c d : Int) : Edges :=
  ⟨a*b,a*c,a*d,b*c,b*d,c*d⟩

end TriameterQ3Four

namespace TriameterQ3Graph

universe u

/-- A simple undirected graph: adjacency is symmetric and irreflexive. -/
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

namespace Walk
variable {V : Type u} {G : SimpleGraph V} {a b c : V} {m n : Nat}

def trivial (G : SimpleGraph V) (a : V) : Walk G a a 0 :=
  ⟨fun _ => a, rfl, rfl, fun _ h => (Nat.not_lt_zero _ h).elim⟩
end Walk

variable {V : Type u}

/-- Connectivity expressed using actual unweighted-edge walks. -/
def Connected (G : SimpleGraph V) : Prop :=
  ∀ a b : V, ∃ n : Nat, Nonempty (Walk G a b n)

/-- Shortest-walk distances plus an exact finite-length witness for every pair. -/
structure ShortestDistances (G : SimpleGraph V) where
  dist : V → V → Nat
  geodesic : ∀ a b, Walk G a b (dist a b)
  minimal : ∀ a b n, Walk G a b n → dist a b ≤ n

theorem smallest_witness (P : Nat → Prop) (n : Nat) (hn : P n) :
    ∃ m, P m ∧ ∀ j, P j → m ≤ j := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : ∃ m, m < n ∧ P m
    · obtain ⟨m,hm,hp⟩ := h
      exact ih m hm hp
    · exact ⟨n,hn,fun j hj => Nat.le_of_not_gt (fun h' => h ⟨j,h',hj⟩)⟩

theorem shortest_witness {G : SimpleGraph V} (hc : Connected G)
    (a b : V) : ∃ n, Nonempty (Walk G a b n) ∧
      ∀ m, Nonempty (Walk G a b m) → n ≤ m := by
  obtain ⟨n,hn⟩ := hc a b
  exact smallest_witness _ n hn

/-- Connected undirected graphs provide the shortest-distance data without
assuming any metric identities. -/
noncomputable def distancesOfConnected (G : SimpleGraph V)
    (hc : Connected G) : ShortestDistances G where
  dist := fun a b => (shortest_witness hc a b).choose
  geodesic := fun a b => Classical.choice (shortest_witness hc a b).choose_spec.1
  minimal := fun a b n p => (shortest_witness hc a b).choose_spec.2 n ⟨p⟩

namespace ShortestDistances
variable {G : SimpleGraph V} (M : ShortestDistances G)

theorem dist_self (a : V) : M.dist a a = 0 := by
  exact Nat.le_antisymm (M.minimal a a 0 (Walk.trivial G a)) (Nat.zero_le _)
end ShortestDistances

/-- An actual k-packing, with one index per selected vertex. -/
def IsPacking {G : SimpleGraph V} (M : ShortestDistances G)
    (k : Nat) {p : Nat} (f : Fin p → V) : Prop :=
  ∀ i j, i ≠ j → k < M.dist (f i) (f j)

theorem packing_injective {G : SimpleGraph V} (M : ShortestDistances G)
    {k p : Nat} {f : Fin p → V} (hf : IsPacking M k f) : Function.Injective f := by
  intro i j h
  by_cases he : i = j
  · exact he
  · have hh := hf i j he
    rw [h, M.dist_self] at hh
    exact (Nat.not_lt_zero _ hh).elim

/-- Exact packing number: a certified attaining packing and a universal cap. -/
structure ExactPacking {G : SimpleGraph V} (M : ShortestDistances G)
    (k p : Nat) : Prop where
  attained : ∃ f : Fin p → V, IsPacking M k f
  upper : ∀ n (f : Fin n → V), IsPacking M k f → n ≤ p

theorem finite_packing_bound {n p k : Nat} {G : SimpleGraph (Fin n)}
    (M : ShortestDistances G) (f : Fin p → Fin n) (h : IsPacking M k f) :
    p ≤ n := by
  have hf := packing_injective M h
  have hn : ((List.finRange p).map f).Nodup :=
    List.Pairwise.map f (fun a b ne e => ne (hf e)) (List.nodup_finRange p)
  have hs : (List.finRange p).map f ⊆ List.finRange n := fun {x} _ => List.mem_finRange x
  have hlen := hn.length_le_of_subset hs
  simpa only [List.length_map, List.length_finRange] using hlen

theorem largest_bounded_witness (P : Nat → Prop) (n : Nat)
    (h0 : P 0) : ∃ p, p ≤ n ∧ P p ∧ ∀ q, q ≤ n → P q → q ≤ p := by
  induction n with
  | zero => exact ⟨0,Nat.le_refl _,h0,fun q hq _ => hq⟩
  | succ n ih =>
    by_cases hn : P (n+1)
    · exact ⟨n+1,Nat.le_refl _,hn,fun q hq _ => hq⟩
    · obtain ⟨p,hp,hit,hu⟩ := ih
      refine ⟨p,Nat.le_trans hp (Nat.le_succ n),hit,?_⟩
      intro q hq hP
      have he : q ≠ n+1 := by intro e; exact hn (e ▸ hP)
      exact hu q (Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hq he)) hP

theorem finite_exact_packing_exists {n : Nat} {G : SimpleGraph (Fin n)}
    (M : ShortestDistances G) (k : Nat) : ∃ p, ExactPacking M k p := by
  let P (p : Nat) := ∃ f : Fin p → Fin n, IsPacking M k f
  have P0 : P 0 := ⟨Fin.elim0, fun i => Fin.elim0 i⟩
  obtain ⟨p,_,ha,hu⟩ := largest_bounded_witness P n P0
  refine ⟨p,⟨ha,?_⟩⟩
  exact fun q f hf => hu q (finite_packing_bound M f hf) ⟨f,hf⟩

/-- Actual distance-packing number of a connected finite graph. -/
noncomputable def packingNumber {n : Nat} {G : SimpleGraph (Fin n)}
    (M : ShortestDistances G) (k : Nat) : Nat :=
  (finite_exact_packing_exists M k).choose

theorem packingNumber_is_exact {n : Nat} {G : SimpleGraph (Fin n)}
    (M : ShortestDistances G) (k : Nat) : ExactPacking M k (packingNumber M k) :=
  (finite_exact_packing_exists M k).choose_spec

end TriameterQ3Graph

namespace TriameterQ3Graph

open TriameterQ3Four
universe u
variable {V : Type u} {G : SimpleGraph V}

/-- The four prescribed vertices, explicitly indexed a,b,c,d. -/
structure Terminals (V : Type u) where
  a : V
  b : V
  c : V
  d : V

/-- The terminal set really has four distinct vertices. -/
def Terminals.Distinct (T : Terminals V) : Prop :=
  T.a ≠ T.b ∧ T.a ≠ T.c ∧ T.a ≠ T.d ∧
  T.b ≠ T.c ∧ T.b ≠ T.d ∧ T.c ≠ T.d

/-- Shortest-walk distances on the six unordered pairs of terminal vertices. -/
def distanceVector (M : ShortestDistances G) (T : Terminals V) : Edges :=
  ⟨M.dist T.a T.b, M.dist T.a T.c, M.dist T.a T.d,
   M.dist T.b T.c, M.dist T.b T.d, M.dist T.c T.d⟩

/-- The part of the pair-diameter bound in excess of k. -/
def excess (k p : Nat) : Nat := (k+1)*(p-1)

/-- A nonnegative integer weight is assigned to each terminal. -/
structure Weights where
  a : Int
  b : Int
  c : Int
  d : Int

def Weights.Nonnegative (w : Weights) : Prop :=
  0 ≤ w.a ∧ 0 ≤ w.b ∧ 0 ≤ w.c ∧ 0 ≤ w.d

/-- Sum of terminal distances weighted by the products of the terminal weights. -/
def weightedTerminalSum (M : ShortestDistances G) (T : Terminals V) (w : Weights) : Int :=
  dot (distanceVector M T) (terminalCoefficients w.a w.b w.c w.d)

/-- Total product weight of the six unordered terminal pairs. -/
def pairMass (w : Weights) : Int :=
  coefficientSum (terminalCoefficients w.a w.b w.c w.d)

/-- Largest product-weight cut cost among all bipartitions of the terminals. -/
def cutMass (w : Weights) : Int :=
  maxCut (terminalCoefficients w.a w.b w.c w.d)

end TriameterQ3Graph

namespace TriameterQ3Attainment
open TriameterQ3Graph TriameterQ3Four

/-- Unweighted sum of the six unordered shortest terminal-pair distances. -/
def terminalPairSum {V : Type} {G : SimpleGraph V} (M : ShortestDistances G)
    (T : Terminals V) : Nat :=
  M.dist T.a T.b + M.dist T.a T.c + M.dist T.a T.d +
  M.dist T.b T.c + M.dist T.b T.d + M.dist T.c T.d

/-- Exactly the greatest possible terminal pair-distance sum with the given
nonnegative integer vertex weights and the given distance-packing number. -/
theorem weighted_four_terminal_exact (k p : Nat) (hk : 0 < k) (hp : 0 < p)
    (w : Weights) (hw : w.Nonnegative) :
    (∀ (n : Nat) (G : SimpleGraph (Fin n)) (hC : Connected G) (T : Terminals (Fin n)),
      T.Distinct → packingNumber (distancesOfConnected G hC) k = p →
      weightedTerminalSum (distancesOfConnected G hC) T w ≤
        (k : Int)*pairMass w + (excess k p : Int)*cutMass w) ∧
    (∃ (n : Nat) (G : SimpleGraph (Fin n)) (hC : Connected G) (T : Terminals (Fin n)),
      T.Distinct ∧ packingNumber (distancesOfConnected G hC) k = p ∧
      weightedTerminalSum (distancesOfConnected G hC) T w =
        (k : Int)*pairMass w + (excess k p : Int)*cutMass w) := by
  sorry

/-- Exact unweighted extremum for four prescribed distinct vertices, measured
by the sum over the six unordered pairs. This answers the four-terminal
packing branch, not the higher-terminal finite or separator branches. -/
theorem four_terminal_unweighted_exact (k p : Nat) (hk : 0 < k) (hp : 0 < p) :
    (∀ (n : Nat) (G : SimpleGraph (Fin n)) (hC : Connected G) (T : Terminals (Fin n)),
      T.Distinct → packingNumber (distancesOfConnected G hC) k = p →
      terminalPairSum (distancesOfConnected G hC) T ≤ 6*k+4*(k+1)*(p-1)) ∧
    (∃ (n : Nat) (G : SimpleGraph (Fin n)) (hC : Connected G) (T : Terminals (Fin n)),
      T.Distinct ∧ packingNumber (distancesOfConnected G hC) k = p ∧
      terminalPairSum (distancesOfConnected G hC) T = 6*k+4*(k+1)*(p-1)) := by
  sorry

end TriameterQ3Attainment
