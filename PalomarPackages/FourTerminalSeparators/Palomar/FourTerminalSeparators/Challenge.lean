module

public import Std

@[expose] public section

/-!
# Sharp four-terminal vertex and edge separator bounds

In a finite connected simple graph choose four distinct marked vertices
with six-distance sum S. The exact universal minimum is (S-7)/4 in
natural arithmetic, or max(0, ceil((S-10)/4)). Separator sets avoid all
marked vertices and each separates at least one marked pair. Both
existence for all graphs and a sharp example for each S≥6 are stated.
The analogous separately attained edge bound is (S+1)/4; cuts are
undirected edge sets and may meet marked vertices at their endpoint.
-/

namespace TriameterQ3Graph

universe u
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

/-- Shortest-walk distances plus an exact finite-length witness for every pair. -/
structure ShortestDistances (G : SimpleGraph V) where
  dist : V → V → Nat
  geodesic : ∀ a b, Walk G a b (dist a b)
  minimal : ∀ a b n, Walk G a b n → dist a b ≤ n

end TriameterQ3Graph

namespace HakKozerenkoSeparatorGraph

open TriameterQ3Graph
universe u
variable {V : Type u} {G : SimpleGraph V}

/-- A walk is blocked exactly when it meets S. This includes endpoint
indices, harmless when S excludes all terminals. -/
def Separates (G : SimpleGraph V) (S : V → Prop) (a b : V) : Prop :=
  ∀ (n : Nat) (W : Walk G a b n), ∃ j, j ≤ n ∧ S (W.point j)

def TSeparator (G : SimpleGraph V) (T S : V → Prop) : Prop :=
  (∀ v, S v → ¬T v) ∧ ∃ a b, T a ∧ T b ∧ Separates G S a b

structure VertexFamily (G : SimpleGraph V) (T : V → Prop) (q : Nat) where
  part : Fin q → V → Prop
  each : ∀ i, TSeparator G T (part i)
  disjoint : ∀ i j, i ≠ j → ∀ v, part i v → part j v → False

def PackingCap (G : SimpleGraph V) (T : V → Prop) (c : Nat) : Prop :=
  ∀ q, VertexFamily G T q → q ≤ c

def markFour (a b c d v : V) : Prop := v=a ∨ v=b ∨ v=c ∨ v=d

structure FourApart (a b c d : V) : Prop where
  ab : a≠b
  ac : a≠c
  ad : a≠d
  bc : b≠c
  bd : b≠d
  cd : c≠d

def fourSum (M : ShortestDistances G) (a b c d : V) : Nat :=
  M.dist a b+M.dist c d+M.dist a c+M.dist b d+M.dist a d+M.dist b c

/-- A realization witnessing the exact four-terminal vertex bound at S. -/
def VertexAttains (S : Nat) : Prop :=
  ∃ n : Nat, ∃ G : SimpleGraph (Fin n), ∃ M : ShortestDistances G,
    ∃ a b c d : Fin n, FourApart a b c d ∧ fourSum M a b c d=S ∧
      PackingCap G (markFour a b c d) ((S-7)/4)

/-- Given any natural terminal sum at least six, the exact universal
minimum number of disjoint four-terminal vertex separators is
(S-7)/4 in natural arithmetic, equivalently max(0, ceil((S-10)/4)).
The first conjunct gives a family in every actual finite graph with
that sum, and the second supplies an actual realization whose every
family has size at most the displayed number. -/
theorem sharp_four_vertex_separator_bound (S : Nat) (hS : 6≤S) :
    (∀ (n : Nat) (G : SimpleGraph (Fin n)) (M : ShortestDistances G)
      (a b c d : Fin n), FourApart a b c d → fourSum M a b c d=S →
       Nonempty (VertexFamily G (markFour a b c d) ((S-7)/4))) ∧
    VertexAttains S := by
  sorry

end HakKozerenkoSeparatorGraph

namespace HakKozerenkoEdgeSeparator
open TriameterQ3Graph HakKozerenkoSeparatorGraph
universe u
variable {V : Type u} {G : SimpleGraph V} {T : V → Prop}

def EdgeSeparates (G : SimpleGraph V) (A : V→V→Prop) (s t : V) : Prop :=
  ∀ (n : Nat) (W : Walk G s t n), ∃ j, j<n ∧ A (W.point j) (W.point (j+1))

structure EdgeFamily (G : SimpleGraph V) (T : V→Prop) (m : Nat) where
  part : Fin m → V → V → Prop
  symm : ∀ i x y, part i x y → part i y x
  valid : ∀ i x y, part i x y → G.adj x y
  each : ∀ i, ∃ s t, T s ∧ T t ∧ EdgeSeparates G (part i) s t
  disjoint : ∀ i j, i≠j → ∀ x y, part i x y → part j x y → False

def EdgeCap (G : SimpleGraph V) (T : V→Prop) (e : Nat) : Prop :=
  ∀ m, EdgeFamily G T m → m≤e

def fourSumEdge (M : ShortestDistances G) (a b c d : V) : Nat :=
  M.dist a b+M.dist c d+M.dist a c+M.dist b d+M.dist a d+M.dist b c

def markFourEdge (a b c d v : V) : Prop := v=a ∨ v=b ∨ v=c ∨ v=d

def EdgeAttains (S : Nat) : Prop :=
  ∃ n : Nat, ∃ G : SimpleGraph (Fin n), ∃ M : ShortestDistances G,
    ∃ a b c d : Fin n, FourApart a b c d ∧ fourSumEdge M a b c d=S ∧
      EdgeCap G (markFourEdge a b c d) ((S+1)/4)

/-- Exact universal minimum for families of pairwise edge-disjoint edge
separators of four distinct terminals, given the sum S of six
graph distances. Every S≥6 occurs in a finite connected simple graph. -/
theorem sharp_four_edge_separator_bound (S : Nat) (hS : 6≤S) :
    (∀ (n : Nat) (G : SimpleGraph (Fin n)) (M : ShortestDistances G)
      (a b c d : Fin n), FourApart a b c d → fourSumEdge M a b c d=S →
        Nonempty (EdgeFamily G (markFourEdge a b c d) ((S+1)/4))) ∧
    EdgeAttains S := by
  sorry

end HakKozerenkoEdgeSeparator
