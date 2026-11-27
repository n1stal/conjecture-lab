module

public import Palomar.CazenaveC2.RationalArithmetic
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Cazenave §7 Conjecture 2 (#20829), exact 11-vertex graph adapter.
Numbers are literal finite graph data, not trusted external spectral values.
This is a private source draft. -/
namespace CazenaveC2

open Matrix
open scoped Matrix BigOperators

def edgeList : List (Fin 11 × Fin 11) :=
  [(0,1),(0,2),(1,2),(1,3),(2,3),(4,5),(4,6),(5,6),(5,7),(6,7),
   (0,8),(8,9),(9,10),(10,4)]

def rawEdge (i j : Fin 11) : Prop := (i,j) ∈ edgeList

instance rawEdge_decidable : DecidableRel rawEdge := fun i j =>
  inferInstanceAs (Decidable ((i,j) ∈ edgeList))

def G : SimpleGraph (Fin 11) := SimpleGraph.fromRel rawEdge

instance adjacency_decidable : DecidableRel G.Adj := by
  unfold G
  infer_instance

/-- Actual graph connectivity, proved by the spanning paths from vertex zero. -/
theorem G_connected : G.Connected := by
  apply (G.connected_iff_exists_forall_reachable).mpr
  refine ⟨0, ?_⟩
  have h1 : G.Reachable 0 1 := (show G.Adj 0 1 by decide).reachable
  have h2 : G.Reachable 0 2 := (show G.Adj 0 2 by decide).reachable
  have h3 : G.Reachable 0 3 := h1.trans (show G.Adj 1 3 by decide).reachable
  have h8 : G.Reachable 0 8 := (show G.Adj 0 8 by decide).reachable
  have h9 : G.Reachable 0 9 := h8.trans (show G.Adj 8 9 by decide).reachable
  have h10 : G.Reachable 0 10 := h9.trans (show G.Adj 9 10 by decide).reachable
  have h4 : G.Reachable 0 4 := h10.trans (show G.Adj 10 4 by decide).reachable
  have h5 : G.Reachable 0 5 := h4.trans (show G.Adj 4 5 by decide).reachable
  have h6 : G.Reachable 0 6 := h4.trans (show G.Adj 4 6 by decide).reachable
  have h7 : G.Reachable 0 7 := h5.trans (show G.Adj 5 7 by decide).reachable
  intro i
  fin_cases i
  · exact ⟨.nil⟩
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
  · exact h10

def neighbors : Fin 11 → Finset (Fin 11) :=
  ![{1,2,8}, {0,2,3}, {0,1,3}, {1,2}, {5,6,10}, {4,6,7},
    {4,5,7}, {5,6}, {0,9}, {8,10}, {9,4}]

def degreeRow : Fin 11 → ℕ := ![3,3,3,2,3,3,3,2,2,2,2]

theorem neighbor_ledger (i : Fin 11) : G.neighborFinset i = neighbors i := by
  rw [SimpleGraph.neighborFinset_eq_filter]
  fin_cases i <;> decide

theorem degree_ledger (i : Fin 11) : G.degree i = degreeRow i := by
  rw [← G.card_neighborFinset_eq_degree, neighbor_ledger]
  fin_cases i <;> decide

noncomputable def A : Matrix (Fin 11) (Fin 11) ℝ := G.adjMatrix ℝ
noncomputable def L : Matrix (Fin 11) (Fin 11) ℝ := G.lapMatrix ℝ

theorem A_hermitian : A.IsHermitian := G.isHermitian_adjMatrix ℝ
theorem L_hermitian : L.IsHermitian := G.isHermitian_lapMatrix ℝ

def adjAction (x : Fin 11 → ℝ) : Fin 11 → ℝ :=
  ![x 1+x 2+x 8, x 0+x 2+x 3, x 0+x 1+x 3, x 1+x 2,
    x 5+x 6+x 10, x 4+x 6+x 7, x 4+x 5+x 7, x 5+x 6,
    x 0+x 9, x 8+x 10, x 9+x 4]

theorem adjAction_apply (x : Fin 11 → ℝ) (i : Fin 11) :
    (A *ᵥ x) i = adjAction x i := by
  rw [A, SimpleGraph.adjMatrix_mulVec_apply, neighbor_ledger]
  fin_cases i <;>
    norm_num [neighbors, adjAction, Finset.sum_insert, Finset.sum_singleton]
    <;> ring

theorem lapAction_apply (x : Fin 11 → ℝ) (i : Fin 11) :
    (L *ᵥ x) i = (degreeRow i : ℝ)*x i - adjAction x i := by
  have ha := adjAction_apply x i
  rw [A, SimpleGraph.adjMatrix_mulVec_apply] at ha
  rw [L, SimpleGraph.lapMatrix_mulVec_apply, degree_ledger, ha]

/-- Native Laplacian energy and the explicit positive square form agree. -/
theorem lapShift_eval (x : Fin 11 → ℝ) :
    (37/8:ℝ)*dotProduct x x - dotProduct x (L *ᵥ x) = lapShiftForm x := by
  simp [dotProduct, lapAction_apply, lapShiftForm, diamondForm, degreeRow,
    adjAction, Fin.sum_univ_succ]
  ring

end CazenaveC2
