module

public import Std
public import Lean.Elab.Tactic.Omega
public import Lean.Elab.Tactic.RCases

@[expose] public section

/-! Exact edge-table statement of the 11-vertex counterexample. -/
namespace StrongArboricityCore

abbrev V := Fin 11
abbrev E := Fin 19
abbrev Color := Fin 3

def edgeArray : Array (V × V) :=
  #[(0,1),(0,2),(1,2),(0,3),(1,3),(0,4),(1,4),
    (2,5),(3,5),(2,6),(3,6),(2,7),(4,7),(2,8),(4,8),(3,9),(4,9),(3,10),(4,10)]

theorem edgeArray_size : edgeArray.size = 19 := by decide

def ends (e : E) : V × V := edgeArray[e.val]'e.isLt

def On (e : E) (u v : V) : Prop := ends e = (u,v) ∨ ends e = (v,u)

instance (e : E) (u v : V) : Decidable (On e u v) := by
  unfold On
  infer_instance

theorem On.flip {e : E} {u v : V} (h : On e u v) : On e v u := by
  cases h with
  | inl h => exact Or.inr h
  | inr h => exact Or.inl h

/-- A path with ordered vertex and edge witnesses. No graph library needed. -/
inductive EdgePath : List V → List E → Prop
  | one (u : V) : EdgePath [u] []
  | step {u v : V} {vs : List V} {e : E} {es : List E} :
      On e u v → EdgePath (v::vs) es → EdgePath (u::v::vs) (e::es)

/-- A simple path of length at least two, with a closing edge, is exactly a
broken simple cycle. Palette function has one value for each actual edge. -/
def Strong (f : E → Color) : Prop :=
  ∀ (vs : List V) (es : List E), EdgePath vs es → vs.Nodup →
    2 ≤ es.length → (∃ (u v : V) (e : E),
      vs.head? = some u ∧ vs.getLast? = some v ∧ On e u v) →
    ∀ c : Color, (∀ e ∈ es, f e = c) → False

/-- For this increasing simple edge table, one earlier neighbor is counted
once per pair whose second endpoint is this vertex. -/
def backDegree (v : V) : Nat :=
  (edgeArray.toList.filter fun e => decide (e.2=v)).length

/-- Printed conjecture 3 fails: displayed order bounds the coloring
number by 3, yet no strongly woody coloring with 3 colors exists. -/
def Counterexample : Prop :=
  (edgeArray.toList.map fun p => (p.1.val,p.2.val)).Nodup ∧
  (edgeArray.toList.all fun p => decide (p.1.val<p.2.val)) = true ∧
  (∀ v : V, backDegree v ≤ 2) ∧
  ¬ ∃ f : E → Color, Strong f

theorem strong_arboricity_coloring_number_counterexample : Counterexample := by
  sorry

end StrongArboricityCore
