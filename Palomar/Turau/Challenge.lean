module

public import Lean

@[expose] public section

/-!
Independent statement of the stretched path-and-ear flooding family.
The implementation uses zero-based send rounds (index 0 is physical round 1).
The centers are the displayed sources. The optimality deduction from Turau's
Theorem 4(3) is cited, not a declaration in this Challenge.
-/

namespace AmnesiacStretched

inductive Role (L : Nat)
  | center
  | ear
  | arm (right : Bool) (depth : Fin L)
  deriving DecidableEq

abbrev Vertex (k L : Nat) := Fin k × Role L

abbrev Msg (k L : Nat) := Vertex k L → Vertex k L → Prop

def localAdj {L : Nat} : Role L → Role L → Prop
  | .center, .ear | .ear, .center => True
  | .center, .arm _ j | .arm _ j, .center => j.val = 0
  | .ear, .arm _ j | .arm _ j, .ear => j.val = 0
  | .arm s i, .arm t j => s=t ∧ (i.val+1=j.val ∨ j.val+1=i.val)
  | _, _ => False

def bridge {k L : Nat} (u v : Vertex k L) : Prop :=
  match u.2,v.2 with
  | .arm s i,.arm t j => i.val+1=L ∧ j.val+1=L ∧
      ((s=true ∧ t=false ∧ u.1.val+1=v.1.val) ∨
       (s=false ∧ t=true ∧ v.1.val+1=u.1.val))
  | _, _ => False

def adj {k L : Nat} (u v : Vertex k L) : Prop :=
  (u.1=v.1 ∧ localAdj u.2 v.2) ∨ bridge u v

def seed {k L : Nat} (u : Vertex k L) : Prop := u.2=.center

def next {k L : Nat} (M : Msg k L) (u v : Vertex k L) : Prop :=
  adj u v ∧ (∃ w, M w u) ∧ ¬ M v u

def rounds {k L : Nat} : Nat → Msg k L
  | 0 => fun u v => seed u ∧ adj u v
  | r+1 => next (rounds r)

def localTrace {L : Nat} (r : Nat) : Role L → Role L → Prop
  | .center, .ear => r=0
  | .center, .arm _ j => j.val=0 ∧ r=0
  | .ear, .center => r=2
  | .ear, .arm _ j => j.val=0 ∧ r=1
  | .arm _ j, .center => j.val=0 ∧ r=2
  | .arm _ j, .ear => j.val=0 ∧ r=1
  | .arm s i, .arm t j => s=t ∧ i.val+1=j.val ∧ (r=i.val+1 ∨ r=i.val+2)
  | _,_ => False

def trace {k L : Nat} (r : Nat) (u v : Vertex k L) : Prop :=
  (u.1=v.1 ∧ localTrace r u.2 v.2) ∨ (bridge u v ∧ r=L)

def width (L : Nat) : Nat := 2*L+1

inductive Walk {k L : Nat} : Vertex k L → Vertex k L → Nat → Prop
  | nil (u) : Walk u u 0
  | cons {u v w n} : adj u v → Walk v w n → Walk u w (n+1)

def radiusAtMost {k L : Nat} (r : Nat) : Prop :=
  ∃ u : Vertex k L, ∀ v, ∃ n≤r, Walk u v n

def centerOf {L : Nat} {k : Nat} (i : Fin k) : Vertex k L := (i,.center)

theorem literal_trace {k L : Nat} (hL : 0<L) (r : Nat) (u v : Vertex k L) :
    rounds r u v ↔ trace r u v := by
  sorry

theorem center_injective {k L : Nat} : Function.Injective (centerOf (k:=k) (L:=L)) := by
  sorry

theorem seed_image {k L : Nat} (u : Vertex k L) :
    seed u ↔ ∃ i : Fin k, centerOf i=u := by
  sorry

theorem graph_symm {k L : Nat} {u v : Vertex k L} (h : adj u v) : adj v u := by
  sorry

theorem graph_loopless {k L : Nat} (u : Vertex k L) : ¬ adj u u := by
  sorry

theorem graph_nonbip {k L : Nat} (hk : 0<k) (hL : 0<L) :
    ¬ ∃ f : Vertex k L → Bool, ∀ u v, adj u v → f u ≠ f v := by
  sorry

theorem graph_connected {k L : Nat} (hk : 0<k) (hL : 0<L)
    (u v : Vertex k L) : ∃ n, Walk u v n := by
  sorry

theorem exact_radius {k L r : Nat} (hk : 0<k) (hL : 0<L) :
    radiusAtMost (k:=k) (L:=L) r ↔ k*width L/2≤r := by
  sorry

theorem all_vertices_receive {k L : Nat} (hL : 2≤L) (u : Vertex k L) :
    ∃ r≤L, ∃ v, rounds r v u := by
  sorry

theorem exact_displayed_time {k t : Nat} (hk : 0<k) (ht : 3≤t) (n : Nat) :
    (∃ u v : Vertex k (t-1), rounds n u v) ↔ n<t := by
  sorry

theorem stretched_disproof {k t : Nat} (hk : 4≤k) (ht : 3≤t) :
    (∀ r, radiusAtMost (k:=k) (L:=t-1) r ↔ k*t-(k+1)/2≤r) ∧
    (∀ n, (∃ u v : Vertex k (t-1), rounds n u v) ↔ n<t) ∧
    k*t<(k*t-(k+1)/2)+k-1 := by
  sorry

end AmnesiacStretched
