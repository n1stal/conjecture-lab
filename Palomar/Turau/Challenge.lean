module

public import Lean

@[expose] public section

/-!
Standalone statement model, intentionally without imports from this
repository. Definitions are kept verbatim from the checked development so
the Solution can reuse the proof without recreating the mathematics.
Round index 0 means the first physical round. Silence at index t
means no messages in the (t+1)-st round, not that the empty round is counted.
-/

namespace Flooding

abbrev Arc (n : Nat) := Fin n × Fin n

abbrev Edges (n : Nat) := List (Arc n)

def symmetric {n : Nat} (E : Edges n) : Prop :=
  ∀ u v, (u,v) ∈ E → (v,u) ∈ E

def loopless {n : Nat} (E : Edges n) : Prop :=
  ∀ u, (u,u) ∉ E

inductive Walk {n : Nat} (E : Edges n) : Fin n → Fin n → Nat → Prop
  | nil (u : Fin n) : Walk E u u 0
  | cons {u v w : Fin n} {l : Nat} :
      (u,v) ∈ E → Walk E v w l → Walk E u w (l+1)

def connected {n : Nat} (E : Edges n) : Prop :=
  ∀ u v, ∃ l, Walk E u v l

def bipartite {n : Nat} (E : Edges n) : Prop :=
  ∃ colors : Fin n → Bool, ∀ u v, (u,v) ∈ E → colors u ≠ colors v

def radiusAtMost {n : Nat} (E : Edges n) (bound : Nat) : Prop :=
  ∃ u, ∀ v, ∃ l ≤ bound, Walk E u v l

def first {n : Nat} (E : Edges n) (S : List (Fin n)) : Edges n :=
  E.filter fun e => decide (e.1 ∈ S)

def next {n : Nat} (E M : Edges n) : Edges n :=
  E.filter fun e => (M.any fun j => decide (j.2 = e.1)) && !(M.contains (e.2,e.1))

def messages {n : Nat} (E : Edges n) (S : List (Fin n)) : Nat → Edges n :=
  Nat.rec (first E S) (fun _ M => next E M)

def quietAfter {n : Nat} (E : Edges n) (S : List (Fin n)) (r : Nat) : Prop :=
  messages E S r = []

def isFloodNumber {n : Nat} (E : Edges n) (k t : Nat) : Prop :=
  (∃ S : List (Fin n), (S.Nodup ∧ S.length = k) ∧ quietAfter E S t) ∧
  ∀ (S : List (Fin n)) (r : Nat), S.Nodup ∧ S.length = k → quietAfter E S r → t ≤ r

def isRadius {n : Nat} (E : Edges n) (r : Nat) : Prop :=
  radiusAtMost E r ∧ ∀ s, radiusAtMost E s → r ≤ s

def TurauConjecture : Prop :=
  ∀ (n : Nat) (E : Edges n) (k t r : Nat),
    symmetric E → loopless E → connected E → ¬ bipartite E →
    1 ≤ k → k ≤ n → isFloodNumber E k t → isRadius E r →
    r + k - 1 ≤ k*t

abbrev V := Fin 24

def core : Edges 24 :=
  [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),
   (10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(16,17),(17,18),(18,19),
   (20,1),(20,2),(20,3),(21,6),(21,7),(21,8),
   (22,11),(22,12),(22,13),(23,16),(23,17),(23,18)]

def graph : Edges 24 := core ++ core.map Prod.swap

def seed : List V := [2,7,12,17]

end Flooding

namespace FloodFamily

abbrev Role := Fin 6 -- a,b,c,d,e,x

abbrev Vertex (k : Nat) := Fin k × Role

abbrev Matrix := Role → Role → Bool

def roleEdges : List (Role × Role) :=
  [(0,1),(1,2),(2,3),(3,4),(1,5),(2,5),(3,5)]

def localAdj : Matrix := fun u v =>
  roleEdges.contains (u,v) || roleEdges.contains (v,u)

def linked {k : Nat} (u v : Vertex k) : Prop :=
  (u.2 = 4 ∧ v.2 = 0 ∧ u.1.val+1=v.1.val) ∨
  (u.2 = 0 ∧ v.2 = 4 ∧ v.1.val+1=u.1.val)

def adj {k : Nat} (u v : Vertex k) : Prop :=
  (u.1=v.1 ∧ localAdj u.2 v.2 = true) ∨ linked u v

abbrev Msg (k : Nat) := Vertex k → Vertex k → Prop

def next {k : Nat} (M : Msg k) (u v : Vertex k) : Prop :=
  adj u v ∧ (∃ w, M w u) ∧ ¬ M v u

inductive Walk {k : Nat} : Vertex k → Vertex k → Nat → Prop
  | nil (u) : Walk u u 0
  | cons {u v w l} : adj u v → Walk v w l → Walk u w (l+1)

def radiusAtMost {k : Nat} (r : Nat) : Prop :=
  ∃ u : Vertex k, ∀ v, ∃ l ≤ r, Walk u v l

def roundsFrom {k : Nat} (S : Vertex k → Prop) : Nat → Msg k :=
  Nat.rec (fun u v => S u ∧ adj u v) (fun _ M => next M)

def hasKSeeds {k : Nat} (S : Vertex k → Prop) : Prop :=
  ∃ f : Fin k → Vertex k, (∀ i j, f i = f j → i = j) ∧ ∀ v, S v ↔ ∃ i, f i = v

def quietAfter {k : Nat} (S : Vertex k → Prop) (t : Nat) : Prop :=
  ∀ u v : Vertex k, ¬ roundsFrom S t u v

def isFloodNumber {k : Nat} (t : Nat) : Prop :=
  (∃ S : Vertex k → Prop, hasKSeeds S ∧ quietAfter S t) ∧
  ∀ (S : Vertex k → Prop) r, hasKSeeds S → quietAfter S r → t ≤ r

def isRadius {k : Nat} (r : Nat) : Prop :=
  radiusAtMost (k:=k) r ∧ ∀ s, radiusAtMost (k:=k) s → r ≤ s

end FloodFamily

namespace ConjectureLab.TurauSubmission

/-- Exact negation of the inequality posed in Turau, arXiv:2002.10752v4, §8.
This is not the weaker proved bound in Theorem 4. -/
theorem conjecture_false : ¬ Flooding.TurauConjecture := by sorry

/-- Explicit 24-vertex certificate, with physical rounds 1, 2 and 3
carrying 12, 24 and 26 messages and round 4 empty. -/
theorem concrete_counterexample :
    Flooding.symmetric Flooding.graph ∧ Flooding.loopless Flooding.graph ∧
    Flooding.connected Flooding.graph ∧ ¬ Flooding.bipartite Flooding.graph ∧
    Flooding.seed.Nodup ∧ Flooding.seed.length = 4 ∧
    (Flooding.messages Flooding.graph Flooding.seed 0).length = 12 ∧
    (Flooding.messages Flooding.graph Flooding.seed 1).length = 24 ∧
    (Flooding.messages Flooding.graph Flooding.seed 2).length = 26 ∧
    (Flooding.messages Flooding.graph Flooding.seed 3).length = 0 ∧
    ∃ t, Flooding.isFloodNumber Flooding.graph 4 t ∧
      Flooding.isRadius Flooding.graph 10 ∧ t ≤ 3 ∧ 4*t < 10+4-1 := by sorry

/-- The chain of k six-vertex gadgets is a simple connected non-bipartite
counterexample for each k ≥ 4. The literal optimal k-seed time t is at
most 3; the exact radius is floor(5k/2). -/
theorem infinite_family (k : Nat) (hk : 4 ≤ k) :
    (∀ u v : FloodFamily.Vertex k, FloodFamily.adj u v → FloodFamily.adj v u) ∧
    (∀ u : FloodFamily.Vertex k, ¬ FloodFamily.adj u u) ∧
    (∀ u v : FloodFamily.Vertex k, ∃ l, FloodFamily.Walk u v l) ∧
    (¬ ∃ color : FloodFamily.Vertex k → Bool,
      ∀ u v, FloodFamily.adj u v → color u ≠ color v) ∧
    ∃ t, FloodFamily.isFloodNumber (k:=k) t ∧ FloodFamily.isRadius (k:=k) (5*k/2) ∧
      t ≤ 3 ∧ k*t < (5*k/2)+k-1 ∧ (5*k/2)+k-1-k*t ≥ k/2-1 := by sorry

end ConjectureLab.TurauSubmission
