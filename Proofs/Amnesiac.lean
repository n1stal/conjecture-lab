module

public import Lean

@[expose] public section

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

theorem Walk.append {n : Nat} {E : Edges n} {u v w : Fin n} {a b : Nat}
    (h : Walk E u v a) (k : Walk E v w b) : Walk E u w (a+b) := by
  induction h with
  | nil => simpa using k
  | cons e h ih => simpa only [Nat.add_comm 1 b, Nat.add_assoc] using Walk.cons e (ih k)

theorem Walk.reverse {n : Nat} {E : Edges n} (sym : symmetric E)
    {u v : Fin n} {l : Nat} (h : Walk E u v l) : Walk E v u l := by
  induction h with
  | nil => exact Walk.nil _
  | @cons u v w l e h ih => exact ih.append (Walk.cons (sym u v e) (Walk.nil u))

def connected {n : Nat} (E : Edges n) : Prop :=
  ∀ u v, ∃ l, Walk E u v l

def bipartite {n : Nat} (E : Edges n) : Prop :=
  ∃ colors : Fin n → Bool, ∀ u v, (u,v) ∈ E → colors u ≠ colors v

def radiusAtMost {n : Nat} (E : Edges n) (bound : Nat) : Prop :=
  ∃ u, ∀ v, ∃ l ≤ bound, Walk E u v l

/-- The seed nodes send to every neighbor on round one. -/
def first {n : Nat} (E : Edges n) (S : List (Fin n)) : Edges n :=
  E.filter fun e => decide (e.1 ∈ S)

theorem first_iff {n : Nat} {E : Edges n} {S : List (Fin n)} {u v : Fin n} :
    (u,v) ∈ first E S ↔ (u,v) ∈ E ∧ u ∈ S := by
  simp [first]

/-- A node sends along an edge on the next round iff it just received at least
one message, and received none from that edge's other endpoint. -/
def next {n : Nat} (E M : Edges n) : Edges n :=
  E.filter fun e => (M.any fun j => decide (j.2 = e.1)) && !(M.contains (e.2,e.1))

theorem next_iff {n : Nat} {E M : Edges n} {u v : Fin n} :
    (u,v) ∈ next E M ↔ (u,v) ∈ E ∧ (∃ w, (w,u) ∈ M) ∧ (v,u) ∉ M := by
  simp only [next,List.mem_filter,Bool.and_eq_true,List.any_eq_true,decide_eq_true_eq,
    Bool.not_eq_true',List.contains_eq_mem,decide_eq_false_iff_not]
  constructor
  · rintro ⟨he, ⟨⟨⟨w,u'⟩,hm,hu⟩,hn⟩⟩
    change u' = u at hu
    subst u'
    exact ⟨he,⟨w,hm⟩,hn⟩
  · rintro ⟨he,⟨w,hw⟩,hn⟩
    exact ⟨he,⟨⟨(w,u),hw,rfl⟩,hn⟩⟩

/-- Zero-indexed: messages E S 0 is the first physical round. -/
def messages {n : Nat} (E : Edges n) (S : List (Fin n)) : Nat → Edges n
  | 0 => first E S
  | r+1 => next E (messages E S r)

def quietAfter {n : Nat} (E : Edges n) (S : List (Fin n)) (r : Nat) : Prop :=
  messages E S r = []

theorem empty_absorbing {n : Nat} (E : Edges n) : next E [] = [] := by
  unfold next; simp

theorem stays_quiet {n : Nat} {E : Edges n} {S : List (Fin n)} {r : Nat}
    (h : quietAfter E S r) (k : Nat) : messages E S (r+k) = [] := by
  induction k with
  | zero => exact h
  | succ k ih => rw [Nat.add_succ,messages,ih,empty_absorbing]

/-- If this is the least flood time across k-element seed sets, every empty
round after r physical rounds must have r at least t. Conversely it attains t. -/
def isFloodNumber {n : Nat} (E : Edges n) (k t : Nat) : Prop :=
  (∃ S : List (Fin n), (S.Nodup ∧ S.length = k) ∧ quietAfter E S t) ∧
  ∀ (S : List (Fin n)) (r : Nat), S.Nodup ∧ S.length = k → quietAfter E S r → t ≤ r

/-- Radius is the smallest common bound on shortest walk lengths from a vertex. -/
def isRadius {n : Nat} (E : Edges n) (r : Nat) : Prop :=
  radiusAtMost E r ∧ ∀ s, radiusAtMost E s → r ≤ s

/-- Exact inequality in §8 of Turau arXiv:2002.10752v4, with the minimum
of flooding times and the radius defined relationally. -/
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

theorem graph_symm : symmetric graph := by
  intro u v he
  rcases List.mem_append.mp he with h|h
  · exact List.mem_append_right _ (List.mem_map.mpr ⟨_,h,rfl⟩)
  · obtain ⟨⟨a,b⟩,h,e⟩ := List.mem_map.mp h
    change (b,a)=(u,v) at e
    cases e
    exact List.mem_append_left _ h

set_option maxRecDepth 10000 in
theorem graph_loopless : loopless graph := by
  have h : graph.all (fun e => decide (e.1 ≠ e.2)) = true := by decide
  intro u hu
  have := (List.all_eq_true.mp h) _ hu
  simp at this

theorem graph_nonbip : ¬bipartite graph := by
  rintro ⟨f,h⟩
  have impossible : ∀ a b c : Bool, a ≠ b → b ≠ c → c ≠ a → False := by decide
  exact impossible (f 1) (f 2) (f 20)
    (h 1 2 (by decide)) (h 2 20 (by decide)) (h 20 1 (by decide))

def label (u : V) : Nat := if u.val < 20 then u.val else 5*(u.val-20)+2

set_option maxRecDepth 10000 in
theorem labels_local : ∀ u v, (u,v) ∈ graph →
    label u ≤ label v + 1 ∧ label v ≤ label u + 1 := by
  have h : graph.all (fun e => decide (label e.1 ≤ label e.2+1 ∧ label e.2 ≤ label e.1+1)) = true := by decide
  intro u v uv
  exact of_decide_eq_true ((List.all_eq_true.mp h) (u,v) uv)

theorem labels_walk {u v : V} {l : Nat} (h : Walk graph u v l) :
    label u ≤ label v + l ∧ label v ≤ label u + l := by
  induction h with
  | nil => simp
  | @cons u v w l e _ ih =>
    obtain ⟨a,b⟩ := labels_local u v e
    obtain ⟨c,d⟩ := ih
    omega

theorem radius_lower : ¬radiusAtMost graph 9 := by
  rintro ⟨u,h⟩
  obtain ⟨a,ha,wa⟩ := h 0
  obtain ⟨b,hb,wb⟩ := h 19
  have h1 := (labels_walk wa).1
  have h2 := (labels_walk wb).2
  have e0 : label 0 = 0 := by decide
  have e1 : label 19 = 19 := by decide
  rw [e0] at h1
  rw [e1] at h2
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem termination : quietAfter graph seed 3 := by
  unfold quietAfter
  decide

def pathsFromZero : Array (List V) := #[[], [1], [1, 2], [1, 2, 3], [1, 2, 3, 4], [1, 2, 3, 4, 5], [1, 2, 3, 4, 5, 6], [1, 2, 3, 4, 5, 6, 7], [1, 2, 3, 4, 5, 6, 7, 8], [1, 2, 3, 4, 5, 6, 7, 8, 9], [1, 2, 3, 4, 5, 6, 7, 8, 9, 10], [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12], [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13], [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14], [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16], [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17], [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18], [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19], [1, 20], [1, 2, 3, 4, 5, 6, 21], [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 22], [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 23]]
def pathsFromTen : Array (List V) := #[[9, 8, 7, 6, 5, 4, 3, 2, 1, 0], [9, 8, 7, 6, 5, 4, 3, 2, 1], [9, 8, 7, 6, 5, 4, 3, 2], [9, 8, 7, 6, 5, 4, 3], [9, 8, 7, 6, 5, 4], [9, 8, 7, 6, 5], [9, 8, 7, 6], [9, 8, 7], [9, 8], [9], [], [11], [11, 12], [11, 12, 13], [11, 12, 13, 14], [11, 12, 13, 14, 15], [11, 12, 13, 14, 15, 16], [11, 12, 13, 14, 15, 16, 17], [11, 12, 13, 14, 15, 16, 17, 18], [11, 12, 13, 14, 15, 16, 17, 18, 19], [9, 8, 7, 6, 5, 4, 3, 20], [9, 8, 21], [11, 22], [11, 12, 13, 14, 15, 16, 23]]

def follow {n : Nat} (E : Edges n) (u : Fin n) : List (Fin n) → Bool
  | [] => true
  | v::vs => decide ((u,v) ∈ E) && follow E v vs

def arrive {n : Nat} (u : Fin n) : List (Fin n) → Fin n
  | [] => u
  | v::vs => arrive v vs

theorem walk_of_follow {n : Nat} (E : Edges n) (u : Fin n) (vs : List (Fin n))
    (h : follow E u vs = true) : Walk E u (arrive u vs) vs.length := by
  induction vs generalizing u with
  | nil => exact Walk.nil u
  | cons v vs ih =>
    simp only [follow,Bool.and_eq_true,decide_eq_true_eq] at h
    exact Walk.cons h.1 (ih v h.2)

theorem mem_fin_range {n : Nat} (v : Fin n) : v ∈ List.finRange n := by
  have hv : v.val < (List.finRange n).length := by simp
  apply List.mem_of_getElem (h := hv)
  rw [List.getElem_finRange]
  rfl

def routeCert (paths : Array (List V)) (start v : V) (bound : Nat) : Bool :=
  let route := paths[v.val]!
  follow graph start route && decide (arrive start route = v ∧ route.length ≤ bound)

set_option maxRecDepth 100000 in
theorem walk_zero : ∀ v : V, ∃ l, Walk graph 0 v l := by
  have cert : (List.finRange 24).all (fun v => routeCert pathsFromZero 0 v 24) = true := by decide
  intro v
  have h := List.all_eq_true.mp cert v (mem_fin_range v)
  simp only [routeCert,Bool.and_eq_true,decide_eq_true_eq] at h
  have w := walk_of_follow graph 0 _ h.1
  rw [h.2.1] at w
  exact ⟨_,w⟩

theorem graph_connected : connected graph := by
  intro u v
  obtain ⟨a,wa⟩ := walk_zero u
  obtain ⟨b,wb⟩ := walk_zero v
  exact ⟨a+b,(wa.reverse graph_symm).append wb⟩

set_option maxRecDepth 100000 in
theorem radius_upper : radiusAtMost graph 10 := by
  have cert : (List.finRange 24).all (fun v => routeCert pathsFromTen 10 v 10) = true := by decide
  refine ⟨10,?_⟩
  intro v
  have h := List.all_eq_true.mp cert v (mem_fin_range v)
  simp only [routeCert,Bool.and_eq_true,decide_eq_true_eq] at h
  have w := walk_of_follow graph 10 _ h.1
  rw [h.2.1] at w
  exact ⟨_,h.2.2,w⟩

theorem radius_exact : isRadius graph 10 := by
  refine ⟨radius_upper,?_⟩
  intro s hs
  apply Classical.byContradiction
  intro hn
  have hb : s ≤ 9 := by omega
  obtain ⟨u,h⟩ := hs
  apply radius_lower
  refine ⟨u,?_⟩
  intro v
  obtain ⟨l,hl,hW⟩ := h v
  exact ⟨l, Nat.le_trans hl hb,hW⟩

theorem least_witness (P : Nat → Prop) (r : Nat) (h : P r) :
    ∃ t, P t ∧ ∀ s, P s → t ≤ s := by
  classical
  induction r using Nat.strongRecOn with
  | ind r ih =>
    by_cases hex : ∃ t < r, P t
    · obtain ⟨t,ht,hP⟩ := hex
      exact ih t ht hP
    · refine ⟨r,h,?_⟩
      intro s hs
      apply Classical.byContradiction
      intro hbad
      exact hex ⟨s,by omega,hs⟩

theorem finite_counterexample :
    ∃ t, isFloodNumber graph 4 t ∧ isRadius graph 10 ∧ 4*t < 10+4-1 := by
  let P := fun t => ∃ S : List V, (S.Nodup ∧ S.length = 4) ∧ quietAfter graph S t
  obtain ⟨t,ht,hmin⟩ := least_witness P 3 ⟨seed,by decide,termination⟩
  have ht3 : t ≤ 3 := hmin 3 ⟨seed,by decide,termination⟩
  refine ⟨t,⟨ht,?_⟩,radius_exact,by omega⟩
  exact fun S r hs hr => hmin r ⟨S,hs,hr⟩

theorem turau_false : ¬ TurauConjecture := by
  intro h
  obtain ⟨t,hf,hr,hn⟩ := finite_counterexample
  have hc := h 24 graph 4 t 10 graph_symm graph_loopless graph_connected graph_nonbip
    (by decide) (by decide) hf hr
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem round_counts :
    (messages graph seed 0).length = 12 ∧ (messages graph seed 1).length = 24 ∧
    (messages graph seed 2).length = 26 ∧ (messages graph seed 3).length = 0 := by
  decide

end Flooding

#print axioms Flooding.termination
#print axioms Flooding.radius_lower

#print axioms Flooding.next_iff
#print axioms Flooding.turau_false

#print axioms Flooding.first_iff
#print axioms Flooding.round_counts
