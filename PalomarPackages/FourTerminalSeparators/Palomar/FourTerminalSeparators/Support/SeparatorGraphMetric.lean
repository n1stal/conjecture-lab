module

public import Std
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-! Source reading of unweighted finite simple graph shortest paths, in
Lean core/Std, independent of Mathlib and the four-terminal algebra. -/
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

namespace Walk
variable {V : Type u} {G : SimpleGraph V} {a b c : V} {m n : Nat}

def trivial (G : SimpleGraph V) (a : V) : Walk G a a 0 :=
  ⟨fun _ => a, rfl, rfl, fun _ h => (Nat.not_lt_zero _ h).elim⟩

def concat (p : Walk G a b m) (q : Walk G b c n) : Walk G a c (m+n) := by
  refine ⟨fun i => if i ≤ m then p.point i else q.point (i-m), ?_, ?_, ?_⟩
  · simpa only [ite_eq_left (Nat.zero_le m)] using p.first
  · by_cases h : n = 0
    · subst n
      have hbc := q.first.symm.trans q.last
      simpa only [Nat.add_zero, ite_eq_left (Nat.le_refl m)] using p.last.trans hbc
    · have hn : ¬ m+n ≤ m := by omega
      simpa only [ite_eq_right hn, Nat.add_sub_cancel_left] using q.last
  · intro i hi
    by_cases h : i < m
    · have hu : i ≤ m := by omega
      have hv : i+1 ≤ m := by omega
      simpa only [ite_eq_left hu, ite_eq_left hv] using p.step i h
    · have hn : ¬ i+1 ≤ m := by omega
      by_cases he : i = m
      · subst i
        have ht : 0 < n := by omega
        have h1 : m+1-m = 1 := by omega
        have heq := q.first.trans p.last.symm
        simpa only [ite_eq_left (Nat.le_refl m), ite_eq_right hn, h1, heq, Nat.zero_add] using q.step 0 ht
      · have hu : ¬ i ≤ m := by omega
        have hs : i-m < n := by omega
        have hj : i+1-m = (i-m)+1 := by omega
        simpa only [ite_eq_right hu, ite_eq_right hn, hj] using q.step (i-m) hs

def slice (p : Walk G a b n) (i j : Nat) (hij : i ≤ j) (hj : j ≤ n) :
    Walk G (p.point i) (p.point j) (j-i) := by
  refine ⟨fun t => p.point (i+t), by simp, ?_, ?_⟩
  · have h : i+(j-i) = j := by omega
    rw [h]
  · intro t ht
    have h : i+t < n := by omega
    simpa only [Nat.add_assoc] using p.step (i+t) h

theorem zero_endpoints (p : Walk G a b 0) : a = b :=
  p.first.symm.trans p.last

def reverse (p : Walk G a b n) : Walk G b a n := by
  refine ⟨fun i => p.point (n-i), ?_, ?_, ?_⟩
  · simpa only [Nat.sub_zero] using p.last
  · simpa only [Nat.sub_self] using p.first
  · intro i hi
    have hh : n-(i+1) < n := by omega
    have he : n-(i+1)+1 = n-i := by omega
    simpa only [he] using G.symm (p.step (n-(i+1)) hh)
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
  have h := M.minimal a a 0 (Walk.trivial G a)
  omega

theorem dist_eq_zero_iff (a b : V) : M.dist a b = 0 ↔ a = b := by
  constructor
  · intro h
    have p := M.geodesic a b
    rw [h] at p
    exact p.zero_endpoints
  · rintro rfl
    exact dist_self M a

theorem dist_symm (a b : V) : M.dist a b = M.dist b a :=
  Nat.le_antisymm
    (M.minimal a b _ (M.geodesic b a).reverse)
    (M.minimal b a _ (M.geodesic a b).reverse)

theorem dist_triangle (a b c : V) : M.dist a c ≤ M.dist a b+M.dist b c :=
  M.minimal a c _ ((M.geodesic a b).concat (M.geodesic b c))

theorem unique (N : ShortestDistances G) (a b : V) : M.dist a b = N.dist a b :=
  Nat.le_antisymm (M.minimal a b _ (N.geodesic a b)) (N.minimal a b _ (M.geodesic a b))

theorem geodesic_slice_eq (a b : V) (i j : Nat)
    (hij : i ≤ j) (hj : j ≤ M.dist a b) :
    let w := M.geodesic a b
    M.dist (w.point i) (w.point j) = j-i := by
  let w := M.geodesic a b
  change M.dist (w.point i) (w.point j) = j-i
  have hii : i ≤ M.dist a b := Nat.le_trans hij hj
  have uw := M.minimal _ _ _ (w.slice i j hij hj)
  have right := w.slice j (M.dist a b) hj (Nat.le_refl _)
  have left := w.slice 0 i (Nat.zero_le i) hii
  have middle := M.geodesic (w.point i) (w.point j)
  have c := (left.concat middle).concat right
  have cz := M.minimal _ _ _ c
  rw [w.first, w.last] at cz
  omega
end ShortestDistances

end TriameterQ3Graph
