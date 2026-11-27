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
    omega

/-- Exact packing number: a certified attaining packing and a universal cap. -/
structure ExactPacking {G : SimpleGraph V} (M : ShortestDistances G)
    (k p : Nat) : Prop where
  attained : ∃ f : Fin p → V, IsPacking M k f
  upper : ∀ n (f : Fin n → V), IsPacking M k f → n ≤ p

theorem exactPacking_pos {G : SimpleGraph V} (M : ShortestDistances G)
    {k p : Nat} (P : ExactPacking M k p) (v : V) : 1 ≤ p :=
  P.upper 1 (fun _ => v) (fun i j hij => (hij (Subsingleton.elim i j)).elim)

/-- The geodesic diameter bound with the exact step convention d>k. -/
theorem diameter_le_of_packing {G : SimpleGraph V} (M : ShortestDistances G)
    {k p : Nat} (P : ExactPacking M k p) (a b : V) :
    M.dist a b ≤ (k+1)*p-1 := by
  have hp := exactPacking_pos M P a
  have hpos : 0 < (k+1)*p := Nat.mul_pos (Nat.succ_pos k) (by omega)
  by_cases hw : (k+1)*p ≤ M.dist a b
  · let w := M.geodesic a b
    let f : Fin (p+1) → V := fun i => w.point ((k+1)*i.val)
    have step (i j : Fin (p+1)) (hij : i.val < j.val) :
        k < M.dist (f i) (f j) := by
      have hle : i.val ≤ j.val := by omega
      have hbound := Nat.mul_le_mul_left (k+1) hle
      have hjp : j.val ≤ p := by have hh := j.isLt; omega
      have hlast := Nat.le_trans (Nat.mul_le_mul_left (k+1) hjp) hw
      have hh := M.geodesic_slice_eq a b _ _ hbound hlast
      have hinc : i.val+1 ≤ j.val := by omega
      have hs := Nat.mul_le_mul_left (k+1) hinc
      rw [Nat.mul_add, Nat.mul_one] at hs
      change M.dist (f i) (f j) = (k+1)*j.val-(k+1)*i.val at hh
      omega
    have hpack : IsPacking M k f := by
      intro i j h
      have hne : i.val ≠ j.val := fun he => h (Fin.ext he)
      rcases Nat.lt_or_gt_of_ne hne with hij | hji
      · exact step _ _ hij
      · rw [M.dist_symm]
        exact step _ _ hji
    have hbad := P.upper (p+1) f hpack
    omega
  · omega

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
      refine ⟨p,by omega,hit,?_⟩
      intro q hq hP
      have he : q ≠ n+1 := by intro e; exact hn (e ▸ hP)
      exact hu q (by omega) hP

theorem finite_exact_packing_exists {n : Nat} {G : SimpleGraph (Fin n)}
    (M : ShortestDistances G) (k : Nat) : ∃ p, ExactPacking M k p := by
  let P (p : Nat) := ∃ f : Fin p → Fin n, IsPacking M k f
  have P0 : P 0 := ⟨Fin.elim0, fun i => Fin.elim0 i⟩
  obtain ⟨p,_,ha,hu⟩ := largest_bounded_witness P n P0
  refine ⟨p,⟨ha,?_⟩⟩
  exact fun q f hf => hu q (finite_packing_bound M f hf) ⟨f,hf⟩

theorem exact_packing_unique {G : SimpleGraph V} (M : ShortestDistances G)
    {k p q : Nat} (hp : ExactPacking M k p) (hq : ExactPacking M k q) :
    p = q := by
  obtain ⟨f,hf⟩ := hp.attained
  obtain ⟨g,hg⟩ := hq.attained
  exact Nat.le_antisymm (hq.upper p f hf) (hp.upper q g hg)

/-- Actual distance-packing number of a connected finite graph. -/
noncomputable def packingNumber {n : Nat} {G : SimpleGraph (Fin n)}
    (M : ShortestDistances G) (k : Nat) : Nat :=
  (finite_exact_packing_exists M k).choose

theorem packingNumber_is_exact {n : Nat} {G : SimpleGraph (Fin n)}
    (M : ShortestDistances G) (k : Nat) : ExactPacking M k (packingNumber M k) :=
  (finite_exact_packing_exists M k).choose_spec


end TriameterQ3Graph

namespace TriameterQ3PackingWindows
open TriameterQ3Graph

theorem maximal_packing_cover {V : Type} {G : SimpleGraph V} (M : ShortestDistances G)
    {k p : Nat} (P : ExactPacking M k p) (f : Fin p → V) (hf : IsPacking M k f)
    (x : V) : ∃ j, M.dist x (f j) ≤ k := by
  by_cases H : ∃ j, M.dist x (f j) ≤ k
  · exact H
  · have hfwd (i : Fin p) : k < M.dist x (f i) := Nat.lt_of_not_ge (fun h => H ⟨i,h⟩)
    have hrev (i : Fin p) : k < M.dist (f i) x := by rw [M.dist_symm]; exact hfwd i
    let g : Fin (p+1) → V := Fin.cases x f
    have hg : IsPacking M k g := by
      intro i j hn
      refine Fin.cases (motive := fun i => i ≠ j → k < M.dist (g i) (g j)) ?_ ?_ i hn
      · refine Fin.cases (motive := fun j => (0 : Fin (p+1)) ≠ j →
          k < M.dist (g 0) (g j)) ?_ ?_ j
        · exact fun h => (h rfl).elim
        · intro j _
          simpa [g] using hfwd j
      · intro i hi
        apply Fin.cases (motive := fun j => i.succ ≠ j → k < M.dist (g i.succ) (g j)) ?_ ?_ j hi
        · intro _
          simpa [g] using hrev i
        · intro j he
          exact hf i j (fun e => he (congrArg Fin.succ e))
    have bad := P.upper (p+1) g hg
    omega

def unit_walk {V : Type} {G : SimpleGraph V} {x y : V} (h : G.adj x y) :
    Walk G x y 1 := by
  refine ⟨fun i => if i = 0 then x else y,by simp,by simp,?_⟩
  intro i hi
  have he : i = 0 := by omega
  subst i
  simpa using h

/-- Exact graph-geodesic necessary condition for metric realizability with
given maximum distance-k packing. The two window inequalities are written
without truncated subtraction. -/
theorem geodesic_center_windows {V : Type} {G : SimpleGraph V}
    (M : ShortestDistances G) {k p : Nat} (P : ExactPacking M k p)
    (f : Fin p → V) (hf : IsPacking M k f) (a b : Fin p) :
    let D := M.dist (f a) (f b)
    ∃ h : Nat → Fin p, h 0 = a ∧ h D = b ∧
      (∀ t, t ≤ D →
        M.dist (f a) (f (h t)) ≤ t+k ∧ t ≤ M.dist (f a) (f (h t))+k ∧
        M.dist (f b) (f (h t)) ≤ D-t+k ∧ D-t ≤ M.dist (f b) (f (h t))+k) ∧
      ∀ t, t < D → M.dist (f (h t)) (f (h (t+1))) ≤ 2*k+1 := by
  dsimp
  let D := M.dist (f a) (f b)
  let w := M.geodesic (f a) (f b)
  let h (t : Nat) := (maximal_packing_cover M P f hf (w.point t)).choose
  have H (t : Nat) : M.dist (w.point t) (f (h t)) ≤ k :=
    (maximal_packing_cover M P f hf (w.point t)).choose_spec
  have hZero : h 0 = a := by
    have H0 := H 0
    rw [w.first] at H0
    by_cases he : a = h 0
    · exact he.symm
    · have bad := hf a (h 0) he
      omega
  have hLast : h D = b := by
    have HD := H D
    rw [w.last] at HD
    by_cases he : b = h D
    · exact he.symm
    · have bad := hf b (h D) he
      omega
  refine ⟨h,hZero,hLast,?_,?_⟩
  · intro t ht
    have had : M.dist (f a) (w.point t) = t := by
      have hs := M.geodesic_slice_eq (f a) (f b) 0 t (Nat.zero_le _) ht
      change M.dist (w.point 0) (w.point t) = _ at hs
      simpa only [w.first,Nat.sub_zero] using hs
    have hbd : M.dist (f b) (w.point t) = D-t := by
      have hs := M.geodesic_slice_eq (f a) (f b) t D ht (Nat.le_refl _)
      change M.dist (w.point t) (w.point D) = _ at hs
      rw [w.last,M.dist_symm] at hs
      exact hs
    have ht' := H t
    have hs' := M.dist_symm (f (h t)) (w.point t)
    have ha := M.dist_triangle (f a) (w.point t) (f (h t))
    have hb := M.dist_triangle (f a) (f (h t)) (w.point t)
    have hc := M.dist_triangle (f b) (w.point t) (f (h t))
    have hd := M.dist_triangle (f b) (f (h t)) (w.point t)
    exact ⟨by omega,by omega,by omega,by omega⟩
  · intro t ht
    have H0 := H t
    have H1 := H (t+1)
    have hrev := M.dist_symm (f (h t)) (w.point t)
    have hD := M.minimal _ _ 1 (unit_walk (w.step t ht))
    have h0 := M.dist_triangle (f (h t)) (w.point t) (f (h (t+1)))
    have h1 := M.dist_triangle (w.point t) (w.point (t+1)) (f (h (t+1)))
    omega

/-- Crossing from label zero to at least two with upward jumps at most one
requires a consecutive one-to-two transition. -/
theorem walk_crosses_one_two (z : Nat → Nat) (D : Nat) (h0 : z 0 = 0) (hD : 2 ≤ z D)
    (step : ∀ i, i < D → z (i+1) ≤ z i+1) :
    ∃ i, i < D ∧ z i = 1 ∧ z (i+1) = 2 := by
  have induct (n : Nat) : n ≤ D → 2 ≤ z n →
      ∃ i, i < n ∧ z i = 1 ∧ z (i+1) = 2 := by
    induction n with
    | zero => intro _ h; omega
    | succ n IH =>
      intro hn h
      by_cases he : 2 ≤ z n
      · obtain ⟨i,hi,hj,hm⟩ := IH (by omega) he
        exact ⟨i,by omega,hj,hm⟩
      · have hs := step n (by omega)
        exact ⟨n,by omega,by omega,by omega⟩
  exact induct D (Nat.le_refl _) hD

/-- Arithmetic end of the path case. The positions i,i+1 are where a
covering-center path switches labels from 1 to 2. -/
theorem pentagon_path_windows_contradiction (a x y z u v i : Nat)
    (hsmall : x+y+z+u+v+3 < a)
    (hpre : i+u ≤ 2*a+y) (hpost : 3*a ≤ i+x+2) : False := by
  omega

end TriameterQ3PackingWindows

namespace TriameterQ3PackingWindows
open TriameterQ3Graph

theorem fin5_cases (i : Fin 5) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
  have hi := i.isLt
  have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 := by omega
  rcases h with h|h|h|h|h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext h))))

theorem ordered_nonpath_far (d : Fin 5 → Fin 5 → Nat) (k : Nat)
    (h02 : 2*k+1 < d 0 2) (h03 : 2*k+1 < d 0 3) (h04 : 2*k+1 < d 0 4)
    (h13 : 2*k+1 < d 1 3) (h14 : 2*k+1 < d 1 4) (h24 : 2*k+1 < d 2 4)
    (i j : Fin 5) (h : i.val+1 < j.val) : 2*k+1 < d i j := by
  rcases fin5_cases i with rfl|rfl|rfl|rfl|rfl <;>
    rcases fin5_cases j with rfl|rfl|rfl|rfl|rfl <;>
    first | assumption | (change _ < _ at h; omega)

/-- The hard graph-realizability case of the 5-cycle excess bound.
The maximum k-packing consists of five labeled vertices, and the four
consecutive labels are low pairs: d≤2k+1. The complementary 5-cycle then
has perimeter at most 5k + 16(k+1). -/
theorem complementary_pentagon_bound {V : Type} {G : SimpleGraph V}
    (M : ShortestDistances G) (k : Nat) (P : ExactPacking M k 5)
    (f : Fin 5 → V) (hf : IsPacking M k f)
    (h01 : M.dist (f 0) (f 1) ≤ 2*k+1)
    (h12 : M.dist (f 1) (f 2) ≤ 2*k+1)
    (h23 : M.dist (f 2) (f 3) ≤ 2*k+1)
    (h34 : M.dist (f 3) (f 4) ≤ 2*k+1) :
    M.dist (f 0) (f 2) + M.dist (f 0) (f 3) + M.dist (f 1) (f 3) +
      M.dist (f 1) (f 4) + M.dist (f 2) (f 4) ≤ 5*k+16*(k+1) := by
  let d (i j : Fin 5) := M.dist (f i) (f j)
  change d 0 2 + d 0 3 + d 1 3 + d 1 4 + d 2 4 ≤ _
  by_cases h : d 0 2 + d 0 3 + d 1 3 + d 1 4 + d 2 4 ≤ 5*k+16*(k+1)
  · exact h
  have t02 : d 0 2 ≤ d 0 1 + d 1 2 := M.dist_triangle (f 0) (f 1) (f 2)
  have t13 : d 1 3 ≤ d 1 2 + d 2 3 := M.dist_triangle (f 1) (f 2) (f 3)
  have t24 : d 2 4 ≤ d 2 3 + d 3 4 := M.dist_triangle (f 2) (f 3) (f 4)
  have t034 : d 0 3 ≤ d 0 4 + d 3 4 := by
    have ht := M.dist_triangle (f 0) (f 4) (f 3)
    rw [M.dist_symm (f 4) (f 3)] at ht
    exact ht
  have b03 : d 0 3 ≤ 5*k+4 := by
    have t := diameter_le_of_packing M P (f 0) (f 3)
    change d 0 3 ≤ _ at t
    omega
  have b14 : d 1 4 ≤ 5*k+4 := by
    have t := diameter_le_of_packing M P (f 1) (f 4)
    change d 1 4 ≤ _ at t
    omega
  change d 0 1 ≤ _ at h01
  change d 1 2 ≤ _ at h12
  change d 2 3 ≤ _ at h23
  change d 3 4 ≤ _ at h34
  let x := 4*k+2-d 0 2
  let y := 4*k+2-d 1 3
  let z := 4*k+2-d 2 4
  let u := 5*k+4-d 0 3
  let v := 5*k+4-d 1 4
  have hx : x+d 0 2 = 4*k+2 := by dsimp [x]; omega
  have hy : y+d 1 3 = 4*k+2 := by dsimp [y]; omega
  have hz : z+d 2 4 = 4*k+2 := by dsimp [z]; omega
  have hu : u+d 0 3 = 5*k+4 := by dsimp [u]; omega
  have hv : v+d 1 4 = 5*k+4 := by dsimp [v]; omega
  have small : x+y+z+u+v+3 < k+1 := by omega
  have far (i j : Fin 5) (hj : i.val+1 < j.val) : 2*k+1 < d i j :=
    ordered_nonpath_far d k (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) i j hj
  obtain ⟨s,h0,hD,hw,hstep⟩ := geodesic_center_windows M P f hf (0 : Fin 5) 3
  let D := d 0 3
  change s D = 3 at hD
  have jump (i : Nat) (hi : i < D) : (s (i+1)).val ≤ (s i).val+1 := by
    have hstep' : d (s i) (s (i+1)) ≤ 2*k+1 := hstep i hi
    by_cases hj : (s i).val+1 < (s (i+1)).val
    · exact (Nat.not_lt_of_ge hstep' (far _ _ hj)).elim
    · omega
  have hZ : (s 0).val = 0 := by rw [h0]; rfl
  have h3 : 2 ≤ (s D).val := by rw [hD]; decide
  obtain ⟨i,hi,h1,h2⟩ := walk_crosses_one_two (fun t => (s t).val) D hZ h3 jump
  have e1 : s i = 1 := Fin.ext h1
  have e2 : s (i+1) = 2 := Fin.ext h2
  have w1 := (hw i (Nat.le_of_lt hi)).2.2.1
  have hSucc : i+1 ≤ D := by omega
  have w2 := (hw (i+1) hSucc).1
  rw [e1,M.dist_symm (f 3) (f 1)] at w1
  rw [e2] at w2
  change d 1 3 ≤ D-i+k at w1
  change d 0 2 ≤ i+1+k at w2
  change i < d 0 3 at hi
  change d 1 3 ≤ d 0 3-i+k at w1
  exact (pentagon_path_windows_contradiction (k+1) x y z u v i small
    (by omega) (by omega)).elim

end TriameterQ3PackingWindows

/-! Direct proof of the numeric Hak–Kozerenko Theorem 1.1 inequality.
The source's parity/outer-and-residue argument is credited, while this
module uses only chosen terminal geodesics, not a surjective graph quotient. -/
namespace TriameterQ3Graph

universe u
variable {V : Type u} {G : SimpleGraph V}
variable (M : ShortestDistances G)

/-- A length-L geodesic section pointing inward from terminal a. -/
structure Arm (M : ShortestDistances G) (a : V) (L : Nat) where
  point : Nat → V
  near : ∀ x ≤ L, M.dist a (point x) = L-x
  along : ∀ x y, x ≤ y → y ≤ L → M.dist (point x) (point y) = y-x

def armOfGeodesic (a b : V) (L : Nat) (h : L ≤ M.dist a b) : Arm M a L := by
  let w := M.geodesic a b
  refine ⟨fun x => w.point (L-x), ?_, ?_⟩
  · intro x hx
    have he := M.geodesic_slice_eq a b 0 (L-x) (Nat.zero_le _) (by omega)
    change M.dist (w.point 0) (w.point (L-x)) = (L-x)-0 at he
    simpa only [w.first, Nat.sub_zero] using he
  · intro x y hxy hy
    have he := M.geodesic_slice_eq a b (L-y) (L-x) (by omega) (by omega)
    change M.dist (w.point (L-y)) (w.point (L-x)) = (L-x)-(L-y) at he
    rw [M.dist_symm]
    omega

theorem different_arms_lower {a b : V} {L U e : Nat} (A : Arm M a L) (B : Arm M b U)
    (hd : M.dist a b = L+U+e) (x y : Nat) (hx : x ≤ L) (hy : y ≤ U) :
    x+y+e ≤ M.dist (A.point x) (B.point y) := by
  have t0 := M.dist_triangle a (A.point x) b
  have t1 := M.dist_triangle (A.point x) (B.point y) b
  have hx' := A.near x hx
  have hy' := B.near y hy
  rw [M.dist_symm] at hy'
  omega

def positions (k L mark : Nat) := L/(k+1)+mark
def indexStep (mark : Nat) (i : Nat) := i+1-mark
def depth (k L mark i : Nat) := L%(k+1)+(k+1)*indexStep mark i

theorem depth_fits {k L mark : Nat} (i : Fin (positions k L mark)) :
    depth k L mark i.val ≤ L := by
  have hi := i.isLt
  unfold positions at hi
  have hq0 : (0 : Int) ≤ (L/(k+1) : Nat) := Int.natCast_nonneg _
  have hi' : indexStep mark i.val ≤ L/(k+1) := by unfold indexStep; omega
  have hm := Nat.mul_le_mul_left (k+1) hi'
  have hdiv := Nat.mod_add_div L (k+1)
  unfold depth
  omega

theorem depth_gap {k L mark : Nat} (hmark : mark ≤ 1)
    {i j : Nat} (hij : i < j) :
    depth k L mark i + (k+1) ≤ depth k L mark j := by
  have hi : indexStep mark i+1 ≤ indexStep mark j := by unfold indexStep; omega
  have hm := Nat.mul_le_mul_left (k+1) hi
  rw [Nat.mul_add, Nat.mul_one] at hm
  unfold depth
  omega

theorem depth_ge_mod (k L mark i : Nat) :
    L%(k+1) ≤ depth k L mark i := by unfold depth; omega

theorem depth_big_or_mark (k L mark i : Nat) (hm : mark ≤ 1) :
    k+1 ≤ depth k L mark i ∨ mark = 1 := by
  by_cases h : mark=1
  · exact Or.inr h
  · have hi : 1 ≤ indexStep mark i := by unfold indexStep; omega
    have he := Nat.mul_le_mul_left (k+1) hi
    rw [Nat.mul_one] at he
    unfold depth
    exact Or.inl (by omega)

def armSelect {a : V} {L : Nat} (A : Arm M a L) (k mark : Nat) :
    Fin (positions k L mark) → V :=
  fun i => A.point (depth k L mark i.val)

theorem arm_packs {a : V} {L k mark : Nat} (hm : mark ≤ 1)
    (A : Arm M a L) : IsPacking M k (armSelect M A k mark) := by
  intro i j hn
  have hne : i.val ≠ j.val := fun h => hn (Fin.ext h)
  have step (i j : Fin (positions k L mark)) (hij : i.val < j.val) :
      k < M.dist (armSelect M A k mark i) (armSelect M A k mark j) := by
    have hgap := depth_gap (k := k) (L := L) hm hij
    have hd := A.along (depth k L mark i.val) (depth k L mark j.val) (by omega) (depth_fits j)
    unfold armSelect
    omega
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact step _ _ h
  · rw [M.dist_symm]
    exact step _ _ h

theorem arm_cross {a b : V} {L U e k m n : Nat} (A : Arm M a L) (B : Arm M b U)
    (hL : M.dist a b = L+U+e) (hm : m ≤ 1) (hn : n ≤ 1)
    (hinner : m=1 → n=1 → k < L%(k+1)+U%(k+1)+e)
    (i : Fin (positions k L m)) (j : Fin (positions k U n)) :
    k < M.dist (armSelect M A k m i) (armSelect M B k n j) := by
  have hdist := different_arms_lower M A B hL _ _ (depth_fits i) (depth_fits j)
  have hx := depth_ge_mod k L m i.val
  have hy := depth_ge_mod k U n j.val
  unfold armSelect
  rcases depth_big_or_mark k L m i.val hm with h | he
  · omega
  · rcases depth_big_or_mark k U n j.val hn with h | hf
    · omega
    · have hh := hinner he hf
      omega

def appendIndex {p q : Nat} (f : Fin p → V) (g : Fin q → V)
    (i : Fin (p+q)) : V :=
  if h : i.val < p then f ⟨i.val,h⟩ else g ⟨i.val-p,by have ht := i.isLt; omega⟩

theorem appendPacking {k p q : Nat} (f : Fin p → V) (g : Fin q → V)
    (hf : IsPacking M k f) (hg : IsPacking M k g)
    (hcross : ∀ i j, k < M.dist (f i) (g j)) : IsPacking M k (appendIndex f g) := by
  intro i j h
  have hval : i.val ≠ j.val := fun he => h (Fin.ext he)
  unfold appendIndex
  split <;> split
  · rename_i hi hj
    exact hf _ _ (fun he => hval (congrArg (fun v : Fin p => v.val) he))
  · exact hcross _ _
  · rw [M.dist_symm]
    exact hcross _ _
  · rename_i hi hj
    apply hg
    intro he
    have hs := congrArg Fin.val he
    change i.val-p = j.val-p at hs
    omega

theorem threeArmPacking {a b c : V} {L U J e k p : Nat}
    (A : Arm M a L) (B : Arm M b U) (C : Arm M c J)
    (hab : M.dist a b = L+U+e) (hac : M.dist a c = L+J+e) (hbc : M.dist b c = U+J+e)
    (P : ExactPacking M k p) {m n o : Nat} (hm : m ≤ 1) (hn : n ≤ 1) (ho : o ≤ 1)
    (hi01 : m=1 → n=1 → k < L%(k+1)+U%(k+1)+e)
    (hi02 : m=1 → o=1 → k < L%(k+1)+J%(k+1)+e)
    (hi12 : n=1 → o=1 → k < U%(k+1)+J%(k+1)+e) :
    L/(k+1)+U/(k+1)+J/(k+1)+m+n+o ≤ p := by
  let f := armSelect M A k m
  let g := armSelect M B k n
  let h := armSelect M C k o
  have hAB := appendPacking M f g (arm_packs M hm A) (arm_packs M hn B)
    (arm_cross M A B hab hm hn hi01)
  have hC (i : Fin (positions k L m+positions k U n)) (j : Fin (positions k J o)) :
      k < M.dist (appendIndex f g i) (h j) := by
    unfold appendIndex
    split
    · exact arm_cross M A C hac hm ho hi02 _ _
    · exact arm_cross M B C hbc hn ho hi12 _ _
  have hp := P.upper _ (appendIndex (appendIndex f g) h)
    (appendPacking M _ h hAB (arm_packs M ho C) hC)
  unfold positions at hp
  omega

/-- Complete parity-adjusted arm lengths calculated directly from any
three distances satisfying the triangle inequalities. -/
theorem parity_arm_lengths (x y z : Nat) (h₀ : x ≤ y+z) (h₁ : y ≤ x+z) (h₂ : z ≤ x+y) :
    let e := (x+y+z)%2
    let L := (x+y-z)/2
    let U := (x+z-y)/2
    let J := (y+z-x)/2
    e ≤ 1 ∧ x=L+U+e ∧ y=L+J+e ∧ z=U+J+e := by
  exact ⟨by omega,by omega,by omega,by omega⟩

/-- The numeric part of Hak–Kozerenko Theorem 1.1. No classification of
equality triples, global projection, or graph-realization conclusion. -/
theorem triple_perimeter_packing_bound {k p : Nat} (P : ExactPacking M k p)
    (a b c : V) :
    M.dist a b + M.dist a c + M.dist b c + 2 ≤ 2*(k+1)*p+k := by
  let x := M.dist a b
  let y := M.dist a c
  let z := M.dist b c
  let e := (x+y+z)%2
  let L := (x+y-z)/2
  let U := (x+z-y)/2
  let J := (y+z-x)/2
  have h₀ : x ≤ y+z := by
    have ht := M.dist_triangle a c b
    rw [M.dist_symm c b] at ht
    exact ht
  have h₁ : y ≤ x+z := M.dist_triangle a b c
  have h₂ : z ≤ x+y := by
    have ht := M.dist_triangle b a c
    rw [M.dist_symm b a] at ht
    exact ht
  have heq : e ≤ 1 ∧ x=L+U+e ∧ y=L+J+e ∧ z=U+J+e := parity_arm_lengths x y z h₀ h₁ h₂
  obtain ⟨he,hx,hy,hz⟩ := heq
  have ha : L ≤ M.dist a b := by change L ≤ x; omega
  have hb : U ≤ M.dist b a := by rw [M.dist_symm]; change U ≤ x; omega
  have hc : J ≤ M.dist c a := by rw [M.dist_symm]; change J ≤ y; omega
  let A := armOfGeodesic M a b L ha
  let B := armOfGeodesic M b a U hb
  let C := armOfGeodesic M c a J hc
  let r := L%(k+1)
  let s := U%(k+1)
  let t := J%(k+1)
  let Q := L/(k+1)+U/(k+1)+J/(k+1)
  have hr : r ≤ k := Nat.le_of_lt_succ (Nat.mod_lt L (Nat.succ_pos k))
  have hs : s ≤ k := Nat.le_of_lt_succ (Nat.mod_lt U (Nat.succ_pos k))
  have ht : t ≤ k := Nat.le_of_lt_succ (Nat.mod_lt J (Nat.succ_pos k))
  have hSum : L+U+J = r+s+t+(k+1)*Q := by
    have dL := Nat.mod_add_div L (k+1)
    have dU := Nat.mod_add_div U (k+1)
    have dJ := Nat.mod_add_div J (k+1)
    dsimp [r,s,t,Q]
    simp only [Nat.mul_add]
    omega
  have hPer : x+y+z = 2*((k+1)*Q) + 2*(r+s+t)+3*e := by omega
  have pack {m n o : Nat} (hm : m ≤ 1) (hn : n ≤ 1) (ho : o ≤ 1)
      (h01 : m=1 → n=1 → k < r+s+e)
      (h02 : m=1 → o=1 → k < r+t+e)
      (h12 : n=1 → o=1 → k < s+t+e) : Q+m+n+o ≤ p :=
    threeArmPacking M A B C hx hy hz P hm hn ho h01 h02 h12
  have finish (b : Nat) (hb : Q+b ≤ p)
      (hsmall : 2*(r+s+t)+3*e+2 ≤ (2*(k+1))*b+k) :
      x+y+z+2 ≤ 2*(k+1)*p+k := by
    have hm := Nat.mul_le_mul_left (2*(k+1)) hb
    rw [Nat.mul_add, Nat.mul_assoc 2 (k+1) Q] at hm
    omega
  change x+y+z+2 ≤ 2*(k+1)*p+k
  by_cases h01 : k < r+s+e
  · by_cases h02 : k < r+t+e
    · by_cases h12 : k < s+t+e
      · apply finish 3
        · exact pack (m:=1) (n:=1) (o:=1) (by decide) (by decide) (by decide)
            (fun _ _ => h01) (fun _ _ => h02) (fun _ _ => h12)
        · omega
      · apply finish 2
        · exact pack (m:=1) (n:=1) (o:=0) (by decide) (by decide) (by decide)
            (fun _ _ => h01) (by omega) (by omega)
        · omega
    · apply finish 2
      · exact pack (m:=1) (n:=1) (o:=0) (by decide) (by decide) (by decide)
          (fun _ _ => h01) (by omega) (by omega)
      · omega
  · by_cases h02 : k < r+t+e
    · apply finish 2
      · exact pack (m:=1) (n:=0) (o:=1) (by decide) (by decide) (by decide)
          (by omega) (fun _ _ => h02) (by omega)
      · omega
    · by_cases h12 : k < s+t+e
      · apply finish 2
        · exact pack (m:=0) (n:=1) (o:=1) (by decide) (by decide) (by decide)
            (by omega) (by omega) (fun _ _ => h12)
        · omega
      · apply finish 1
        · exact pack (m:=1) (n:=0) (o:=0) (by decide) (by decide) (by decide)
            (by omega) (by omega) (by omega)
        · omega

end TriameterQ3Graph

/-! Integer K₄ cut decomposition: a constructive proof for the scaled
four-terminal packing polytope, independent of Mathlib or an LP oracle. -/
namespace TriameterQ3Four

structure Edges where
  ab : Int
  ac : Int
  ad : Int
  bc : Int
  bd : Int
  cd : Int

def Nonneg (x : Edges) : Prop :=
  0 ≤ x.ab ∧
  0 ≤ x.ac ∧
  0 ≤ x.ad ∧
  0 ≤ x.bc ∧
  0 ≤ x.bd ∧
  0 ≤ x.cd

def Below (x y : Edges) : Prop :=
  x.ab ≤ y.ab ∧
  x.ac ≤ y.ac ∧
  x.ad ≤ y.ad ∧
  x.bc ≤ y.bc ∧
  x.bd ≤ y.bd ∧
  x.cd ≤ y.cd

def Feasible (R : Int) (x : Edges) : Prop :=
  0 ≤ x.ab ∧
  0 ≤ x.ac ∧
  0 ≤ x.ad ∧
  0 ≤ x.bc ∧
  0 ≤ x.bd ∧
  0 ≤ x.cd ∧
  x.ab ≤ R ∧
  x.ac ≤ R ∧
  x.ad ≤ R ∧
  x.bc ≤ R ∧
  x.bd ≤ R ∧
  x.cd ≤ R ∧
  x.ab + x.ac + x.bc ≤ 2*R ∧
  x.ab + x.ad + x.bd ≤ 2*R ∧
  x.ac + x.ad + x.cd ≤ 2*R ∧
  x.bc + x.bd + x.cd ≤ 2*R

def BlockAB (R : Int) (x : Edges) : Prop :=
  x.ab = R ∨ x.ab + x.ac + x.bc = 2*R ∨ x.ab + x.ad + x.bd = 2*R

def raiseAB (R : Int) (x : Edges) : Edges :=
  {x with ab := min R (min (2*R - x.ac - x.bc) (2*R - x.ad - x.bd))}

def BlockAC (R : Int) (x : Edges) : Prop :=
  x.ac = R ∨ x.ab + x.ac + x.bc = 2*R ∨ x.ac + x.ad + x.cd = 2*R

def raiseAC (R : Int) (x : Edges) : Edges :=
  {x with ac := min R (min (2*R - x.ab - x.bc) (2*R - x.ad - x.cd))}

def BlockAD (R : Int) (x : Edges) : Prop :=
  x.ad = R ∨ x.ab + x.ad + x.bd = 2*R ∨ x.ac + x.ad + x.cd = 2*R

def raiseAD (R : Int) (x : Edges) : Edges :=
  {x with ad := min R (min (2*R - x.ab - x.bd) (2*R - x.ac - x.cd))}

def BlockBC (R : Int) (x : Edges) : Prop :=
  x.bc = R ∨ x.ab + x.ac + x.bc = 2*R ∨ x.bc + x.bd + x.cd = 2*R

def raiseBC (R : Int) (x : Edges) : Edges :=
  {x with bc := min R (min (2*R - x.ab - x.ac) (2*R - x.bd - x.cd))}

def BlockBD (R : Int) (x : Edges) : Prop :=
  x.bd = R ∨ x.ab + x.ad + x.bd = 2*R ∨ x.bc + x.bd + x.cd = 2*R

def raiseBD (R : Int) (x : Edges) : Edges :=
  {x with bd := min R (min (2*R - x.ab - x.ad) (2*R - x.bc - x.cd))}

def BlockCD (R : Int) (x : Edges) : Prop :=
  x.cd = R ∨ x.ac + x.ad + x.cd = 2*R ∨ x.bc + x.bd + x.cd = 2*R

def raiseCD (R : Int) (x : Edges) : Edges :=
  {x with cd := min R (min (2*R - x.ac - x.ad) (2*R - x.bc - x.bd))}

def Saturated (R : Int) (x : Edges) : Prop :=
  BlockAB R x ∧
  BlockAC R x ∧
  BlockAD R x ∧
  BlockBC R x ∧
  BlockBD R x ∧
  BlockCD R x

def LowerTriangles (x : Edges) : Prop :=
  x.ab ≤ x.ac + x.bc ∧
  x.ac ≤ x.ab + x.bc ∧
  x.bc ≤ x.ab + x.ac ∧
  x.ab ≤ x.ad + x.bd ∧
  x.ad ≤ x.ab + x.bd ∧
  x.bd ≤ x.ab + x.ad ∧
  x.ac ≤ x.ad + x.cd ∧
  x.ad ≤ x.ac + x.cd ∧
  x.cd ≤ x.ac + x.ad ∧
  x.bc ≤ x.bd + x.cd ∧
  x.bd ≤ x.bc + x.cd ∧
  x.cd ≤ x.bc + x.bd

theorem below_trans (x y z : Edges) (hxy : Below x y) (hyz : Below y z) :
    Below x z := by
  rcases hxy with ⟨a0, a1, a2, a3, a4, a5⟩
  rcases hyz with ⟨b0, b1, b2, b3, b4, b5⟩
  exact ⟨Int.le_trans a0 b0, Int.le_trans a1 b1, Int.le_trans a2 b2, Int.le_trans a3 b3, Int.le_trans a4 b4, Int.le_trans a5 b5⟩

theorem raiseAB_good (R : Int) (x : Edges) (hx : Feasible R x) :
    Feasible R (raiseAB R x) := by
  rcases hx with ⟨n0, n1, n2, n3, n4, n5, u0, u1, u2, u3, u4, u5, t0, t1, t2, t3⟩
  unfold Feasible
  dsimp [raiseAB]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem raiseAB_above (R : Int) (x : Edges) (hx : Feasible R x) :
    Below x (raiseAB R x) := by
  rcases hx with ⟨n0, n1, n2, n3, n4, n5, u0, u1, u2, u3, u4, u5, t0, t1, t2, t3⟩
  unfold Below
  dsimp [raiseAB]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem raiseAB_block (R : Int) (x : Edges) :
    BlockAB R (raiseAB R x) := by
  unfold BlockAB
  dsimp [raiseAB]
  omega

theorem blockAB_up (R : Int) (x y : Edges)
    (hxy : Below x y) (hy : Feasible R y) (hx : BlockAB R x) : BlockAB R y := by
  rcases hxy with ⟨l0, l1, l2, l3, l4, l5⟩
  rcases hy with ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15⟩
  unfold BlockAB at hx ⊢
  rcases hx with h | h | h <;> omega

theorem raiseAC_good (R : Int) (x : Edges) (hx : Feasible R x) :
    Feasible R (raiseAC R x) := by
  rcases hx with ⟨n0, n1, n2, n3, n4, n5, u0, u1, u2, u3, u4, u5, t0, t1, t2, t3⟩
  unfold Feasible
  dsimp [raiseAC]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem raiseAC_above (R : Int) (x : Edges) (hx : Feasible R x) :
    Below x (raiseAC R x) := by
  rcases hx with ⟨n0, n1, n2, n3, n4, n5, u0, u1, u2, u3, u4, u5, t0, t1, t2, t3⟩
  unfold Below
  dsimp [raiseAC]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem raiseAC_block (R : Int) (x : Edges) :
    BlockAC R (raiseAC R x) := by
  unfold BlockAC
  dsimp [raiseAC]
  omega

theorem blockAC_up (R : Int) (x y : Edges)
    (hxy : Below x y) (hy : Feasible R y) (hx : BlockAC R x) : BlockAC R y := by
  rcases hxy with ⟨l0, l1, l2, l3, l4, l5⟩
  rcases hy with ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15⟩
  unfold BlockAC at hx ⊢
  rcases hx with h | h | h <;> omega

theorem raiseAD_good (R : Int) (x : Edges) (hx : Feasible R x) :
    Feasible R (raiseAD R x) := by
  rcases hx with ⟨n0, n1, n2, n3, n4, n5, u0, u1, u2, u3, u4, u5, t0, t1, t2, t3⟩
  unfold Feasible
  dsimp [raiseAD]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem raiseAD_above (R : Int) (x : Edges) (hx : Feasible R x) :
    Below x (raiseAD R x) := by
  rcases hx with ⟨n0, n1, n2, n3, n4, n5, u0, u1, u2, u3, u4, u5, t0, t1, t2, t3⟩
  unfold Below
  dsimp [raiseAD]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem raiseAD_block (R : Int) (x : Edges) :
    BlockAD R (raiseAD R x) := by
  unfold BlockAD
  dsimp [raiseAD]
  omega

theorem blockAD_up (R : Int) (x y : Edges)
    (hxy : Below x y) (hy : Feasible R y) (hx : BlockAD R x) : BlockAD R y := by
  rcases hxy with ⟨l0, l1, l2, l3, l4, l5⟩
  rcases hy with ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15⟩
  unfold BlockAD at hx ⊢
  rcases hx with h | h | h <;> omega

theorem raiseBC_good (R : Int) (x : Edges) (hx : Feasible R x) :
    Feasible R (raiseBC R x) := by
  rcases hx with ⟨n0, n1, n2, n3, n4, n5, u0, u1, u2, u3, u4, u5, t0, t1, t2, t3⟩
  unfold Feasible
  dsimp [raiseBC]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem raiseBC_above (R : Int) (x : Edges) (hx : Feasible R x) :
    Below x (raiseBC R x) := by
  rcases hx with ⟨n0, n1, n2, n3, n4, n5, u0, u1, u2, u3, u4, u5, t0, t1, t2, t3⟩
  unfold Below
  dsimp [raiseBC]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem raiseBC_block (R : Int) (x : Edges) :
    BlockBC R (raiseBC R x) := by
  unfold BlockBC
  dsimp [raiseBC]
  omega

theorem blockBC_up (R : Int) (x y : Edges)
    (hxy : Below x y) (hy : Feasible R y) (hx : BlockBC R x) : BlockBC R y := by
  rcases hxy with ⟨l0, l1, l2, l3, l4, l5⟩
  rcases hy with ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15⟩
  unfold BlockBC at hx ⊢
  rcases hx with h | h | h <;> omega

theorem raiseBD_good (R : Int) (x : Edges) (hx : Feasible R x) :
    Feasible R (raiseBD R x) := by
  rcases hx with ⟨n0, n1, n2, n3, n4, n5, u0, u1, u2, u3, u4, u5, t0, t1, t2, t3⟩
  unfold Feasible
  dsimp [raiseBD]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem raiseBD_above (R : Int) (x : Edges) (hx : Feasible R x) :
    Below x (raiseBD R x) := by
  rcases hx with ⟨n0, n1, n2, n3, n4, n5, u0, u1, u2, u3, u4, u5, t0, t1, t2, t3⟩
  unfold Below
  dsimp [raiseBD]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem raiseBD_block (R : Int) (x : Edges) :
    BlockBD R (raiseBD R x) := by
  unfold BlockBD
  dsimp [raiseBD]
  omega

theorem blockBD_up (R : Int) (x y : Edges)
    (hxy : Below x y) (hy : Feasible R y) (hx : BlockBD R x) : BlockBD R y := by
  rcases hxy with ⟨l0, l1, l2, l3, l4, l5⟩
  rcases hy with ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15⟩
  unfold BlockBD at hx ⊢
  rcases hx with h | h | h <;> omega

theorem raiseCD_good (R : Int) (x : Edges) (hx : Feasible R x) :
    Feasible R (raiseCD R x) := by
  rcases hx with ⟨n0, n1, n2, n3, n4, n5, u0, u1, u2, u3, u4, u5, t0, t1, t2, t3⟩
  unfold Feasible
  dsimp [raiseCD]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem raiseCD_above (R : Int) (x : Edges) (hx : Feasible R x) :
    Below x (raiseCD R x) := by
  rcases hx with ⟨n0, n1, n2, n3, n4, n5, u0, u1, u2, u3, u4, u5, t0, t1, t2, t3⟩
  unfold Below
  dsimp [raiseCD]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem raiseCD_block (R : Int) (x : Edges) :
    BlockCD R (raiseCD R x) := by
  unfold BlockCD
  dsimp [raiseCD]
  omega

theorem blockCD_up (R : Int) (x y : Edges)
    (hxy : Below x y) (hy : Feasible R y) (hx : BlockCD R x) : BlockCD R y := by
  rcases hxy with ⟨l0, l1, l2, l3, l4, l5⟩
  rcases hy with ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15⟩
  unfold BlockCD at hx ⊢
  rcases hx with h | h | h <;> omega

/-- Raise every coordinate once; later raises never unblock an earlier one. -/
theorem saturated_extension (R : Int) (x : Edges) (h : Feasible R x) :
    ∃ y : Edges, Feasible R y ∧ Below x y ∧ Saturated R y := by

  let x1 := raiseAB R x
  have g1 : Feasible R x1 := raiseAB_good R x h
  have a1 : Below x x1 := raiseAB_above R x h
  have b1 : BlockAB R x1 := raiseAB_block R x
  let x2 := raiseAC R x1
  have g2 : Feasible R x2 := raiseAC_good R x1 g1
  have a2 : Below x1 x2 := raiseAC_above R x1 g1
  have b2 : BlockAC R x2 := raiseAC_block R x1
  have bchain2 := below_trans _ _ _ a1 a2
  let x3 := raiseAD R x2
  have g3 : Feasible R x3 := raiseAD_good R x2 g2
  have a3 : Below x2 x3 := raiseAD_above R x2 g2
  have b3 : BlockAD R x3 := raiseAD_block R x2
  have bchain3 := below_trans _ _ _ bchain2 a3
  let x4 := raiseBC R x3
  have g4 : Feasible R x4 := raiseBC_good R x3 g3
  have a4 : Below x3 x4 := raiseBC_above R x3 g3
  have b4 : BlockBC R x4 := raiseBC_block R x3
  have bchain4 := below_trans _ _ _ bchain3 a4
  let x5 := raiseBD R x4
  have g5 : Feasible R x5 := raiseBD_good R x4 g4
  have a5 : Below x4 x5 := raiseBD_above R x4 g4
  have b5 : BlockBD R x5 := raiseBD_block R x4
  have bchain5 := below_trans _ _ _ bchain4 a5
  let x6 := raiseCD R x5
  have g6 : Feasible R x6 := raiseCD_good R x5 g5
  have a6 : Below x5 x6 := raiseCD_above R x5 g5
  have b6 : BlockCD R x6 := raiseCD_block R x5
  have bchain6 := below_trans _ _ _ bchain5 a6
  refine ⟨x6, g6, bchain6, ?_⟩
  unfold Saturated
  exact ⟨blockAB_up R x1 x6 (below_trans _ _ _ (below_trans _ _ _ (below_trans _ _ _ (below_trans _ _ _ a2 a3) a4) a5) a6) g6 b1, blockAC_up R x2 x6 (below_trans _ _ _ (below_trans _ _ _ (below_trans _ _ _ a3 a4) a5) a6) g6 b2, blockAD_up R x3 x6 (below_trans _ _ _ (below_trans _ _ _ a4 a5) a6) g6 b3, blockBC_up R x4 x6 (below_trans _ _ _ a5 a6) g6 b4, blockBD_up R x5 x6 a6 g6 b5, b6⟩

theorem saturated_lower (R : Int) (x : Edges) (hx : Feasible R x)
    (hs : Saturated R x) : LowerTriangles x := by
  rcases hx with ⟨n0, n1, n2, n3, n4, n5, u0, u1, u2, u3, u4, u5, t0, t1, t2, t3⟩
  rcases hs with ⟨b0, b1, b2, b3, b4, b5⟩
  unfold LowerTriangles
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩

  · unfold BlockAC at b1
    unfold BlockBC at b3
    rcases b1 with h | h | h <;> rcases b3 with j | j | j <;> omega
  · unfold BlockAB at b0
    unfold BlockBC at b3
    rcases b0 with h | h | h <;> rcases b3 with j | j | j <;> omega
  · unfold BlockAB at b0
    unfold BlockAC at b1
    rcases b0 with h | h | h <;> rcases b1 with j | j | j <;> omega
  · unfold BlockAD at b2
    unfold BlockBD at b4
    rcases b2 with h | h | h <;> rcases b4 with j | j | j <;> omega
  · unfold BlockAB at b0
    unfold BlockBD at b4
    rcases b0 with h | h | h <;> rcases b4 with j | j | j <;> omega
  · unfold BlockAB at b0
    unfold BlockAD at b2
    rcases b0 with h | h | h <;> rcases b2 with j | j | j <;> omega
  · unfold BlockAD at b2
    unfold BlockCD at b5
    rcases b2 with h | h | h <;> rcases b5 with j | j | j <;> omega
  · unfold BlockAC at b1
    unfold BlockCD at b5
    rcases b1 with h | h | h <;> rcases b5 with j | j | j <;> omega
  · unfold BlockAC at b1
    unfold BlockAD at b2
    rcases b1 with h | h | h <;> rcases b2 with j | j | j <;> omega
  · unfold BlockBD at b4
    unfold BlockCD at b5
    rcases b4 with h | h | h <;> rcases b5 with j | j | j <;> omega
  · unfold BlockBC at b3
    unfold BlockCD at b5
    rcases b3 with h | h | h <;> rcases b5 with j | j | j <;> omega
  · unfold BlockBC at b3
    unfold BlockBD at b4
    rcases b3 with h | h | h <;> rcases b4 with j | j | j <;> omega

structure Atoms where
  p000 : Int
  p001 : Int
  p010 : Int
  p011 : Int
  p100 : Int
  p101 : Int
  p110 : Int
  p111 : Int

def AtomNonneg (p : Atoms) : Prop :=
  0 ≤ p.p000 ∧
  0 ≤ p.p001 ∧
  0 ≤ p.p010 ∧
  0 ≤ p.p011 ∧
  0 ≤ p.p100 ∧
  0 ≤ p.p101 ∧
  0 ≤ p.p110 ∧
  0 ≤ p.p111

def mass (p : Atoms) : Int :=
  p.p000 + p.p001 + p.p010 + p.p011 + p.p100 + p.p101 + p.p110 + p.p111

def marginals (p : Atoms) : Edges :=
  ⟨p.p100 + p.p101 + p.p110 + p.p111,
   p.p010 + p.p011 + p.p110 + p.p111,
   p.p001 + p.p011 + p.p101 + p.p111,
   p.p010 + p.p011 + p.p100 + p.p101,
   p.p001 + p.p011 + p.p100 + p.p110,
   p.p001 + p.p010 + p.p101 + p.p110⟩

def Double (x : Edges) : Edges :=
  ⟨2*x.ab, 2*x.ac, 2*x.ad, 2*x.bc, 2*x.bd, 2*x.cd⟩

theorem saturated_decomposition (R : Int) (x : Edges) (hx : Feasible R x)
    (hl : LowerTriangles x) :
    ∃ p : Atoms, AtomNonneg p ∧ mass p = 2*R ∧ marginals p = Double x := by
  rcases hx with ⟨n0, n1, n2, n3, n4, n5, u0, u1, u2, u3, u4, u5, t0, t1, t2, t3⟩
  rcases hl with ⟨l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11⟩
  let b := 2*x.ab
  let c := 2*x.ac
  let d := 2*x.ad
  let bc := x.ab+x.ac-x.bc
  let bd := x.ab+x.ad-x.bd
  let cd := x.ac+x.ad-x.cd
  let t := max 0 (max (bc+bd-b) (max (bc+cd-c) (bd+cd-d)))
  let p : Atoms := ⟨2*R-b-c-d+bc+bd+cd-t, d-bd-cd+t, c-bc-cd+t, cd-t,
    b-bc-bd+t, bd-t, bc-t, t⟩
  refine ⟨p, ?_, ?_, ?_⟩
  · unfold AtomNonneg
    dsimp [p, t, b, c, d, bc, bd, cd]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
  · dsimp [mass, p]
    omega
  · have h_ab : (marginals p).ab = (Double x).ab := by dsimp [marginals, p, Double, b]; omega
    have h_ac : (marginals p).ac = (Double x).ac := by dsimp [marginals, p, Double, c]; omega
    have h_ad : (marginals p).ad = (Double x).ad := by dsimp [marginals, p, Double, d]; omega
    have h_bc : (marginals p).bc = (Double x).bc := by dsimp [marginals, p, Double, b, c, bc]; omega
    have h_bd : (marginals p).bd = (Double x).bd := by dsimp [marginals, p, Double, b, d, bd]; omega
    have h_cd : (marginals p).cd = (Double x).cd := by dsimp [marginals, p, Double, c, d, cd]; omega
    rcases hp : marginals p with ⟨za, zb, zc, zd, ze, zf⟩
    rw [hp] at h_ab h_ac h_ad h_bc h_bd h_cd
    dsimp [Double] at *
    rw [h_ab, h_ac, h_ad, h_bc, h_bd, h_cd]

/-- A dominated integer distance vector is a marginal of an explicitly
constructed scaled integral cut distribution. Its total mass is 2R. -/
theorem domination_by_cut_distribution (R : Int) (x : Edges) (h : Feasible R x) :
    ∃ p : Atoms, AtomNonneg p ∧ mass p = 2*R ∧ Below (Double x) (marginals p) := by
  obtain ⟨y,hy,hle,hb⟩ := saturated_extension R x h
  obtain ⟨p,hn,hm,hpg⟩ := saturated_decomposition R y hy (saturated_lower R y hy hb)
  refine ⟨p,hn,hm,?_⟩
  rw [hpg]
  rcases hle with ⟨a0, a1, a2, a3, a4, a5⟩
  unfold Below
  dsimp [Double]
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

def dot (x c : Edges) : Int :=
  x.ab*c.ab + x.ac*c.ac + x.ad*c.ad + x.bc*c.bc + x.bd*c.bd + x.cd*c.cd

def coefficientSum (c : Edges) : Int :=
  c.ab + c.ac + c.ad + c.bc + c.bd + c.cd

def cutCosts (c : Edges) : Atoms :=
  ⟨0,
   c.ad + c.bd + c.cd,
   c.ac + c.bc + c.cd,
   c.ac + c.ad + c.bc + c.bd,
   c.ab + c.bc + c.bd,
   c.ab + c.ad + c.bc + c.cd,
   c.ab + c.ac + c.bd + c.cd,
   c.ab + c.ac + c.ad⟩

def atomDot (p c : Atoms) : Int :=
  p.p000*c.p000 + p.p001*c.p001 + p.p010*c.p010 + p.p011*c.p011 + p.p100*c.p100 + p.p101*c.p101 + p.p110*c.p110 + p.p111*c.p111

def maxCut (c : Edges) : Int :=
  max (cutCosts c).p111 (max (cutCosts c).p110 (max (cutCosts c).p101 (max (cutCosts c).p100 (max (cutCosts c).p011 (max (cutCosts c).p010 (max (cutCosts c).p001 (0)))))))

def CutBound (c : Edges) (Q : Int) : Prop :=
  (cutCosts c).p000 ≤ Q ∧
  (cutCosts c).p001 ≤ Q ∧
  (cutCosts c).p010 ≤ Q ∧
  (cutCosts c).p011 ≤ Q ∧
  (cutCosts c).p100 ≤ Q ∧
  (cutCosts c).p101 ≤ Q ∧
  (cutCosts c).p110 ≤ Q ∧
  (cutCosts c).p111 ≤ Q

theorem maxCut_is_bound (c : Edges) : CutBound c (maxCut c) := by
  unfold CutBound maxCut
  dsimp [cutCosts]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem dot_mono (x y c : Edges) (hx : Below x y) (hc : Nonneg c) :
    dot x c ≤ dot y c := by

  rcases hx with ⟨b0, b1, b2, b3, b4, b5⟩
  rcases hc with ⟨a0, a1, a2, a3, a4, a5⟩
  have h0 : x.ab*c.ab ≤ y.ab*c.ab := Int.mul_le_mul_of_nonneg_right b0 a0
  have h1 : x.ac*c.ac ≤ y.ac*c.ac := Int.mul_le_mul_of_nonneg_right b1 a1
  have h2 : x.ad*c.ad ≤ y.ad*c.ad := Int.mul_le_mul_of_nonneg_right b2 a2
  have h3 : x.bc*c.bc ≤ y.bc*c.bc := Int.mul_le_mul_of_nonneg_right b3 a3
  have h4 : x.bd*c.bd ≤ y.bd*c.bd := Int.mul_le_mul_of_nonneg_right b4 a4
  have h5 : x.cd*c.cd ≤ y.cd*c.cd := Int.mul_le_mul_of_nonneg_right b5 a5
  unfold dot
  omega

theorem marginals_dot (p : Atoms) (c : Edges) :
    dot (marginals p) c = atomDot p (cutCosts c) := by
  simp only [dot, marginals, atomDot, cutCosts, Int.add_mul, Int.mul_add, Int.mul_zero,
    Int.zero_add]
  ac_rfl

theorem double_dot (p c : Edges) : dot (Double p) c = 2*dot p c := by
  simp only [dot, Double, Int.mul_assoc, Int.mul_add]

theorem convex_cut_bound (p : Atoms) (c : Edges) (Q : Int)
    (hp : AtomNonneg p) (hq : CutBound c Q) :
    atomDot p (cutCosts c) ≤ mass p * Q := by

  rcases hp with ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩
  rcases hq with ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩
  have h0 : p.p000*(cutCosts c).p000 ≤ p.p000*Q := Int.mul_le_mul_of_nonneg_left b0 a0
  have h1 : p.p001*(cutCosts c).p001 ≤ p.p001*Q := Int.mul_le_mul_of_nonneg_left b1 a1
  have h2 : p.p010*(cutCosts c).p010 ≤ p.p010*Q := Int.mul_le_mul_of_nonneg_left b2 a2
  have h3 : p.p011*(cutCosts c).p011 ≤ p.p011*Q := Int.mul_le_mul_of_nonneg_left b3 a3
  have h4 : p.p100*(cutCosts c).p100 ≤ p.p100*Q := Int.mul_le_mul_of_nonneg_left b4 a4
  have h5 : p.p101*(cutCosts c).p101 ≤ p.p101*Q := Int.mul_le_mul_of_nonneg_left b5 a5
  have h6 : p.p110*(cutCosts c).p110 ≤ p.p110*Q := Int.mul_le_mul_of_nonneg_left b6 a6
  have h7 : p.p111*(cutCosts c).p111 ≤ p.p111*Q := Int.mul_le_mul_of_nonneg_left b7 a7
  unfold atomDot mass
  simp only [Int.add_mul]
  omega

/-- Sharp upper cut functional bound for arbitrary nonnegative integer
edge coefficients; it is not restricted to products of terminal weights. -/
theorem scaled_cut_bound (R : Int) (x c : Edges) (Q : Int)
    (hx : Feasible R x) (hc : Nonneg c) (hQ : CutBound c Q) :
    dot x c ≤ R*Q := by
  obtain ⟨p,hp,hm,habove⟩ := domination_by_cut_distribution R x hx
  have he := dot_mono _ _ c habove hc
  rw [double_dot, marginals_dot] at he
  have hf := convex_cut_bound p c Q hp hQ
  rw [hm, Int.mul_assoc] at hf
  omega

def DistanceCaps (k R : Int) (d : Edges) : Prop :=
  d.ab ≤ k+R ∧
  d.ac ≤ k+R ∧
  d.ad ≤ k+R ∧
  d.bc ≤ k+R ∧
  d.bd ≤ k+R ∧
  d.cd ≤ k+R ∧
  d.ab + d.ac + d.bc ≤ 3*k+2*R ∧
  d.ab + d.ad + d.bd ≤ 3*k+2*R ∧
  d.ac + d.ad + d.cd ≤ 3*k+2*R ∧
  d.bc + d.bd + d.cd ≤ 3*k+2*R

def clipped (k : Int) (d : Edges) : Edges :=
  ⟨max 0 (d.ab-k), max 0 (d.ac-k), max 0 (d.ad-k), max 0 (d.bc-k), max 0 (d.bd-k), max 0 (d.cd-k)⟩

theorem clipped_feasible (k R : Int) (d : Edges)
    (hR : 0 ≤ R) (h : DistanceCaps k R d) : Feasible R (clipped k d) := by
  rcases h with ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9⟩
  unfold Feasible
  dsimp [clipped]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem clip_dot_bound (k : Int) (d c : Edges) (hc : Nonneg c) :
    dot d c ≤ k*coefficientSum c + dot (clipped k d) c := by

  rcases hc with ⟨a0, a1, a2, a3, a4, a5⟩
  have h0 : d.ab ≤ k+(clipped k d).ab := by dsimp [clipped]; omega
  have p0 := Int.mul_le_mul_of_nonneg_right h0 a0
  rw [Int.add_mul] at p0
  have h1 : d.ac ≤ k+(clipped k d).ac := by dsimp [clipped]; omega
  have p1 := Int.mul_le_mul_of_nonneg_right h1 a1
  rw [Int.add_mul] at p1
  have h2 : d.ad ≤ k+(clipped k d).ad := by dsimp [clipped]; omega
  have p2 := Int.mul_le_mul_of_nonneg_right h2 a2
  rw [Int.add_mul] at p2
  have h3 : d.bc ≤ k+(clipped k d).bc := by dsimp [clipped]; omega
  have p3 := Int.mul_le_mul_of_nonneg_right h3 a3
  rw [Int.add_mul] at p3
  have h4 : d.bd ≤ k+(clipped k d).bd := by dsimp [clipped]; omega
  have p4 := Int.mul_le_mul_of_nonneg_right h4 a4
  rw [Int.add_mul] at p4
  have h5 : d.cd ≤ k+(clipped k d).cd := by dsimp [clipped]; omega
  have p5 := Int.mul_le_mul_of_nonneg_right h5 a5
  rw [Int.add_mul] at p5
  unfold dot coefficientSum
  simp only [Int.mul_add]
  omega

/-- Four-terminal upper bound from the six individual and four triple
distance caps, with no LP oracle and no assumptions on how d was obtained. -/
theorem four_terminal_cut_bound (k R : Int) (d c : Edges)
    (hR : 0 ≤ R) (hd : DistanceCaps k R d) (hc : Nonneg c) :
    dot d c ≤ k*coefficientSum c + R*maxCut c := by
  have a := clip_dot_bound k d c hc
  have b := scaled_cut_bound R (clipped k d) c (maxCut c)
    (clipped_feasible k R d hR hd) hc (maxCut_is_bound c)
  omega

def terminalCoefficients (a b c d : Int) : Edges :=
  ⟨a*b,a*c,a*d,b*c,b*d,c*d⟩

/-- Product weights are the special case that yields the weighted graph
formula. Here R is D-k, i.e. (k+1)(p-1) in the packing application. -/
theorem four_terminal_product_bound (k R : Int) (x : Edges)
    (a b c d : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hR : 0 ≤ R) (hx : DistanceCaps k R x) :
    dot x (terminalCoefficients a b c d) ≤
      k*coefficientSum (terminalCoefficients a b c d) +
        R*maxCut (terminalCoefficients a b c d) := by
  apply four_terminal_cut_bound k R x _ hR hx
  exact ⟨Int.mul_nonneg ha hb, Int.mul_nonneg ha hc, Int.mul_nonneg ha hd,
    Int.mul_nonneg hb hc, Int.mul_nonneg hb hd, Int.mul_nonneg hc hd⟩

inductive Cut where
  | c000
  | c001
  | c010
  | c011
  | c100
  | c101
  | c110
  | c111

def cutCost (c : Edges) : Cut → Int
  | .c000 => (cutCosts c).p000
  | .c001 => (cutCosts c).p001
  | .c010 => (cutCosts c).p010
  | .c011 => (cutCosts c).p011
  | .c100 => (cutCosts c).p100
  | .c101 => (cutCosts c).p101
  | .c110 => (cutCosts c).p110
  | .c111 => (cutCosts c).p111

def scaledCut (R : Int) : Cut → Edges
  | .c000 => ⟨0, 0, 0, 0, 0, 0⟩
  | .c001 => ⟨0, 0, R, 0, R, R⟩
  | .c010 => ⟨0, R, 0, R, 0, R⟩
  | .c011 => ⟨0, R, R, R, R, 0⟩
  | .c100 => ⟨R, 0, 0, R, R, 0⟩
  | .c101 => ⟨R, 0, R, R, 0, R⟩
  | .c110 => ⟨R, R, 0, 0, R, R⟩
  | .c111 => ⟨R, R, R, 0, 0, 0⟩

theorem maxCut_cases (c : Edges) :
    maxCut c = (cutCosts c).p000 ∨
      maxCut c = (cutCosts c).p001 ∨
      maxCut c = (cutCosts c).p010 ∨
      maxCut c = (cutCosts c).p011 ∨
      maxCut c = (cutCosts c).p100 ∨
      maxCut c = (cutCosts c).p101 ∨
      maxCut c = (cutCosts c).p110 ∨
      maxCut c = (cutCosts c).p111 := by
  unfold maxCut
  dsimp [cutCosts]
  omega

theorem maxCut_realized (c : Edges) : ∃ b : Cut, maxCut c = cutCost c b := by
  rcases maxCut_cases c with h | h | h | h | h | h | h | h

  · exact ⟨.c000, h⟩
  · exact ⟨.c001, h⟩
  · exact ⟨.c010, h⟩
  · exact ⟨.c011, h⟩
  · exact ⟨.c100, h⟩
  · exact ⟨.c101, h⟩
  · exact ⟨.c110, h⟩
  · exact ⟨.c111, h⟩

theorem scaledCut_feasible (R : Int) (hR : 0 ≤ R) (b : Cut) :
    Feasible R (scaledCut R b) := by
  cases b <;> unfold Feasible <;> dsimp [scaledCut] <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem scaledCut_dot (R : Int) (c : Edges) (b : Cut) :
    dot (scaledCut R b) c = R * cutCost c b := by
  cases b <;>
    simp [dot, scaledCut, cutCost, cutCosts, Int.mul_add]

/-- The maximum of the four-terminal scaled feasible polytope is attained
by a single actual cut, not merely approached by a weighted solution. -/
theorem scaled_polytope_maximum (R : Int) (hR : 0 ≤ R) (c : Edges) (hc : Nonneg c) :
    (∀ x, Feasible R x → dot x c ≤ R*maxCut c) ∧
    ∃ x, Feasible R x ∧ dot x c = R*maxCut c := by
  refine ⟨fun x hx => scaled_cut_bound R x c _ hx hc (maxCut_is_bound c), ?_⟩
  obtain ⟨b,hb⟩ := maxCut_realized c
  exact ⟨scaledCut R b, scaledCut_feasible R hR b, (scaledCut_dot R c b).trans (congrArg (R*·) hb.symm)⟩

end TriameterQ3Four

namespace TriameterQ3SmallPacking

def vsum : (n : Nat) → (Fin n → Nat) → Nat
  | 0, _ => 0
  | n+1, f => f 0 + vsum n (fun i => f i.succ)

def psum : (n : Nat) → (Fin n → Fin n → Nat) → Nat
  | 0, _ => 0
  | n+1, f => vsum n (fun i => f 0 i.succ) + psum n (fun i j => f i.succ j.succ)

theorem vsum_congr {n : Nat} {f g : Fin n → Nat} (h : ∀ i, f i = g i) :
    vsum n f = vsum n g := congrArg (vsum n) (funext h)

theorem vsum_zero (n : Nat) : vsum n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [vsum,ih]

theorem vsum_le {n : Nat} {f g : Fin n → Nat} (h : ∀ i, f i ≤ g i) :
    vsum n f ≤ vsum n g := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih => exact Nat.add_le_add (h 0) (ih (fun i => h i.succ))

theorem vsum_add {n : Nat} (f g : Fin n → Nat) :
    vsum n (fun i => f i + g i) = vsum n f + vsum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [vsum,ih]
    omega

theorem vsum_mul_left {n : Nat} (m : Nat) (f : Fin n → Nat) :
    vsum n (fun i => m*f i) = m*vsum n f := by
  induction n with
  | zero => simp [vsum]
  | succ n ih => simp only [vsum,ih,Nat.mul_add]

theorem vsum_mul_right {n : Nat} (m : Nat) (f : Fin n → Nat) :
    vsum n (fun i => f i*m) = vsum n f*m := by
  simp only [Nat.mul_comm _ m,vsum_mul_left]

theorem vsum_swap {n m : Nat} (f : Fin n → Fin m → Nat) :
    vsum n (fun i => vsum m (f i)) = vsum m (fun j => vsum n (fun i => f i j)) := by
  induction n with
  | zero => simp [vsum,vsum_zero]
  | succ n ih =>
    simp only [vsum,ih,vsum_add]

theorem psum_congr {n : Nat} {f g : Fin n → Fin n → Nat} (h : ∀ i j, f i j = g i j) :
    psum n f = psum n g := congrArg (psum n) (funext (fun i => funext (h i)))

theorem psum_add {n : Nat} (f g : Fin n → Fin n → Nat) :
    psum n (fun i j => f i j+g i j) = psum n f+psum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [psum,ih,vsum_add]
    omega

theorem psum_mul_left {n : Nat} (m : Nat) (f : Fin n → Fin n → Nat) :
    psum n (fun i j => m*f i j) = m*psum n f := by
  induction n with
  | zero => simp [psum]
  | succ n ih => simp only [psum,ih,vsum_mul_left,Nat.mul_add]

theorem psum_mul_right {n : Nat} (m : Nat) (f : Fin n → Fin n → Nat) :
    psum n (fun i j => f i j*m) = psum n f*m := by
  simp only [Nat.mul_comm _ m,psum_mul_left]

theorem psum_le {n : Nat} {f g : Fin n → Fin n → Nat}
    (h : ∀ i j, i ≠ j → f i j ≤ g i j) : psum n f ≤ psum n g := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    have h₁ := vsum_le (fun i => h 0 i.succ (fun he => Fin.succ_ne_zero i he.symm))
    have h₂ := ih (fun i j hne => h i.succ j.succ (fun hEq => hne (Fin.succ_inj.mp hEq)))
    exact Nat.add_le_add h₁ h₂

theorem double_psum {n : Nat} (f : Fin n → Fin n → Nat) (hs : ∀ i j, f i j = f j i)
    (hd : ∀ i, f i i = 0) : vsum n (fun i => vsum n (f i)) = 2*psum n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      vsum (n+1) (fun i => vsum (n+1) (f i)) =
          f 0 0 + vsum n (fun j => f 0 j.succ) +
          vsum n (fun i => f i.succ 0 + vsum n (fun j => f i.succ j.succ)) := rfl
      _ = 2*psum (n+1) f := by
        rw [hd 0,vsum_add]
        have h := ih (fun i j => f i.succ j.succ) (fun i j => hs i.succ j.succ) (fun i => hd i.succ)
        rw [h]
        have hc : vsum n (fun i => f i.succ 0) = vsum n (fun i => f 0 i.succ) :=
          vsum_congr (fun i => hs i.succ 0)
        rw [hc]
        simp only [psum]
        omega

theorem max_fin_exists {n : Nat} (hn : 0 < n) (f : Fin n → Nat) :
    ∃ i : Fin n, ∀ j, f j ≤ f i := by
  cases n with
  | zero => exact (Nat.not_lt_zero _ hn).elim
  | succ n =>
    clear hn
    induction n with
    | zero => exact ⟨0,fun j => by
        have hj := j.isLt
        have e : j = 0 := Fin.ext (by omega)
        simp [e]⟩
    | succ n ih =>
      obtain ⟨s,hs⟩ := ih (fun i => f i.succ)
      by_cases h : f 0 ≤ f s.succ
      · refine ⟨s.succ,fun j => Fin.cases h (fun j => hs j) j⟩
      · refine ⟨0,fun j => Fin.cases (Nat.le_refl _) (fun j => ?_) j⟩
        exact Nat.le_trans (hs j) (Nat.le_of_lt (Nat.lt_of_not_ge h))

theorem max_bounded_nat_exists (P : Nat → Prop) (n : Nat) (h0 : P 0) :
    ∃ p, p ≤ n ∧ P p ∧ ∀ q, q ≤ n → P q → q ≤ p := by
  induction n with
  | zero => exact ⟨0,Nat.le_refl _,h0,fun q hq _ => hq⟩
  | succ n ih =>
    by_cases hn : P (n+1)
    · exact ⟨n+1,Nat.le_refl _,hn,fun q hq _ => hq⟩
    · obtain ⟨p,hp,hit,hu⟩ := ih
      refine ⟨p,by omega,hit,?_⟩
      intro q hq hP
      have he : q ≠ n+1 := by intro e; exact hn (e ▸ hP)
      exact hu q (by omega) hP

end TriameterQ3SmallPacking

/-! A weighted triangle-free graph's edge sum is at most the weight of
one complete cut of the vertex set, not merely at most W squared over 4. -/
namespace TriameterQ3SmallPacking

def edgeTerm {n : Nat} (w : Fin n → Nat) (A : Fin n → Fin n → Bool)
    (i j : Fin n) : Nat := if A i j then w i*w j else 0

def edgeWeight {n : Nat} (w : Fin n → Nat) (A : Fin n → Fin n → Bool) : Nat :=
  psum n (edgeTerm w A)

def symmetric {n : Nat} (A : Fin n → Fin n → Bool) : Prop :=
  ∀ i j, A i j = A j i

def diagonalZero {n : Nat} (A : Fin n → Fin n → Bool) : Prop :=
  ∀ i, A i i = false

def triangleFree {n : Nat} (A : Fin n → Fin n → Bool) : Prop :=
  ∀ i j ℓ, A i j = true → A i ℓ = true → A j ℓ = false

def degreeWeight {n : Nat} (w : Fin n → Nat) (A : Fin n → Fin n → Bool) (i : Fin n) : Nat :=
  vsum n (fun j => if A i j then w j else 0)

def partWeight {n : Nat} (w : Fin n → Nat) (s : Fin n → Bool) (a : Bool) : Nat :=
  vsum n (fun i => if s i = a then w i else 0)

def cutWeight {n : Nat} (w : Fin n → Nat) (s : Fin n → Bool) : Nat :=
  partWeight w s true * partWeight w s false

def cutAdj {n : Nat} (s : Fin n → Bool) (i j : Fin n) : Bool :=
  decide (s i ≠ s j)

theorem edgeTerm_symm {n : Nat} (w : Fin n → Nat)
    (A : Fin n → Fin n → Bool) (hs : symmetric A) (i j : Fin n) :
    edgeTerm w A i j = edgeTerm w A j i := by
  unfold edgeTerm
  rw [hs i j,Nat.mul_comm (w i) (w j)]

theorem edgeTerm_diagonal {n : Nat} (w : Fin n → Nat)
    (A : Fin n → Fin n → Bool) (hd : diagonalZero A) (i : Fin n) :
    edgeTerm w A i i = 0 := by simp [edgeTerm,hd i]

theorem rowWeight {n : Nat} (w : Fin n → Nat)
    (A : Fin n → Fin n → Bool) (i : Fin n) :
    vsum n (edgeTerm w A i) = w i * degreeWeight w A i := by
  rw [degreeWeight,←vsum_mul_left]
  apply vsum_congr
  intro j
  cases h : A i j <;> simp [edgeTerm,h]

theorem cut_edge_weight {n : Nat} (w : Fin n → Nat) (s : Fin n → Bool) :
    edgeWeight w (cutAdj s) = cutWeight w s := by
  have hs : symmetric (cutAdj s) := by
    intro i j
    cases hi : s i <;> cases hj : s j <;> simp [cutAdj,hi,hj]
  have hd : diagonalZero (cutAdj s) := by
    intro i
    simp [cutAdj]
  let a := fun i => if s i = true then w i else 0
  let b := fun i => if s i = false then w i else 0
  have hrow (i j : Fin n) : edgeTerm w (cutAdj s) i j = a i*b j+b i*a j := by
    cases hi : s i <;> cases hj : s j <;> simp [a,b,edgeTerm,cutAdj,hi,hj]
  have hsum : vsum n (fun i => vsum n (edgeTerm w (cutAdj s) i)) =
      2*cutWeight w s := by
    calc
      _ = vsum n (fun i => vsum n (fun j => a i*b j+b i*a j)) :=
        vsum_congr (fun i => vsum_congr (hrow i))
      _ = _ := by
        simp only [vsum_add,vsum_mul_left,vsum_mul_right]
        change vsum n a * vsum n b + vsum n b * vsum n a =
          2*(vsum n a*vsum n b)
        rw [Nat.mul_comm (vsum n b) (vsum n a)]
        omega
  have h := double_psum (edgeTerm w (cutAdj s))
    (edgeTerm_symm w _ hs) (edgeTerm_diagonal w _ hd)
  unfold edgeWeight
  omega

theorem cutWeight_max_exists {n : Nat} (w : Fin n → Nat) :
    ∃ s : Fin n → Bool, ∀ t, cutWeight w t ≤ cutWeight w s := by
  let W := vsum n w
  have hle (s : Fin n → Bool) (a : Bool) : partWeight w s a ≤ W := by
    apply vsum_le
    intro i
    split <;> omega
  have hbound (s : Fin n → Bool) : cutWeight w s ≤ W*W :=
    Nat.mul_le_mul (hle s true) (hle s false)
  let P (v : Nat) := ∃ s : Fin n → Bool, cutWeight w s = v
  have h0 : P 0 := by
    refine ⟨fun _ => false,?_⟩
    simp [cutWeight,partWeight,vsum_zero]
  obtain ⟨z,_,⟨s,hs⟩,hmax⟩ := max_bounded_nat_exists P (W*W) h0
  exact ⟨s,fun t => hs ▸ hmax _ (hbound t) ⟨t,rfl⟩⟩

noncomputable def largestCutWeight {n : Nat} (w : Fin n → Nat) : Nat :=
  cutWeight w (cutWeight_max_exists w).choose

theorem largestCutWeight_bounds {n : Nat} (w : Fin n → Nat) (s : Fin n → Bool) :
    cutWeight w s ≤ largestCutWeight w := (cutWeight_max_exists w).choose_spec s

theorem largestCutWeight_attained {n : Nat} (w : Fin n → Nat) :
    ∃ s : Fin n → Bool, cutWeight w s = largestCutWeight w :=
  ⟨(cutWeight_max_exists w).choose,rfl⟩

theorem edges_charged_to_complement {n : Nat} (w : Fin n → Nat)
    (A : Fin n → Fin n → Bool) (hs : symmetric A) (hd : diagonalZero A)
    (s : Fin n → Bool) (hInd : ∀ i j, s i = true → s j = true → A i j = false) :
    edgeWeight w A ≤ vsum n (fun i => if s i = false then w i*degreeWeight w A i else 0) := by
  let E := edgeTerm w A
  let B : Fin n → Fin n → Nat := fun i j => if s i = false then E i j else 0
  have hcharge (i j : Fin n) : E i j ≤ B i j+B j i := by
    cases hi : s i <;> cases hj : s j
    · have he := edgeTerm_symm w A hs i j
      dsimp [E,B]
      simp [hi,hj,he]
    · simp [B,hi,hj]
    · simpa [B,hi,hj] using Nat.le_of_eq (edgeTerm_symm w A hs i j)
    · have ha := hInd i j hi hj
      simp [B,E,edgeTerm,hi,hj,ha]
  have h1 : vsum n (fun i => vsum n (E i)) ≤
      vsum n (fun i => vsum n (fun j => B i j+B j i)) :=
    vsum_le (fun i => vsum_le (hcharge i))
  have h2 : vsum n (fun i => vsum n (fun j => B i j+B j i)) =
      2*vsum n (fun i => vsum n (B i)) := by
    simp only [vsum_add]
    have hs' := vsum_swap B
    omega
  have h3 : vsum n (fun i => vsum n (B i)) =
      vsum n (fun i => if s i = false then w i*degreeWeight w A i else 0) := by
    apply vsum_congr
    intro i
    cases hi : s i
    · simp [B,hi,E,rowWeight]
    · simp [B,hi,vsum_zero]
  have he := double_psum E (edgeTerm_symm w A hs) (edgeTerm_diagonal w A hd)
  rw [h2,h3,he] at h1
  unfold edgeWeight
  change edgeWeight w A ≤ _
  change 2*edgeWeight w A ≤ _ at h1
  omega

theorem weighted_triangle_free_cut {n : Nat} (w : Fin n → Nat) (A : Fin n → Fin n → Bool)
    (hs : symmetric A) (hd : diagonalZero A) (ht : triangleFree A) :
    ∃ s : Fin n → Bool, edgeWeight w A ≤ cutWeight w s := by
  cases n with
  | zero => exact ⟨Fin.elim0,Nat.le_refl 0⟩
  | succ n =>
    obtain ⟨b,hb⟩ := max_fin_exists (Nat.succ_pos n) (degreeWeight w A)
    let s := A b
    have hInd : ∀ i j, s i = true → s j = true → A i j = false := fun i j => ht b i j
    have h := edges_charged_to_complement w A hs hd s hInd
    have hsdeg : partWeight w s true = degreeWeight w A b := by
      apply vsum_congr
      intro i
      cases he : A b i <;> simp [s,he]
    have hp : vsum (n+1) (fun i => if s i = false then w i*degreeWeight w A i else 0) ≤
        vsum (n+1) (fun i => (if s i = false then w i else 0)*degreeWeight w A b) := by
      apply vsum_le
      intro i
      cases he : s i <;> simp [Nat.mul_le_mul_left _ (hb i)]
    rw [vsum_mul_right] at hp
    change _ ≤ partWeight w s false * degreeWeight w A b at hp
    refine ⟨s,Nat.le_trans h ?_⟩
    simpa only [cutWeight,hsdeg,Nat.mul_comm (degreeWeight w A b)] using hp

theorem weighted_triangle_free_maxcut {n : Nat} (w : Fin n → Nat)
    (A : Fin n → Fin n → Bool) (hs : symmetric A) (hd : diagonalZero A)
    (ht : triangleFree A) : edgeWeight w A ≤ largestCutWeight w := by
  obtain ⟨s,h⟩ := weighted_triangle_free_cut w A hs hd ht
  exact Nat.le_trans h (largestCutWeight_bounds w s)

end TriameterQ3SmallPacking

namespace TriameterQ3SmallPacking
open TriameterQ3Graph

/-- Six no longer plays a special role: sum once over each unordered pair
of terminal labels, with the product of its two natural-valued weights. -/
def terminalScore {V : Type} {G : SimpleGraph V} (M : ShortestDistances G)
    {r : Nat} (T : Fin r → V) (w : Fin r → Nat) : Nat :=
  psum r (fun i j => w i*w j*M.dist (T i) (T j))

def pairWeight {r : Nat} (w : Fin r → Nat) : Nat :=
  psum r (fun i j => w i*w j)

def packingRadius (k p : Nat) : Nat := (k+1)*(p-1)

def farAdj {V : Type} {G : SimpleGraph V} (M : ShortestDistances G) (k : Nat)
    {r : Nat} (T : Fin r → V) (i j : Fin r) : Bool :=
  decide (k < M.dist (T i) (T j))

theorem farAdj_symm {V : Type} {G : SimpleGraph V} (M : ShortestDistances G) (k : Nat)
    {r : Nat} (T : Fin r → V) : symmetric (farAdj M k T) := by
  intro i j
  simp [farAdj,M.dist_symm (T i) (T j)]

theorem farAdj_diag {V : Type} {G : SimpleGraph V} (M : ShortestDistances G) (k : Nat)
    {r : Nat} (T : Fin r → V) : diagonalZero (farAdj M k T) := by
  intro i
  simp [farAdj,M.dist_self]

theorem fin3_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  have h := i.isLt
  have h' : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
  rcases h' with i0 | i1 | i2
  · exact Or.inl (Fin.ext i0)
  · exact Or.inr (Or.inl (Fin.ext i1))
  · exact Or.inr (Or.inr (Fin.ext i2))

theorem pack_of_three {V : Type} {G : SimpleGraph V} (M : ShortestDistances G) (k : Nat)
    (a b c : V) (ab : k < M.dist a b) (ac : k < M.dist a c) (bc : k < M.dist b c) :
    ∃ f : Fin 3 → V, IsPacking M k f := by
  let f : Fin 3 → V := fun i => if i = 0 then a else if i = 1 then b else c
  have ba : k < M.dist b a := by simpa only [M.dist_symm b a] using ab
  have ca : k < M.dist c a := by simpa only [M.dist_symm c a] using ac
  have cb : k < M.dist c b := by simpa only [M.dist_symm c b] using bc
  refine ⟨f,?_⟩
  intro i j h
  rcases fin3_cases i with rfl | rfl | rfl <;>
    rcases fin3_cases j with rfl | rfl | rfl <;>
    first | exact (h rfl).elim | solve | simpa [f] using ab | simpa [f] using ac |
      simpa [f] using ba | simpa [f] using bc | simpa [f] using ca | simpa [f] using cb

theorem farAdj_triangleFree {V : Type} {G : SimpleGraph V} (M : ShortestDistances G)
    (k p : Nat) (hp : p ≤ 2) (P : ExactPacking M k p) {r : Nat} (T : Fin r → V) :
    triangleFree (farAdj M k T) := by
  intro i j l hij hil
  cases hjl : farAdj M k T j l
  · rfl
  · have hab : k < M.dist (T i) (T j) := of_decide_eq_true hij
    have hac : k < M.dist (T i) (T l) := of_decide_eq_true hil
    have hbc : k < M.dist (T j) (T l) := of_decide_eq_true hjl
    obtain ⟨f,hf⟩ := pack_of_three M k (T i) (T j) (T l) hab hac hbc
    have bad := P.upper 3 f hf
    omega

theorem packing_diam {V : Type} {G : SimpleGraph V} (M : ShortestDistances G)
    (k p : Nat) (P : ExactPacking M k p) (x y : V) :
    M.dist x y ≤ k + packingRadius k p := by
  have h := diameter_le_of_packing M P x y
  have hp := exactPacking_pos M P x
  have hpred : (p-1)+1=p := by omega
  have hmul : (k+1)*p = packingRadius k p + (k+1) := by
    calc
      _ = (k+1)*((p-1)+1) := congrArg ((k+1)*·) hpred.symm
      _ = _ := by simp only [packingRadius,Nat.mul_add,Nat.mul_one]
  omega

theorem graph_score_clip {V : Type} {G : SimpleGraph V} (M : ShortestDistances G)
    (k p : Nat) (P : ExactPacking M k p) {r : Nat} (T : Fin r → V) (w : Fin r → Nat) :
    terminalScore M T w ≤ k*pairWeight w +
      packingRadius k p * edgeWeight w (farAdj M k T) := by
  let R := packingRadius k p
  let A := farAdj M k T
  have hpairs (i j : Fin r) (_ : i ≠ j) :
      w i*w j * M.dist (T i) (T j) ≤ w i*w j*k + R*edgeTerm w A i j := by
    by_cases h : k < M.dist (T i) (T j)
    · have hD := packing_diam M k p P (T i) (T j)
      change _ ≤ k+R at hD
      have hh := Nat.mul_le_mul_left (w i*w j) hD
      rw [Nat.mul_add,Nat.mul_comm (w i*w j) R] at hh
      simpa [edgeTerm,A,farAdj,h] using hh
    · have hh := Nat.mul_le_mul_left (w i*w j) (Nat.le_of_not_gt h)
      simpa [edgeTerm,A,farAdj,h] using hh
  have hsum := psum_le hpairs
  rw [psum_add,psum_mul_right,psum_mul_left] at hsum
  unfold terminalScore pairWeight edgeWeight
  rw [Nat.mul_comm k (psum r (fun i j => w i*w j))]
  exact hsum

theorem weighted_smallpacking_upper {V : Type} {G : SimpleGraph V}
    (M : ShortestDistances G) (k p : Nat) (hp : p ≤ 2)
    (P : ExactPacking M k p) {r : Nat} (T : Fin r → V) (w : Fin r → Nat) :
    terminalScore M T w ≤ k*pairWeight w + packingRadius k p * largestCutWeight w := by
  have hh := weighted_triangle_free_maxcut w (farAdj M k T)
    (farAdj_symm M k T) (farAdj_diag M k T) (farAdj_triangleFree M k p hp P T)
  exact Nat.le_trans (graph_score_clip M k p P T w)
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ hh) _)

end TriameterQ3SmallPacking

/-! Finite low-edge case certificates for five-terminal packing.
The Boolean classification has only ten flags and is checked by kernel
reduction. No distance optimization or finite graph enumeration is used. -/
namespace TriameterQ3PackingWindows
open TriameterQ3Graph

set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 10000
set_option maxSynthPendingDepth 1000

structure LowBits where
  b01 : Bool
  b02 : Bool
  b03 : Bool
  b04 : Bool
  b12 : Bool
  b13 : Bool
  b14 : Bool
  b23 : Bool
  b24 : Bool
  b34 : Bool

def allEdges : List (Fin 5 × Fin 5) := [(0,1), (0,2), (0,3), (0,4), (1,2), (1,3), (1,4), (2,3), (2,4), (3,4)]

def LowBits.get (L : LowBits) (x : Fin 5 × Fin 5) : Bool :=
  if x = (0,1) then L.b01
  else if x = (0,2) then L.b02
  else if x = (0,3) then L.b03
  else if x = (0,4) then L.b04
  else if x = (1,2) then L.b12
  else if x = (1,3) then L.b13
  else if x = (1,4) then L.b14
  else if x = (2,3) then L.b23
  else if x = (2,4) then L.b24
  else if x = (3,4) then L.b34
  else false

def cutSide (m : Fin 15) (i : Fin 5) : Bool := (2*(m.val+1)).testBit i.val

def crosses (L : LowBits) (m : Fin 15) : Bool :=
  allEdges.any (fun e => (cutSide m e.1 != cutSide m e.2) && L.get e)

def connectedBits (L : LowBits) : Prop := ∀ m : Fin 15, crosses L m = true

instance (L : LowBits) : Decidable (connectedBits L) := inferInstanceAs (Decidable (∀ m : Fin 15, crosses L m = true))

def CycleCases (L : LowBits) : Prop :=
  let ⟨b01,b02,b03,b04,b12,b13,b14,b23,b24,b34⟩ := L
  ((b01 = true ∧ b12 = true)
    ∨ (b01 = true ∧ b23 = true)
    ∨ (b01 = true ∧ b34 = true)
    ∨ (b01 = true ∧ b04 = true)
    ∨ (b12 = true ∧ b23 = true)
    ∨ (b12 = true ∧ b34 = true)
    ∨ (b12 = true ∧ b04 = true)
    ∨ (b23 = true ∧ b34 = true)
    ∨ (b23 = true ∧ b04 = true)
    ∨ (b34 = true ∧ b04 = true)
    ∨ (b02 = true ∧ b24 = true ∧ b01 = true)
    ∨ (b02 = true ∧ b24 = true ∧ b12 = true)
    ∨ (b02 = true ∧ b24 = true ∧ b23 = true)
    ∨ (b02 = true ∧ b24 = true ∧ b34 = true)
    ∨ (b03 = true ∧ b13 = true ∧ b12 = true)
    ∨ (b03 = true ∧ b13 = true ∧ b23 = true)
    ∨ (b03 = true ∧ b13 = true ∧ b34 = true)
    ∨ (b03 = true ∧ b13 = true ∧ b04 = true)
    ∨ (b14 = true ∧ b24 = true ∧ b01 = true)
    ∨ (b14 = true ∧ b24 = true ∧ b23 = true)
    ∨ (b14 = true ∧ b24 = true ∧ b34 = true)
    ∨ (b14 = true ∧ b24 = true ∧ b04 = true)
    ∨ (b02 = true ∧ b03 = true ∧ b01 = true)
    ∨ (b02 = true ∧ b03 = true ∧ b12 = true)
    ∨ (b02 = true ∧ b03 = true ∧ b34 = true)
    ∨ (b02 = true ∧ b03 = true ∧ b04 = true)
    ∨ (b13 = true ∧ b14 = true ∧ b01 = true)
    ∨ (b13 = true ∧ b14 = true ∧ b12 = true)
    ∨ (b13 = true ∧ b14 = true ∧ b23 = true)
    ∨ (b13 = true ∧ b14 = true ∧ b04 = true)
    ∨ (b03 = true ∧ b13 = true ∧ b14 = true ∧ b24 = true)
    ∨ (b02 = true ∧ b24 = true ∧ b14 = true ∧ b13 = true)
    ∨ (b14 = true ∧ b24 = true ∧ b02 = true ∧ b03 = true)
    ∨ (b13 = true ∧ b03 = true ∧ b02 = true ∧ b24 = true)
    ∨ (b02 = true ∧ b03 = true ∧ b13 = true ∧ b14 = true))

def TotalCases (L : LowBits) : Prop :=
  let ⟨b01,b02,b03,b04,b12,b13,b14,b23,b24,b34⟩ := L
  ((b01 = true ∧ b02 = true ∧ b03 = true ∧ b04 = true)
    ∨ (b01 = true ∧ b02 = true ∧ b03 = true ∧ b14 = true)
    ∨ (b01 = true ∧ b02 = true ∧ b03 = true ∧ b24 = true)
    ∨ (b01 = true ∧ b02 = true ∧ b03 = true ∧ b34 = true)
    ∨ (b01 = true ∧ b02 = true ∧ b04 = true ∧ b13 = true)
    ∨ (b01 = true ∧ b02 = true ∧ b04 = true ∧ b23 = true)
    ∨ (b01 = true ∧ b02 = true ∧ b04 = true ∧ b34 = true)
    ∨ (b01 = true ∧ b02 = true ∧ b13 = true ∧ b14 = true)
    ∨ (b01 = true ∧ b02 = true ∧ b13 = true ∧ b24 = true)
    ∨ (b01 = true ∧ b02 = true ∧ b13 = true ∧ b34 = true)
    ∨ (b01 = true ∧ b02 = true ∧ b14 = true ∧ b23 = true)
    ∨ (b01 = true ∧ b02 = true ∧ b14 = true ∧ b34 = true)
    ∨ (b01 = true ∧ b02 = true ∧ b23 = true ∧ b24 = true)
    ∨ (b01 = true ∧ b02 = true ∧ b23 = true ∧ b34 = true)
    ∨ (b01 = true ∧ b02 = true ∧ b24 = true ∧ b34 = true)
    ∨ (b01 = true ∧ b03 = true ∧ b04 = true ∧ b12 = true)
    ∨ (b01 = true ∧ b03 = true ∧ b04 = true ∧ b23 = true)
    ∨ (b01 = true ∧ b03 = true ∧ b04 = true ∧ b24 = true)
    ∨ (b01 = true ∧ b03 = true ∧ b12 = true ∧ b14 = true)
    ∨ (b01 = true ∧ b03 = true ∧ b12 = true ∧ b24 = true)
    ∨ (b01 = true ∧ b03 = true ∧ b12 = true ∧ b34 = true)
    ∨ (b01 = true ∧ b03 = true ∧ b14 = true ∧ b23 = true)
    ∨ (b01 = true ∧ b03 = true ∧ b14 = true ∧ b24 = true)
    ∨ (b01 = true ∧ b03 = true ∧ b23 = true ∧ b24 = true)
    ∨ (b01 = true ∧ b03 = true ∧ b23 = true ∧ b34 = true)
    ∨ (b01 = true ∧ b03 = true ∧ b24 = true ∧ b34 = true)
    ∨ (b01 = true ∧ b04 = true ∧ b12 = true ∧ b13 = true)
    ∨ (b01 = true ∧ b04 = true ∧ b12 = true ∧ b23 = true)
    ∨ (b01 = true ∧ b04 = true ∧ b12 = true ∧ b34 = true)
    ∨ (b01 = true ∧ b04 = true ∧ b13 = true ∧ b23 = true)
    ∨ (b01 = true ∧ b04 = true ∧ b13 = true ∧ b24 = true)
    ∨ (b01 = true ∧ b04 = true ∧ b23 = true ∧ b24 = true)
    ∨ (b01 = true ∧ b04 = true ∧ b23 = true ∧ b34 = true)
    ∨ (b01 = true ∧ b04 = true ∧ b24 = true ∧ b34 = true)
    ∨ (b01 = true ∧ b12 = true ∧ b13 = true ∧ b14 = true)
    ∨ (b01 = true ∧ b12 = true ∧ b13 = true ∧ b24 = true)
    ∨ (b01 = true ∧ b12 = true ∧ b13 = true ∧ b34 = true)
    ∨ (b01 = true ∧ b12 = true ∧ b14 = true ∧ b23 = true)
    ∨ (b01 = true ∧ b12 = true ∧ b14 = true ∧ b34 = true)
    ∨ (b01 = true ∧ b12 = true ∧ b23 = true ∧ b24 = true)
    ∨ (b01 = true ∧ b12 = true ∧ b23 = true ∧ b34 = true)
    ∨ (b01 = true ∧ b12 = true ∧ b24 = true ∧ b34 = true)
    ∨ (b01 = true ∧ b13 = true ∧ b14 = true ∧ b23 = true)
    ∨ (b01 = true ∧ b13 = true ∧ b14 = true ∧ b24 = true)
    ∨ (b01 = true ∧ b13 = true ∧ b23 = true ∧ b24 = true)
    ∨ (b01 = true ∧ b13 = true ∧ b23 = true ∧ b34 = true)
    ∨ (b01 = true ∧ b13 = true ∧ b24 = true ∧ b34 = true)
    ∨ (b01 = true ∧ b14 = true ∧ b23 = true ∧ b24 = true)
    ∨ (b01 = true ∧ b14 = true ∧ b23 = true ∧ b34 = true)
    ∨ (b01 = true ∧ b14 = true ∧ b24 = true ∧ b34 = true)
    ∨ (b02 = true ∧ b03 = true ∧ b04 = true ∧ b12 = true)
    ∨ (b02 = true ∧ b03 = true ∧ b04 = true ∧ b13 = true)
    ∨ (b02 = true ∧ b03 = true ∧ b04 = true ∧ b14 = true)
    ∨ (b02 = true ∧ b03 = true ∧ b12 = true ∧ b14 = true)
    ∨ (b02 = true ∧ b03 = true ∧ b12 = true ∧ b24 = true)
    ∨ (b02 = true ∧ b03 = true ∧ b12 = true ∧ b34 = true)
    ∨ (b02 = true ∧ b03 = true ∧ b13 = true ∧ b14 = true)
    ∨ (b02 = true ∧ b03 = true ∧ b13 = true ∧ b24 = true)
    ∨ (b02 = true ∧ b03 = true ∧ b13 = true ∧ b34 = true)
    ∨ (b02 = true ∧ b03 = true ∧ b14 = true ∧ b24 = true)
    ∨ (b02 = true ∧ b03 = true ∧ b14 = true ∧ b34 = true)
    ∨ (b02 = true ∧ b04 = true ∧ b12 = true ∧ b13 = true)
    ∨ (b02 = true ∧ b04 = true ∧ b12 = true ∧ b23 = true)
    ∨ (b02 = true ∧ b04 = true ∧ b12 = true ∧ b34 = true)
    ∨ (b02 = true ∧ b04 = true ∧ b13 = true ∧ b14 = true)
    ∨ (b02 = true ∧ b04 = true ∧ b13 = true ∧ b23 = true)
    ∨ (b02 = true ∧ b04 = true ∧ b13 = true ∧ b34 = true)
    ∨ (b02 = true ∧ b04 = true ∧ b14 = true ∧ b23 = true)
    ∨ (b02 = true ∧ b04 = true ∧ b14 = true ∧ b34 = true)
    ∨ (b02 = true ∧ b12 = true ∧ b13 = true ∧ b14 = true)
    ∨ (b02 = true ∧ b12 = true ∧ b13 = true ∧ b24 = true)
    ∨ (b02 = true ∧ b12 = true ∧ b13 = true ∧ b34 = true)
    ∨ (b02 = true ∧ b12 = true ∧ b14 = true ∧ b23 = true)
    ∨ (b02 = true ∧ b12 = true ∧ b14 = true ∧ b34 = true)
    ∨ (b02 = true ∧ b12 = true ∧ b23 = true ∧ b24 = true)
    ∨ (b02 = true ∧ b12 = true ∧ b23 = true ∧ b34 = true)
    ∨ (b02 = true ∧ b12 = true ∧ b24 = true ∧ b34 = true)
    ∨ (b02 = true ∧ b13 = true ∧ b14 = true ∧ b23 = true)
    ∨ (b02 = true ∧ b13 = true ∧ b14 = true ∧ b24 = true)
    ∨ (b02 = true ∧ b13 = true ∧ b23 = true ∧ b24 = true)
    ∨ (b02 = true ∧ b13 = true ∧ b23 = true ∧ b34 = true)
    ∨ (b02 = true ∧ b13 = true ∧ b24 = true ∧ b34 = true)
    ∨ (b02 = true ∧ b14 = true ∧ b23 = true ∧ b24 = true)
    ∨ (b02 = true ∧ b14 = true ∧ b23 = true ∧ b34 = true)
    ∨ (b02 = true ∧ b14 = true ∧ b24 = true ∧ b34 = true)
    ∨ (b03 = true ∧ b04 = true ∧ b12 = true ∧ b13 = true)
    ∨ (b03 = true ∧ b04 = true ∧ b12 = true ∧ b14 = true)
    ∨ (b03 = true ∧ b04 = true ∧ b12 = true ∧ b23 = true)
    ∨ (b03 = true ∧ b04 = true ∧ b12 = true ∧ b24 = true)
    ∨ (b03 = true ∧ b04 = true ∧ b13 = true ∧ b23 = true)
    ∨ (b03 = true ∧ b04 = true ∧ b13 = true ∧ b24 = true)
    ∨ (b03 = true ∧ b04 = true ∧ b14 = true ∧ b23 = true)
    ∨ (b03 = true ∧ b04 = true ∧ b14 = true ∧ b24 = true)
    ∨ (b03 = true ∧ b12 = true ∧ b13 = true ∧ b14 = true)
    ∨ (b03 = true ∧ b12 = true ∧ b13 = true ∧ b24 = true)
    ∨ (b03 = true ∧ b12 = true ∧ b13 = true ∧ b34 = true)
    ∨ (b03 = true ∧ b12 = true ∧ b14 = true ∧ b23 = true)
    ∨ (b03 = true ∧ b12 = true ∧ b14 = true ∧ b34 = true)
    ∨ (b03 = true ∧ b12 = true ∧ b23 = true ∧ b24 = true)
    ∨ (b03 = true ∧ b12 = true ∧ b23 = true ∧ b34 = true)
    ∨ (b03 = true ∧ b12 = true ∧ b24 = true ∧ b34 = true)
    ∨ (b03 = true ∧ b13 = true ∧ b14 = true ∧ b23 = true)
    ∨ (b03 = true ∧ b13 = true ∧ b14 = true ∧ b24 = true)
    ∨ (b03 = true ∧ b13 = true ∧ b23 = true ∧ b24 = true)
    ∨ (b03 = true ∧ b13 = true ∧ b23 = true ∧ b34 = true)
    ∨ (b03 = true ∧ b13 = true ∧ b24 = true ∧ b34 = true)
    ∨ (b03 = true ∧ b14 = true ∧ b23 = true ∧ b24 = true)
    ∨ (b03 = true ∧ b14 = true ∧ b23 = true ∧ b34 = true)
    ∨ (b03 = true ∧ b14 = true ∧ b24 = true ∧ b34 = true)
    ∨ (b04 = true ∧ b12 = true ∧ b13 = true ∧ b14 = true)
    ∨ (b04 = true ∧ b12 = true ∧ b13 = true ∧ b24 = true)
    ∨ (b04 = true ∧ b12 = true ∧ b13 = true ∧ b34 = true)
    ∨ (b04 = true ∧ b12 = true ∧ b14 = true ∧ b23 = true)
    ∨ (b04 = true ∧ b12 = true ∧ b14 = true ∧ b34 = true)
    ∨ (b04 = true ∧ b12 = true ∧ b23 = true ∧ b24 = true)
    ∨ (b04 = true ∧ b12 = true ∧ b23 = true ∧ b34 = true)
    ∨ (b04 = true ∧ b12 = true ∧ b24 = true ∧ b34 = true)
    ∨ (b04 = true ∧ b13 = true ∧ b14 = true ∧ b23 = true)
    ∨ (b04 = true ∧ b13 = true ∧ b14 = true ∧ b24 = true)
    ∨ (b04 = true ∧ b13 = true ∧ b23 = true ∧ b24 = true)
    ∨ (b04 = true ∧ b13 = true ∧ b23 = true ∧ b34 = true)
    ∨ (b04 = true ∧ b13 = true ∧ b24 = true ∧ b34 = true)
    ∨ (b04 = true ∧ b14 = true ∧ b23 = true ∧ b24 = true)
    ∨ (b04 = true ∧ b14 = true ∧ b23 = true ∧ b34 = true)
    ∨ (b04 = true ∧ b14 = true ∧ b24 = true ∧ b34 = true))

private instance (L : LowBits) : Decidable (CycleCases L) := by cases L; dsimp [CycleCases]; infer_instance
private instance (L : LowBits) : Decidable (TotalCases L) := by cases L; dsimp [TotalCases]; infer_instance

theorem all_cases :
    ∀ b01 b02 b03 b04 b12 b13 b14 b23 b24 b34 : Bool,
      let L : LowBits := ⟨b01,b02,b03,b04,b12,b13,b14,b23,b24,b34⟩
      connectedBits L → CycleCases L ∧ TotalCases L := by decide

theorem low_cases (L : LowBits) (hc : connectedBits L) : CycleCases L ∧ TotalCases L := by
  cases L
  exact all_cases _ _ _ _ _ _ _ _ _ _ hc

end TriameterQ3PackingWindows

namespace TriameterQ3PackingWindows
open TriameterQ3Graph

theorem fin5_cases' (i : Fin 5) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
  have hi := i.isLt
  have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 := by omega
  rcases h with h|h|h|h|h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext h))))

theorem ordered_edge_mem (i j : Fin 5) (h : i.val < j.val) : (i,j) ∈ allEdges := by
  rcases fin5_cases' i with rfl|rfl|rfl|rfl|rfl <;>
    rcases fin5_cases' j with rfl|rfl|rfl|rfl|rfl <;>
    first | decide | omega

def bitsFrom (d : Fin 5 → Fin 5 → Nat) (k : Nat) : LowBits :=
  ⟨decide (d 0 1 ≤ 2*k+1), decide (d 0 2 ≤ 2*k+1), decide (d 0 3 ≤ 2*k+1),
   decide (d 0 4 ≤ 2*k+1), decide (d 1 2 ≤ 2*k+1), decide (d 1 3 ≤ 2*k+1),
   decide (d 1 4 ≤ 2*k+1), decide (d 2 3 ≤ 2*k+1), decide (d 2 4 ≤ 2*k+1),
   decide (d 3 4 ≤ 2*k+1)⟩

theorem bit_value (d : Fin 5 → Fin 5 → Nat) (k : Nat) (e : Fin 5 × Fin 5)
    (h : e ∈ allEdges) : (bitsFrom d k).get e = decide (d e.1 e.2 ≤ 2*k+1) := by
  simp only [allEdges,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with e0|e0|e0|e0|e0|e0|e0|e0|e0|e0 <;> subst e <;> rfl

theorem cut_crossing (side : Nat → Bool) (D : Nat) (hD : side 0 ≠ side D) :
    ∃ i, i < D ∧ side i ≠ side (i+1) := by
  by_cases H : ∃ i, i < D ∧ side i ≠ side (i+1)
  · exact H
  · have all (n : Nat) : n ≤ D → side 0 = side n := by
      induction n with
      | zero => intro _; rfl
      | succ n ih =>
        intro hn
        have e : side n = side (n+1) := Classical.byContradiction (fun h => H ⟨n,by omega,h⟩)
        exact (ih (by omega)).trans e
    exact (hD (all D (Nat.le_refl _))).elim

theorem bit_cut_exists : ∀ m : Fin 15, ∃ j : Fin 5, cutSide m 0 ≠ cutSide m j := by
  decide

theorem graph_center_cut_crossing {V : Type} {G : SimpleGraph V} (M : ShortestDistances G)
    {p k : Nat} (P : ExactPacking M k p) (f : Fin p → V) (hf : IsPacking M k f)
    (side : Fin p → Bool) (a b : Fin p) (hne : side a ≠ side b) :
    ∃ i j : Fin p, i.val < j.val ∧ side i ≠ side j ∧ M.dist (f i) (f j) ≤ 2*k+1 := by
  obtain ⟨s,h0,hD,_,hstep⟩ := geodesic_center_windows M P f hf a b
  have hc : side (s 0) ≠ side (s (M.dist (f a) (f b))) := by simpa only [h0,hD] using hne
  obtain ⟨t,ht,hcut⟩ := cut_crossing (fun t => side (s t)) (M.dist (f a) (f b)) hc
  have hd := hstep t ht
  by_cases hv : (s t).val < (s (t+1)).val
  · exact ⟨s t,s (t+1),hv,hcut,hd⟩
  · have hh : (s (t+1)).val < (s t).val := by
      have hn : (s t).val ≠ (s (t+1)).val := fun h => hcut (congrArg side (Fin.ext h))
      omega
    exact ⟨s (t+1),s t,hh,Ne.symm hcut,by simpa only [M.dist_symm (f (s (t+1))) (f (s t))] using hd⟩

theorem graph_connectedBits {V : Type} {G : SimpleGraph V} (M : ShortestDistances G)
    {k : Nat} (P : ExactPacking M k 5) (f : Fin 5 → V) (hf : IsPacking M k f) :
    connectedBits (bitsFrom (fun a b => M.dist (f a) (f b)) k) := by
  intro m
  obtain ⟨j,hj⟩ := bit_cut_exists m
  obtain ⟨a,b,hab,hcut,hd⟩ := graph_center_cut_crossing M P f hf (cutSide m) 0 j hj
  have hm := ordered_edge_mem a b hab
  change (allEdges.any _) = true
  apply List.any_eq_true.mpr
  refine ⟨(a,b),hm,?_⟩
  rw [Bool.and_eq_true]
  refine ⟨?_,?_⟩
  · cases ha : cutSide m a <;> cases hb : cutSide m b <;> simp_all
  · rw [bit_value _ _ _ hm]
    exact decide_eq_true hd

end TriameterQ3PackingWindows

namespace TriameterQ3PackingWindows
open TriameterQ3Graph
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 10000
set_option maxSynthPendingDepth 1000

/-- Actual graph distance facet after retaining all five packed centers. -/
theorem graph_five_cycle_perimeter {V : Type} {G : SimpleGraph V}
    (M : ShortestDistances G) (k : Nat) (P : ExactPacking M k 5)
    (f : Fin 5 → V) (hf : IsPacking M k f) :
    M.dist (f 0) (f 1) + M.dist (f 1) (f 2) + M.dist (f 2) (f 3) + M.dist (f 3) (f 4) + M.dist (f 0) (f 4) ≤ 5*k+16*(k+1) := by
  let d (i j : Fin 5) := M.dist (f i) (f j)
  change d 0 1 + d 1 2 + d 2 3 + d 3 4 + d 0 4 ≤ _
  have bound (i j : Fin 5) : d i j ≤ 5*k+4 := by
    have h := diameter_le_of_packing M P (f i) (f j)
    change d i j ≤ _ at h
    omega
  have cases0 := low_cases (bitsFrom d k) (graph_connectedBits M P f hf)
  have H01 := bound 0 1
  have H12 := bound 1 2
  have H23 := bound 2 3
  have H34 := bound 3 4
  have H04 := bound 0 4
  have cs := cases0.1
  dsimp only [CycleCases,bitsFrom] at cs
  rcases cs with hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc
  · rcases hc with ⟨h01, h12⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    omega
  · rcases hc with ⟨h01, h23⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    omega
  · rcases hc with ⟨h01, h34⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    omega
  · rcases hc with ⟨h01, h04⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    omega
  · rcases hc with ⟨h12, h23⟩
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    omega
  · rcases hc with ⟨h12, h34⟩
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    omega
  · rcases hc with ⟨h12, h04⟩
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    omega
  · rcases hc with ⟨h23, h34⟩
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    omega
  · rcases hc with ⟨h23, h04⟩
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    omega
  · rcases hc with ⟨h34, h04⟩
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    omega
  · rcases hc with ⟨h02, h24, h01⟩
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have hTri : d 0 4 ≤ d 0 2 + d 2 4 := by
      have hh := M.dist_triangle (f 0) (f 2) (f 4)
      exact hh
    omega
  · rcases hc with ⟨h02, h24, h12⟩
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have hTri : d 0 4 ≤ d 0 2 + d 2 4 := by
      have hh := M.dist_triangle (f 0) (f 2) (f 4)
      exact hh
    omega
  · rcases hc with ⟨h02, h24, h23⟩
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have hTri : d 0 4 ≤ d 0 2 + d 2 4 := by
      have hh := M.dist_triangle (f 0) (f 2) (f 4)
      exact hh
    omega
  · rcases hc with ⟨h02, h24, h34⟩
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hTri : d 0 4 ≤ d 0 2 + d 2 4 := by
      have hh := M.dist_triangle (f 0) (f 2) (f 4)
      exact hh
    omega
  · rcases hc with ⟨h03, h13, h12⟩
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have hTri : d 0 1 ≤ d 0 3 + d 1 3 := by
      have hh := M.dist_triangle (f 0) (f 3) (f 1)
      rw [M.dist_symm (f 3) (f 1)] at hh
      exact hh
    omega
  · rcases hc with ⟨h03, h13, h23⟩
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have hTri : d 0 1 ≤ d 0 3 + d 1 3 := by
      have hh := M.dist_triangle (f 0) (f 3) (f 1)
      rw [M.dist_symm (f 3) (f 1)] at hh
      exact hh
    omega
  · rcases hc with ⟨h03, h13, h34⟩
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hTri : d 0 1 ≤ d 0 3 + d 1 3 := by
      have hh := M.dist_triangle (f 0) (f 3) (f 1)
      rw [M.dist_symm (f 3) (f 1)] at hh
      exact hh
    omega
  · rcases hc with ⟨h03, h13, h04⟩
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have hTri : d 0 1 ≤ d 0 3 + d 1 3 := by
      have hh := M.dist_triangle (f 0) (f 3) (f 1)
      rw [M.dist_symm (f 3) (f 1)] at hh
      exact hh
    omega
  · rcases hc with ⟨h14, h24, h01⟩
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have hTri : d 1 2 ≤ d 1 4 + d 2 4 := by
      have hh := M.dist_triangle (f 1) (f 4) (f 2)
      rw [M.dist_symm (f 4) (f 2)] at hh
      exact hh
    omega
  · rcases hc with ⟨h14, h24, h23⟩
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have hTri : d 1 2 ≤ d 1 4 + d 2 4 := by
      have hh := M.dist_triangle (f 1) (f 4) (f 2)
      rw [M.dist_symm (f 4) (f 2)] at hh
      exact hh
    omega
  · rcases hc with ⟨h14, h24, h34⟩
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hTri : d 1 2 ≤ d 1 4 + d 2 4 := by
      have hh := M.dist_triangle (f 1) (f 4) (f 2)
      rw [M.dist_symm (f 4) (f 2)] at hh
      exact hh
    omega
  · rcases hc with ⟨h14, h24, h04⟩
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have hTri : d 1 2 ≤ d 1 4 + d 2 4 := by
      have hh := M.dist_triangle (f 1) (f 4) (f 2)
      rw [M.dist_symm (f 4) (f 2)] at hh
      exact hh
    omega
  · rcases hc with ⟨h02, h03, h01⟩
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have hTri : d 2 3 ≤ d 0 2 + d 0 3 := by
      have hh := M.dist_triangle (f 2) (f 0) (f 3)
      rw [M.dist_symm (f 2) (f 0)] at hh
      exact hh
    omega
  · rcases hc with ⟨h02, h03, h12⟩
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have hTri : d 2 3 ≤ d 0 2 + d 0 3 := by
      have hh := M.dist_triangle (f 2) (f 0) (f 3)
      rw [M.dist_symm (f 2) (f 0)] at hh
      exact hh
    omega
  · rcases hc with ⟨h02, h03, h34⟩
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hTri : d 2 3 ≤ d 0 2 + d 0 3 := by
      have hh := M.dist_triangle (f 2) (f 0) (f 3)
      rw [M.dist_symm (f 2) (f 0)] at hh
      exact hh
    omega
  · rcases hc with ⟨h02, h03, h04⟩
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have hTri : d 2 3 ≤ d 0 2 + d 0 3 := by
      have hh := M.dist_triangle (f 2) (f 0) (f 3)
      rw [M.dist_symm (f 2) (f 0)] at hh
      exact hh
    omega
  · rcases hc with ⟨h13, h14, h01⟩
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have hTri : d 3 4 ≤ d 1 3 + d 1 4 := by
      have hh := M.dist_triangle (f 3) (f 1) (f 4)
      rw [M.dist_symm (f 3) (f 1)] at hh
      exact hh
    omega
  · rcases hc with ⟨h13, h14, h12⟩
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have hTri : d 3 4 ≤ d 1 3 + d 1 4 := by
      have hh := M.dist_triangle (f 3) (f 1) (f 4)
      rw [M.dist_symm (f 3) (f 1)] at hh
      exact hh
    omega
  · rcases hc with ⟨h13, h14, h23⟩
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have hTri : d 3 4 ≤ d 1 3 + d 1 4 := by
      have hh := M.dist_triangle (f 3) (f 1) (f 4)
      rw [M.dist_symm (f 3) (f 1)] at hh
      exact hh
    omega
  · rcases hc with ⟨h13, h14, h04⟩
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have hTri : d 3 4 ≤ d 1 3 + d 1 4 := by
      have hh := M.dist_triangle (f 3) (f 1) (f 4)
      rw [M.dist_symm (f 3) (f 1)] at hh
      exact hh
    omega
  · rcases hc with ⟨h03, h13, h14, h24⟩
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    let σ : Fin 5 → Fin 5 := fun i => if i = 0 then 0 else if i = 1 then 3 else if i = 2 then 1 else if i = 3 then 4 else 2
    have hInj : ∀ i j : Fin 5, i ≠ j → σ i ≠ σ j := by dsimp [σ]; decide
    have hPack : IsPacking M k (fun i => f (σ i)) := fun i j he => hf _ _ (hInj i j he)
    have low0 : M.dist (f (σ 0)) (f (σ 1)) ≤ 2*k+1 := by
      change M.dist (f 0) (f 3) ≤ _
      exact Hlow03
    have low1 : M.dist (f (σ 1)) (f (σ 2)) ≤ 2*k+1 := by
      change M.dist (f 3) (f 1) ≤ _
      rw [M.dist_symm (f 3) (f 1)]
      exact Hlow13
    have low2 : M.dist (f (σ 2)) (f (σ 3)) ≤ 2*k+1 := by
      change M.dist (f 1) (f 4) ≤ _
      exact Hlow14
    have low3 : M.dist (f (σ 3)) (f (σ 4)) ≤ 2*k+1 := by
      change M.dist (f 4) (f 2) ≤ _
      rw [M.dist_symm (f 4) (f 2)]
      exact Hlow24
    have hP := complementary_pentagon_bound M k P (fun i => f (σ i)) hPack low0 low1 low2 low3
    change d 0 1 + d 0 4 + d 3 4 + d 3 2 + d 1 2 ≤ _ at hP
    rw [show d 3 2 = d 2 3 from M.dist_symm _ _] at hP
    omega
  · rcases hc with ⟨h02, h24, h14, h13⟩
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    let σ : Fin 5 → Fin 5 := fun i => if i = 0 then 0 else if i = 1 then 2 else if i = 2 then 4 else if i = 3 then 1 else 3
    have hInj : ∀ i j : Fin 5, i ≠ j → σ i ≠ σ j := by dsimp [σ]; decide
    have hPack : IsPacking M k (fun i => f (σ i)) := fun i j he => hf _ _ (hInj i j he)
    have low0 : M.dist (f (σ 0)) (f (σ 1)) ≤ 2*k+1 := by
      change M.dist (f 0) (f 2) ≤ _
      exact Hlow02
    have low1 : M.dist (f (σ 1)) (f (σ 2)) ≤ 2*k+1 := by
      change M.dist (f 2) (f 4) ≤ _
      exact Hlow24
    have low2 : M.dist (f (σ 2)) (f (σ 3)) ≤ 2*k+1 := by
      change M.dist (f 4) (f 1) ≤ _
      rw [M.dist_symm (f 4) (f 1)]
      exact Hlow14
    have low3 : M.dist (f (σ 3)) (f (σ 4)) ≤ 2*k+1 := by
      change M.dist (f 1) (f 3) ≤ _
      exact Hlow13
    have hP := complementary_pentagon_bound M k P (fun i => f (σ i)) hPack low0 low1 low2 low3
    change d 0 4 + d 0 1 + d 2 1 + d 2 3 + d 4 3 ≤ _ at hP
    rw [show d 2 1 = d 1 2 from M.dist_symm _ _] at hP
    rw [show d 4 3 = d 3 4 from M.dist_symm _ _] at hP
    omega
  · rcases hc with ⟨h14, h24, h02, h03⟩
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    let σ : Fin 5 → Fin 5 := fun i => if i = 0 then 1 else if i = 1 then 4 else if i = 2 then 2 else if i = 3 then 0 else 3
    have hInj : ∀ i j : Fin 5, i ≠ j → σ i ≠ σ j := by dsimp [σ]; decide
    have hPack : IsPacking M k (fun i => f (σ i)) := fun i j he => hf _ _ (hInj i j he)
    have low0 : M.dist (f (σ 0)) (f (σ 1)) ≤ 2*k+1 := by
      change M.dist (f 1) (f 4) ≤ _
      exact Hlow14
    have low1 : M.dist (f (σ 1)) (f (σ 2)) ≤ 2*k+1 := by
      change M.dist (f 4) (f 2) ≤ _
      rw [M.dist_symm (f 4) (f 2)]
      exact Hlow24
    have low2 : M.dist (f (σ 2)) (f (σ 3)) ≤ 2*k+1 := by
      change M.dist (f 2) (f 0) ≤ _
      rw [M.dist_symm (f 2) (f 0)]
      exact Hlow02
    have low3 : M.dist (f (σ 3)) (f (σ 4)) ≤ 2*k+1 := by
      change M.dist (f 0) (f 3) ≤ _
      exact Hlow03
    have hP := complementary_pentagon_bound M k P (fun i => f (σ i)) hPack low0 low1 low2 low3
    change d 1 2 + d 1 0 + d 4 0 + d 4 3 + d 2 3 ≤ _ at hP
    rw [show d 1 0 = d 0 1 from M.dist_symm _ _] at hP
    rw [show d 4 0 = d 0 4 from M.dist_symm _ _] at hP
    rw [show d 4 3 = d 3 4 from M.dist_symm _ _] at hP
    omega
  · rcases hc with ⟨h13, h03, h02, h24⟩
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    let σ : Fin 5 → Fin 5 := fun i => if i = 0 then 1 else if i = 1 then 3 else if i = 2 then 0 else if i = 3 then 2 else 4
    have hInj : ∀ i j : Fin 5, i ≠ j → σ i ≠ σ j := by dsimp [σ]; decide
    have hPack : IsPacking M k (fun i => f (σ i)) := fun i j he => hf _ _ (hInj i j he)
    have low0 : M.dist (f (σ 0)) (f (σ 1)) ≤ 2*k+1 := by
      change M.dist (f 1) (f 3) ≤ _
      exact Hlow13
    have low1 : M.dist (f (σ 1)) (f (σ 2)) ≤ 2*k+1 := by
      change M.dist (f 3) (f 0) ≤ _
      rw [M.dist_symm (f 3) (f 0)]
      exact Hlow03
    have low2 : M.dist (f (σ 2)) (f (σ 3)) ≤ 2*k+1 := by
      change M.dist (f 0) (f 2) ≤ _
      exact Hlow02
    have low3 : M.dist (f (σ 3)) (f (σ 4)) ≤ 2*k+1 := by
      change M.dist (f 2) (f 4) ≤ _
      exact Hlow24
    have hP := complementary_pentagon_bound M k P (fun i => f (σ i)) hPack low0 low1 low2 low3
    change d 1 0 + d 1 2 + d 3 2 + d 3 4 + d 0 4 ≤ _ at hP
    rw [show d 1 0 = d 0 1 from M.dist_symm _ _] at hP
    rw [show d 3 2 = d 2 3 from M.dist_symm _ _] at hP
    omega
  · rcases hc with ⟨h02, h03, h13, h14⟩
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    let σ : Fin 5 → Fin 5 := fun i => if i = 0 then 2 else if i = 1 then 0 else if i = 2 then 3 else if i = 3 then 1 else 4
    have hInj : ∀ i j : Fin 5, i ≠ j → σ i ≠ σ j := by dsimp [σ]; decide
    have hPack : IsPacking M k (fun i => f (σ i)) := fun i j he => hf _ _ (hInj i j he)
    have low0 : M.dist (f (σ 0)) (f (σ 1)) ≤ 2*k+1 := by
      change M.dist (f 2) (f 0) ≤ _
      rw [M.dist_symm (f 2) (f 0)]
      exact Hlow02
    have low1 : M.dist (f (σ 1)) (f (σ 2)) ≤ 2*k+1 := by
      change M.dist (f 0) (f 3) ≤ _
      exact Hlow03
    have low2 : M.dist (f (σ 2)) (f (σ 3)) ≤ 2*k+1 := by
      change M.dist (f 3) (f 1) ≤ _
      rw [M.dist_symm (f 3) (f 1)]
      exact Hlow13
    have low3 : M.dist (f (σ 3)) (f (σ 4)) ≤ 2*k+1 := by
      change M.dist (f 1) (f 4) ≤ _
      exact Hlow14
    have hP := complementary_pentagon_bound M k P (fun i => f (σ i)) hPack low0 low1 low2 low3
    change d 2 3 + d 2 1 + d 0 1 + d 0 4 + d 3 4 ≤ _ at hP
    rw [show d 2 1 = d 1 2 from M.dist_symm _ _] at hP
    omega

/-- Actual graph distance facet after retaining all five packed centers. -/
theorem graph_five_total_perimeter {V : Type} {G : SimpleGraph V}
    (M : ShortestDistances G) (k : Nat) (P : ExactPacking M k 5)
    (f : Fin 5 → V) (hf : IsPacking M k f) :
    M.dist (f 0) (f 1) + M.dist (f 0) (f 2) + M.dist (f 0) (f 3) + M.dist (f 0) (f 4) + M.dist (f 1) (f 2) + M.dist (f 1) (f 3) + M.dist (f 1) (f 4) + M.dist (f 2) (f 3) + M.dist (f 2) (f 4) + M.dist (f 3) (f 4) ≤ 10*k+24*(k+1) := by
  let d (i j : Fin 5) := M.dist (f i) (f j)
  change d 0 1 + d 0 2 + d 0 3 + d 0 4 + d 1 2 + d 1 3 + d 1 4 + d 2 3 + d 2 4 + d 3 4 ≤ _
  have bound (i j : Fin 5) : d i j ≤ 5*k+4 := by
    have h := diameter_le_of_packing M P (f i) (f j)
    change d i j ≤ _ at h
    omega
  have cases0 := low_cases (bitsFrom d k) (graph_connectedBits M P f hf)
  have H01 := bound 0 1
  have H02 := bound 0 2
  have H03 := bound 0 3
  have H04 := bound 0 4
  have H12 := bound 1 2
  have H13 := bound 1 3
  have H14 := bound 1 4
  have H23 := bound 2 3
  have H24 := bound 2 4
  have H34 := bound 3 4
  have tri (i j l : Fin 5) : d i j+d i l+d j l ≤ 11*k+8 := by
    have h := triple_perimeter_packing_bound M P (f i) (f j) (f l)
    change d i j+d i l+d j l + 2 ≤ _ at h
    omega
  have cs := cases0.2
  dsimp only [TotalCases,bitsFrom] at cs
  rcases cs with hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc
  · rcases hc with ⟨h01, h02, h03, h04⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have hh := tri 1 2 3
    omega
  · rcases hc with ⟨h01, h02, h03, h14⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have hh := tri 1 2 3
    omega
  · rcases hc with ⟨h01, h02, h03, h24⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have hh := tri 1 2 3
    omega
  · rcases hc with ⟨h01, h02, h03, h34⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hh := tri 1 2 3
    omega
  · rcases hc with ⟨h01, h02, h04, h13⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have hh := tri 1 2 4
    omega
  · rcases hc with ⟨h01, h02, h04, h23⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have hh := tri 1 2 4
    omega
  · rcases hc with ⟨h01, h02, h04, h34⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hh := tri 1 2 3
    omega
  · rcases hc with ⟨h01, h02, h13, h14⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have hh := tri 0 3 4
    omega
  · rcases hc with ⟨h01, h02, h13, h24⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have hh := tri 0 3 4
    omega
  · rcases hc with ⟨h01, h02, h13, h34⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hh := tri 1 2 4
    omega
  · rcases hc with ⟨h01, h02, h14, h23⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have hh := tri 0 3 4
    omega
  · rcases hc with ⟨h01, h02, h14, h34⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hh := tri 1 2 3
    omega
  · rcases hc with ⟨h01, h02, h23, h24⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have hh := tri 0 3 4
    omega
  · rcases hc with ⟨h01, h02, h23, h34⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hh := tri 1 2 4
    omega
  · rcases hc with ⟨h01, h02, h24, h34⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hh := tri 1 2 3
    omega
  · rcases hc with ⟨h01, h03, h04, h12⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have hh := tri 1 3 4
    omega
  · rcases hc with ⟨h01, h03, h04, h23⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have hh := tri 1 2 4
    omega
  · rcases hc with ⟨h01, h03, h04, h24⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have hh := tri 1 2 3
    omega
  · rcases hc with ⟨h01, h03, h12, h14⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have hh := tri 0 2 4
    omega
  · rcases hc with ⟨h01, h03, h12, h24⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have hh := tri 1 3 4
    omega
  · rcases hc with ⟨h01, h03, h12, h34⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hh := tri 0 2 4
    omega
  · rcases hc with ⟨h01, h03, h14, h23⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have hh := tri 0 2 4
    omega
  · rcases hc with ⟨h01, h03, h14, h24⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have hh := tri 1 2 3
    omega
  · rcases hc with ⟨h01, h03, h23, h24⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have hh := tri 1 3 4
    omega
  · rcases hc with ⟨h01, h03, h23, h34⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hh := tri 0 2 4
    omega
  · rcases hc with ⟨h01, h03, h24, h34⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hh := tri 1 2 3
    omega
  · rcases hc with ⟨h01, h04, h12, h13⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have hh := tri 0 2 3
    omega
  · rcases hc with ⟨h01, h04, h12, h23⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have hh := tri 1 3 4
    omega
  · rcases hc with ⟨h01, h04, h12, h34⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hh := tri 0 2 3
    omega
  · rcases hc with ⟨h01, h04, h13, h23⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have hh := tri 1 2 4
    omega
  · rcases hc with ⟨h01, h04, h13, h24⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have hh := tri 0 2 3
    omega
  · rcases hc with ⟨h01, h04, h23, h24⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have hh := tri 1 3 4
    omega
  · rcases hc with ⟨h01, h04, h23, h34⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hh := tri 1 2 4
    omega
  · rcases hc with ⟨h01, h04, h24, h34⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hh := tri 0 2 3
    omega
  · rcases hc with ⟨h01, h12, h13, h14⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have hh := tri 0 2 3
    omega
  · rcases hc with ⟨h01, h12, h13, h24⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have hh := tri 0 2 3
    omega
  · rcases hc with ⟨h01, h12, h13, h34⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hh := tri 0 2 3
    omega
  · rcases hc with ⟨h01, h12, h14, h23⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have hh := tri 0 2 4
    omega
  · rcases hc with ⟨h01, h12, h14, h34⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hh := tri 0 2 3
    omega
  · rcases hc with ⟨h01, h12, h23, h24⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have hh := tri 0 3 4
    omega
  · rcases hc with ⟨h01, h12, h23, h34⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hh := tri 0 2 4
    omega
  · rcases hc with ⟨h01, h12, h24, h34⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hh := tri 0 2 3
    omega
  · rcases hc with ⟨h01, h13, h14, h23⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have hh := tri 0 2 4
    omega
  · rcases hc with ⟨h01, h13, h14, h24⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have hh := tri 0 2 3
    omega
  · rcases hc with ⟨h01, h13, h23, h24⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have hh := tri 0 3 4
    omega
  · rcases hc with ⟨h01, h13, h23, h34⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hh := tri 0 2 4
    omega
  · rcases hc with ⟨h01, h13, h24, h34⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hh := tri 0 2 3
    omega
  · rcases hc with ⟨h01, h14, h23, h24⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have hh := tri 0 3 4
    omega
  · rcases hc with ⟨h01, h14, h23, h34⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hh := tri 0 2 4
    omega
  · rcases hc with ⟨h01, h14, h24, h34⟩
    have Hlow01 : d 0 1 ≤ 2*k+1 := of_decide_eq_true h01
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hh := tri 0 2 3
    omega
  · rcases hc with ⟨h02, h03, h04, h12⟩
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have hh := tri 1 3 4
    omega
  · rcases hc with ⟨h02, h03, h04, h13⟩
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have hh := tri 1 2 4
    omega
  · rcases hc with ⟨h02, h03, h04, h14⟩
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have hh := tri 1 2 3
    omega
  · rcases hc with ⟨h02, h03, h12, h14⟩
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have hh := tri 2 3 4
    omega
  · rcases hc with ⟨h02, h03, h12, h24⟩
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have hh := tri 0 1 4
    omega
  · rcases hc with ⟨h02, h03, h12, h34⟩
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hh := tri 0 1 4
    omega
  · rcases hc with ⟨h02, h03, h13, h14⟩
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have hh := tri 2 3 4
    omega
  · rcases hc with ⟨h02, h03, h13, h24⟩
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have hh := tri 0 1 4
    omega
  · rcases hc with ⟨h02, h03, h13, h34⟩
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hh := tri 0 1 4
    omega
  · rcases hc with ⟨h02, h03, h14, h24⟩
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have hh := tri 1 2 3
    omega
  · rcases hc with ⟨h02, h03, h14, h34⟩
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hh := tri 1 2 3
    omega
  · rcases hc with ⟨h02, h04, h12, h13⟩
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have hh := tri 2 3 4
    omega
  · rcases hc with ⟨h02, h04, h12, h23⟩
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have hh := tri 0 1 3
    omega
  · rcases hc with ⟨h02, h04, h12, h34⟩
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hh := tri 0 1 3
    omega
  · rcases hc with ⟨h02, h04, h13, h14⟩
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have hh := tri 2 3 4
    omega
  · rcases hc with ⟨h02, h04, h13, h23⟩
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have hh := tri 1 2 4
    omega
  · rcases hc with ⟨h02, h04, h13, h34⟩
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hh := tri 1 2 4
    omega
  · rcases hc with ⟨h02, h04, h14, h23⟩
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have hh := tri 0 1 3
    omega
  · rcases hc with ⟨h02, h04, h14, h34⟩
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hh := tri 0 1 3
    omega
  · rcases hc with ⟨h02, h12, h13, h14⟩
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have hh := tri 0 3 4
    omega
  · rcases hc with ⟨h02, h12, h13, h24⟩
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have hh := tri 0 1 4
    omega
  · rcases hc with ⟨h02, h12, h13, h34⟩
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hh := tri 0 1 4
    omega
  · rcases hc with ⟨h02, h12, h14, h23⟩
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have hh := tri 0 1 3
    omega
  · rcases hc with ⟨h02, h12, h14, h34⟩
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hh := tri 0 1 3
    omega
  · rcases hc with ⟨h02, h12, h23, h24⟩
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have hh := tri 0 1 3
    omega
  · rcases hc with ⟨h02, h12, h23, h34⟩
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hh := tri 0 1 3
    omega
  · rcases hc with ⟨h02, h12, h24, h34⟩
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hh := tri 0 1 3
    omega
  · rcases hc with ⟨h02, h13, h14, h23⟩
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have hh := tri 0 3 4
    omega
  · rcases hc with ⟨h02, h13, h14, h24⟩
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have hh := tri 0 3 4
    omega
  · rcases hc with ⟨h02, h13, h23, h24⟩
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have hh := tri 0 1 4
    omega
  · rcases hc with ⟨h02, h13, h23, h34⟩
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hh := tri 0 1 4
    omega
  · rcases hc with ⟨h02, h13, h24, h34⟩
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hh := tri 0 1 4
    omega
  · rcases hc with ⟨h02, h14, h23, h24⟩
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have hh := tri 0 1 3
    omega
  · rcases hc with ⟨h02, h14, h23, h34⟩
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hh := tri 0 1 3
    omega
  · rcases hc with ⟨h02, h14, h24, h34⟩
    have Hlow02 : d 0 2 ≤ 2*k+1 := of_decide_eq_true h02
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hh := tri 0 1 3
    omega
  · rcases hc with ⟨h03, h04, h12, h13⟩
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have hh := tri 2 3 4
    omega
  · rcases hc with ⟨h03, h04, h12, h14⟩
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have hh := tri 2 3 4
    omega
  · rcases hc with ⟨h03, h04, h12, h23⟩
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have hh := tri 1 3 4
    omega
  · rcases hc with ⟨h03, h04, h12, h24⟩
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have hh := tri 1 3 4
    omega
  · rcases hc with ⟨h03, h04, h13, h23⟩
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have hh := tri 0 1 2
    omega
  · rcases hc with ⟨h03, h04, h13, h24⟩
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have hh := tri 0 1 2
    omega
  · rcases hc with ⟨h03, h04, h14, h23⟩
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have hh := tri 0 1 2
    omega
  · rcases hc with ⟨h03, h04, h14, h24⟩
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have hh := tri 0 1 2
    omega
  · rcases hc with ⟨h03, h12, h13, h14⟩
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have hh := tri 0 2 4
    omega
  · rcases hc with ⟨h03, h12, h13, h24⟩
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have hh := tri 0 1 4
    omega
  · rcases hc with ⟨h03, h12, h13, h34⟩
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hh := tri 0 1 4
    omega
  · rcases hc with ⟨h03, h12, h14, h23⟩
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have hh := tri 0 2 4
    omega
  · rcases hc with ⟨h03, h12, h14, h34⟩
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hh := tri 0 2 4
    omega
  · rcases hc with ⟨h03, h12, h23, h24⟩
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have hh := tri 0 1 4
    omega
  · rcases hc with ⟨h03, h12, h23, h34⟩
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hh := tri 0 1 4
    omega
  · rcases hc with ⟨h03, h12, h24, h34⟩
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hh := tri 0 1 4
    omega
  · rcases hc with ⟨h03, h13, h14, h23⟩
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have hh := tri 0 1 2
    omega
  · rcases hc with ⟨h03, h13, h14, h24⟩
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have hh := tri 0 1 2
    omega
  · rcases hc with ⟨h03, h13, h23, h24⟩
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have hh := tri 0 1 2
    omega
  · rcases hc with ⟨h03, h13, h23, h34⟩
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hh := tri 0 1 2
    omega
  · rcases hc with ⟨h03, h13, h24, h34⟩
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hh := tri 0 1 2
    omega
  · rcases hc with ⟨h03, h14, h23, h24⟩
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have hh := tri 0 1 2
    omega
  · rcases hc with ⟨h03, h14, h23, h34⟩
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hh := tri 0 1 2
    omega
  · rcases hc with ⟨h03, h14, h24, h34⟩
    have Hlow03 : d 0 3 ≤ 2*k+1 := of_decide_eq_true h03
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hh := tri 0 1 2
    omega
  · rcases hc with ⟨h04, h12, h13, h14⟩
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have hh := tri 0 2 3
    omega
  · rcases hc with ⟨h04, h12, h13, h24⟩
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have hh := tri 0 2 3
    omega
  · rcases hc with ⟨h04, h12, h13, h34⟩
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hh := tri 0 2 3
    omega
  · rcases hc with ⟨h04, h12, h14, h23⟩
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have hh := tri 0 1 3
    omega
  · rcases hc with ⟨h04, h12, h14, h34⟩
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hh := tri 0 1 3
    omega
  · rcases hc with ⟨h04, h12, h23, h24⟩
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have hh := tri 0 1 3
    omega
  · rcases hc with ⟨h04, h12, h23, h34⟩
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hh := tri 0 1 3
    omega
  · rcases hc with ⟨h04, h12, h24, h34⟩
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have Hlow12 : d 1 2 ≤ 2*k+1 := of_decide_eq_true h12
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hh := tri 0 1 3
    omega
  · rcases hc with ⟨h04, h13, h14, h23⟩
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have hh := tri 0 1 2
    omega
  · rcases hc with ⟨h04, h13, h14, h24⟩
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have hh := tri 0 1 2
    omega
  · rcases hc with ⟨h04, h13, h23, h24⟩
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have hh := tri 0 1 2
    omega
  · rcases hc with ⟨h04, h13, h23, h34⟩
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hh := tri 0 1 2
    omega
  · rcases hc with ⟨h04, h13, h24, h34⟩
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have Hlow13 : d 1 3 ≤ 2*k+1 := of_decide_eq_true h13
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hh := tri 0 1 2
    omega
  · rcases hc with ⟨h04, h14, h23, h24⟩
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have hh := tri 0 1 2
    omega
  · rcases hc with ⟨h04, h14, h23, h34⟩
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have Hlow23 : d 2 3 ≤ 2*k+1 := of_decide_eq_true h23
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hh := tri 0 1 2
    omega
  · rcases hc with ⟨h04, h14, h24, h34⟩
    have Hlow04 : d 0 4 ≤ 2*k+1 := of_decide_eq_true h04
    have Hlow14 : d 1 4 ≤ 2*k+1 := of_decide_eq_true h14
    have Hlow24 : d 2 4 ≤ 2*k+1 := of_decide_eq_true h24
    have Hlow34 : d 3 4 ≤ 2*k+1 := of_decide_eq_true h34
    have hh := tri 0 1 2
    omega


end TriameterQ3PackingWindows

/-! Exact bridge from the graph-side five facets to the weighted objective.
The one polyhedral theorem needed for complete closure is exposed as a
Prop, not asserted as an axiom: `FiveCutHullAssertion`. -/
namespace TriameterQ3PackingWindows
open TriameterQ3Graph TriameterQ3SmallPacking

def clipped {V : Type} {G : SimpleGraph V} (M : ShortestDistances G) (k : Nat)
    {r : Nat} (f : Fin r → V) (i j : Fin r) : Nat := M.dist (f i) (f j)-k

def cycleSum5 (x : Fin 5 → Fin 5 → Nat) (f : Fin 5 → Fin 5) : Nat :=
  x (f 0) (f 1)+x (f 1) (f 2)+x (f 2) (f 3)+x (f 3) (f 4)+x (f 0) (f 4)

def fullSum5 (x : Fin 5 → Fin 5 → Nat) : Nat :=
  x 0 1+x 0 2+x 0 3+x 0 4+x 1 2+x 1 3+x 1 4+x 2 3+x 2 4+x 3 4

/-- The homogenized nonnegative five-point bipartite subgraph facets.
The scale R in the graph application is 4(k+1). -/
structure FiveFacets (R : Nat) (x : Fin 5 → Fin 5 → Nat) : Prop where
  symmetric : ∀ i j, x i j = x j i
  diagonal : ∀ i, x i i = 0
  box : ∀ i j, x i j ≤ R
  triangle : ∀ i j l, x i j+x i l+x j l ≤ 2*R
  cycle : ∀ g : Fin 5 → Fin 5, Function.Injective g → cycleSum5 x g ≤ 4*R
  total : fullSum5 x ≤ 6*R

theorem graph_five_facets {V : Type} {G : SimpleGraph V} (M : ShortestDistances G)
    (k : Nat) (P : ExactPacking M k 5) (f : Fin 5 → V) (hf : IsPacking M k f) :
    FiveFacets (4*(k+1)) (clipped M k f) := by
  have hBox (i j : Fin 5) : clipped M k f i j ≤ 4*(k+1) := by
    have h := diameter_le_of_packing M P (f i) (f j)
    unfold clipped
    omega
  have hDiag (i : Fin 5) : clipped M k f i i = 0 := by simp [clipped,M.dist_self]
  have hSym (i j : Fin 5) : clipped M k f i j = clipped M k f j i := by
    simp [clipped,M.dist_symm (f i) (f j)]
  refine ⟨hSym,hDiag,hBox,?_,?_,?_⟩
  · intro i j l
    by_cases hij : i = j
    · subst j
      have h := hBox i l
      rw [hDiag]
      omega
    · by_cases hil : i = l
      · subst l
        have h := hBox i j
        rw [hDiag,hSym j i]
        omega
      · by_cases hjl : j = l
        · subst l
          have h := hBox i j
          rw [hDiag]
          omega
        · have H0 := hf i j hij
          have H1 := hf i l hil
          have H2 := hf j l hjl
          have H := triple_perimeter_packing_bound M P (f i) (f j) (f l)
          unfold clipped
          omega
  · intro g hg
    have pack : IsPacking M k (fun i => f (g i)) := fun i j ne => hf _ _ (fun h => ne (hg h))
    have H := graph_five_cycle_perimeter M k P (fun i => f (g i)) pack
    have h01 := pack 0 1 (by decide)
    have h12 := pack 1 2 (by decide)
    have h23 := pack 2 3 (by decide)
    have h34 := pack 3 4 (by decide)
    have h04 := pack 0 4 (by decide)
    dsimp [cycleSum5,clipped] at *
    omega
  · have H := graph_five_total_perimeter M k P f hf
    have h01 := hf 0 1 (by decide)
    have h02 := hf 0 2 (by decide)
    have h03 := hf 0 3 (by decide)
    have h04 := hf 0 4 (by decide)
    have h12 := hf 1 2 (by decide)
    have h13 := hf 1 3 (by decide)
    have h14 := hf 1 4 (by decide)
    have h23 := hf 2 3 (by decide)
    have h24 := hf 2 4 (by decide)
    have h34 := hf 3 4 (by decide)
    unfold fullSum5 clipped
    omega

def cutBits (s : Fin 32) (i : Fin 5) : Bool := s.val.testBit i.val

def gate (s : Fin 32) (i j : Fin 5) (a : Nat) : Nat :=
  if cutBits s i = cutBits s j then 0 else a

/-- Denominator-cleared, verifiable domination by a convex combination of
cuts. At most 32 cuts are used because cut labels may include complements. -/
structure CutCertificate5 (R : Nat) (x : Fin 5 → Fin 5 → Nat) where
  denominator : Nat
  atom : Fin 32 → Nat
  positive : 0 < denominator
  budget : vsum 32 atom ≤ denominator*R
  marginals : ∀ i j, denominator*x i j ≤ vsum 32 (fun s => gate s i j (atom s))

/-- The finite rational consequence of Galli–Letchford, Section 2 / Table 1.
This named hypothesis is deliberately NOT admitted or asserted. -/
def FiveCutHullAssertion : Prop :=
  ∀ (R : Nat) (x : Fin 5 → Fin 5 → Nat), FiveFacets R x → Nonempty (CutCertificate5 R x)

def pairScore {r : Nat} (w : Fin r → Nat) (x : Fin r → Fin r → Nat) : Nat :=
  psum r (fun i j => w i*w j*x i j)

theorem psum_vsum_swap {n m : Nat} (f : Fin m → Fin n → Fin n → Nat) :
    psum n (fun i j => vsum m (fun s => f s i j)) =
      vsum m (fun s => psum n (f s)) := by
  induction n with
  | zero => simp [psum,vsum_zero]
  | succ n ih =>
    simp only [psum,ih,vsum_add]
    rw [vsum_swap]

theorem pullback_cut_certificate {R : Nat} {x : Fin 5 → Fin 5 → Nat}
    (C : CutCertificate5 R x) {r : Nat} (w : Fin r → Nat) (label : Fin r → Fin 5) :
    pairScore w (fun i j => x (label i) (label j)) ≤ R*largestCutWeight w := by
  let W := largestCutWeight w
  let a := C.atom
  let q := C.denominator
  have edge (i j : Fin r) (_ : i ≠ j) :
      q*(w i*w j*x (label i) (label j)) ≤
        vsum 32 (fun s => a s * edgeTerm w (cutAdj (fun i => cutBits s (label i))) i j) := by
    have H := Nat.mul_le_mul_left (w i*w j) (C.marginals (label i) (label j))
    rw [←vsum_mul_left] at H
    have hrow (s : Fin 32) :
        w i*w j * gate s (label i) (label j) (a s) =
          a s * edgeTerm w (cutAdj (fun i => cutBits s (label i))) i j := by
      by_cases h : cutBits s (label i) = cutBits s (label j)
      · simp [gate,edgeTerm,cutAdj,h]
      · simp [gate,edgeTerm,cutAdj,h,Nat.mul_comm (w i*w j)]
    have hsum := vsum_congr hrow
    rw [hsum] at H
    simpa only [q,Nat.mul_left_comm (w i*w j) C.denominator] using H
  have hsum := psum_le edge
  rw [psum_mul_left,psum_vsum_swap] at hsum
  have hcut (s : Fin 32) :
      psum r (fun i j => a s * edgeTerm w (cutAdj (fun i => cutBits s (label i))) i j) =
        a s*cutWeight w (fun i => cutBits s (label i)) := by
    rw [psum_mul_left]
    congr 1
    exact cut_edge_weight w _
  have ht := vsum_congr hcut
  rw [ht] at hsum
  have hfull : vsum 32 (fun s => a s*cutWeight w (fun i => cutBits s (label i))) ≤ q*R*W := by
    have hm := vsum_le (fun s => Nat.mul_le_mul_left (a s)
      (largestCutWeight_bounds w (fun i => cutBits s (label i))))
    rw [vsum_mul_right] at hm
    exact Nat.le_trans hm (Nat.mul_le_mul_right W C.budget)
  have h := Nat.le_trans hsum hfull
  rw [Nat.mul_assoc] at h
  exact Nat.le_of_mul_le_mul_left h C.positive

theorem graph_score_baseline {V : Type} {G : SimpleGraph V} (M : ShortestDistances G)
    (k : Nat) {r : Nat} (T : Fin r → V) (w : Fin r → Nat) :
    terminalScore M T w ≤ k*pairWeight w + pairScore w (clipped M k T) := by
  have h (i j : Fin r) (_ : i ≠ j) : w i*w j*M.dist (T i) (T j) ≤
      k*(w i*w j)+w i*w j*clipped M k T i j := by
    have hm : M.dist (T i) (T j) ≤ k+clipped M k T i j := by unfold clipped; omega
    have hh := Nat.mul_le_mul_left (w i*w j) hm
    simpa only [Nat.mul_add,Nat.mul_comm (w i*w j) k] using hh
  have H := psum_le h
  rw [psum_add,psum_mul_left] at H
  exact H

/-- Arbitrarily many original terminal labels. If the positive excess can
be compressed without loss into the five named representatives, the
only remaining input is a certificate of their finite cut hull. -/
theorem arbitrary_terminal_weighted_upper_hook {V : Type} {G : SimpleGraph V}
    (M : ShortestDistances G) (k R : Nat) {r : Nat} (T : Fin r → V) (w : Fin r → Nat)
    (x : Fin 5 → Fin 5 → Nat) (label : Fin r → Fin 5)
    (C : CutCertificate5 R x)
    (comp : pairScore w (clipped M k T) ≤ pairScore w (fun i j => x (label i) (label j))) :
    terminalScore M T w ≤ k*pairWeight w+R*largestCutWeight w := by
  exact Nat.le_trans (graph_score_baseline M k T w)
    (Nat.add_le_add_left (Nat.le_trans comp (pullback_cut_certificate C w label)) _)

theorem exact_five_packing_weighted_upper_hook (hull : FiveCutHullAssertion)
    {V : Type} {G : SimpleGraph V} (M : ShortestDistances G) (k : Nat)
    (P : ExactPacking M k 5) (f : Fin 5 → V) (hf : IsPacking M k f)
    {r : Nat} (T : Fin r → V) (w : Fin r → Nat) (label : Fin r → Fin 5)
    (comp : pairScore w (clipped M k T) ≤
      pairScore w (fun i j => clipped M k f (label i) (label j))) :
    terminalScore M T w ≤ k*pairWeight w+4*(k+1)*largestCutWeight w := by
  obtain ⟨C⟩ := hull (4*(k+1)) (clipped M k f) (graph_five_facets M k P f hf)
  exact arbitrary_terminal_weighted_upper_hook M k (4*(k+1)) T w _ label C comp

end TriameterQ3PackingWindows

/-! Finite weighted compression: algebra for the no-loss move and its
compatibility with transport of the original terminal labels. -/
namespace TriameterQ3PackingWindows
open TriameterQ3SmallPacking

theorem vsum_indicator {n : Nat} (j : Fin n) (a : Nat) :
    vsum n (fun i => if i = j then a else 0) = a := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    refine Fin.cases ?_ ?_ j
    · simp [vsum,Fin.succ_ne_zero,vsum_zero]
    · intro i
      have h0 : (0 : Fin (n+1)) ≠ i.succ := fun he => Fin.succ_ne_zero i he.symm
      simp only [vsum,ite_eq_right h0,Fin.succ_inj,Nat.zero_add]
      exact ih i

def pushedMass {n : Nat} (w : Fin n → Nat) (s : Fin n → Fin n) (j : Fin n) : Nat :=
  vsum n (fun i => if s i = j then w i else 0)

theorem transport_sum {n : Nat} (w h : Fin n → Nat) (s : Fin n → Fin n) :
    vsum n (fun i => w i*h (s i)) = vsum n (fun j => pushedMass w s j*h j) := by
  unfold pushedMass
  simp only [←vsum_mul_right]
  rw [vsum_swap]
  apply vsum_congr
  intro i
  have hh (j : Fin n) : ((if s i = j then w i else 0)*h j) =
      (if j = s i then w i*h (s i) else 0) := by
    by_cases hd : j = s i
    · subst j
      simp
    · simp [hd,Ne.symm hd]
  rw [vsum_congr hh,vsum_indicator]

def bilinear {n : Nat} (x : Fin n → Fin n → Nat) (u v : Fin n → Nat) : Nat :=
  vsum n (fun i => vsum n (fun j => u i * (v j*x i j)))

def rowValue {n : Nat} (x : Fin n → Fin n → Nat) (w : Fin n → Nat) (i : Fin n) : Nat :=
  vsum n (fun j => w j*x i j)

theorem bilinear_row {n : Nat} (x : Fin n → Fin n → Nat) (u v : Fin n → Nat) :
    bilinear x u v = vsum n (fun i => u i*rowValue x v i) := by
  unfold bilinear rowValue
  simp only [vsum_mul_left]

theorem bilinear_symm {n : Nat} (x : Fin n → Fin n → Nat)
    (hs : ∀ i j, x i j = x j i) (u v : Fin n → Nat) :
    bilinear x u v = bilinear x v u := by
  unfold bilinear
  rw [vsum_swap]
  apply vsum_congr
  intro i
  apply vsum_congr
  intro j
  rw [hs j i]
  ac_rfl

theorem bilinear_add_left {n : Nat} (x : Fin n → Fin n → Nat) (u v w : Fin n → Nat) :
    bilinear x (fun i => u i + v i) w = bilinear x u w+bilinear x v w := by
  simp only [bilinear_row,Nat.add_mul,vsum_add]

theorem bilinear_add_right {n : Nat} (x : Fin n → Fin n → Nat) (u v w : Fin n → Nat) :
    bilinear x u (fun i => v i + w i) = bilinear x u v+bilinear x u w := by
  simp [bilinear,Nat.add_mul,Nat.mul_add,vsum_add]

theorem double_pair_score {n : Nat} (x : Fin n → Fin n → Nat)
    (hs : ∀ i j, x i j = x j i) (hd : ∀ i, x i i = 0) (w : Fin n → Nat) :
    bilinear x w w = 2*pairScore w x := by
  unfold bilinear pairScore
  simp only [←Nat.mul_assoc]
  apply double_psum
  · intro i j
    rw [hs i j,Nat.mul_comm (w i) (w j)]
  · intro i
    simp [hd i]

theorem pullback_score_as_mass {n : Nat} (x : Fin n → Fin n → Nat)
    (hs : ∀ i j, x i j = x j i) (hd : ∀ i, x i i = 0)
    (w : Fin n → Nat) (s : Fin n → Fin n) :
    pairScore w (fun i j => x (s i) (s j)) = pairScore (pushedMass w s) x := by
  have H0 := double_pair_score (fun i j => x (s i) (s j)) (fun i j => hs _ _)
    (fun i => hd _) w
  have H1 := double_pair_score x hs hd (pushedMass w s)
  have H : bilinear (fun i j => x (s i) (s j)) w w =
      bilinear x (pushedMass w s) (pushedMass w s) := by
    rw [bilinear_row,bilinear_row]
    have HR (i : Fin n) : rowValue (fun i j => x (s i) (s j)) w i =
        rowValue x (pushedMass w s) (s i) := transport_sum w _ s
    have Hleft := vsum_congr (fun i => congrArg (w i*·) (HR i))
    rw [Hleft]
    exact transport_sum w _ s
  omega

def spike {n : Nat} (i : Fin n) (q : Nat) (j : Fin n) : Nat :=
  if j = i then q else 0

def withoutPair {n : Nat} (w : Fin n → Nat) (u v : Fin n) (j : Fin n) : Nat :=
  if j = u ∨ j = v then 0 else w j

def mergeWeights {n : Nat} (w : Fin n → Nat) (u v : Fin n) (j : Fin n) : Nat :=
  if j = v then 0 else if j = u then w u+w v else w j

theorem row_spike {n : Nat} (x : Fin n → Fin n → Nat) (i j : Fin n) (q : Nat) :
    rowValue x (spike j q) i = q*x i j := by
  unfold rowValue
  have hh (l : Fin n) : spike j q l*x i l = if l = j then q*x i j else 0 := by
    by_cases he : l = j
    · subst l
      simp [spike]
    · simp [spike,he]
  rw [vsum_congr hh,vsum_indicator]

theorem bilinear_spike_left {n : Nat} (x : Fin n → Fin n → Nat) (u : Fin n)
    (q : Nat) (w : Fin n → Nat) :
    bilinear x (spike u q) w = q*rowValue x w u := by
  rw [bilinear_row]
  have hh (l : Fin n) : spike u q l*rowValue x w l =
      if l = u then q*rowValue x w u else 0 := by
    by_cases he : l = u
    · subst l
      simp [spike]
    · simp [spike,he]
  rw [vsum_congr hh,vsum_indicator]

theorem w_decomp {n : Nat} (w : Fin n → Nat) (u v : Fin n) (hne : u ≠ v) :
    w = (fun j => (withoutPair w u v j+spike u (w u) j)+spike v (w v) j) := by
  funext j
  by_cases h1 : j = u
  · subst j
    simp [withoutPair,spike,hne]
  · by_cases h2 : j = v
    · subst j
      simp [withoutPair,spike,Ne.symm hne]
    · simp [withoutPair,spike,h1,h2]

theorem merged_decomp {n : Nat} (w : Fin n → Nat) (u v : Fin n) (hne : u ≠ v) :
    mergeWeights w u v = fun j => withoutPair w u v j + spike u (w u+w v) j := by
  funext j
  by_cases h1 : j = u
  · subst j
    simp [withoutPair,mergeWeights,spike,hne]
  · by_cases h2 : j = v
    · subst j
      simp [withoutPair,mergeWeights,spike,Ne.symm hne]
    · simp [withoutPair,mergeWeights,spike,h1,h2]

theorem withoutPair_symm {n : Nat} (w : Fin n → Nat) (u v : Fin n) :
    withoutPair w u v = withoutPair w v u := by
  funext j
  by_cases h1 : j = u <;> by_cases h2 : j = v <;> simp [withoutPair,h1,h2]

theorem merge_choose_larger_row {n : Nat} (x : Fin n → Fin n → Nat)
    (hs : ∀ i j, x i j = x j i) (hd : ∀ i, x i i = 0)
    (w : Fin n → Nat) (u v : Fin n) (hne : u ≠ v) (hz : x u v = 0)
    (hge : rowValue x (withoutPair w u v) v ≤ rowValue x (withoutPair w u v) u) :
    pairScore w x ≤ pairScore (mergeWeights w u v) x := by
  let B := withoutPair w u v
  let U := spike u (w u)
  let V := spike v (w v)
  have W : w = fun i => (B i + U i)+V i := w_decomp w u v hne
  have W' : mergeWeights w u v = fun i => B i+spike u (w u+w v) i := merged_decomp w u v hne
  have H0 : bilinear x w w =
      bilinear x B B + 2*(w u*rowValue x B u + w v*rowValue x B v) := by
    conv => lhs; rw [W]
    simp only [bilinear_add_left,bilinear_add_right]
    have hBU := bilinear_symm x hs B U
    have hBV := bilinear_symm x hs B V
    change bilinear x B (spike u (w u)) = _ at hBU
    change bilinear x B (spike v (w v)) = _ at hBV
    dsimp only [U,V]
    rw [hBU,hBV]
    dsimp only [U,V]
    simp only [bilinear_spike_left,row_spike,hd u,hd v,hz,show x v u = 0 from (hs v u).trans hz,
      Nat.mul_zero,Nat.add_zero]
    omega
  have H1 : bilinear x (mergeWeights w u v) (mergeWeights w u v) =
      bilinear x B B + 2*((w u+w v)*rowValue x B u) := by
    rw [W']
    simp only [bilinear_add_left,bilinear_add_right]
    rw [bilinear_symm x hs B (spike u (w u+w v))]
    simp only [bilinear_spike_left,row_spike,hd u,Nat.mul_zero,Nat.add_zero]
    omega
  rw [double_pair_score x hs hd] at H0 H1
  have h := Nat.mul_le_mul_left (w v) hge
  change w v*rowValue x B v ≤ w v*rowValue x B u at h
  rw [Nat.add_mul] at H1
  omega

theorem no_loss_weight_merge {n : Nat} (x : Fin n → Fin n → Nat)
    (hs : ∀ i j, x i j = x j i) (hd : ∀ i, x i i = 0)
    (w : Fin n → Nat) (u v : Fin n) (hne : u ≠ v) (hz : x u v = 0) :
    pairScore w x ≤ pairScore (mergeWeights w u v) x ∨
    pairScore w x ≤ pairScore (mergeWeights w v u) x := by
  rcases Nat.le_total (rowValue x (withoutPair w u v) v) (rowValue x (withoutPair w u v) u) with h|h
  · exact Or.inl (merge_choose_larger_row x hs hd w u v hne hz h)
  · have hz' : x v u = 0 := (hs v u).trans hz
    exact Or.inr (merge_choose_larger_row x hs hd w v u (Ne.symm hne) hz'
      (by rwa [←withoutPair_symm w u v]))

end TriameterQ3PackingWindows

namespace TriameterQ3PackingWindows
open TriameterQ3SmallPacking

def redirect {n : Nat} (s : Fin n → Fin n) (u v : Fin n) (i : Fin n) : Fin n :=
  if s i = v then u else s i

theorem pushedMass_redirect {n : Nat} (w : Fin n → Nat) (s : Fin n → Fin n)
    (u v : Fin n) (hne : u ≠ v) :
    pushedMass w (redirect s u v) = mergeWeights (pushedMass w s) u v := by
  funext j
  by_cases hv : j = v
  · subst j
    change pushedMass w (redirect s u v) v = mergeWeights (pushedMass w s) u v v
    have hr : mergeWeights (pushedMass w s) u v v = 0 := by simp [mergeWeights]
    rw [hr,←vsum_zero n]
    unfold pushedMass
    apply vsum_congr
    intro i
    by_cases he : s i = v <;> simp [redirect,he,hne]
  · by_cases hu : j = u
    · subst j
      simp only [pushedMass,mergeWeights,ite_eq_right hne,↓reduceIte,←vsum_add]
      apply vsum_congr
      intro i
      by_cases he : s i = v
      · simp [redirect,he,Ne.symm hne]
      · simp [redirect,he]
    · simp only [pushedMass,mergeWeights,ite_eq_right hv,ite_eq_right hu]
      apply vsum_congr
      intro i
      by_cases he : s i = v
      · simp [redirect,he,Ne.symm hu,Ne.symm hv]
      · simp [redirect,he]

theorem vsum_lt_at {n : Nat} {f g : Fin n → Nat} (j : Fin n)
    (he : ∀ i, f i ≤ g i) (hj : f j < g j) : vsum n f < vsum n g := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    revert hj
    refine Fin.cases ?_ ?_ j
    · intro h0
      change f 0+vsum n (fun i => f i.succ) < g 0+vsum n (fun i => g i.succ)
      exact Nat.add_lt_add_of_lt_of_le h0 (vsum_le (fun i => he i.succ))
    · intro i hi
      change f 0+vsum n (fun i => f i.succ) < g 0+vsum n (fun i => g i.succ)
      exact Nat.add_lt_add_of_le_of_lt (he 0) (ih i (fun j => he j.succ) hi)

def activeCount {n : Nat} (w : Fin n → Nat) : Nat :=
  vsum n (fun i => if w i = 0 then 0 else 1)

theorem merge_decreases {n : Nat} (w : Fin n → Nat) (u v : Fin n)
    (hne : u ≠ v) (hU : 0 < w u) (hV : 0 < w v) :
    activeCount (mergeWeights w u v) < activeCount w := by
  unfold activeCount
  apply vsum_lt_at v
  · intro i
    by_cases hv : i = v
    · subst i
      simp [mergeWeights]
    · by_cases hu : i = u
      · subst i
        simp [mergeWeights,hne,Nat.ne_of_gt hU]
      · simp [mergeWeights,hv,hu]
  · simp [mergeWeights,Nat.ne_of_gt hV]

theorem positive_mass_of_label {n : Nat} (w : Fin n → Nat) (s : Fin n → Fin n)
    (i : Fin n) (h : 0 < w i) : 0 < pushedMass w s (s i) := by
  have H : (vsum n fun j => if j=i then w i else 0) ≤ pushedMass w s (s i) := by
    unfold pushedMass
    apply vsum_le
    intro j
    by_cases hj : j=i
    · subst j
      simp
    · simp [hj]
  rw [vsum_indicator] at H
  omega

theorem pushedMass_id {n : Nat} (w : Fin n → Nat) : pushedMass w id = w := by
  funext i
  unfold pushedMass
  have hh (j : Fin n) : (if id j = i then w j else 0) = if j=i then w i else 0 := by
    by_cases h : j=i
    · subst j; simp
    · simp [h]
  rw [vsum_congr hh,vsum_indicator]

/-- Every nonnegative product-weight objective admits a nondecreasing
relocation to a support where all distinct representatives are separated
by positive entries. Original labels survive the map. -/
theorem weight_compression {n : Nat} (x : Fin n → Fin n → Nat)
    (hs : ∀ i j, x i j = x j i) (hd : ∀ i, x i i = 0) (w : Fin n → Nat) :
    ∃ s : Fin n → Fin n,
      pairScore w x ≤ pairScore w (fun i j => x (s i) (s j)) ∧
      ∀ u v, u ≠ v → 0 < pushedMass w s u → 0 < pushedMass w s v → 0 < x u v := by
  have compress (m : Nat) : ∀ s : Fin n → Fin n, activeCount (pushedMass w s) = m →
      ∃ t : Fin n → Fin n,
        pairScore (pushedMass w s) x ≤ pairScore (pushedMass w t) x ∧
        ∀ u v, u ≠ v → 0 < pushedMass w t u → 0 < pushedMass w t v → 0 < x u v := by
    induction m using Nat.strongRecOn with
    | ind m ih =>
      intro s hm
      by_cases h : ∃ u v, u ≠ v ∧ 0 < pushedMass w s u ∧ 0 < pushedMass w s v ∧ x u v = 0
      · obtain ⟨u,v,hne,hU,hV,h0⟩ := h
        rcases no_loss_weight_merge x hs hd (pushedMass w s) u v hne h0 with hL|hR
        · let t := redirect s u v
          have ht := pushedMass_redirect w s u v hne
          have hLt : activeCount (pushedMass w t) < m := by
            change activeCount (pushedMass w (redirect s u v)) < _
            rw [ht,←hm]
            exact merge_decreases _ _ _ hne hU hV
          obtain ⟨l,hobj,hsep⟩ := ih _ hLt t rfl
          rw [←ht] at hL
          exact ⟨l,Nat.le_trans hL hobj,hsep⟩
        · let t := redirect s v u
          have ht := pushedMass_redirect w s v u (Ne.symm hne)
          have hLt : activeCount (pushedMass w t) < m := by
            change activeCount (pushedMass w (redirect s v u)) < _
            rw [ht,←hm]
            exact merge_decreases _ _ _ (Ne.symm hne) hV hU
          obtain ⟨l,hobj,hsep⟩ := ih _ hLt t rfl
          rw [←ht] at hR
          exact ⟨l,Nat.le_trans hR hobj,hsep⟩
      · refine ⟨s,Nat.le_refl _,?_⟩
        intro u v hne hU hV
        exact Nat.pos_of_ne_zero (fun h0 => h ⟨u,v,hne,hU,hV,h0⟩)
  obtain ⟨s,hobj,hsep⟩ := compress _ id rfl
  rw [pushedMass_id,←pullback_score_as_mass x hs hd w s] at hobj
  exact ⟨s,hobj,hsep⟩

end TriameterQ3PackingWindows

namespace TriameterQ3PackingWindows
open TriameterQ3Graph TriameterQ3SmallPacking

def padFive {q : Nat} (x : Fin q → Fin q → Nat) (i j : Fin 5) : Nat :=
  if hi : i.val < q then if hj : j.val < q then x ⟨i.val,hi⟩ ⟨j.val,hj⟩ else 0
  else 0

theorem padFive_cast {q : Nat} (x : Fin q → Fin q → Nat)
    (h : q ≤ 5) (i j : Fin q) : padFive x (Fin.castLE h i) (Fin.castLE h j) = x i j := by
  unfold padFive
  simp only [Fin.val_castLE,dite_eq_left i.isLt,dite_eq_left j.isLt]

theorem finite_injection_bound {p q : Nat} (f : Fin p → Fin q)
    (hf : Function.Injective f) : p ≤ q := by
  have hn : ((List.finRange p).map f).Nodup :=
    List.Pairwise.map f (fun a b ne e => ne (hf e)) (List.nodup_finRange p)
  have hs : (List.finRange p).map f ⊆ List.finRange q := fun {x} _ => List.mem_finRange x
  have hlen := hn.length_le_of_subset hs
  simpa only [List.length_map,List.length_finRange] using hlen

theorem injective_hits_four (g : Fin 5 → Fin 5) (hg : Function.Injective g) :
    ∃ i, g i = 4 := by
  by_cases H : ∃ i, g i = 4
  · exact H
  · have hb (i : Fin 5) : (g i).val < 4 := by
      have h0 := (g i).isLt
      have h1 : (g i).val ≠ 4 := fun e => H ⟨i,Fin.ext e⟩
      omega
    let f : Fin 5 → Fin 4 := fun i => ⟨(g i).val,hb i⟩
    have hf : Function.Injective f := by
      intro i j he
      have hv := congrArg (@Fin.val 4) he
      exact hg (Fin.ext hv)
    have bad := finite_injection_bound f hf
    omega

theorem fin5_enum (i : Fin 5) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
  have hi := i.isLt
  have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 := by omega
  rcases h with h|h|h|h|h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext h))))

theorem small_support_pad_facets {q R : Nat} (hq : q ≤ 4) (x : Fin q → Fin q → Nat)
    (hs : ∀ i j, x i j = x j i) (hd : ∀ i, x i i = 0)
    (hb : ∀ i j, x i j ≤ R) (ht : ∀ i j l, x i j+x i l+x j l ≤ 2*R) :
    FiveFacets R (padFive x) := by
  have hSym (i j : Fin 5) : padFive x i j = padFive x j i := by
    by_cases hi : i.val < q <;> by_cases hj : j.val < q <;> simp [padFive,hi,hj,hs]
  have hDiag (i : Fin 5) : padFive x i i = 0 := by
    by_cases hi : i.val < q <;> simp [padFive,hi,hd]
  have hBox (i j : Fin 5) : padFive x i j ≤ R := by
    by_cases hi : i.val < q <;> by_cases hj : j.val < q <;> simp [padFive,hi,hj,hb]
  have hz (i : Fin 5) : padFive x 4 i = 0 := by
    unfold padFive
    have h4 : ¬ (4 : Fin 5).val < q := by omega
    simp [h4]
  have hz' (i : Fin 5) : padFive x i 4 = 0 := (hSym _ _).trans (hz i)
  refine ⟨hSym,hDiag,hBox,?_,?_,?_⟩
  · intro i j l
    have hib := hBox i j
    have hjb := hBox i l
    have hlb := hBox j l
    by_cases hi : i.val < q <;> by_cases hj : j.val < q <;> by_cases hl : l.val < q
    · simpa [padFive,hi,hj,hl] using ht ⟨i.val,hi⟩ ⟨j.val,hj⟩ ⟨l.val,hl⟩
    all_goals
      simp only [padFive,hi,hj,hl,↓reduceDIte,Nat.zero_add,Nat.add_zero] at *
      omega
  · intro g hg
    obtain ⟨i,hi⟩ := injective_hits_four g hg
    have h01 := hBox (g 0) (g 1)
    have h12 := hBox (g 1) (g 2)
    have h23 := hBox (g 2) (g 3)
    have h34 := hBox (g 3) (g 4)
    have h04 := hBox (g 0) (g 4)
    unfold cycleSum5
    rcases fin5_enum i with rfl|rfl|rfl|rfl|rfl <;> rw [hi] <;>
      simp only [hz,hz',Nat.zero_add,Nat.add_zero] <;> omega
  · have h01 := hBox 0 1
    have h02 := hBox 0 2
    have h03 := hBox 0 3
    have h12 := hBox 1 2
    have h13 := hBox 1 3
    have h23 := hBox 2 3
    unfold fullSum5
    simp only [hz',Nat.add_zero]
    omega

theorem clipped_triangle_general {V : Type} {G : SimpleGraph V} (M : ShortestDistances G)
    (k p : Nat) (P : ExactPacking M k p) {r : Nat} (f : Fin r → V) (i j l : Fin r) :
    clipped M k f i j+clipped M k f i l+clipped M k f j l ≤ 2*packingRadius k p := by
  have hp := exactPacking_pos M P (f i)
  have hpred : (p-1)+1=p := by omega
  have hmul : (k+1)*p = packingRadius k p + (k+1) := by
    calc
      _ = (k+1)*((p-1)+1) := congrArg ((k+1)*·) hpred.symm
      _ = _ := by simp only [packingRadius,Nat.mul_add,Nat.mul_one]
  have h := triple_perimeter_packing_bound M P (f i) (f j) (f l)
  have h3 : M.dist (f i) (f j)+M.dist (f i) (f l)+M.dist (f j) (f l) ≤ 3*k+2*packingRadius k p := by
    rw [Nat.mul_assoc,hmul] at h
    omega
  have hab := packing_diam M k p P (f i) (f j)
  have hac := packing_diam M k p P (f i) (f l)
  have hbc := packing_diam M k p P (f j) (f l)
  unfold clipped
  omega

theorem packed_padding_facets {V : Type} {G : SimpleGraph V} (M : ShortestDistances G)
    (k p q : Nat) (P : ExactPacking M k p) (hp : p ≤ 5) (f : Fin q → V) (hf : IsPacking M k f) :
    FiveFacets (packingRadius k p) (padFive (clipped M k f)) := by
  have hq : q ≤ p := P.upper q f hf
  by_cases hq5 : q = 5
  · subst q
    have hp5 : p = 5 := by omega
    subst p
    have hpadded : padFive (clipped M k f) = clipped M k f := by
      funext i j
      exact padFive_cast _ (Nat.le_refl _) i j
    have hR : packingRadius k 5 = 4*(k+1) := by unfold packingRadius; omega
    rw [hpadded,hR]
    exact graph_five_facets M k P f hf
  · have hq4 : q ≤ 4 := by omega
    apply small_support_pad_facets hq4
    · intro i j
      simp [clipped,M.dist_symm (f i) (f j)]
    · intro i
      simp [clipped,M.dist_self]
    · intro i j
      have h := packing_diam M k p P (f i) (f j)
      unfold clipped
      omega
    · exact clipped_triangle_general M k p P f

def supportList {n : Nat} (w : Fin n → Nat) (s : Fin n → Fin n) : List (Fin n) :=
  (List.finRange n).filter (fun i => decide (0 < pushedMass w s i))

theorem supportList_mem {n : Nat} (w : Fin n → Nat) (s : Fin n → Fin n) (i : Fin n) :
    i ∈ supportList w s ↔ 0 < pushedMass w s i := by
  simp [supportList,List.mem_finRange]

theorem supportList_injective {n : Nat} (w : Fin n → Nat) (s : Fin n → Fin n) :
    Function.Injective (supportList w s).get := by
  have H : (supportList w s).Nodup := (List.nodup_finRange n).filter (fun i => decide (0 < pushedMass w s i))
  intro i j hij
  apply Fin.ext
  exact H.eq_of_getElem_eq i.isLt j.isLt hij

/-- Complete arbitrary-terminal upper bridge; the sole additional
mathematical premise is the explicit finite rational cut-hull theorem. -/
theorem weighted_upper_from_packed_certificates
    {V : Type} {G : SimpleGraph V} (M : ShortestDistances G)
    (k p : Nat) (hp : p ≤ 5) (P : ExactPacking M k p)
    (provider : ∀ (q : Nat) (f : Fin q → V), IsPacking M k f →
      Nonempty (CutCertificate5 (packingRadius k p) (padFive (clipped M k f))))
    {r : Nat} (T : Fin r → V) (w : Fin r → Nat) :
    terminalScore M T w ≤ k*pairWeight w+packingRadius k p*largestCutWeight w := by
  let x := clipped M k T
  have hs (i j : Fin r) : x i j = x j i := by simp [x,clipped,M.dist_symm (T i) (T j)]
  have hd (i : Fin r) : x i i = 0 := by simp [x,clipped,M.dist_self]
  obtain ⟨s,hobj,hsep⟩ := weight_compression x hs hd w
  let L := supportList w s
  let q := L.length
  let f : Fin q → V := fun i => T (L.get i)
  have hf : IsPacking M k f := by
    intro i j h
    have hi := (supportList_mem w s (L.get i)).1 (List.get_mem L i)
    have hj := (supportList_mem w s (L.get j)).1 (List.get_mem L j)
    have hij : L.get i ≠ L.get j := fun he => h (supportList_injective w s he)
    have hh := hsep (L.get i) (L.get j) hij hi hj
    change 0 < M.dist (f i) (f j)-k at hh
    omega
  have hq : q ≤ 5 := Nat.le_trans (P.upper q f hf) hp
  let y := padFive (clipped M k f)
  have active (i : Fin r) (h : 0 < w i) : ∃ j : Fin q, L.get j = s i :=
    List.mem_iff_get.1 ((supportList_mem w s (s i)).2 (positive_mass_of_label w s i h))
  let label : Fin r → Fin 5 := fun i => if h : 0 < w i then
    Fin.castLE hq (active i h).choose else 0
  have hY (i j : Fin r) (hi : 0 < w i) (hj : 0 < w j) :
      y (label i) (label j) = x (s i) (s j) := by
    have he1 := (active i hi).choose_spec
    have he2 := (active j hj).choose_spec
    simp only [label,dite_eq_left hi,dite_eq_left hj,y,padFive_cast]
    change M.dist (T (L.get (active i hi).choose)) (T (L.get (active j hj).choose))-k =
      M.dist (T (s i)) (T (s j))-k
    rw [he1,he2]
  have heq : pairScore w (fun i j => y (label i) (label j)) =
      pairScore w (fun i j => x (s i) (s j)) := by
    unfold pairScore
    apply psum_congr
    intro i j
    by_cases hi : 0 < w i
    · by_cases hj : 0 < w j
      · exact congrArg (fun z => w i*w j*z) (hY i j hi hj)
      · have he : w j = 0 := by omega
        simp [he]
    · have he : w i = 0 := by omega
      simp [he]
  obtain ⟨C⟩ := provider q f hf
  exact arbitrary_terminal_weighted_upper_hook M k (packingRadius k p) T w y label C
    (by rw [heq]; exact hobj)

/-- All graph and weight-compression steps are native; just the explicit
finite rational cut geometry is accepted as a premise. -/
theorem weighted_p_le_five_upper (hull : FiveCutHullAssertion)
    {V : Type} {G : SimpleGraph V} (M : ShortestDistances G)
    (k p : Nat) (hp : p ≤ 5) (P : ExactPacking M k p)
    {r : Nat} (T : Fin r → V) (w : Fin r → Nat) :
    terminalScore M T w ≤ k*pairWeight w+packingRadius k p*largestCutWeight w :=
  weighted_upper_from_packed_certificates M k p hp P
    (fun q f hf => hull _ _ (packed_padding_facets M k p q P hp f hf)) T w

/-- Actual finite graph and actual packing number, with arbitrary labels.
No geometry assumption remains; only the finite cut-hull premise. -/
theorem native_finite_weighted_p_le_five_upper (hull : FiveCutHullAssertion)
    (n : Nat) (G : SimpleGraph (Fin n)) (hC : Connected G) (k : Nat)
    (hp : packingNumber (distancesOfConnected G hC) k ≤ 5)
    {r : Nat} (T : Fin r → Fin n) (w : Fin r → Nat) :
    let M := distancesOfConnected G hC
    let p := packingNumber M k
    terminalScore M T w ≤ k*pairWeight w+packingRadius k p*largestCutWeight w :=
  weighted_p_le_five_upper hull _ k _ hp (packingNumber_is_exact _ k) T w

end TriameterQ3PackingWindows

namespace TriameterQ3PackingWindows
open TriameterQ3Graph TriameterQ3SmallPacking TriameterQ3Four

def eightAtoms (a : Atoms) (s : Fin 32) : Nat :=
  spike 0 a.p000.toNat s + spike 8 a.p001.toNat s +
  spike 4 a.p010.toNat s + spike 12 a.p011.toNat s +
  spike 2 a.p100.toNat s + spike 10 a.p101.toNat s +
  spike 6 a.p110.toNat s + spike 14 a.p111.toNat s

theorem eightAtoms_sum (a : Atoms) :
    vsum 32 (eightAtoms a) = a.p000.toNat+a.p001.toNat+a.p010.toNat+a.p011.toNat+
      a.p100.toNat+a.p101.toNat+a.p110.toNat+a.p111.toNat := by
  change vsum 32 (fun s => eightAtoms a s) = _
  simp only [eightAtoms,vsum_add,spike,vsum_indicator]

theorem gate_add (s : Fin 32) (i j : Fin 5) (a b : Nat) :
    gate s i j (a+b) = gate s i j a+gate s i j b := by
  by_cases h : cutBits s i = cutBits s j <;> simp [gate,h]

theorem gate_spike (i j : Fin 5) (z : Fin 32) (m : Nat) :
    vsum 32 (fun s => gate s i j (spike z m s)) = gate z i j m := by
  have h (s : Fin 32) : gate s i j (spike z m s) = if s = z then gate z i j m else 0 := by
    by_cases e : s = z
    · subst s
      simp [spike]
    · simp [spike,gate,e]
  rw [vsum_congr h,vsum_indicator]

theorem eightAtoms_marginal (a : Atoms) (i j : Fin 5) :
    vsum 32 (fun s => gate s i j (eightAtoms a s)) =
      gate 0 i j a.p000.toNat + gate 8 i j a.p001.toNat +
      gate 4 i j a.p010.toNat + gate 12 i j a.p011.toNat +
      gate 2 i j a.p100.toNat + gate 10 i j a.p101.toNat +
      gate 6 i j a.p110.toNat + gate 14 i j a.p111.toNat := by
  simp only [eightAtoms,gate_add,vsum_add,gate_spike]

theorem gate_symm (s : Fin 32) (i j : Fin 5) (m : Nat) :
    gate s i j m = gate s j i m := by
  unfold gate
  by_cases h : cutBits s i = cutBits s j
  · simp only [ite_eq_left h,ite_eq_left h.symm]
  · simp only [ite_eq_right h,ite_eq_right (Ne.symm h)]

theorem fin5_enum' (i : Fin 5) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
  have hi := i.isLt
  have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 := by omega
  rcases h with h|h|h|h|h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext h))))

theorem four_supported_cut_certificate (R : Nat) (x : Fin 5 → Fin 5 → Nat)
    (F : FiveFacets R x) (zero4 : ∀ i, x 4 i = 0) :
    Nonempty (CutCertificate5 R x) := by
  let X : Edges := ⟨x 0 1,x 0 2,x 0 3,x 1 2,x 1 3,x 2 3⟩
  have F4 : Feasible (R : Int) X := by
    have h01 := F.box 0 1
    have h02 := F.box 0 2
    have h03 := F.box 0 3
    have h12 := F.box 1 2
    have h13 := F.box 1 3
    have h23 := F.box 2 3
    have h012 := F.triangle 0 1 2
    have h013 := F.triangle 0 1 3
    have h023 := F.triangle 0 2 3
    have h123 := F.triangle 1 2 3
    unfold Feasible
    dsimp [X]
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega
  obtain ⟨a,ha,hTot,hMarg⟩ := domination_by_cut_distribution (R : Int) X F4
  rcases ha with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
  rcases hMarg with ⟨m01,m02,m03,m12,m13,m23⟩
  dsimp [Double,marginals,X] at m01 m02 m03 m12 m13 m23
  refine ⟨⟨2,eightAtoms a,by decide,?_,?_⟩⟩
  · rw [eightAtoms_sum]
    unfold mass at hTot
    omega
  · let H (i j : Fin 5) := 2*x i j ≤ vsum 32 (fun s => gate s i j (eightAtoms a s))
    have Hswap (i j : Fin 5) (h : H i j) : H j i := by
      unfold H at h ⊢
      rw [F.symmetric j i]
      have he := vsum_congr (fun s => gate_symm s j i (eightAtoms a s))
      rw [he]
      exact h
    have Hz (i : Fin 5) : H 4 i := by unfold H; rw [zero4]; exact Nat.zero_le _
    have Hd (i : Fin 5) : H i i := by unfold H; rw [F.diagonal]; exact Nat.zero_le _
    have H01 : H 0 1 := by
      unfold H
      rw [eightAtoms_marginal]
      change 2*x 0 1 ≤ 0+0+0+0+a.p100.toNat+a.p101.toNat+a.p110.toNat+a.p111.toNat
      omega
    have H02 : H 0 2 := by
      unfold H
      rw [eightAtoms_marginal]
      change 2*x 0 2 ≤ 0+0+a.p010.toNat+a.p011.toNat+0+0+a.p110.toNat+a.p111.toNat
      omega
    have H03 : H 0 3 := by
      unfold H
      rw [eightAtoms_marginal]
      change 2*x 0 3 ≤ 0+a.p001.toNat+0+a.p011.toNat+0+a.p101.toNat+0+a.p111.toNat
      omega
    have H12 : H 1 2 := by
      unfold H
      rw [eightAtoms_marginal]
      change 2*x 1 2 ≤ 0+0+a.p010.toNat+a.p011.toNat+a.p100.toNat+a.p101.toNat+0+0
      omega
    have H13 : H 1 3 := by
      unfold H
      rw [eightAtoms_marginal]
      change 2*x 1 3 ≤ 0+a.p001.toNat+0+a.p011.toNat+a.p100.toNat+0+a.p110.toNat+0
      omega
    have H23 : H 2 3 := by
      unfold H
      rw [eightAtoms_marginal]
      change 2*x 2 3 ≤ 0+a.p001.toNat+a.p010.toNat+0+0+a.p101.toNat+a.p110.toNat+0
      omega
    intro i j
    change H i j
    rcases fin5_enum' i with rfl|rfl|rfl|rfl|rfl <;>
      rcases fin5_enum' j with rfl|rfl|rfl|rfl|rfl <;>
      first | exact Hd _ | exact Hz _ | assumption |
        (apply Hswap; first | exact Hz _ | assumption)

theorem weighted_p_le_four_upper
    {V : Type} {G : SimpleGraph V} (M : ShortestDistances G)
    (k p : Nat) (hp : p ≤ 4) (P : ExactPacking M k p)
    {r : Nat} (T : Fin r → V) (w : Fin r → Nat) :
    terminalScore M T w ≤ k*pairWeight w+packingRadius k p*largestCutWeight w := by
  have hp5 : p ≤ 5 := by omega
  apply weighted_upper_from_packed_certificates M k p hp5 P _ T w
  intro q f hf
  have hq : q ≤ 4 := Nat.le_trans (P.upper q f hf) hp
  have facets := packed_padding_facets M k p q P hp5 f hf
  apply four_supported_cut_certificate _ _ facets
  intro i
  have h : ¬ (4 : Fin 5).val < q := by omega
  simp [padFive,h]

theorem native_finite_weighted_p_le_four_upper
    (n : Nat) (G : SimpleGraph (Fin n)) (hC : Connected G) (k : Nat)
    (hp : packingNumber (distancesOfConnected G hC) k ≤ 4)
    {r : Nat} (T : Fin r → Fin n) (w : Fin r → Nat) :
    let M := distancesOfConnected G hC
    let p := packingNumber M k
    terminalScore M T w ≤ k*pairWeight w+packingRadius k p*largestCutWeight w :=
  weighted_p_le_four_upper _ k _ hp (packingNumber_is_exact _ k) T w

end TriameterQ3PackingWindows

/-! Finite trunk with arbitrarily many terminal arms and odd-parity first-layer cliques. -/
namespace TriameterQ3SmallWitness
open TriameterQ3Graph

abbrev Vertex (r L H : Nat) := Fin (L+1) ⊕ (Fin r × Fin H)

def delta (a b : Nat) : Nat := a-b+(b-a)

theorem delta_symm (a b : Nat) : delta a b = delta b a := by
  unfold delta
  omega

theorem delta_triangle (a b c : Nat) : delta a c ≤ delta a b+delta b c := by
  unfold delta
  omega

theorem delta_step (a b : Nat) : delta a (b+1) ≤ delta a b+1 := by
  unfold delta
  omega

def treeDist {r L H : Nat} (anchor : Fin r → Fin (L+1)) (e : Nat) :
    Vertex r L H → Vertex r L H → Nat
  | .inl x, .inl y => delta x.val y.val
  | .inl x, .inr (a,d) => delta x.val (anchor a).val + (d.val+1)
  | .inr (a,d), .inl y => delta (anchor a).val y.val + (d.val+1)
  | .inr (a,d), .inr (b,f) =>
      if a = b then delta d.val f.val
      else delta (anchor a).val (anchor b).val + (d.val+1) + (f.val+1) -
        (if anchor a = anchor b then e else 0)

theorem treeDist_symm {r L H : Nat} (anchor : Fin r → Fin (L+1)) (e : Nat)
    (x y : Vertex r L H) : treeDist anchor e x y = treeDist anchor e y x := by
  rcases x with x | ⟨a,d⟩ <;> rcases y with y | ⟨b,f⟩
  · exact delta_symm _ _
  · simp only [treeDist, delta_symm x.val (anchor b).val]
  · simp only [treeDist, delta_symm (anchor a).val y.val]
  · simp only [treeDist, eq_comm (a := b), eq_comm (a := anchor b), delta_symm f.val d.val,
      delta_symm (anchor b).val (anchor a).val]
    split <;> omega

theorem treeDist_self {r L H : Nat} (anchor : Fin r → Fin (L+1)) (e : Nat)
    (x : Vertex r L H) : treeDist anchor e x x = 0 := by
  rcases x with x | ⟨a,d⟩ <;> simp [treeDist, delta]

theorem correction_symm {r L : Nat} (anchor : Fin r → Fin (L+1)) (e : Nat)
    (a b : Fin r) : (if anchor a = anchor b then e else 0) =
      (if anchor b = anchor a then e else 0) := by
  by_cases h : anchor a = anchor b
  · exact congrArg (fun n : Nat => n) ((ite_eq_left h).trans (ite_eq_left h.symm).symm)
  · exact (ite_eq_right h).trans (ite_eq_right (Ne.symm h)).symm

theorem treeDist_triangle {r L H : Nat} (anchor : Fin r → Fin (L+1))
    (e : Nat) (he : e ≤ 1) (x y z : Vertex r L H) :
    treeDist anchor e x z ≤ treeDist anchor e x y+treeDist anchor e y z := by
  rcases x with x | ⟨a,d⟩ <;> rcases y with y | ⟨b,f⟩ <;> rcases z with z | ⟨c,g⟩
  · exact delta_triangle _ _ _
  · have ha := delta_triangle x.val y.val (anchor c).val
    simp only [treeDist]
    omega
  · have ha := delta_triangle x.val (anchor b).val z.val
    simp only [treeDist]
    omega
  · by_cases hbc : b = c
    · subst c
      simp [treeDist, delta]
      omega
    · have ha := delta_triangle x.val (anchor b).val (anchor c).val
      simp only [treeDist, ite_eq_right hbc]
      split <;> omega
  · have ha := delta_triangle (anchor a).val y.val z.val
    simp only [treeDist]
    omega
  · by_cases hac : a = c
    · subst c
      simp [treeDist, delta]
      omega
    · have ha := delta_triangle (anchor a).val y.val (anchor c).val
      simp only [treeDist, ite_eq_right hac]
      omega
  · by_cases hab : a = b
    · subst b
      simp [treeDist, delta]
      omega
    · have ha := delta_triangle (anchor a).val (anchor b).val z.val
      simp only [treeDist, ite_eq_right hab]
      split <;> omega
  · by_cases hab : a = b
    · subst b
      by_cases hac : a = c
      · subst c
        simpa [treeDist] using delta_triangle d.val f.val g.val
      · simp only [treeDist, ite_eq_right hac, ↓reduceIte]
        unfold delta
        omega
    · by_cases hbc : b = c
      · subst c
        simp only [treeDist, ite_eq_right hab, ↓reduceIte]
        unfold delta
        omega
      · by_cases hac : a = c
        · subst c
          have hba : b ≠ a := Ne.symm hab
          simp only [treeDist, ite_eq_right hab, ite_eq_right hba, ↓reduceIte]
          rw [← correction_symm anchor e a b]
          by_cases hh : anchor a = anchor b <;> simp [hh, delta] <;> omega
        · have ha := delta_triangle (anchor a).val (anchor b).val (anchor c).val
          simp only [treeDist, ite_eq_right hab, ite_eq_right hbc, ite_eq_right hac]
          repeat' first | split
          all_goals omega

def graph {r L H : Nat} (anchor : Fin r → Fin (L+1)) (e : Nat) :
    SimpleGraph (Vertex r L H) where
  adj x y := treeDist anchor e x y = 1
  symm := fun {x y} h => (treeDist_symm anchor e y x).trans h
  loopless := fun x h => by rw [treeDist_self] at h; contradiction

theorem lower_of_walk {r L H : Nat} (anchor : Fin r → Fin (L+1)) (e : Nat)
    (he : e ≤ 1) {x y : Vertex r L H} {n : Nat} (w : Walk (graph anchor e) x y n) :
    treeDist anchor e x y ≤ n := by
  have step (i : Nat) (hi : i ≤ n) : treeDist anchor e (w.point 0) (w.point i) ≤ i := by
    induction i with
    | zero => simp [treeDist_self]
    | succ i ih =>
      have hi' : i < n := by omega
      have ht := treeDist_triangle anchor e he (w.point 0) (w.point i) (w.point (i+1))
      have hs := w.step i hi'
      change treeDist anchor e (w.point i) (w.point (i+1)) = 1 at hs
      have hp := ih (by omega)
      omega
  simpa only [w.first,w.last] using step n (Nat.le_refl n)

end TriameterQ3SmallWitness

namespace TriameterQ3SmallWitness
open TriameterQ3Graph

def unit {V : Type} {G : SimpleGraph V} {a b : V} (h : G.adj a b) :
    Walk G a b 1 := by
  refine ⟨fun i => if i = 0 then a else b,by simp,by simp,?_⟩
  intro i hi
  have e : i = 0 := by omega
  subst i
  simpa using h

def segmentUp {V : Type} {G : SimpleGraph V} {N : Nat}
    (line : Fin (N+1) → V)
    (edge : ∀ i : Nat, ∀ h : i < N,
      G.adj (line ⟨i,by omega⟩) (line ⟨i+1,by omega⟩))
    (a b : Fin (N+1)) (hab : a.val ≤ b.val) :
    Walk G (line a) (line b) (b.val-a.val) := by
  refine ⟨fun j => if h : a.val+j ≤ N then line ⟨a.val+j,by omega⟩ else line b, ?_, ?_, ?_⟩
  · have ha : a.val ≤ N := by omega
    simp [ha]
  · have hh : a.val+(b.val-a.val) = b.val := by omega
    have hb : b.val ≤ N := by omega
    simp [hh,hb]
  · intro i hi
    have hl : a.val+i < N := by omega
    have hr : a.val+(i+1) ≤ N := by omega
    have hs : a.val+i ≤ N := by omega
    simpa only [dite_eq_left hs,dite_eq_left hr,Nat.add_assoc] using edge _ hl

def segment {V : Type} {G : SimpleGraph V} {N : Nat}
    (line : Fin (N+1) → V)
    (edge : ∀ i : Nat, ∀ h : i < N,
      G.adj (line ⟨i,by omega⟩) (line ⟨i+1,by omega⟩)) (a b : Fin (N+1)) :
    Walk G (line a) (line b) (delta a.val b.val) := by
  by_cases h : a.val ≤ b.val
  · have hn : delta a.val b.val = b.val-a.val := by unfold delta; omega
    rw [hn]
    exact segmentUp line edge a b h
  · have hn : delta a.val b.val = a.val-b.val := by unfold delta; omega
    rw [hn]
    exact (segmentUp line edge b a (by omega)).reverse

def branch {r L H : Nat} (anchor : Fin r → Fin (L+1)) (a : Fin r)
    (j : Fin (H+1)) : Vertex r L H :=
  if h : j.val = 0 then .inl (anchor a) else .inr (a,⟨j.val-1,by omega⟩)

def branchZero (H : Nat) : Fin (H+1) := ⟨0,by omega⟩
def branchDepth {H : Nat} (d : Fin H) : Fin (H+1) := ⟨d.val+1,by omega⟩

@[simp] theorem branch_zero {r L H : Nat} (anchor : Fin r → Fin (L+1)) (a : Fin r) :
    branch anchor a (branchZero H) = .inl (anchor a) := by
  rfl

@[simp] theorem branch_depth {r L H : Nat} (anchor : Fin r → Fin (L+1)) (a : Fin r) (d : Fin H) :
    branch anchor a (branchDepth d) = .inr (a,d) := by
  simp [branch,branchDepth]

def trunkWalk {r L H : Nat} (anchor : Fin r → Fin (L+1)) (e : Nat)
    (a b : Fin (L+1)) :
    Walk (graph (H:=H) anchor e) (.inl a) (.inl b) (delta a.val b.val) := by
  apply segment Sum.inl _ a b
  intro i hi
  change delta i (i+1) = 1
  unfold delta
  omega

def branchWalk {r L H : Nat} (anchor : Fin r → Fin (L+1)) (e : Nat) (a : Fin r)
    (i j : Fin (H+1)) :
    Walk (graph anchor e) (branch anchor a i) (branch anchor a j) (delta i.val j.val) := by
  apply segment (branch anchor a) _ i j
  intro t ht
  by_cases h : t = 0
  · subst t
    change treeDist anchor e (branch anchor a ⟨0,_⟩) (branch anchor a ⟨1,_⟩) = 1
    simp [branch,treeDist,delta]
  · change treeDist anchor e (branch anchor a ⟨t,_⟩) (branch anchor a ⟨t+1,_⟩) = 1
    simp [branch,h,treeDist,delta]
    omega

def rootToArm {r L H : Nat} (anchor : Fin r → Fin (L+1)) (e : Nat)
    (a : Fin r) (d : Fin H) :
    Walk (graph anchor e) (.inl (anchor a)) (.inr (a,d)) (d.val+1) := by
  have h0 : delta (branchZero H).val (branchDepth d).val = d.val+1 := by
    simp [branchZero,branchDepth,delta]
  simpa only [branch_zero,branch_depth,h0] using
    branchWalk anchor e a (branchZero H) (branchDepth d)

def sameArm {r L H : Nat} (anchor : Fin r → Fin (L+1)) (e : Nat)
    (a : Fin r) (d f : Fin H) :
    Walk (graph anchor e) (.inr (a,d)) (.inr (a,f)) (delta d.val f.val) := by
  have hd : delta (branchDepth d).val (branchDepth f).val = delta d.val f.val := by
    change delta (d.val+1) (f.val+1) = delta d.val f.val
    unfold delta
    omega
  simpa only [branch_depth,hd] using
    branchWalk anchor e a (branchDepth d) (branchDepth f)

def generalThroughRoots {r L H : Nat} (anchor : Fin r → Fin (L+1)) (e : Nat)
    (a b : Fin r) (d f : Fin H) :
    Walk (graph anchor e) (.inr (a,d)) (.inr (b,f))
      (delta (anchor a).val (anchor b).val+(d.val+1)+(f.val+1)) := by
  have hw := (((rootToArm anchor e a d).reverse).concat
      (trunkWalk (H:=H) anchor e (anchor a) (anchor b))).concat (rootToArm anchor e b f)
  have hh : (d.val+1)+delta (anchor a).val (anchor b).val+(f.val+1) =
      delta (anchor a).val (anchor b).val+(d.val+1)+(f.val+1) := by omega
  rw [←hh]
  exact hw

def oddShortcut {r L H : Nat} (anchor : Fin r → Fin (L+1))
    (a b : Fin r) (d f : Fin H) (hab : a ≠ b) (he : anchor a = anchor b) :
    Walk (graph anchor 1) (.inr (a,d)) (.inr (b,f)) ((d.val+1)+(f.val+1)-1) := by
  have hh : 0 < H := by have h := d.isLt; omega
  let zero : Fin H := ⟨0,hh⟩
  have hedge : (graph anchor 1).adj (.inr (a,zero)) (.inr (b,zero)) := by
    change treeDist anchor 1 (.inr (a,zero)) (.inr (b,zero)) = 1
    simp [treeDist,hab,he,zero,delta]
  have hp := ((sameArm anchor 1 a d zero).concat (unit hedge)).concat
      (sameArm anchor 1 b zero f)
  have hlen : delta d.val zero.val + 1 + delta zero.val f.val =
      (d.val+1)+(f.val+1)-1 := by
    simp [zero,delta]
  rw [←hlen]
  exact hp

def realizeWalk {r L H : Nat} (anchor : Fin r → Fin (L+1)) (e : Nat) (he : e ≤ 1)
    (x y : Vertex r L H) : Walk (graph anchor e) x y (treeDist anchor e x y) := by
  rcases x with x | ⟨a,d⟩ <;> rcases y with y | ⟨b,f⟩
  · exact trunkWalk anchor e x y
  · exact (trunkWalk anchor e x (anchor b)).concat (rootToArm anchor e b f)
  · rw [treeDist_symm]
    exact ((trunkWalk anchor e y (anchor a)).concat (rootToArm anchor e a d)).reverse
  · by_cases hab : a = b
    · subst b
      simpa [treeDist] using sameArm anchor e a d f
    · by_cases ha : anchor a = anchor b
      · by_cases hz : e = 0
        · subst e
          simpa [treeDist,hab] using generalThroughRoots anchor 0 a b d f
        · have h1 : e = 1 := by omega
          subst e
          simpa [treeDist,hab,ha,delta] using oddShortcut anchor a b d f hab ha
      · simpa [treeDist,hab,ha] using generalThroughRoots anchor e a b d f

/-- The displayed coordinate formula is the actual shortest-walk metric,
not merely a metric lower bound on the resulting unweighted graph. -/
def exactDistances {r L H : Nat} (anchor : Fin r → Fin (L+1)) (e : Nat) (he : e ≤ 1) :
    ShortestDistances (graph (H:=H) anchor e) where
  dist := treeDist anchor e
  geodesic := realizeWalk anchor e he
  minimal := fun _ _ _ => lower_of_walk anchor e he

theorem graph_connected {r L H : Nat} (anchor : Fin r → Fin (L+1)) (e : Nat) (he : e ≤ 1) :
    Connected (graph (H:=H) anchor e) :=
  fun x y => ⟨_,⟨realizeWalk anchor e he x y⟩⟩

end TriameterQ3SmallWitness

namespace TriameterQ3SmallWitness
open TriameterQ3Graph

abbrev order (r L H : Nat) := L+1+H*r

def encode {r L H : Nat} : Vertex r L H → Fin (order r L H)
  | .inl t => ⟨t.val,by have h := t.isLt; unfold order; omega⟩
  | .inr (a,d) => ⟨L+1+H*a.val+d.val,by
      have ha : a.val+1 ≤ r := by have h := a.isLt; omega
      have hm := Nat.mul_le_mul_left H ha
      rw [Nat.mul_add,Nat.mul_one] at hm
      have hd := d.isLt
      unfold order
      omega⟩

def decode {r L H : Nat} (t : Fin (order r L H)) : Vertex r L H :=
  if h : t.val < L+1 then .inl ⟨t.val,h⟩
  else
    let b := t.val-(L+1)
    have hr : b < H*r := by have ht := t.isLt; unfold order at ht; dsimp [b]; omega
    have hp : 0 < H := by
      by_cases hz : H = 0
      · simp [hz] at hr
      · omega
    .inr (⟨b/H, (Nat.div_lt_iff_lt_mul hp).2 (by rw [Nat.mul_comm]; exact hr)⟩,
      ⟨b%H,Nat.mod_lt b hp⟩)

theorem encode_decode {r L H : Nat} (t : Fin (order r L H)) :
    encode (decode t) = t := by
  classical
  unfold decode
  split
  · apply Fin.ext
    rfl
  · rename_i hn
    have hh := Nat.mod_add_div (t.val-(L+1)) H
    apply Fin.ext
    change L+1+H*((t.val-(L+1))/H)+(t.val-(L+1))%H = t.val
    omega

theorem decode_encode {r L H : Nat} (t : Vertex r L H) :
    decode (encode t) = t := by
  classical
  rcases t with t | ⟨a,d⟩
  · unfold decode
    have h : (encode (r:=r) (H:=H) (.inl t)).val < L+1 := t.isLt
    rw [dite_eq_left h]
    rfl
  · unfold decode
    have hn : ¬ (encode (L:=L) (.inr (a,d))).val < L+1 := by
      change ¬ L+1+H*a.val+d.val < L+1
      omega
    rw [dite_eq_right hn]
    have hh : L+1 + H*a.val + d.val - (L+1) = d.val+a.val*H := by
      rw [Nat.mul_comm a.val H]
      omega
    have hH : 0 < H := by have h := d.isLt; omega
    have hd : d.val/H = 0 := Nat.div_eq_of_lt d.isLt
    apply congrArg Sum.inr
    apply Prod.ext
    · apply Fin.ext
      change (L+1+H*a.val+d.val-(L+1))/H = a.val
      rw [hh,Nat.add_mul_div_right _ _ hH,hd,Nat.zero_add]
    · apply Fin.ext
      change (L+1+H*a.val+d.val-(L+1))%H = d.val
      rw [hh,Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt d.isLt]

theorem encode_injective {r L H : Nat} : Function.Injective (encode (r:=r) (L:=L) (H:=H)) := by
  intro x y hh
  rw [← decode_encode x,← decode_encode y,hh]

def graphFin {r L H : Nat} (G : SimpleGraph (Vertex r L H)) : SimpleGraph (Fin (order r L H)) where
  adj a b := G.adj (decode a) (decode b)
  symm := G.symm
  loopless := fun a => G.loopless (decode a)

def pullWalk {r L H : Nat} {G : SimpleGraph (Vertex r L H)} {x y : Vertex r L H} {n : Nat}
    (w : Walk G x y n) : Walk (graphFin G) (encode x) (encode y) n where
  point := fun i => encode (w.point i)
  first := congrArg encode w.first
  last := congrArg encode w.last
  step := by
    intro i hi
    change G.adj (decode (encode (w.point i))) (decode (encode (w.point (i+1))))
    rw [decode_encode,decode_encode]
    exact w.step i hi

def pushWalk {r L H : Nat} {G : SimpleGraph (Vertex r L H)} {x y : Fin (order r L H)} {n : Nat}
    (w : Walk (graphFin G) x y n) : Walk G (decode x) (decode y) n where
  point := fun i => decode (w.point i)
  first := congrArg decode w.first
  last := congrArg decode w.last
  step := w.step

def distancesFin {r L H : Nat} {G : SimpleGraph (Vertex r L H)} (M : ShortestDistances G) :
    ShortestDistances (graphFin G) where
  dist x y := M.dist (decode x) (decode y)
  geodesic x y := by
    simpa only [encode_decode] using pullWalk (M.geodesic (decode x) (decode y))
  minimal x y n p := M.minimal (decode x) (decode y) n (pushWalk p)

theorem graphFin_connected {r L H : Nat} {G : SimpleGraph (Vertex r L H)} (M : ShortestDistances G) :
    Connected (graphFin G) :=
  fun x y => ⟨_,⟨(distancesFin M).geodesic x y⟩⟩

theorem exactPackingFin {r L H : Nat} {G : SimpleGraph (Vertex r L H)} {M : ShortestDistances G}
    {k p : Nat} (P : ExactPacking M k p) : ExactPacking (distancesFin M) k p := by
  constructor
  · obtain ⟨f,hf⟩ := P.attained
    refine ⟨fun i => encode (f i),?_⟩
    intro i j hij
    change k < M.dist (decode (encode (f i))) (decode (encode (f j)))
    rw [decode_encode,decode_encode]
    exact hf i j hij
  · intro n f hf
    exact P.upper n (fun i => decode (f i)) hf

theorem unique_exactPacking {V : Type} {G : SimpleGraph V} {M N : ShortestDistances G}
    {k p : Nat} (P : ExactPacking M k p) : ExactPacking N k p := by
  constructor
  · obtain ⟨f,hf⟩ := P.attained
    exact ⟨f,fun i j hij => (N.unique M (f i) (f j)).symm ▸ hf i j hij⟩
  · exact fun n f hf => P.upper n f (fun i j hij => N.unique M (f i) (f j) ▸ hf i j hij)

theorem exactPacking_unique_number {V : Type} {G : SimpleGraph V} {M : ShortestDistances G}
    {k p q : Nat} (P : ExactPacking M k p) (Q : ExactPacking M k q) : p = q := by
  obtain ⟨f,hf⟩ := P.attained
  obtain ⟨g,hg⟩ := Q.attained
  exact Nat.le_antisymm (Q.upper _ f hf) (P.upper _ g hg)

end TriameterQ3SmallWitness

namespace TriameterQ3SmallWitness
open TriameterQ3Graph

def cap {r L H : Nat} (anchor : Fin r → Fin (L+1)) (h : Nat) (c : Fin (L+1)) :
    Vertex r L H → Prop
  | .inl t => delta t.val c.val ≤ h
  | .inr (a,_) => anchor a = c

theorem cap_diameter {r L H : Nat} (anchor : Fin r → Fin (L+1)) (h e k : Nat)
    (hk : 2*h+e = k) (hH : H ≤ h+e) (c : Fin (L+1)) (x y : Vertex r L H)
    (hx : cap anchor h c x) (hy : cap anchor h c y) :
    treeDist anchor e x y ≤ k := by
  rcases x with x | ⟨a,d⟩ <;> rcases y with y | ⟨b,f⟩
  · have hu := delta_triangle x.val c.val y.val
    have hb := delta_symm c.val y.val
    change delta x.val c.val ≤ h at hx
    change delta y.val c.val ≤ h at hy
    change delta x.val y.val ≤ k
    omega
  · change delta x.val c.val ≤ h at hx
    change anchor b = c at hy
    rw [treeDist, hy]
    omega
  · change anchor a = c at hx
    change delta y.val c.val ≤ h at hy
    rw [treeDist, hx, delta_symm]
    omega
  · change anchor a = c at hx
    change anchor b = c at hy
    by_cases hab : a = b
    · subst b
      simp [treeDist,delta]
      omega
    · simp [treeDist,hab,hx,hy,delta]
      omega

def leftEnd (L : Nat) : Fin (L+1) := ⟨0,by omega⟩
def rightEnd (L : Nat) : Fin (L+1) := ⟨L,by omega⟩

theorem fin_injection_bound {p q : Nat} (f : Fin p → Fin q)
    (hf : Function.Injective f) : p ≤ q := by
  have hn : ((List.finRange p).map f).Nodup :=
    List.Pairwise.map f (fun a b ne e => ne (hf e)) (List.nodup_finRange p)
  have hs : (List.finRange p).map f ⊆ List.finRange q := fun {x} _ => List.mem_finRange x
  have hlen := hn.length_le_of_subset hs
  simpa only [List.length_map,List.length_finRange] using hlen

theorem packing_from_distance {V : Type} {G : SimpleGraph V} (M : ShortestDistances G)
    (k p : Nat) (a b : V) (hab : (k+1)*(p-1) ≤ M.dist a b) :
    ∃ f : Fin p → V, IsPacking M k f := by
  let w := M.geodesic a b
  let f : Fin p → V := fun i => w.point ((k+1)*i.val)
  refine ⟨f,?_⟩
  have step (i j : Fin p) (hij : i.val < j.val) : k < M.dist (f i) (f j) := by
    have hi : i.val+1 ≤ j.val := by omega
    have hle : i.val ≤ j.val := by omega
    have hj : j.val ≤ p-1 := by omega
    have hs := Nat.mul_le_mul_left (k+1) hi
    rw [Nat.mul_add,Nat.mul_one] at hs
    have ht := Nat.le_trans (Nat.mul_le_mul_left (k+1) hj) hab
    have hd := M.geodesic_slice_eq a b _ _ (Nat.mul_le_mul_left (k+1) hle) ht
    change M.dist (f i) (f j) = _ at hd
    omega
  intro i j hij
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hne with hij' | hji'
  · exact step i j hij'
  · rw [M.dist_symm]
    exact step j i hji'

theorem packing_upper_by_coloring {V : Type} {G : SimpleGraph V}
    (M : ShortestDistances G) (k p : Nat) (f : V → Fin p)
    (hf : ∀ x y, f x = f y → M.dist x y ≤ k) :
    ∀ s (g : Fin s → V), IsPacking M k g → s ≤ p := by
  intro s g h
  refine fin_injection_bound (fun i => f (g i)) ?_
  intro i j he
  by_cases hne : i = j
  · exact hne
  · exact (Nat.not_lt_of_ge (hf (g i) (g j) he) (h i j hne)).elim

theorem exact_packing_one {r L H : Nat} (anchor : Fin r → Fin (L+1))
    (h e k : Nat) (he : e ≤ 1) (hk : 2*h+e = k) (hH : H ≤ h+e)
    (c : Fin (L+1)) (all : ∀ x : Vertex r L H, cap anchor h c x) :
    ExactPacking (exactDistances (H:=H) anchor e he) k 1 := by
  constructor
  · exact ⟨fun _ => .inl c,fun i j hij => (hij (Subsingleton.elim i j)).elim⟩
  · refine packing_upper_by_coloring _ k 1 (fun _ => 0) ?_
    intro x y _
    exact cap_diameter anchor h e k hk hH c x y (all x) (all y)

theorem exact_packing_two {r L H : Nat} (anchor : Fin r → Fin (L+1))
    (h e k : Nat) (he : e ≤ 1) (hk : 2*h+e = k) (hH : H ≤ h+e)
    (cover : ∀ x : Vertex r L H, cap anchor h (leftEnd L) x ∨ cap anchor h (rightEnd L) x)
    (a b : Vertex r L H) (hab : k+1 ≤ treeDist anchor e a b) :
    ExactPacking (exactDistances (H:=H) anchor e he) k 2 := by
  classical
  constructor
  · apply packing_from_distance _ k 2 a b
    change (k+1)*(2-1) ≤ treeDist anchor e a b
    simpa using hab
  · let f : Vertex r L H → Fin 2 := fun x => if cap anchor h (leftEnd L) x then 0 else 1
    refine packing_upper_by_coloring _ k 2 f ?_
    intro x y heq
    by_cases hx : cap anchor h (leftEnd L) x <;> by_cases hy : cap anchor h (leftEnd L) y
    · exact cap_diameter anchor h e k hk hH _ x y hx hy
    · simp [f,hx,hy] at heq
    · simp [f,hx,hy] at heq
    · exact cap_diameter anchor h e k hk hH _ x y
        ((cover x).resolve_left hx) ((cover y).resolve_left hy)

end TriameterQ3SmallWitness

namespace TriameterQ3SmallWitness
open TriameterQ3Graph TriameterQ3SmallPacking

def anchors {r : Nat} (side : Fin r → Bool) (L : Nat) (i : Fin r) : Fin (L+1) :=
  if side i then rightEnd L else leftEnd L

theorem anchors_ends {r : Nat} (side : Fin r → Bool) (L : Nat) (i : Fin r) :
    anchors side L i = leftEnd L ∨ anchors side L i = rightEnd L := by
  unfold anchors
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

def tip {r : Nat} (L H : Nat) (hH : 0 < H) (i : Fin r) : Vertex r L H :=
  .inr (i,⟨H-1,by omega⟩)

theorem tip_injective {r : Nat} (L H : Nat) (hH : 0 < H) :
    Function.Injective (tip (r:=r) L H hH) := by
  intro i j h
  unfold tip at h
  cases h
  rfl

theorem tip_metric {r : Nat} (side : Fin r → Bool) (L H e k R : Nat) (hH : 0 < H)
    (hk : 2*H = k+e) (hL : (L = 0 ∧ R = 0) ∨ (0 < L ∧ L+e = R))
    (a c : Fin r) (hac : a ≠ c) :
    treeDist (anchors side L) e (tip L H hH a) (tip L H hH c) =
      k + (if side a = side c then 0 else R) := by
  have h0 : ∀ x y : Fin (L+1), L = 0 → x = y := by
    intro x y hz
    apply Fin.ext
    have hx := x.isLt
    have hy := y.isLt
    omega
  have hSame (heq : anchors side L a = anchors side L c) :
      treeDist (anchors side L) e (tip L H hH a) (tip L H hH c) = k := by
    simp [treeDist,tip,hac,heq,delta]
    omega
  by_cases hb : side a = side c
  · have ha : anchors side L a = anchors side L c := by simp [anchors,hb]
    simpa [hb] using hSame ha
  · rcases hL with ⟨hz,hR⟩ | ⟨hp,hR⟩
    · simpa [hR] using hSame (h0 _ _ hz)
    · have hs : (side a = true ∧ side c = false) ∨
          (side a = false ∧ side c = true) := by
        cases ha : side a <;> cases hc : side c <;> simp_all
      have hz : L ≠ 0 := by omega
      rcases hs with ⟨ha,hc⟩ | ⟨ha,hc⟩ <;>
        simp [treeDist,tip,hac,ha,hc,anchors,delta,leftEnd,rightEnd,hz] <;> omega

def armIndex {r : Nat} (i : Fin r) : Fin (r+2) := ⟨i.val,by omega⟩
def extraLeft (r : Nat) : Fin (r+2) := ⟨r,by omega⟩
def extraRight (r : Nat) : Fin (r+2) := ⟨r+1,by omega⟩

theorem armIndex_injective {r : Nat} : Function.Injective (armIndex (r:=r)) := by
  intro i j hh
  have hv := congrArg (@Fin.val (r+2)) hh
  exact Fin.ext hv

def armSide {r : Nat} (s : Fin r → Bool) (i : Fin (r+2)) : Bool :=
  if h : i.val < r then s ⟨i.val,h⟩ else decide (i.val = r+1)

@[simp] theorem armSide_index {r : Nat} (s : Fin r → Bool) (i : Fin r) :
    armSide s (armIndex i) = s i := by
  have hp : (armIndex i).val < r := i.isLt
  rw [armSide,dite_eq_left hp]
  rfl

@[simp] theorem armSide_extraLeft {r : Nat} (s : Fin r → Bool) :
    armSide s (extraLeft r) = false := by simp [armSide,extraLeft]

@[simp] theorem armSide_extraRight {r : Nat} (s : Fin r → Bool) :
    armSide s (extraRight r) = true := by simp [armSide,extraRight,show ¬ r+1 < r by omega]

theorem extra_ne (r : Nat) : extraLeft r ≠ extraRight r := by
  intro h
  have hh := congrArg Fin.val h
  change r = r+1 at hh
  omega

theorem cover_two_ends {r L H h : Nat} (s : Fin r → Bool) (hL : L = 2*h+1) :
    ∀ x : Vertex r L H,
      cap (anchors s L) h (leftEnd L) x ∨ cap (anchors s L) h (rightEnd L) x := by
  intro x
  rcases x with t | ⟨i,d⟩
  · have hThis := t.isLt
    by_cases ht : t.val ≤ h
    · left
      simpa [cap,leftEnd,delta] using ht
    · right
      change delta t.val L ≤ h
      unfold delta
      omega
  · exact anchors_ends s L i

theorem common_end {r H h : Nat} (s : Fin r → Bool) :
    ∀ x : Vertex r 0 H, cap (anchors s 0) h (leftEnd 0) x := by
  have center (t : Fin (0+1)) : t = leftEnd 0 := by
    apply Fin.ext
    have ht := t.isLt
    change t.val = 0
    omega
  intro x
  rcases x with t | ⟨i,d⟩
  · simp [center t,cap,delta]
  · exact center (anchors s 0 i)

/-- Every prescribed terminal cut is realized. The two extra arms are
not among the terminals, and guarantee a crossing geodesic even if the
cut is trivial or there are fewer than two prescribed vertices. -/
theorem native_cut_graph {r : Nat} (s : Fin r → Bool) (k p : Nat)
    (hk : 0 < k) (hp : p = 1 ∨ p = 2) :
    ∃ L H e : Nat, ∃ hH : 0 < H, ∃ he : e ≤ 1,
      let M := exactDistances (H:=H) (anchors (armSide s) L) e he
      let T : Fin r → Vertex (r+2) L H := fun i => tip L H hH (armIndex i)
      ExactPacking M k p ∧ Function.Injective T ∧
      ∀ i j, i ≠ j → M.dist (T i) (T j) =
        k + (if s i = s j then 0 else packingRadius k p) := by
  let h := k/2
  let e := k%2
  let H := h+e
  have he : e ≤ 1 := by dsimp [e]; omega
  have hke : 2*h+e = k := by dsimp [h,e]; omega
  have hH : 0 < H := by dsimp [H]; omega
  have hdepth : 2*H = k+e := by dsimp [H]; omega
  let L := if p = 1 then 0 else 2*h+1
  let a := anchors (armSide s) L
  have hL : (L = 0 ∧ packingRadius k p = 0) ∨ (0 < L ∧ L+e = packingRadius k p) := by
    rcases hp with rfl | rfl
    · exact Or.inl ⟨rfl,by simp [packingRadius]⟩
    · right
      simp [L,packingRadius]
      omega
  have ht := tip_metric (armSide s) L H e k (packingRadius k p) hH hdepth hL
  refine ⟨L,H,e,hH,he,?_,?_,?_⟩
  · change ExactPacking (exactDistances a e he) k p
    rcases hp with rfl | rfl
    · exact exact_packing_one a h e k he hke (Nat.le_refl H) (leftEnd 0)
        (common_end (armSide s))
    · have hD := ht (extraLeft r) (extraRight r) (extra_ne r)
      simp at hD
      have hh : k+1 ≤ k+packingRadius k 2 := by simp [packingRadius]
      exact exact_packing_two a h e k he hke (Nat.le_refl H)
        (cover_two_ends (armSide s) rfl) _ _ (by rwa [hD])
  · exact fun i j hEq => armIndex_injective (tip_injective L H hH hEq)
  · intro i j hij
    have hneq := fun e => hij (armIndex_injective e)
    simpa only [exactDistances,armSide_index] using ht (armIndex i) (armIndex j) hneq

end TriameterQ3SmallWitness

namespace TriameterQ3SmallPacking
open TriameterQ3Graph TriameterQ3SmallWitness

theorem psum_congr_offdiag {n : Nat} {f g : Fin n → Fin n → Nat}
    (h : ∀ i j, i ≠ j → f i j = g i j) : psum n f = psum n g :=
  Nat.le_antisymm (psum_le (fun i j hne => Nat.le_of_eq (h i j hne)))
    (psum_le (fun i j hne => Nat.le_of_eq (h i j hne).symm))

theorem score_of_cut {V : Type} {G : SimpleGraph V} (M : ShortestDistances G)
    {r : Nat} (T : Fin r → V) (w : Fin r → Nat) (s : Fin r → Bool) (k R : Nat)
    (hd : ∀ i j, i ≠ j → M.dist (T i) (T j) = k+(if s i = s j then 0 else R)) :
    terminalScore M T w = k*pairWeight w+R*cutWeight w s := by
  unfold terminalScore pairWeight
  rw [←cut_edge_weight]
  unfold edgeWeight
  rw [←psum_mul_left,←psum_mul_left,←psum_add]
  apply psum_congr_offdiag
  intro i j hij
  rw [hd i j hij]
  by_cases he : s i = s j
  · simp [he,edgeTerm,cutAdj,Nat.mul_comm k]
  · simp [he,edgeTerm,cutAdj,Nat.mul_add,Nat.mul_comm k,Nat.mul_comm R]

theorem cut_graph_fin {r : Nat} (s : Fin r → Bool) (k p : Nat)
    (hk : 0 < k) (hp : p = 1 ∨ p = 2) :
    ∃ (n : Nat) (G : SimpleGraph (Fin n)) (hC : Connected G) (T : Fin r → Fin n),
      Function.Injective T ∧ packingNumber (distancesOfConnected G hC) k = p ∧
      ∀ i j, i ≠ j → (distancesOfConnected G hC).dist (T i) (T j) =
        k+(if s i = s j then 0 else packingRadius k p) := by
  obtain ⟨L,H,e,hH,he,P,hI,hd⟩ := native_cut_graph s k p hk hp
  let A := anchors (armSide s) L
  let G := graphFin (graph (H:=H) A e)
  let M := exactDistances (H:=H) A e he
  let hC : Connected G := graphFin_connected M
  let N := distancesOfConnected G hC
  let U : Fin r → Vertex (r+2) L H := fun i => tip L H hH (armIndex i)
  let T : Fin r → Fin (order (r+2) L H) := fun i => encode (U i)
  have P' : ExactPacking N k p := unique_exactPacking (exactPackingFin P)
  refine ⟨order (r+2) L H,G,hC,T,fun i j heq => hI (encode_injective heq),
    exact_packing_unique N (packingNumber_is_exact N k) P',?_⟩
  intro i j hij
  have h := N.unique (distancesFin M) (T i) (T j)
  change N.dist (T i) (T j) = M.dist (decode (encode (U i))) (decode (encode (U j))) at h
  rw [h,decode_encode,decode_encode]
  exact hd i j hij

/-- For all numbers of distinct prescribed terminals, all k≥1 and p=1 or
p=2, the exact maximum weighted distance sum is k times pair mass plus the
packing radius times maximum cut mass. Natural weights express arbitrary
nonnegative integral terminal weights. -/
theorem weighted_all_terminals_smallpacking_exact {r : Nat} (w : Fin r → Nat) (k p : Nat)
    (hk : 0 < k) (hp : p = 1 ∨ p = 2) :
    (∀ (n : Nat) (G : SimpleGraph (Fin n)) (hC : Connected G) (T : Fin r → Fin n),
      Function.Injective T → packingNumber (distancesOfConnected G hC) k = p →
      terminalScore (distancesOfConnected G hC) T w ≤
        k*pairWeight w + packingRadius k p*largestCutWeight w) ∧
    (∃ (n : Nat) (G : SimpleGraph (Fin n)) (hC : Connected G) (T : Fin r → Fin n),
      Function.Injective T ∧ packingNumber (distancesOfConnected G hC) k = p ∧
      terminalScore (distancesOfConnected G hC) T w =
        k*pairWeight w + packingRadius k p*largestCutWeight w) := by
  constructor
  · intro n G hC T _ hP
    let M := distancesOfConnected G hC
    have hp2 : p ≤ 2 := by rcases hp with rfl | rfl <;> omega
    have P : ExactPacking M k p := hP ▸ packingNumber_is_exact M k
    exact weighted_smallpacking_upper M k p hp2 P T w
  · obtain ⟨s,hs⟩ := largestCutWeight_attained w
    obtain ⟨n,G,hC,T,hI,hP,hd⟩ := cut_graph_fin s k p hk hp
    refine ⟨n,G,hC,T,hI,hP,?_⟩
    rw [score_of_cut (distancesOfConnected G hC) T w s k (packingRadius k p) hd,hs]

end TriameterQ3SmallPacking

namespace TriameterQ3SmallWitness
open TriameterQ3Graph

def color {r L H : Nat} (anchor : Fin r → Fin (L+1)) (h k q : Nat) :
    Vertex r L H → Nat
  | .inl t =>
    if t.val ≤ h then 0
    else if L-t.val ≤ h then q+1
    else 1+(t.val-h-1)/(k+1)
  | .inr (a,_) => if anchor a = leftEnd L then 0 else q+1

theorem interior_quotient {L h k q t : Nat} (hL : L = 2*h+1+(k+1)*q)
    (hleft : ¬ t ≤ h) (hright : ¬ L-t ≤ h) :
    (t-h-1)/(k+1) < q := by
  apply (Nat.div_lt_iff_lt_mul (by omega : 0 < k+1)).2
  rw [Nat.mul_comm]
  omega

theorem color_bounded {r L H : Nat} (anchor : Fin r → Fin (L+1)) (h k q : Nat)
    (hL : L = 2*h+1+(k+1)*q) (x : Vertex r L H) : color anchor h k q x < q+2 := by
  rcases x with t | ⟨a,d⟩
  · simp only [color]
    split
    · omega
    · rename_i hleft
      split
      · omega
      · rename_i hright
        have hh := interior_quotient hL hleft hright
        omega
  · simp only [color]
    split <;> omega

theorem color_zero_cap {r L H : Nat} (anchor : Fin r → Fin (L+1))
    (h k q : Nat) (x : Vertex r L H) (hx : color anchor h k q x = 0) :
    cap anchor h (leftEnd L) x := by
  rcases x with t | ⟨a,d⟩
  · simp only [color] at hx
    simp only [cap,leftEnd,delta, Nat.sub_zero, Nat.zero_sub,Nat.add_zero]
    split at hx
    · assumption
    · split at hx
      · omega
      · have hh : 0 < 1+(t.val-h-1)/(k+1) := by
          rw [Nat.add_comm]
          exact Nat.zero_lt_succ _
        omega
  · simp only [color] at hx
    split at hx
    · exact ‹anchor a = leftEnd L›
    · omega

theorem color_last_cap {r L H : Nat} (anchor : Fin r → Fin (L+1))
    (ends : ∀ a, anchor a = leftEnd L ∨ anchor a = rightEnd L) (h k q : Nat)
    (hL : L = 2*h+1+(k+1)*q) (x : Vertex r L H) (hx : color anchor h k q x = q+1) :
    cap anchor h (rightEnd L) x := by
  rcases x with t | ⟨a,d⟩
  · simp only [color] at hx
    simp only [cap,rightEnd,delta]
    split at hx
    · omega
    · rename_i hleft
      split at hx
      · omega
      · rename_i hright
        have hh := interior_quotient hL hleft hright
        omega
  · simp only [color] at hx
    split at hx
    · omega
    · rename_i hnot
      exact (ends a).resolve_left hnot

theorem color_interior {r L H : Nat} (anchor : Fin r → Fin (L+1))
    (h k q : Nat) (x : Vertex r L H)
    (hz : color anchor h k q x ≠ 0) (hl : color anchor h k q x ≠ q+1) :
    ∃ t : Fin (L+1), x = .inl t ∧ h < t.val ∧
      color anchor h k q x = 1+(t.val-h-1)/(k+1) := by
  rcases x with t | ⟨a,d⟩
  · refine ⟨t,rfl,?_,?_⟩
    · by_cases hle : t.val ≤ h
      · simp [color,hle] at hz
      · omega
    · change (if t.val ≤ h then 0 else if L-t.val ≤ h then q+1 else
          1+(t.val-h-1)/(k+1)) = _
      split
      · rename_i ht
        exact (hz (by simp [color,ht])).elim
      · rename_i ht
        split
        · rename_i hr
          exact (hl (by simp [color,ht,hr])).elim
        · rfl
  · simp only [color] at hz hl
    split at hz
    · exact (hz rfl).elim
    · rename_i he
      simp [he] at hl

theorem within_bucket {k u v : Nat} (hu : u/(k+1) = v/(k+1)) :
    delta u v ≤ k := by
  have hfu := Nat.mod_add_div u (k+1)
  have hfv := Nat.mod_add_div v (k+1)
  have hum := Nat.mod_lt u (by omega : 0 < k+1)
  have hvm := Nat.mod_lt v (by omega : 0 < k+1)
  rw [hu] at hfu
  unfold delta
  omega

theorem color_diameter {r L H : Nat} (anchor : Fin r → Fin (L+1))
    (ends : ∀ a, anchor a = leftEnd L ∨ anchor a = rightEnd L) (h e k q : Nat)
    (hL : L = 2*h+1+(k+1)*q) (hk : 2*h+e = k) (hH : H ≤ h+e)
    (x y : Vertex r L H) (hxy : color anchor h k q x = color anchor h k q y) :
    treeDist anchor e x y ≤ k := by
  by_cases hz : color anchor h k q x = 0
  · exact cap_diameter anchor h e k hk hH _ _ _
      (color_zero_cap anchor h k q x hz)
      (color_zero_cap anchor h k q y (hxy.symm.trans hz))
  · by_cases hl : color anchor h k q x = q+1
    · exact cap_diameter anchor h e k hk hH _ _ _
        (color_last_cap anchor ends h k q hL x hl)
        (color_last_cap anchor ends h k q hL y (hxy.symm.trans hl))
    · obtain ⟨x,rfl,hx,ex⟩ := color_interior anchor h k q x hz hl
      obtain ⟨y,rfl,hy,ey⟩ := color_interior anchor h k q y
        (fun t => hz (hxy.trans t)) (fun t => hl (hxy.trans t))
      have hEq : (x.val-h-1)/(k+1) = (y.val-h-1)/(k+1) := by omega
      have hb := within_bucket hEq
      simp only [treeDist]
      unfold delta at *
      omega

theorem exact_packing_many {r L H : Nat} (anchor : Fin r → Fin (L+1))
    (ends : ∀ a, anchor a = leftEnd L ∨ anchor a = rightEnd L)
    (h e k q : Nat) (he : e ≤ 1) (hL : L = 2*h+1+(k+1)*q)
    (hk : 2*h+e = k) (hH : H ≤ h+e)
    (a b : Vertex r L H) (hab : (k+1)*(q+2-1) ≤ treeDist anchor e a b) :
    ExactPacking (exactDistances (H:=H) anchor e he) k (q+2) := by
  constructor
  · exact packing_from_distance _ k (q+2) a b hab
  · refine packing_upper_by_coloring _ k (q+2)
      (fun x => ⟨color anchor h k q x,color_bounded anchor h k q hL x⟩) ?_
    intro x y heq
    exact color_diameter anchor ends h e k q hL hk hH x y (congrArg Fin.val heq)

end TriameterQ3SmallWitness

namespace TriameterQ3SmallWitness
open TriameterQ3Graph TriameterQ3SmallPacking

theorem common_end' {r H h : Nat} (s : Fin r → Bool) :
    ∀ x : Vertex r 0 H, cap (anchors s 0) h (leftEnd 0) x := by
  have center (t : Fin (0+1)) : t = leftEnd 0 := by
    apply Fin.ext
    have ht := t.isLt
    change t.val = 0
    omega
  intro x
  rcases x with t | ⟨i,d⟩
  · simp [center t,cap,delta]
  · exact center (anchors s 0 i)

theorem native_cut_graph_all {r : Nat} (s : Fin r → Bool) (k p : Nat)
    (hk : 0 < k) (hp : 0 < p) :
    ∃ L H e : Nat, ∃ hH : 0 < H, ∃ he : e ≤ 1,
      let M := exactDistances (H:=H) (anchors (armSide s) L) e he
      let T : Fin r → Vertex (r+2) L H := fun i => tip L H hH (armIndex i)
      ExactPacking M k p ∧ Function.Injective T ∧
      ∀ i j, i ≠ j → M.dist (T i) (T j) =
        k + (if s i = s j then 0 else packingRadius k p) := by
  let h := k/2
  let e := k%2
  let H := h+e
  let q := p-2
  have he : e ≤ 1 := by dsimp [e]; omega
  have hke : 2*h+e = k := by dsimp [h,e]; omega
  have hH : 0 < H := by dsimp [H]; omega
  have hdepth : 2*H = k+e := by dsimp [H]; omega
  let L := if p = 1 then 0 else 2*h+1+(k+1)*q
  let a := anchors (armSide s) L
  have hL : (L = 0 ∧ packingRadius k p = 0) ∨ (0 < L ∧ L+e = packingRadius k p) := by
    by_cases hp1 : p = 1
    · refine Or.inl ⟨by simp [L,hp1],by simp [packingRadius,hp1]⟩
    · right
      have hpq : p-1 = q+1 := by dsimp [q]; omega
      simp only [L,ite_eq_right hp1,packingRadius,hpq,Nat.mul_add,Nat.mul_one]
      omega
  have ht := tip_metric (armSide s) L H e k (packingRadius k p) hH hdepth hL
  refine ⟨L,H,e,hH,he,?_,?_,?_⟩
  · change ExactPacking (exactDistances a e he) k p
    by_cases hp1 : p = 1
    · subst p
      exact exact_packing_one a h e k he hke (Nat.le_refl H) (leftEnd 0) (common_end' (armSide s))
    · have hD := ht (extraLeft r) (extraRight r) (extra_ne r)
      simp at hD
      have hpq : p = q+2 := by dsimp [q]; omega
      have hh : (k+1)*(q+2-1) ≤
          treeDist a e (tip L H hH (extraLeft r)) (tip L H hH (extraRight r)) := by
        rw [show treeDist a e _ _ = k+packingRadius k p from hD,packingRadius,←hpq]
        omega
      rw [hpq]
      exact exact_packing_many a (anchors_ends (armSide s) L) h e k q he
        (ite_eq_right hp1) hke (Nat.le_refl H) _ _ hh
  · exact fun i j hEq => armIndex_injective (tip_injective L H hH hEq)
  · intro i j hij
    have hneq := fun e => hij (armIndex_injective e)
    simpa only [exactDistances,armSide_index] using ht (armIndex i) (armIndex j) hneq

end TriameterQ3SmallWitness

namespace TriameterQ3SmallPacking
open TriameterQ3Graph TriameterQ3SmallWitness

theorem cut_graph_fin_all {r : Nat} (s : Fin r → Bool) (k p : Nat)
    (hk : 0 < k) (hp : 0 < p) :
    ∃ (n : Nat) (G : SimpleGraph (Fin n)) (hC : Connected G) (T : Fin r → Fin n),
      Function.Injective T ∧ packingNumber (distancesOfConnected G hC) k = p ∧
      ∀ i j, i ≠ j → (distancesOfConnected G hC).dist (T i) (T j) =
        k+(if s i = s j then 0 else packingRadius k p) := by
  obtain ⟨L,H,e,hH,he,P,hI,hd⟩ := native_cut_graph_all s k p hk hp
  let A := anchors (armSide s) L
  let G := graphFin (graph (H:=H) A e)
  let M := exactDistances (H:=H) A e he
  let hC : Connected G := graphFin_connected M
  let N := distancesOfConnected G hC
  let U : Fin r → Vertex (r+2) L H := fun i => tip L H hH (armIndex i)
  let T : Fin r → Fin (order (r+2) L H) := fun i => encode (U i)
  have P' : ExactPacking N k p := unique_exactPacking (exactPackingFin P)
  refine ⟨order (r+2) L H,G,hC,T,fun i j heq => hI (encode_injective heq),
    exact_packing_unique N (packingNumber_is_exact N k) P',?_⟩
  intro i j hij
  have h := N.unique (distancesFin M) (T i) (T j)
  change N.dist (T i) (T j) = M.dist (decode (encode (U i))) (decode (encode (U j))) at h
  rw [h,decode_encode,decode_encode]
  exact hd i j hij

theorem lower_weighted_all_p {r : Nat} (w : Fin r → Nat) (k p : Nat) (hk : 0 < k) (hp : 0 < p) :
    ∃ (n : Nat) (G : SimpleGraph (Fin n)) (hC : Connected G) (T : Fin r → Fin n),
      Function.Injective T ∧ packingNumber (distancesOfConnected G hC) k = p ∧
      terminalScore (distancesOfConnected G hC) T w =
        k*pairWeight w+packingRadius k p*largestCutWeight w := by
  obtain ⟨s,hs⟩ := largestCutWeight_attained w
  obtain ⟨n,G,hC,T,hI,hP,hd⟩ := cut_graph_fin_all s k p hk hp
  refine ⟨n,G,hC,T,hI,hP,?_⟩
  rw [score_of_cut (distancesOfConnected G hC) T w s k (packingRadius k p) hd,hs]

end TriameterQ3SmallPacking

/-! Denominator-free, nonnegative integer Fourier–Motzkin lift.
Rows are homogeneous and a solution is allowed a common dilation.
No rational arithmetic, optimization axiom or unsafe solver is used. -/
namespace Q3K5Hull

abbrev Row (n : Nat) := Vector Int n

def isum : (n : Nat) → (Fin n → Int) → Int
  | 0, _ => 0
  | n+1, v => v 0+isum n (fun i => v i.succ)

theorem isum_congr {n : Nat} {u v : Fin n → Int} (h : ∀ i, u i = v i) :
    isum n u = isum n v := congrArg (isum n) (funext h)

theorem isum_le {n : Nat} {u v : Fin n → Int} (h : ∀ i, u i ≤ v i) :
    isum n u ≤ isum n v := by
  induction n with
  | zero => exact Int.le_refl _
  | succ n ih => exact Int.add_le_add (h 0) (ih (fun i => h i.succ))

theorem isum_zero (n : Nat) : isum n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [isum,ih]

theorem isum_add {n : Nat} (u v : Fin n → Int) :
    isum n (fun i => u i+v i) = isum n u+isum n v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [isum,ih]
    omega

theorem isum_mul_left {n : Nat} (d : Int) (v : Fin n → Int) :
    isum n (fun i => d*v i) = d*isum n v := by
  induction n with
  | zero => simp [isum]
  | succ n ih => simp only [isum,ih,Int.mul_add]

theorem isum_single {n : Nat} (j : Fin n) (a : Int) :
    isum n (fun i => if i = j then a else 0) = a := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    refine Fin.cases ?_ ?_ j
    · simp [isum,Fin.succ_ne_zero,isum_zero]
    · intro i
      have h0 : (0 : Fin (n+1)) ≠ i.succ := fun e => Fin.succ_ne_zero i e.symm
      simp only [isum,ite_eq_right h0,Fin.succ_inj,Int.zero_add]
      exact ih i

@[simp] theorem get_ofFn {n : Nat} (f : Fin n → Int) (i : Fin n) :
    (Vector.ofFn f).get i = f i := by
  simp [Vector.get]
  exact congrArg f (Fin.ext rfl)

def zeroRow (n : Nat) : Row n := Vector.ofFn (fun _ => 0)
def plus {n : Nat} (u v : Row n) : Row n := Vector.ofFn (fun i => u.get i+v.get i)
def scale {n : Nat} (d : Int) (u : Row n) : Row n := Vector.ofFn (fun i => d*u.get i)
def clear {n : Nat} (r : Row n) (k : Fin n) : Row n :=
  Vector.ofFn (fun i => if i=k then 0 else r.get i)
def combine {n : Nat} (k : Fin n) (p q : Row n) : Row n :=
  plus (scale (-(q.get k)) (clear p k)) (scale (p.get k) (clear q k))
def eval {n : Nat} (r : Row n) (v : Fin n → Int) : Int :=
  isum n (fun i => r.get i*v i)
def rowValid {n : Nat} (r : Row n) (v : Fin n → Int) : Prop := eval r v ≤ 0
def systemValid {n : Nat} (S : List (Row n)) (v : Fin n → Int) : Prop :=
  ∀ r ∈ S, rowValid r v

theorem eval_zero {n : Nat} (v : Fin n → Int) : eval (zeroRow n) v = 0 := by
  simp [eval,zeroRow,isum_zero]

theorem eval_plus {n : Nat} (u w : Row n) (v : Fin n → Int) :
    eval (plus u w) v = eval u v+eval w v := by
  simp only [eval,plus,get_ofFn,Int.add_mul,isum_add]

theorem eval_scale {n : Nat} (d : Int) (r : Row n) (v : Fin n → Int) :
    eval (scale d r) v = d*eval r v := by
  simp only [eval,scale,get_ofFn,Int.mul_assoc,isum_mul_left]

theorem eval_mono {n : Nat} {u w : Row n} (he : ∀ i, u.get i ≤ w.get i)
    (v : Fin n → Int) (hv : ∀ i, 0 ≤ v i) : eval u v ≤ eval w v := by
  apply isum_le
  intro i
  exact Int.mul_le_mul_of_nonneg_right (he i) (hv i)

def liftVals {n : Nat} (k : Fin n) (v : Fin n → Int) (d t : Int) (i : Fin n) : Int :=
  if i=k then t else d*v i

theorem eval_liftVals {n : Nat} (r : Row n) (k : Fin n) (v : Fin n → Int) (d t : Int) :
    eval r (liftVals k v d t) = d*eval (clear r k) v+r.get k*t := by
  unfold eval
  rw [←isum_mul_left,←isum_single k (r.get k*t),←isum_add]
  apply isum_congr
  intro i
  by_cases h : i=k
  · subst i
    simp [liftVals,clear]
  · simp only [liftVals,clear,get_ofFn,ite_eq_right h,Int.add_zero]
    ac_rfl

structure Frac where
  num : Int
  den : Int
  pos : 0 < den

def Frac.ble (a b : Frac) : Prop := a.num*b.den ≤ b.num*a.den

theorem frac_refl (a : Frac) : a.ble a := Int.le_refl _

theorem frac_total (a b : Frac) : a.ble b ∨ b.ble a := Int.le_total _ _

theorem frac_trans (a b c : Frac) (h₁ : a.ble b) (h₂ : b.ble c) : a.ble c := by
  have H1 := Int.mul_le_mul_of_nonneg_right h₁ (Int.le_of_lt c.pos)
  have H2 := Int.mul_le_mul_of_nonneg_right h₂ (Int.le_of_lt a.pos)
  have H1' : (a.num*c.den)*b.den ≤ (b.num*c.den)*a.den := by
    have hL : a.num*b.den*c.den = (a.num*c.den)*b.den := by ac_rfl
    have hR : b.num*a.den*c.den = (b.num*c.den)*a.den := by ac_rfl
    change a.num*b.den*c.den ≤ b.num*a.den*c.den at H1
    rwa [←hL,←hR]
  have H2' : (b.num*c.den)*a.den ≤ (c.num*a.den)*b.den := by
    have hR : c.num*b.den*a.den = (c.num*a.den)*b.den := by ac_rfl
    change b.num*c.den*a.den ≤ c.num*b.den*a.den at H2
    rwa [←hR]
  exact Int.le_of_mul_le_mul_right (Int.le_trans H1' H2') b.pos

theorem greatest_in_cons {α : Type} (f : α → Frac) (a : α) (l : List α) :
    ∃ g ∈ a::l, ∀ z ∈ a::l, (f z).ble (f g) := by
  induction l generalizing a with
  | nil =>
    exact ⟨a,List.mem_cons_self,fun z hz => by
      have h : z=a := by simpa using hz
      subst z
      exact frac_refl _⟩
  | cons b l ih =>
    obtain ⟨g,hg,hall⟩ := ih b
    rcases frac_total (f a) (f g) with ha|ha
    · exact ⟨g,List.mem_cons_of_mem _ hg,fun z hz => by
        rcases List.mem_cons.1 hz with h|h
        · subst z; exact ha
        · exact hall z h⟩
    · exact ⟨a,List.mem_cons_self,fun z hz => by
        rcases List.mem_cons.1 hz with h|h
        · subst z; exact frac_refl _
        · exact frac_trans _ _ _ (hall z h) ha⟩

def lowerFrac {n : Nat} (k : Fin n) (v : Fin n → Int) (r : Option (Row n)) : Frac :=
  match r with
  | none => ⟨0,1,by decide⟩
  | some a =>
    if h : a.get k < 0 then ⟨eval (clear a k) v,-(a.get k),by omega⟩
    else ⟨0,1,by decide⟩

/-- In the projected system: preserve zero-coefficient rows, compare each
positive row with the floor zero, and compare positive against negative. -/
structure Projected {n : Nat} (k : Fin n) (S : List (Row n)) (v : Fin n → Int) : Prop where
  zero : ∀ r ∈ S, r.get k = 0 → rowValid (clear r k) v
  floor : ∀ r ∈ S, 0 < r.get k → rowValid (clear r k) v
  pair : ∀ r ∈ S, ∀ q ∈ S, 0 < r.get k → q.get k < 0 → rowValid (combine k r q) v

/-- Back-substitution only multiplies all old variables by one positive
integer. The new variable is the numerator of a greatest lower ratio. -/
theorem lift_projection {n : Nat} (k : Fin n) (S : List (Row n)) (v : Fin n → Int)
    (hv : ∀ i, 0 ≤ v i) (H : Projected k S v) :
    ∃ (d : Int) (w : Fin n → Int), 0 < d ∧ (∀ i, 0 ≤ w i) ∧
      (∀ i, i ≠ k → w i = d*v i) ∧ systemValid S w := by
  let L := (S.filter (fun r => decide (r.get k < 0))).map Option.some
  obtain ⟨a,ha,hmax⟩ := greatest_in_cons (lowerFrac k v) none L
  let F := lowerFrac k v a
  have gt0 : 0 ≤ F.num := by
    have hh := hmax none List.mem_cons_self
    change 0*F.den ≤ F.num*1 at hh
    simpa using hh
  have ha' : a = none ∨ ∃ q ∈ S, q.get k < 0 ∧ a = some q := by
    rcases List.mem_cons.1 ha with hh|hh
    · exact Or.inl hh
    · obtain ⟨q,hq,hqa⟩ := List.mem_map.1 hh
      have hh' := List.mem_filter.1 hq
      exact Or.inr ⟨q,hh'.1,of_decide_eq_true hh'.2,hqa.symm⟩
  refine ⟨F.den,liftVals k v F.den F.num,F.pos,?_,?_,?_⟩
  · intro i
    by_cases e : i=k
    · simpa [liftVals,e] using gt0
    · simpa [liftVals,e] using Int.mul_nonneg (Int.le_of_lt F.pos) (hv i)
  · intro i hi
    simp [liftVals,hi]
  · intro r hr
    unfold rowValid
    rw [eval_liftVals]
    by_cases hp : 0 < r.get k
    · rcases ha' with he | ⟨q,hq,hn,he⟩
      · have hh := H.floor r hr hp
        simpa [F,lowerFrac,he,rowValid] using hh
      · have hh := H.pair r hr q hq hp hn
        unfold rowValid combine at hh
        rw [eval_plus,eval_scale,eval_scale] at hh
        simpa [F,lowerFrac,he,hn] using hh
    · by_cases hn : r.get k < 0
      · have mem : some r ∈ none::L := List.mem_cons_of_mem _ (List.mem_map.2
          ⟨r,List.mem_filter.2 ⟨hr,decide_eq_true hn⟩,rfl⟩)
        have hh := hmax _ mem
        change (lowerFrac k v (some r)).ble F at hh
        simp only [lowerFrac,dite_eq_left hn,Frac.ble] at hh
        rw [Int.mul_neg,Int.mul_comm (eval (clear r k) v) F.den] at hh
        rw [Int.mul_comm (r.get k) F.num]
        omega
      · have hz : r.get k = 0 := by omega
        have hh := H.zero r hr hz
        have hb := Int.mul_le_mul_of_nonneg_left hh (Int.le_of_lt F.pos)
        simpa [hz] using hb

end Q3K5Hull

namespace Q3K5Hull

structure Combination where
  multiplier : Nat
  terms : List (Nat × Nat)

def rowAt {n : Nat} (T : List (Row n)) (i : Nat) : Row n :=
  (T[i]?).getD (zeroRow n)

def derive {n : Nat} (T : List (Row n)) : List (Nat × Nat) → Row n
  | [] => zeroRow n
  | (i,a)::l => plus (scale (a : Int) (rowAt T i)) (derive T l)

def deriveAt {n : Nat} (T : List (Row n)) (i : Fin n) : List (Nat × Nat) → Int
  | [] => 0
  | (j,b)::l => (b : Int)*(rowAt T j).get i + deriveAt T i l

theorem derive_get {n : Nat} (T : List (Row n)) (i : Fin n) (l : List (Nat × Nat)) :
    (derive T l).get i = deriveAt T i l := by
  induction l with
  | nil => simp [derive,deriveAt,zeroRow]
  | cons hd tl ih =>
    rcases hd with ⟨j,b⟩
    simp [derive,deriveAt,plus,scale,ih]

def derivationCheck {n : Nat} (T : List (Row n)) (r : Row n) (d : Combination) : Bool :=
  decide (0 < d.multiplier) &&
    (List.finRange n).all (fun i =>
      decide ((d.multiplier : Int)*r.get i ≤ deriveAt T i d.terms))

theorem rowAt_valid {n : Nat} (T : List (Row n)) (v : Fin n → Int)
    (hT : systemValid T v) (i : Nat) : rowValid (rowAt T i) v := by
  unfold rowAt
  cases h : T[i]? with
  | none => simp [rowValid,eval_zero]
  | some r =>
    change rowValid r v
    obtain ⟨hi,hr⟩ := List.getElem?_eq_some_iff.1 h
    exact hT r (List.mem_iff_getElem.2 ⟨i,hi,hr⟩)

theorem derived_valid {n : Nat} (T : List (Row n)) (v : Fin n → Int)
    (hT : systemValid T v) (terms : List (Nat × Nat)) :
    rowValid (derive T terms) v := by
  induction terms with
  | nil => simp [derive,rowValid,eval_zero]
  | cons h t ih =>
    rcases h with ⟨j,b⟩
    have hh := rowAt_valid T v hT j
    unfold rowValid at ih hh ⊢
    simp only [derive,eval_plus,eval_scale]
    have hp := Int.mul_le_mul_of_nonneg_left hh (Int.natCast_nonneg b)
    omega

theorem derivation_sound {n : Nat} (T : List (Row n)) (r : Row n)
    (d : Combination) (h : derivationCheck T r d = true)
    (v : Fin n → Int) (hv : ∀ i, 0 ≤ v i) (hT : systemValid T v) :
    rowValid r v := by
  simp only [derivationCheck,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at h
  have hh := eval_mono (u:=scale (d.multiplier : Int) r) (w:=derive T d.terms)
    (fun i => by simpa only [scale,get_ofFn,derive_get] using h.2 i (List.mem_finRange i)) v hv
  rw [eval_scale] at hh
  have hm : 0 < (d.multiplier : Int) := by omega
  have hp := derived_valid T v hT d.terms
  have h1 : (d.multiplier : Int)*eval r v ≤ (d.multiplier : Int)*0 := by
    simpa only [Int.mul_zero] using Int.le_trans hh hp
  exact Int.le_of_mul_le_mul_left h1 hm

def checkRows {n : Nat} (T : List (Row n)) : List (Row n) → List Combination → Bool
  | [], [] => true
  | r::rs,d::ds => derivationCheck T r d && checkRows T rs ds
  | _,_ => false

theorem checkRows_sound {n : Nat} (T S : List (Row n)) (d : List Combination)
    (h : checkRows T S d = true) (v : Fin n → Int) (hv : ∀ i, 0 ≤ v i)
    (hT : systemValid T v) : systemValid S v := by
  induction S generalizing d with
  | nil => simp [systemValid]
  | cons r rs ih =>
    cases d with
    | nil => simp [checkRows] at h
    | cons a as =>
      simp only [checkRows,Bool.and_eq_true] at h
      intro t ht
      rcases List.mem_cons.1 ht with e|he
      · subst t
        exact derivation_sound T r a h.1 v hv hT
      · exact ih as h.2 t he

theorem checkRows_length {n : Nat} (T : List (Row n)) (R : List (Row n))
    (a : List Combination) (h : checkRows T R a = true) : R.length = a.length := by
  induction R generalizing a with
  | nil =>
    cases a with
    | nil => rfl
    | cons x xs => simp [checkRows] at h
  | cons r rs ih =>
    cases a with
    | nil => simp [checkRows] at h
    | cons x xs =>
      simp only [checkRows,Bool.and_eq_true] at h
      simp [ih xs h.2]

theorem checkRows_append {n : Nat} (T : List (Row n))
    (R S : List (Row n)) (a b : List Combination) (h : R.length = a.length) :
    checkRows T (R++S) (a++b) = (checkRows T R a && checkRows T S b) := by
  induction R generalizing a with
  | nil =>
    cases a with
    | nil => rfl
    | cons x xs => simp at h
  | cons r rs ih =>
    cases a with
    | nil => simp at h
    | cons x xs =>
      have hs : rs.length = xs.length := by simpa using h
      simp only [List.cons_append,checkRows,ih xs hs,Bool.and_assoc]

theorem checkRows_glue {n : Nat} (T R : List (Row n)) (a b : List Combination)
    (L : checkRows T (R.take a.length) a = true)
    (U : checkRows T (R.drop a.length) b = true) :
    checkRows T R (a++b) = true := by
  have he := checkRows_length T (R.take a.length) a L
  have H := checkRows_append T (R.take a.length) (R.drop a.length) a b he
  rwa [List.take_append_drop,L,U] at H

def projectedRows {n : Nat} (k : Fin n) (S : List (Row n)) : List (Row n) :=
  let zeros := S.filter (fun r => decide (r.get k = 0))
  let pos := S.filter (fun r => decide (0 < r.get k))
  let neg := S.filter (fun r => decide (r.get k < 0))
  zeros.map (fun r => clear r k) ++
    pos.flatMap (fun r => clear r k :: neg.map (combine k r))

theorem projectedRows_sound {n : Nat} (k : Fin n) (S : List (Row n)) (v : Fin n → Int)
    (h : systemValid (projectedRows k S) v) : Projected k S v := by
  constructor
  · intro r hr hz
    apply h
    apply List.mem_append_left
    exact List.mem_map.2 ⟨r,List.mem_filter.2 ⟨hr,decide_eq_true hz⟩,rfl⟩
  · intro r hr hp
    apply h
    apply List.mem_append_right
    apply List.mem_flatMap.2
    exact ⟨r,List.mem_filter.2 ⟨hr,decide_eq_true hp⟩,List.mem_cons_self⟩
  · intro r hr q hq hp hn
    apply h
    apply List.mem_append_right
    apply List.mem_flatMap.2
    refine ⟨r,List.mem_filter.2 ⟨hr,decide_eq_true hp⟩,List.mem_cons_of_mem _ ?_⟩
    exact List.mem_map.2 ⟨q,List.mem_filter.2 ⟨hq,decide_eq_true hn⟩,rfl⟩

structure Stage (n : Nat) where
  pivot : Fin n
  keep : List (Row n)
  deriveRows : List Combination

def stageCheck {n : Nat} (S : List (Row n)) (p : Stage n) : Bool :=
  checkRows p.keep (projectedRows p.pivot S) p.deriveRows

def finalSystem {n : Nat} (S : List (Row n)) : List (Stage n) → List (Row n)
  | [] => S
  | p::ps => finalSystem p.keep ps

def checkedChain {n : Nat} (S : List (Row n)) : List (Stage n) → Prop
  | [] => True
  | p::ps => stageCheck S p = true ∧ checkedChain p.keep ps

theorem verified_chain_lift {n : Nat} (preserved : Fin n → Prop)
    (S : List (Row n)) (stages : List (Stage n))
    (certified : checkedChain S stages)
    (unused : ∀ p ∈ stages, ¬ preserved p.pivot)
    (v : Fin n → Int) (hv : ∀ i, 0 ≤ v i) (hV : systemValid (finalSystem S stages) v) :
    ∃ (d : Int) (w : Fin n → Int), 0 < d ∧ (∀ i, 0 ≤ w i) ∧
      (∀ i, preserved i → w i = d*v i) ∧ systemValid S w := by
  induction stages generalizing S with
  | nil => exact ⟨1,v,by decide,hv,fun i _ => (Int.one_mul _).symm,hV⟩
  | cons s ss ih =>
    obtain ⟨d,v',hd,hv',dil,hgood⟩ := ih s.keep certified.2
      (fun p h => unused p (List.mem_cons_of_mem _ h)) hV
    have hProj := checkRows_sound s.keep (projectedRows s.pivot S) s.deriveRows
      certified.1 v' hv' hgood
    obtain ⟨b,w,hb,hw,bs,hres⟩ := lift_projection s.pivot S v' hv'
      (projectedRows_sound s.pivot S v' hProj)
    refine ⟨b*d,w,Int.mul_pos hb hd,hw,?_,hres⟩
    intro i hi
    have he : i ≠ s.pivot := fun e => unused s List.mem_cons_self (e ▸ hi)
    rw [bs i he,dil i hi,Int.mul_assoc]

end Q3K5Hull

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

theorem exact_from_upper {r : Nat} (w : Fin r → Nat) (k p : Nat) (hk : 0 < k) (hp : 0 < p)
    (hupper : ∀ (n : Nat) (G : SimpleGraph (Fin n)) (M : ShortestDistances G)
      (T : Fin r → Fin n), ExactPacking M k p →
      terminalScore M T w ≤ k*pairWeight w+packingRadius k p*largestCutWeight w) :
    ∃ C : Nat, IsCutMaximum w C ∧
      ExactWeightedValue w k p (k*pairWeight w+packingRadius k p*C) := by
  refine ⟨largestCutWeight w,⟨largestCutWeight_bounds w,largestCutWeight_attained w⟩,?_,?_⟩
  · intro n G _ M T _ hP
    exact hupper n G M T hP
  · obtain ⟨n,G,hC,T,hI,hP,hScore⟩ := lower_weighted_all_p w k p hk hp
    let M := distancesOfConnected G hC
    refine ⟨n,G,hC,M,T,hI,?_,hScore⟩
    exact hP ▸ packingNumber_is_exact M k

/-- Exact weighted distance sum for arbitrary prescribed terminal count
and packing number at most four. -/
theorem weighted_extremum_up_to_four {r : Nat} (w : Fin r → Nat) (k p : Nat)
    (hk : 0 < k) (hp : 0 < p) (hbound : p ≤ 4) :
    ∃ C : Nat, IsCutMaximum w C ∧
      ExactWeightedValue w k p (k*pairWeight w+packingRadius k p*C) := by
  apply exact_from_upper w k p hk hp
  intro _ _ M T hP
  exact TriameterQ3PackingWindows.weighted_p_le_four_upper M k p hbound hP T w

end TriameterQ3Public
