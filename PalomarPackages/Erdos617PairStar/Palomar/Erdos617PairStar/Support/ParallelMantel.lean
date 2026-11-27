module

public import Std
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
A Mathlib-free graph ledger for the near-Mantel piece of the h=1 parallel-bundle argument.
A simple graph is a symmetric, loopless Bool relation. A finite induced vertex set is
represented by a list with no duplicates. Edges are counted once, in list order.
-/
namespace ParallelMantel

universe u
variable {V : Type u}

def degree (g : V → V → Bool) (v : V) (W : List V) : Nat :=
  (W.filter (g v)).length

def cut (g : V → V → Bool) (X Y : List V) : Nat :=
  (X.map fun x => degree g x Y).sum

def edges (g : V → V → Bool) : List V → Nat
  | [] => 0
  | x :: X => degree g x X + edges g X

def Symmetric (g : V → V → Bool) : Prop := ∀ v w, g v w = g w v
def Loopless (g : V → V → Bool) : Prop := ∀ v, g v v = false
def TriangleFree (g : V → V → Bool) : Prop :=
  ∀ x y z, g x y = true → g x z = true → g y z = false

private theorem degree_cons (g : V → V → Bool) (v x : V) (Xs : List V) :
    degree g v (x :: Xs) = (if g v x then 1 else 0) + degree g v Xs := by
  cases h : g v x <;> simp [degree, h] <;> omega

private theorem degree_append (g : V → V → Bool) (v : V) (X Y : List V) :
    degree g v (X ++ Y) = degree g v X + degree g v Y := by
  simp [degree, List.filter_append]

private theorem cut_append_left (g : V → V → Bool) (X Y Z : List V) :
    cut g (X ++ Y) Z = cut g X Z + cut g Y Z := by
  simp [cut, List.sum_append]

private theorem cut_cons_left (g : V → V → Bool) (x : V) (X Y : List V) :
    cut g (x :: X) Y = degree g x Y + cut g X Y := rfl

private theorem cut_cons_right (g : V → V → Bool) (symm : Symmetric g)
    (X : List V) (y : V) (Y : List V) :
    cut g X (y :: Y) = degree g y X + cut g X Y := by
  induction X with
  | nil => simp [cut, degree]
  | cons x X ih =>
    rw [cut_cons_left, cut_cons_left, ih, degree_cons, degree_cons, symm x y]
    omega

private theorem cut_comm (g : V → V → Bool) (symm : Symmetric g) (X Y : List V) :
    cut g X Y = cut g Y X := by
  induction X with
  | nil =>
    have h (W : List V) : cut g W [] = 0 := by
      induction W with
      | nil => rfl
      | cons x W ih => rw [cut_cons_left, ih]; rfl
    change 0 = cut g Y []
    rw [h]
  | cons x X ih => rw [cut_cons_left, cut_cons_right g symm, ih]

private theorem cut_append_right (g : V → V → Bool) (symm : Symmetric g)
    (X Y Z : List V) : cut g X (Y ++ Z) = cut g X Y + cut g X Z := by
  rw [cut_comm g symm X, cut_append_left, cut_comm g symm Y, cut_comm g symm Z]

theorem twice_edges (g : V → V → Bool) (symm : Symmetric g) (loop : Loopless g)
    (W : List V) : cut g W W = 2 * edges g W := by
  induction W with
  | nil => rfl
  | cons x X ih =>
    rw [cut_cons_left, degree_cons, loop x, cut_cons_right g symm, ih, edges]
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
    omega

private theorem degree_perm (g : V → V → Bool) (x : V) {A B : List V}
    (perm : A.Perm B) : degree g x A = degree g x B :=
  (perm.filter (g x)).length_eq

private theorem cut_perm_right (g : V → V → Bool) (W : List V) {A B : List V}
    (perm : A.Perm B) : cut g W A = cut g W B := by
  induction W with
  | nil => rfl
  | cons x W ih => rw [cut_cons_left, cut_cons_left, degree_perm g x perm, ih]

theorem edges_perm (g : V → V → Bool) (symm : Symmetric g) (loop : Loopless g)
    {A B : List V} (perm : A.Perm B) : edges g A = edges g B := by
  have h : cut g A A = cut g B B := by
    rw [cut_perm_right g A perm, cut_comm g symm A B, cut_perm_right g B perm]
  rw [twice_edges g symm loop, twice_edges g symm loop] at h
  omega

theorem edges_append (g : V → V → Bool) (A B : List V) :
    edges g (A ++ B) = edges g A + edges g B + cut g A B := by
  induction A with
  | nil => simp [edges, cut]
  | cons x A ih =>
    simp only [List.cons_append, edges, cut_cons_left, degree_append, ih]
    omega

private theorem cut_le_const (g : V → V → Bool) (X Y : List V) (d : Nat)
    (h : ∀ x ∈ X, degree g x Y ≤ d) : cut g X Y ≤ X.length * d := by
  induction X with
  | nil => simp [cut]
  | cons x X ih =>
    rw [cut_cons_left, List.length_cons, Nat.add_mul]
    have h₁ := h x (by simp)
    have h₂ := ih (fun z hz => h z (List.mem_cons_of_mem _ hz))
    omega

private theorem edges_zero (g : V → V → Bool) (X : List V)
    (h : ∀ x ∈ X, ∀ y ∈ X, g x y = false) : edges g X = 0 := by
  induction X with
  | nil => rfl
  | cons x X ih =>
    have d0 : degree g x X = 0 := by
      have eq0 : X.filter (g x) = [] := by
        cases e : X.filter (g x) with
        | nil => rfl
        | cons y ys =>
          have p : y ∈ X.filter (g x) := by rw [e]; simp
          obtain ⟨ym, gy⟩ := List.mem_filter.mp p
          have q := h x (by simp) y (List.mem_cons_of_mem x ym)
          rw [q] at gy
          contradiction
      simp [degree, eq0]
    rw [edges, d0, ih (fun a ha b hb =>
      h a (List.mem_cons_of_mem x ha) b (List.mem_cons_of_mem x hb))]

/-- Exact finite graph inequality underlying the h=1 rigidity proof:
given a maximum-degree vertex, its neighborhood is independent and the
number of edges plus the number internal to its nonneighbors is at most
its degree times the number of nonneighbors. The vertex is a nonneighbor. -/
theorem max_neighbor_partition_bound (g : V → V → Bool) (symm : Symmetric g)
    (loop : Loopless g) (triangle : TriangleFree g) (W : List V) (v : V)
    (maxv : ∀ x ∈ W, degree g x W ≤ degree g v W) :
    let A := W.filter (g v)
    let B := W.filter (fun x => !g v x)
    edges g W + edges g B ≤ A.length * B.length := by
  dsimp only
  let A := W.filter (g v)
  let B := W.filter (fun x => !g v x)
  change edges g W + edges g B ≤ A.length * B.length
  have perm : (A ++ B).Perm W := List.filter_append_perm _ _
  have aind : edges g A = 0 := edges_zero g A (by
    intro x hx y hy
    exact triangle v x y (List.mem_filter.mp hx).2 (List.mem_filter.mp hy).2)
  have f := cut_le_const g B W A.length (by
    intro x hx
    exact maxv x (List.mem_filter.mp hx).1)
  rw [← cut_perm_right g B perm, cut_append_right g symm, twice_edges g symm loop] at f
  have he := edges_append g A B
  rw [edges_perm g symm loop perm, aind, Nat.zero_add, cut_comm g symm A B] at he
  rw [Nat.mul_comm A.length B.length]
  omega

private theorem perm_two_first {W : List V} {x y : V}
    (hx : x ∈ W) (hy : y ∈ W) (ne : x ≠ y) :
    ∃ L : List V, W.Perm (x :: y :: L) := by
  obtain ⟨P,Q,hW⟩ := List.append_of_mem hx
  have p : W.Perm (x :: (P ++ Q)) := by
    rw [hW]
    exact List.perm_middle
  have hyn : y ∈ P ++ Q := by
    have h := p.mem_iff.mp hy
    simpa [Ne.symm ne] using h
  obtain ⟨L,M,hPQ⟩ := List.append_of_mem hyn
  have q : (P ++ Q).Perm (y :: (L ++ M)) := by
    rw [hPQ]
    exact List.perm_middle
  exact ⟨L ++ M, p.trans (q.cons x)⟩

private theorem degree_near_pair_loss (g : V → V → Bool) (triangle : TriangleFree g)
    {x y : V} (hxy : g x y = true) (A : List V) :
    degree g x A + degree g y A ≤ A.length := by
  induction A with
  | nil => simp [degree]
  | cons a A ih =>
    simp only [degree_cons, List.length_cons]
    cases hx : g x a with
    | false =>
      cases hy : g y a <;> simp <;> omega
    | true =>
      have hy := triangle x y a hxy hx
      simp [hy]
      omega

private theorem cut_perm_left (g : V → V → Bool) (symm : Symmetric g)
    (W : List V) {A B : List V} (perm : A.Perm B) : cut g A W = cut g B W := by
  rw [cut_comm g symm A, cut_perm_right g W perm, cut_comm g symm W]

private theorem loss_from_internal_edge (g : V → V → Bool) (symm : Symmetric g)
    (loop : Loopless g) (triangle : TriangleFree g) (A B : List V)
    {x y : V} (hx : x ∈ B) (hy : y ∈ B) (hxy : g x y = true) :
    cut g A B + A.length ≤ A.length * B.length := by
  have dxy := degree_near_pair_loss g triangle hxy A
  have ne : x ≠ y := by
    intro eq
    subst y
    rw [loop] at hxy
    contradiction
  obtain ⟨L,perm⟩ := perm_two_first hx hy ne
  have f := cut_le_const g L A A.length (fun z _ => List.length_filter_le (g z) A)
  rw [cut_comm g symm A B, cut_perm_left g symm A perm]
  simp only [cut_cons_left]
  have bl := perm.length_eq
  simp only [List.length_cons] at bl
  rw [bl, Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.mul_comm A.length L.length]
  omega

private theorem has_edge_of_edges_pos (g : V → V → Bool) (W : List V)
    (pos : 0 < edges g W) : ∃ x ∈ W, ∃ y ∈ W, g x y = true := by
  classical
  apply Classical.byContradiction
  intro absent
  apply (Nat.ne_of_gt pos) (edges_zero g W ?_)
  intro x hx y hy
  cases p : g x y with
  | false => rfl
  | true => exact False.elim (absent ⟨x,hx,y,hy,p⟩)

private theorem no_edges_imp_independent (g : V → V → Bool) (symm : Symmetric g)
    (loop : Loopless g) (W : List V) (no : edges g W = 0) :
    ∀ x ∈ W, ∀ y ∈ W, g x y = false := by
  intro x hx y hy
  cases h : g x y with
  | false => rfl
  | true =>
    exfalso
    have ne : x ≠ y := by
      intro eq
      subst y
      rw [loop] at h
      contradiction
    obtain ⟨L,perm⟩ := perm_two_first hx hy ne
    rw [edges_perm g symm loop perm, edges, degree_cons, h] at no
    simp at no

private theorem max_degree_exists (g : V → V → Bool) (W : List V)
    (nonempty : W ≠ []) : ∃ v ∈ W, ∀ x ∈ W, degree g x W ≤ degree g v W := by
  cases h : (W.map (fun x => degree g x W)).max? with
  | none =>
    have q := List.max?_eq_none_iff.mp h
    simp [nonempty] at q
  | some d =>
    have ⟨dm, high⟩ := List.max?_eq_some_iff.mp h
    obtain ⟨v,vm,ve⟩ := List.mem_map.mp dm
    refine ⟨v,vm,?_⟩
    intro x xm
    rw [ve]
    exact high _ (List.mem_map.mpr ⟨x,xm,rfl⟩)

private theorem square_gap {a b R : Nat} (h : a + b = 2 * R) :
    ∃ k : Nat, a * b + k * k = R * R ∧
      ((a + k = R ∧ b = R + k) ∨ (b + k = R ∧ a = R + k)) := by
  have base (x k : Nat) : x * (x + k + k) + k * k = (x + k) * (x + k) := by
    simp only [Nat.mul_add, Nat.add_mul]
    rw [Nat.mul_comm k x]
    omega
  by_cases le : a ≤ b
  · let k := R - a
    have ar : a + k = R := by dsimp [k]; omega
    have br : b = R + k := by omega
    refine ⟨k, ?_, Or.inl ⟨ar,br⟩⟩
    rw [br, ← ar]
    exact base a k
  · let k := R - b
    have br : b + k = R := by dsimp [k]; omega
    have ar : a = R + k := by omega
    refine ⟨k, ?_, Or.inr ⟨br,ar⟩⟩
    rw [Nat.mul_comm a b, ar, ← br]
    exact base b k

private theorem cut_and_missing (g : V → V → Bool) (A B : List V) :
    cut g A B + cut (fun x y => !g x y) A B = A.length * B.length := by
  have row (x : V) : degree g x B + degree (fun x y => !g x y) x B = B.length := by
    simpa [degree] using (List.filter_append_perm (g x) B).length_eq
  induction A with
  | nil => simp [cut]
  | cons x A ih =>
    rw [cut_cons_left, cut_cons_left, List.length_cons, Nat.add_mul, Nat.one_mul]
    have h := row x
    omega

/-- Classification of the outsider graph in the h=1 boundary proof.
A triangle-free graph on 2R vertices with at least R²−1 edges has a partition
into independent parts. Either both sides have size R and at most one
crossing is absent, or the sides have sizes R−1, R+1 with full crossings.
The vertex-list permutation names the actual partition, and the missing
count is taken in the complementary Boolean relation, not an abstract variable. -/
theorem near_mantel_even (g : V → V → Bool) (symm : Symmetric g) (loop : Loopless g)
    (triangle : TriangleFree g) (W : List V) (R : Nat) (hr : 3 ≤ R)
    (size : W.length = 2 * R) (density : R * R ≤ edges g W + 1) :
    ∃ A B : List V, (A ++ B).Perm W ∧
      (∀ x ∈ A, ∀ y ∈ A, g x y = false) ∧
      (∀ x ∈ B, ∀ y ∈ B, g x y = false) ∧
      ((A.length = R ∧ B.length = R ∧ cut (fun x y => !g x y) A B ≤ 1) ∨
       (((A.length + 1 = R ∧ B.length = R + 1) ∨
         (B.length + 1 = R ∧ A.length = R + 1)) ∧ cut (fun x y => !g x y) A B = 0)) := by
  have nonempty : W ≠ [] := by
    intro eq
    rw [eq] at size
    simp at size
    omega
  obtain ⟨v,_,maxv⟩ := max_degree_exists g W nonempty
  let A := W.filter (g v)
  let B := W.filter (fun x => !g v x)
  have perm : (A ++ B).Perm W := List.filter_append_perm _ _
  have hab : A.length + B.length = 2 * R := by
    simpa [size] using perm.length_eq
  have aind : ∀ x ∈ A, ∀ y ∈ A, g x y = false := by
    intro x hx y hy
    exact triangle v x y (List.mem_filter.mp hx).2 (List.mem_filter.mp hy).2
  have cap : edges g W + edges g B ≤ A.length * B.length :=
    max_neighbor_partition_bound g symm loop triangle W v maxv
  obtain ⟨k, gap, sides⟩ := square_gap hab
  have bound : k * k + edges g B ≤ 1 := by omega
  have cutEq := edges_append g A B
  rw [edges_perm g symm loop perm, edges_zero g A aind, Nat.zero_add] at cutEq
  have bzero : edges g B = 0 := by
    apply Classical.byContradiction
    intro bne
    have bp : 0 < edges g B := Nat.pos_of_ne_zero bne
    have kzero : k = 0 := by
      have ksq : k * k = 0 := by omega
      exact (Nat.mul_eq_zero.mp ksq).elim id id
    have lengths : A.length = R ∧ B.length = R := by
      rcases sides with s | s <;> simp_all
    obtain ⟨x,hx,y,hy,hxy⟩ := has_edge_of_edges_pos g B bp
    have loss := loss_from_internal_edge g symm loop triangle A B hx hy hxy
    rw [lengths.1, lengths.2] at loss
    omega
  refine ⟨A,B,perm,aind,no_edges_imp_independent g symm loop B bzero,?_⟩
  have miss := cut_and_missing g A B
  have ksmall : k ≤ 1 := by
    have ksq : k * k ≤ 1 * 1 := by omega
    exact Nat.mul_self_le_mul_self_iff.mp ksq
  by_cases kz : k = 0
  · left
    have lengths : A.length = R ∧ B.length = R := by
      rcases sides with s | s <;> simp_all
    exact ⟨lengths.1,lengths.2,by omega⟩
  · right
    have ko : k = 1 := by omega
    refine ⟨?_,?_⟩
    · simpa [ko] using sides
    · have ks : k * k = 1 := by simp [ko]
      omega

/-- The even-order Mantel bound, reusing the same exact graph ledger. -/
theorem mantel_even (g : V → V → Bool) (symm : Symmetric g) (loop : Loopless g)
    (triangle : TriangleFree g) (W : List V) (R : Nat)
    (size : W.length = 2 * R) : edges g W ≤ R * R := by
  cases W with
  | nil => simp [edges]
  | cons w W =>
    obtain ⟨v,_,maxv⟩ := max_degree_exists g (w :: W) (by simp)
    let A := (w :: W).filter (g v)
    let B := (w :: W).filter (fun x => !g v x)
    have perm : (A ++ B).Perm (w :: W) := List.filter_append_perm _ _
    have hab : A.length + B.length = 2 * R := by
      have raw := perm.length_eq
      rw [List.length_append, size] at raw
      exact raw
    have cap : edges g (w :: W) + edges g B ≤ A.length * B.length :=
      max_neighbor_partition_bound g symm loop triangle (w :: W) v maxv
    obtain ⟨k, gap, _⟩ := square_gap hab
    omega

/-- A finite graph bridge for the shortest odd cycle argument. Supply a genuine
cycle perimeter ledger and the consequence of shortestness that outsiders have
at most two cycle neighbors. This bridge then forces length five, proves the
outsider edge floor, and shows that the combined outsider/cycle-hit deficit is
at most one. The shortestness and its graph consequences are not asserted here. -/
theorem cycle_ledger_to_pentagon (g : V → V → Bool) (symm : Symmetric g)
    (loop : Loopless g) (triangle : TriangleFree g) (W C O : List V)
    (r : Nat) (hr : 12 ≤ r) (perm : (C ++ O).Perm W)
    (size : W.length = 2 * r - 1)
    (density : (r-1) * (r-1) ≤ edges g W)
    (odd : ∃ k : Nat, C.length = 2 * k + 1) (cycle_length : 5 ≤ C.length)
    (perimeter : edges g C = C.length) (outsider : ∀ x ∈ O, degree g x C ≤ 2) :
    C.length = 5 ∧ O.length = 2 * (r-3) ∧
      (r-3) * (r-3) ≤ edges g O + 1 ∧
      edges g O ≤ (r-3) * (r-3) ∧
      (r-3) * (r-3) + 4 * (r-3) ≤ edges g O + cut g O C + 1 := by
  obtain ⟨k,klen⟩ := odd
  have len := perm.length_eq
  rw [List.length_append, size] at len
  have hO : O.length = 2 * (r-k-1) := by omega
  have om := mantel_even g symm loop triangle O (r-k-1) hO
  have oc := cut_le_const g O C 2 outsider
  have count := edges_append g C O
  rw [edges_perm g symm loop perm, perimeter, cut_comm g symm C O] at count
  have c5 : C.length = 5 := by
    apply Classical.byContradiction
    intro nc
    have kb : 3 ≤ k := by omega
    let t := r-4
    have hsmall : r-k-1 ≤ t := by dsimp [t]; omega
    have od := Nat.mul_self_le_mul_self_iff.mpr hsmall
    have hp : r-1 = t+3 := by dsimp [t]; omega
    have hp2 : (r-1)*(r-1) = t*t + 6*t + 9 := by
      rw [hp, Nat.mul_add, Nat.add_mul, Nat.add_mul, Nat.mul_comm t 3]
      omega
    omega
  have olen : O.length = 2 * (r-3) := by omega
  have emax := mantel_even g symm loop triangle O (r-3) olen
  let t := r-3
  have hp : r-1 = t+2 := by dsimp [t]; omega
  have hp2 : (r-1)*(r-1) = t*t + 4*t + 4 := by
    rw [hp, Nat.mul_add, Nat.add_mul, Nat.add_mul, Nat.mul_comm t 2]
    omega
  change O.length = 2 * t at olen
  change edges g O ≤ t*t at emax
  refine ⟨c5,olen,?_,emax,?_⟩
  · change t*t ≤ edges g O + 1
    rw [olen] at oc
    omega
  · change t*t + 4*t ≤ edges g O + cut g O C + 1
    omega

/-- Integrated boundary adapter. With the exact graph consequences of a
shortest odd cycle in hand, this recovers its length-five and cross-deficit
cases, keeping the single unit of slack shared rather than spent twice. -/
theorem pentagon_outside_partition (g : V → V → Bool) (symm : Symmetric g)
    (loop : Loopless g) (triangle : TriangleFree g) (W C O : List V)
    (r : Nat) (hr : 12 ≤ r) (perm : (C ++ O).Perm W)
    (size : W.length = 2 * r - 1)
    (density : (r-1) * (r-1) ≤ edges g W)
    (odd : ∃ k : Nat, C.length = 2 * k + 1) (cycle_length : 5 ≤ C.length)
    (perimeter : edges g C = C.length) (outsider : ∀ x ∈ O, degree g x C ≤ 2) :
    C.length = 5 ∧ ∃ A B : List V, (A ++ B).Perm O ∧
      (∀ x ∈ A, ∀ y ∈ A, g x y = false) ∧
      (∀ x ∈ B, ∀ y ∈ B, g x y = false) ∧
      let R := r - 3
      let missing := cut (fun x y => !g x y) A B
      let hits := cut g O C
      ((A.length = R ∧ B.length = R ∧ missing + (4 * R - hits) ≤ 1) ∨
       (((A.length + 1 = R ∧ B.length = R + 1) ∨
         (B.length + 1 = R ∧ A.length = R + 1)) ∧ missing = 0 ∧ hits = 4 * R)) := by
  obtain ⟨pent, outside_len, outside_low, _, joint⟩ :=
    cycle_ledger_to_pentagon g symm loop triangle W C O r hr perm size density
      odd cycle_length perimeter outsider
  let R := r - 3
  have Rbig : 3 ≤ R := by dsimp [R]; omega
  obtain ⟨A,B,part,indA,indB,cases⟩ :=
    near_mantel_even g symm loop triangle O R Rbig outside_len outside_low
  refine ⟨pent,A,B,part,indA,indB,?_⟩
  let miss := cut (fun x y => !g x y) A B
  let hits := cut g O C
  change ((A.length = R ∧ B.length = R ∧ miss + (4 * R - hits) ≤ 1) ∨
       (((A.length + 1 = R ∧ B.length = R + 1) ∨
         (B.length + 1 = R ∧ A.length = R + 1)) ∧ miss = 0 ∧ hits = 4 * R))
  have edgecut := edges_append g A B
  rw [edges_perm g symm loop part, edges_zero g A indA, edges_zero g B indB] at edgecut
  simp only [Nat.add_zero, Nat.zero_add] at edgecut
  have exactCut := cut_and_missing g A B
  rw [← edgecut] at exactCut
  change edges g O + miss = A.length * B.length at exactCut
  change R * R + 4 * R ≤ edges g O + hits + 1 at joint
  have hbound := cut_le_const g O C 2 outsider
  rw [outside_len] at hbound
  change hits ≤ (2 * R) * 2 at hbound
  rcases cases with ⟨asize,bsize,_⟩ | ⟨sizes,zero⟩
  · left
    refine ⟨asize,bsize,?_⟩
    rw [asize,bsize] at exactCut
    omega
  · right
    refine ⟨sizes,zero,?_⟩
    change miss = 0 at zero
    have sizeProduct (a b : Nat) (small : a + 1 = R) (big : b = R + 1) :
        a * b + 1 = R * R := by
      rw [big, ← small]
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
      omega
    have p : A.length * B.length + 1 = R * R := by
      rcases sizes with ⟨h1,h2⟩ | ⟨h1,h2⟩
      · exact sizeProduct _ _ h1 h2
      · rw [Nat.mul_comm]
        exact sizeProduct _ _ h1 h2
    omega

end ParallelMantel

#print axioms ParallelMantel.twice_edges
#print axioms ParallelMantel.edges_perm
#print axioms ParallelMantel.max_neighbor_partition_bound
#print axioms ParallelMantel.near_mantel_even
#print axioms ParallelMantel.mantel_even
#print axioms ParallelMantel.cycle_ledger_to_pentagon
#print axioms ParallelMantel.pentagon_outside_partition
