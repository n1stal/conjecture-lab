module

public import Palomar.Erdos617PairStarDouble.Support.OddExistence
public import Lean.Elab.Tactic.Omega

@[expose] public section

namespace ParallelMantel

universe u
variable {V : Type u}

def InducedIndependenceCap (g : V→V→Bool) (W : List V) (k : Nat) : Prop :=
  ∀ I : List V, I.Nodup → (∀ x∈I, x∈W) →
    (∀ x∈I, ∀ y∈I, g x y=false) → I.length≤k

private theorem cut_cons_left (g : V→V→Bool) (x : V) (A B : List V) :
    cut g (x::A) B = degree g x B + cut g A B := rfl

private theorem deg_cons (g : V→V→Bool) (a b : V) (A : List V) :
    degree g a (b::A) = degree g a A + (if g a b then 1 else 0) := by
  cases h:g a b <;> simp [degree,h]

private theorem cut_cons_right (g : V→V→Bool) (symm : Symmetric g)
    (X : List V) (a : V) (A : List V) :
    cut g X (a::A) = cut g X A + degree g a X := by
  induction X with
  | nil => rfl
  | cons x X ih =>
    rw [cut_cons_left,cut_cons_left,ih,deg_cons,deg_cons,symm x a]
    omega

private theorem reverse_cut (g : V→V→Bool) (symm : Symmetric g) (A B : List V) :
    cut g A B = cut g B A := by
  induction A with
  | nil =>
    have h : cut g B []=0 := by
      induction B with
      | nil => rfl
      | cons b B ih => rw [cut_cons_left,ih];rfl
    change 0=cut g B []
    rw [h]
  | cons a A ih =>
    rw [cut_cons_left,cut_cons_right g symm,ih,Nat.add_comm]

private theorem cut_app_right (g : V→V→Bool) (symm : Symmetric g) (A B C : List V) :
    cut g A (B++C) = cut g A B+cut g A C := by
  rw [reverse_cut g symm A]
  have z : cut g (B++C) A = cut g B A+cut g C A := by simp [cut,List.sum_append]
  rw [z, reverse_cut g symm B, reverse_cut g symm C]

private theorem cut_perm_right (g : V→V→Bool) (A : List V) {B C : List V} (p : B.Perm C) :
    cut g A B = cut g A C := by
  induction A with
  | nil => rfl
  | cons a A ih =>
    have e : degree g a B=degree g a C := (p.filter (g a)).length_eq
    rw [cut_cons_left,cut_cons_left,e,ih]

private theorem cut_upper (g : V→V→Bool) (A B : List V) (d : Nat)
    (up : ∀ x∈A, degree g x B≤d) : cut g A B≤A.length*d := by
  induction A with
  | nil => simp [cut]
  | cons x A ih =>
    have q := up x (by simp)
    have tail := ih (fun v vm => up v (List.mem_cons_of_mem _ vm))
    rw [cut_cons_left,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

private theorem cut_at_max_degree (g : V→V→Bool) (A B : List V) (d : Nat)
    (up : ∀ x∈A, degree g x B≤d) (low : A.length*d≤cut g A B) :
    ∀ x∈A, degree g x B=d := by
  induction A with
  | nil => simp
  | cons x A ih =>
    have h := up x (by simp)
    have t : ∀ v∈A, degree g v B≤d := fun v vm => up v (List.mem_cons_of_mem _ vm)
    have tb := cut_upper g A B d t
    rw [cut_cons_left,List.length_cons,Nat.add_mul,Nat.one_mul] at low
    intro v vm
    rcases List.mem_cons.mp vm with eq | vm
    · subst v
      omega
    · exact ih t (by omega) v vm

private theorem cut_regular (g : V→V→Bool) (A B : List V) (d : Nat)
    (eq : ∀ x∈A, degree g x B=d) : cut g A B=A.length*d := by
  have high := cut_upper g A B d (fun x xm => by rw [eq x xm]; exact Nat.le_refl _)
  have low : A.length*d≤cut g A B := by
    induction A with
    | nil => simp [cut]
    | cons x A ih =>
      have v := eq x (by simp)
      have w := ih (fun a am => eq a (List.mem_cons_of_mem _ am))
      rw [cut_cons_left,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
  omega

theorem shortest_odd_above_twice_independence {g : V→V→Bool}
    (symm : Symmetric g) (loop : Loopless g) (W : List V) (k : Nat)
    (nd : W.Nodup) (large : 2*k<W.length) (cap : InducedIndependenceCap g W k) :
    ∃ n, ∃ C : TraceCycle g n, C.ShortestOdd W := by
  apply shortest_simple_cycle_of_odd_trace loop
  apply Classical.byContradiction
  intro no
  obtain ⟨A,B,p,ai,bi⟩ := bipartition_of_no_odd_trace symm no
  have ndp := List.nodup_append.mp (p.nodup_iff.mpr nd)
  have ua := cap A ndp.1 (fun v vm => p.mem_iff.mp (List.mem_append_left _ vm)) ai
  have ub := cap B ndp.2.1 (fun v vm => p.mem_iff.mp (List.mem_append_right _ vm)) bi
  have psize := p.length_eq
  rw [List.length_append] at psize
  omega

/-- The prior even-order 2r obstruction: triangle-free graph order 2r,
independence cap r−1, density ≥r(r−1) cannot coexist for r≥6. -/
theorem even_boundary_impossible {g : V→V→Bool} (symm : Symmetric g)
    (loop : Loopless g) (tri : TriangleFree g)
    (W : List V) (r : Nat) (hr : 6≤r)
    (nd : W.Nodup) (size : W.length=2*r)
    (density : r*(r-1)≤edges g W) (cap : InducedIndependenceCap g W (r-1)) :
    False := by
  have maxd (x : V) : degree g x W≤r-1 := by
    exact cap (W.filter (g x)) (List.filter_sublist.nodup nd)
      (fun y ym => (List.mem_filter.mp ym).1)
      (fun y ym z zm => tri x y z (List.mem_filter.mp ym).2 (List.mem_filter.mp zm).2)
  have low : W.length*(r-1)≤cut g W W := by
    rw [size,twice_edges g symm loop,Nat.mul_assoc]
    omega
  have reg := cut_at_max_degree g W W (r-1) (fun x _ => maxd x) low
  obtain ⟨n,C,short⟩ := shortest_odd_above_twice_independence symm loop W (r-1) nd
    (by omega) cap
  classical
  let mark (x : V) : Bool := decide (x∈C.vertices)
  let O := W.filter (fun x=> !mark x)
  have p : (W.filter mark).Perm C.vertices := by
    apply (List.perm_ext_iff_of_nodup (List.filter_sublist.nodup nd) C.vertices_nodup).mpr
    intro x
    constructor
    · intro m
      exact of_decide_eq_true (List.mem_filter.mp m).2
    · intro m
      exact List.mem_filter.mpr ⟨short.2.1 x m,decide_eq_true m⟩
  have part : (C.vertices++O).Perm W :=
    (p.symm.append_right O).trans (List.filter_append_perm mark W)
  have out (x : V) (xm : x∈O) : degree g x C.vertices≤2 := by
    obtain ⟨wm,no⟩ := List.mem_filter.mp xm
    exact C.outsider_degree_le_two symm tri short wm (by simpa [mark] using no)
  have capout := cut_upper g O C.vertices 2 out
  have cdeg := cut_regular g C.vertices W (r-1) (fun x xm => reg x (short.2.1 x xm))
  rw [← cut_perm_right g C.vertices part,cut_app_right g symm,
    twice_edges g symm loop,C.edge_perimeter symm loop short,
    reverse_cut g symm C.vertices O] at cdeg
  have sz := part.length_eq
  rw [List.length_append,size] at sz
  have ll : C.vertices.length=n := List.length_ofFn
  have minN := C.odd_length_ge_five symm tri short.1
  have lim : 5 * (r-1) ≤ C.vertices.length * (r-1) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

end ParallelMantel

#print axioms ParallelMantel.shortest_odd_above_twice_independence
#print axioms ParallelMantel.even_boundary_impossible
