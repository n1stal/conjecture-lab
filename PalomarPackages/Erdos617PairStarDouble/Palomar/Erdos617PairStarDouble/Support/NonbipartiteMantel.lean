module

public import Palomar.Erdos617PairStarDouble.Support.OddExistence
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
Exact nonbipartite Mantel-gap adapter for the pair-routing argument in #617.
This file checks a graph-theory ingredient only, not the full row-routing proof.
-/
namespace ParallelMantel

set_option maxHeartbeats 800000

universe u
variable {V : Type u} {g : V → V → Bool}

/-- floor(n²/4) without division of a product. -/
def mantelBound (n : Nat) : Nat := (n / 2) * ((n + 1) / 2)

theorem balanced_product_bound (a b : Nat) : a*b ≤ mantelBound (a+b) := by
  have one (a b : Nat) (ab : a≤b) : a*b ≤ mantelBound (a+b) := by
    let F := (a+b)/2
    let C := (a+b+1)/2
    let k := F-a
    have fa : a+k=F := by dsimp [F,k]; omega
    have cb : b=C+k := by dsimp [C,k,F]; omega
    have aC : a≤C := by dsimp [C]; omega
    have mul := Nat.mul_le_mul_right k aC
    change a*b ≤ F*C
    rw [← fa, cb, Nat.add_mul, Nat.mul_add, Nat.mul_comm k C]
    omega
  by_cases ab : a≤b
  · exact one a b ab
  · simpa [Nat.add_comm b a,Nat.mul_comm b a] using one b a (by omega)

theorem mantelBound_mono {m n : Nat} (le : m≤n) : mantelBound m≤mantelBound n := by
  unfold mantelBound
  apply Nat.mul_le_mul <;> omega

private theorem mantelBound_add_four (n : Nat) : mantelBound (n+4)=mantelBound n+2*n+4 := by
  unfold mantelBound
  rw [show (n+4)/2=n/2+2 by omega,show (n+4+1)/2=(n+1)/2+2 by omega]
  rw [Nat.mul_add,Nat.add_mul,Nat.add_mul]
  rw [Nat.mul_comm 2 ((n+1)/2),Nat.mul_comm (n/2) 2]
  omega

theorem mantel_general (symm : Symmetric g) (loop : Loopless g) (tri : TriangleFree g)
    (W : List V) : edges g W ≤ mantelBound W.length := by
  cases W with
  | nil => simp [edges,mantelBound]
  | cons w X =>
    obtain ⟨v,vm,maxv⟩ : ∃ v∈w::X, ∀ x∈w::X, degree g x (w::X)≤degree g v (w::X) := by
      cases hh : ((w::X).map fun x => degree g x (w::X)).max? with
      | none => have q := List.max?_eq_none_iff.mp hh; simp at q
      | some d =>
        obtain ⟨dm,high⟩ := List.max?_eq_some_iff.mp hh
        obtain ⟨v,vm,ve⟩ := List.mem_map.mp dm
        exact ⟨v,vm,fun x xm => ve ▸ high _ (List.mem_map.mpr ⟨x,xm,rfl⟩)⟩
    let A := (w::X).filter (g v)
    let B := (w::X).filter (fun x => !g v x)
    have perm : (A++B).Perm (w::X) := List.filter_append_perm _ _
    have len : A.length+B.length=(w::X).length := by simpa using perm.length_eq
    have cap : edges g (w::X)+edges g B ≤ A.length*B.length :=
      max_neighbor_partition_bound g symm loop tri (w::X) v maxv
    have prod := balanced_product_bound A.length B.length
    rw [len] at prod
    omega

private theorem cut_rev (symm : Symmetric g) (loop : Loopless g) (A B : List V) :
    cut g A B = cut g B A := by
  have p : (A++B).Perm (B++A) := List.perm_append_comm
  have same := edges_perm g symm loop p
  have ha := edges_append g A B
  have hb := edges_append g B A
  omega

private theorem cut_upper (A B : List V) (maxd : Nat)
    (bound : ∀ x∈A, degree g x B≤maxd) : cut g A B ≤ A.length*maxd := by
  induction A with
  | nil => simp [cut]
  | cons x A ih =>
    have head := bound x (by simp)
    have tail := ih (fun y ym => bound y (List.mem_cons_of_mem _ ym))
    change degree g x B+cut g A B ≤ (A.length+1)*maxd
    rw [Nat.add_mul,Nat.one_mul]
    omega

/-- Shortest odd trace gives the exact non-bipartite Mantel upper bound. -/
theorem nonbipartite_mantel_of_odd_trace (symm : Symmetric g) (loop : Loopless g)
    (tri : TriangleFree g) (W : List V) (nd : W.Nodup)
    (odd : ∃ n, n%2=1 ∧ Nonempty (ClosedTrace g W n)) :
    edges g W ≤ mantelBound (W.length-1)+1 := by
  obtain ⟨n,C,short⟩ := shortest_simple_cycle_of_odd_trace loop odd
  have five := C.odd_length_ge_five symm tri short.1
  have cl : C.vertices.length=n := List.length_ofFn
  classical
  let mark (x : V) : Bool := decide (x∈C.vertices)
  let O := W.filter (fun x=> !mark x)
  have cyc : (W.filter mark).Perm C.vertices := by
    apply (List.perm_ext_iff_of_nodup (List.filter_sublist.nodup nd) C.vertices_nodup).mpr
    intro x
    constructor
    · intro m
      exact of_decide_eq_true (List.mem_filter.mp m).2
    · intro m
      exact List.mem_filter.mpr ⟨short.2.1 x m,decide_eq_true m⟩
  have part : (C.vertices++O).Perm W :=
    (cyc.symm.append_right O).trans (List.filter_append_perm mark W)
  have out (x : V) (xm : x∈O) : degree g x C.vertices≤2 := by
    obtain ⟨wm,no⟩ := List.mem_filter.mp xm
    exact C.outsider_degree_le_two symm tri short wm (by simpa [mark] using no)
  have capO := mantel_general symm loop tri O
  have capCross := cut_upper O C.vertices 2 out
  have total := edges_append g C.vertices O
  rw [edges_perm g symm loop part, C.edge_perimeter symm loop short, cut_rev symm loop C.vertices O] at total
  have len := part.length_eq
  rw [List.length_append,cl] at len
  have lm : O.length≤W.length-5 := by omega
  have big := mantelBound_mono lm
  have shift : W.length-1=(W.length-5)+4 := by omega
  rw [shift,mantelBound_add_four]
  omega

/-- If its density exceeds the nonbipartite Mantel bound, a finite
triangle-free graph has an actual partition into independent lists. -/
theorem bipartite_of_above_odd_mantel (symm : Symmetric g) (loop : Loopless g)
    (tri : TriangleFree g) (W : List V) (nd : W.Nodup)
    (dense : mantelBound (W.length-1)+1<edges g W) :
    ∃ A B : List V, (A++B).Perm W ∧
      (∀ x∈A, ∀ y∈A, g x y=false) ∧
      (∀ x∈B, ∀ y∈B, g x y=false) := by
  exact bipartition_of_no_odd_trace symm
    (fun odd => Nat.not_le_of_lt dense (nonbipartite_mantel_of_odd_trace symm loop tri W nd odd))


theorem mantelBound_prev {n : Nat} (pos : 0<n) :
    mantelBound n = mantelBound (n-1) + n/2 := by
  unfold mantelBound
  by_cases even : n%2=0
  · let k := (n-2)/2
    have a : n/2=k+1 := by dsimp [k];omega
    have b : (n+1)/2=k+1 := by dsimp [k];omega
    have c : (n-1)/2=k := by dsimp [k];omega
    have d : (n-1+1)/2=k+1 := by dsimp [k];omega
    rw [a,b,c,d,Nat.add_mul,Nat.one_mul]
  · have a : (n+1)/2=n/2+1 := by omega
    have b : (n-1)/2=n/2 := by omega
    have c : (n-1+1)/2=n/2 := by omega
    rw [a,b,c,Nat.mul_add,Nat.mul_one]

private theorem cut_missing (A B : List V) :
    cut g A B + cut (fun x y => !g x y) A B = A.length * B.length := by
  have row (x : V) : degree g x B + degree (fun x y => !g x y) x B=B.length := by
    simpa [degree] using (List.filter_append_perm (g x) B).length_eq
  induction A with
  | nil => simp [cut]
  | cons x A ih =>
    have rowx := row x
    change degree g x B+cut g A B+
      (degree (fun x y => !g x y) x B + cut (fun x y => !g x y) A B)=
      (A.length+1)*B.length
    rw [Nat.add_mul,Nat.one_mul]
    omega

private theorem independent_edges_zero (A : List V)
    (ind : ∀ x∈A, ∀ y∈A, g x y=false) : edges g A=0 := by
  induction A with
  | nil => rfl
  | cons x A ih =>
    have dz : degree g x A=0 := by
      unfold degree
      apply List.length_eq_zero_iff.mpr
      apply List.filter_eq_nil_iff.mpr
      intro y ym
      simp [ind x (by simp) y (List.mem_cons_of_mem _ ym)]
    rw [edges,dz,ih (fun a am b bm => ind a (List.mem_cons_of_mem _ am) b (List.mem_cons_of_mem _ bm))]

/-- An actual shortest pentagon in a triangle-free graph leaves a bipartite
exterior under the sharp odd-Mantel gap, with one budget for all crossing
omissions and lost pentagon incidences. No preselected exterior sides are
assumed. -/
theorem TraceCycle.dense_fiveExterior_split (C : TraceCycle g 5)
    (symm : Symmetric g) (loop : Loopless g) (tri : TriangleFree g)
    (W O : List V) (nd : W.Nodup) (part : (C.vertices++O).Perm W)
    (short : C.ShortestOdd W) (S : Nat)
    (gap : S+1 < O.length/2)
    (ledger : mantelBound O.length+2*O.length+5 ≤ edges g W+S) :
    ∃ A B : List V, (A++B).Perm O ∧
      (∀ x∈A, ∀ y∈A, g x y=false) ∧
      (∀ x∈B, ∀ y∈B, g x y=false) ∧
      cut (fun x y => !g x y) A B + (2*O.length-cut g O C.vertices) ≤ S := by
  have noDu := List.nodup_append.mp (part.nodup_iff.mpr nd)
  have out (x : V) (xm : x∈O) : degree g x C.vertices≤2 := by
    have wm := part.mem_iff.mp (List.mem_append_right C.vertices xm)
    exact C.outsider_degree_le_two symm tri short wm (fun c => noDu.2.2 x c x xm rfl)
  have ch := cut_upper O C.vertices 2 out
  have cl : C.vertices.length=5 := List.length_ofFn
  have edgeSplit := edges_append g C.vertices O
  rw [edges_perm g symm loop part,C.edge_perimeter symm loop short,cl,
    cut_rev symm loop C.vertices O] at edgeSplit
  have op : 0<O.length := by omega
  have eq := mantelBound_prev op
  have dense : mantelBound (O.length-1)+1<edges g O := by omega
  obtain ⟨A,B,p,ai,bi⟩ :=
    bipartite_of_above_odd_mantel symm loop tri O noDu.2.1 dense
  have clen := p.length_eq
  rw [List.length_append] at clen
  have mul := balanced_product_bound A.length B.length
  rw [clen] at mul
  have eab := edges_append g A B
  rw [edges_perm g symm loop p, independent_edges_zero A ai,independent_edges_zero B bi] at eab
  have mc := cut_missing (g:=g) A B
  exact ⟨A,B,p,ai,bi,by omega⟩

end ParallelMantel

#print axioms ParallelMantel.balanced_product_bound
#print axioms ParallelMantel.mantel_general
#print axioms ParallelMantel.nonbipartite_mantel_of_odd_trace
#print axioms ParallelMantel.bipartite_of_above_odd_mantel

#print axioms ParallelMantel.TraceCycle.dense_fiveExterior_split
