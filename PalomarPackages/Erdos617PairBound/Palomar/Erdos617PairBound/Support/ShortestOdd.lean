module

public import Palomar.Erdos617PairBound.Support.ParallelMantel
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-! Simple cycles represented by their injective finite vertex traces. -/
namespace ParallelMantel

universe u
variable {V : Type u} {g : V → V → Bool}

structure TraceCycle (g : V → V → Bool) (n : Nat) where
  length_ge_three : 3 ≤ n
  trace : Fin n → V
  injective : ∀ i j, trace i = trace j → i = j
  step : ∀ i : Fin n, g (trace i) (trace ⟨(i.val + 1) % n, Nat.mod_lt _ (by omega)⟩) = true

def TraceCycle.vertices {n : Nat} (C : TraceCycle g n) : List V :=
  List.ofFn C.trace

def TraceCycle.at {n : Nat} (C : TraceCycle g n) (i : Nat) : V :=
  C.trace ⟨i % n, Nat.mod_lt _ (by have h := C.length_ge_three; omega)⟩

theorem TraceCycle.at_eq_trace {n : Nat} (C : TraceCycle g n) {i : Nat} (hi : i < n) :
    C.at i = C.trace ⟨i,hi⟩ := by
  unfold TraceCycle.at
  congr 1
  exact Fin.eq_of_val_eq (Nat.mod_eq_of_lt hi)

theorem TraceCycle.at_next {n : Nat} (C : TraceCycle g n) (i : Nat) :
    g (C.at i) (C.at (i+1)) = true := by
  unfold TraceCycle.at
  have h := C.step ⟨i % n,Nat.mod_lt _ (by have h := C.length_ge_three; omega)⟩
  have eq : (⟨(i % n + 1) % n,Nat.mod_lt _ (by have h := C.length_ge_three; omega)⟩ : Fin n) =
      ⟨(i+1) % n,Nat.mod_lt _ (by have h := C.length_ge_three; omega)⟩ := by
    apply Fin.eq_of_val_eq
    exact Nat.mod_add_mod i n 1
  exact eq ▸ h

theorem TraceCycle.at_period {n : Nat} (C : TraceCycle g n) (i : Nat) :
    C.at (i+n) = C.at i := by
  unfold TraceCycle.at
  congr 1
  apply Fin.eq_of_val_eq
  change (i+n) % n = i % n
  simp

theorem TraceCycle.at_inj_mod {n : Nat} (C : TraceCycle g n) {i j : Nat}
    (h : C.at i = C.at j) : i % n = j % n :=
  congrArg Fin.val (C.injective _ _ h)

theorem TraceCycle.mem_at {n : Nat} (C : TraceCycle g n) (i : Nat) :
    C.at i ∈ C.vertices :=
  List.mem_ofFn.mpr ⟨_,rfl⟩

theorem TraceCycle.vertices_nodup {n : Nat} (C : TraceCycle g n) :
    C.vertices.Nodup := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  change C.vertices[i] ≠ C.vertices[j]
  unfold TraceCycle.vertices at *
  rw [List.getElem_ofFn,List.getElem_ofFn]
  intro e
  have same := congrArg Fin.val (C.injective _ _ e)
  exact (Nat.ne_of_lt hij) same

private theorem mod_offset_inj {n s i j : Nat} (hs : s < n) (hi : i < n) (hj : j < n)
    (e : (s+i)%n=(s+j)%n) : i=j := by
  by_cases a : s+i < n
  · rw [Nat.mod_eq_of_lt a] at e
    by_cases b : s+j < n
    · rw [Nat.mod_eq_of_lt b] at e
      omega
    · rw [Nat.mod_eq_sub_mod (by omega : n ≤ s+j),
        Nat.mod_eq_of_lt (by omega : s+j-n<n)] at e
      omega
  · rw [Nat.mod_eq_sub_mod (by omega : n ≤ s+i),
      Nat.mod_eq_of_lt (by omega : s+i-n<n)] at e
    by_cases b : s+j < n
    · rw [Nat.mod_eq_of_lt b] at e
      omega
    · rw [Nat.mod_eq_sub_mod (by omega : n ≤ s+j),
        Nat.mod_eq_of_lt (by omega : s+j-n<n)] at e
      omega

theorem TraceCycle.arc_injective {n s : Nat} (C : TraceCycle g n) (hs : s < n)
    {i j : Nat} (hi : i < n) (hj : j < n) (e : C.at (s+i) = C.at (s+j)) : i=j :=
  mod_offset_inj hs hi hj (C.at_inj_mod e)

/-- Close a cyclic arc with a single chord. Its d+1 vertices are distinct. -/
def TraceCycle.closeArc {n s d : Nat} (C : TraceCycle g n) (hs : s < n)
    (dmin : 2 ≤ d) (dmax : d < n) (chord : g (C.at (s+d)) (C.at s) = true) :
    TraceCycle g (d+1) where
  length_ge_three := by omega
  trace i := C.at (s+i.val)
  injective i j e := Fin.eq_of_val_eq
    (C.arc_injective hs (by have h := i.isLt; omega) (by have h := j.isLt; omega) e)
  step i := by
    have hi := i.isLt
    change g (C.at (s+i.val)) (C.at (s+(i.val+1)%(d+1))) = true
    by_cases h : i.val + 1 < d+1
    · rw [Nat.mod_eq_of_lt h, ← Nat.add_assoc]
      exact C.at_next _
    · have t : i.val = d := by omega
      rw [t, Nat.mod_self, Nat.add_zero]
      exact chord

/-- Close a cyclic arc with two links through a genuine outside vertex. -/
def TraceCycle.closeArcThrough {n s d : Nat} (C : TraceCycle g n) (hs : s < n)
    (dmin : 1 ≤ d) (dmax : d < n) (x : V) (outside : x ∉ C.vertices)
    (finish : g (C.at (s+d)) x = true) (beginEdge : g x (C.at s) = true) :
    TraceCycle g (d+2) where
  length_ge_three := by omega
  trace i := if i.val = d+1 then x else C.at (s+i.val)
  injective i j e := by
    apply Fin.eq_of_val_eq
    have hi := i.isLt
    have hj := j.isLt
    change (if i.val = d+1 then x else C.at (s+i.val)) =
      (if j.val = d+1 then x else C.at (s+j.val)) at e
    by_cases h : i.val = d+1 <;> by_cases k : j.val = d+1
    · omega
    · simp [h,k] at e
      exact False.elim (outside (e ▸ C.mem_at (s+j.val)))
    · simp [h,k] at e
      exact False.elim (outside (e ▸ C.mem_at (s+i.val)))
    · simp [h,k] at e
      exact C.arc_injective hs (by omega) (by omega) e
  step i := by
    have hi := i.isLt
    change g (if i.val = d+1 then x else C.at (s+i.val))
      (if (i.val+1)%(d+2) = d+1 then x else C.at (s+(i.val+1)%(d+2))) = true
    by_cases h : i.val = d+1
    · simp [h, beginEdge]
    · rw [ite_eq_right h, Nat.mod_eq_of_lt (by omega : i.val+1 < d+2)]
      by_cases k : i.val+1 = d+1
      · rw [ite_eq_left k, show i.val=d by omega]
        exact finish
      · rw [ite_eq_right k, ← Nat.add_assoc]
        exact C.at_next _

/-- Minimal among simple odd cycles all of whose vertices lie in W. -/
def TraceCycle.ShortestOdd {n : Nat} (C : TraceCycle g n) (W : List V) : Prop :=
  n % 2 = 1 ∧ (∀ v ∈ C.vertices, v ∈ W) ∧
    ∀ m (D : TraceCycle g m), m % 2 = 1 → (∀ v ∈ D.vertices, v ∈ W) → n ≤ m

private theorem vertices_of_closeArc {n s d : Nat} (C : TraceCycle g n) (hs : s<n)
    (hd : 2≤d) (dn : d<n) (ch : g (C.at (s+d)) (C.at s)=true) :
    ∀ v ∈ (C.closeArc hs hd dn ch).vertices, v ∈ C.vertices := by
  intro v hv
  obtain ⟨i,eq⟩ := List.mem_ofFn.mp hv
  change C.at (s+i.val) = v at eq
  exact eq ▸ C.mem_at _

private theorem vertices_of_closeArcThrough {n s d : Nat} (C : TraceCycle g n)
    (hs : s<n) (hd : 1≤d) (dn : d<n) (x : V) (out : x ∉ C.vertices)
    (finish : g (C.at (s+d)) x=true) (beginEdge : g x (C.at s)=true) :
    ∀ v ∈ (C.closeArcThrough hs hd dn x out finish beginEdge).vertices,
      v=x ∨ v ∈ C.vertices := by
  intro v hv
  obtain ⟨i,eq⟩ := List.mem_ofFn.mp hv
  change (if i.val = d+1 then x else C.at (s+i.val)) = v at eq
  by_cases e : i.val = d+1
  · simp [e] at eq
    exact Or.inl eq.symm
  · simp [e] at eq
    exact Or.inr (eq ▸ C.mem_at _)

/-- An odd cycle in a triangle-free graph has at least five vertices. -/
theorem TraceCycle.odd_length_ge_five {n : Nat} (C : TraceCycle g n)
    (symm : Symmetric g) (triangle : TriangleFree g) (odd : n%2=1) : 5≤n := by
  have lower := C.length_ge_three
  by_cases e : n=3
  · have a := C.at_next 0
    have b := C.at_next 1
    have c := C.at_next 2
    change g (C.at 0) (C.at 1)=true at a
    change g (C.at 1) (C.at 2)=true at b
    change g (C.at 2) (C.at 3)=true at c
    have p := C.at_period 0
    rw [Nat.zero_add] at p
    have p3 := (congrArg (fun i => C.at i) e).symm.trans p
    rw [p3, symm (C.at 2) (C.at 0)] at c
    have no := triangle _ _ _ a c
    rw [no] at b
    contradiction
  · omega

/-- A shortest odd cycle has no chord: both arcs closed through a chord
would be shorter, and exactly one of those two cycles has odd length. -/
theorem TraceCycle.shortest_edge_consecutive {n : Nat} (C : TraceCycle g n)
    (symm : Symmetric g) {W : List V} (minOdd : C.ShortestOdd W)
    {i j : Nat} (lt : i < j) (bound : j < n)
    (edge : g (C.at i) (C.at j)=true) :
    j = i+1 ∨ (i=0 ∧ j+1=n) := by
  obtain ⟨odd,sub,short⟩ := minOdd
  apply Classical.byContradiction
  intro notnext
  let d := j-i
  let e := n-d
  have iBound : i < n := by omega
  have idj : i+d=j := by dsimp [d]; omega
  have dmin : 2≤d := by
    by_cases h : 2≤d
    · exact h
    · exact False.elim (notnext (Or.inl (by omega)))
  have emin : 2≤e := by
    by_cases h : 2≤e
    · exact h
    · have two : i=0 ∧ j+1=n := by dsimp [d,e] at *; omega
      exact False.elim (notnext (Or.inr two))
  have sum : d+e=n := by dsimp [e]; omega
  have dn : d<n := by omega
  have en : e<n := by omega
  have chord1 : g (C.at (i+d)) (C.at i)=true := by
    rw [idj, symm (C.at j)]
    exact edge
  have chord2 : g (C.at (j+e)) (C.at j)=true := by
    rw [show j+e=i+n by omega, C.at_period]
    exact edge
  by_cases he : (d+1)%2=1
  · have p := short (d+1) (C.closeArc iBound dmin dn chord1) he
      (fun v hv => sub v (vertices_of_closeArc C iBound dmin dn chord1 v hv))
    omega
  · have ho : (e+1)%2=1 := by omega
    have p := short (e+1) (C.closeArc bound emin en chord2) ho
      (fun v hv => sub v (vertices_of_closeArc C bound emin en chord2 v hv))
    omega

private theorem TraceCycle.no_three_ordered_neighbors {n : Nat} (C : TraceCycle g n)
    (symm : Symmetric g) (triangle : TriangleFree g) {W : List V}
    (minOdd : C.ShortestOdd W) {x : V} (xW : x∈W) (outside : x∉C.vertices)
    {i j k : Nat} (ij : i<j) (jk : j<k) (kn : k<n)
    (ei : g x (C.at i)=true) (ej : g x (C.at j)=true) (ek : g x (C.at k)=true) : False := by
  obtain ⟨odd,sub,short⟩ := minOdd
  let a := j-i
  let b := k-j
  let c := n-k+i
  have inb : i<n := by omega
  have jnb : j<n := by omega
  have ia : i+a=j := by dsimp [a]; omega
  have jb : j+b=k := by dsimp [b]; omega
  have kc : k+c=i+n := by dsimp [c]; omega
  have amin : 2≤a := by
    by_cases h : 2≤a
    · exact h
    · have eq : j=i+1 := by omega
      have yes := C.at_next i
      rw [← eq, triangle x _ _ ei ej] at yes
      contradiction
  have bmin : 2≤b := by
    by_cases h : 2≤b
    · exact h
    · have eq : k=j+1 := by omega
      have yes := C.at_next j
      rw [← eq, triangle x _ _ ej ek] at yes
      contradiction
  have cmin : 2≤c := by
    by_cases h : 2≤c
    · exact h
    · have eq : k+1=i+n := by dsimp [c] at *; omega
      have yes := C.at_next k
      rw [eq,C.at_period, triangle x _ _ ek ei] at yes
      contradiction
  have total : a+b+c=n := by omega
  have close (s d : Nat) (sb : s<n) (dl : 1≤d) (dr : d<n)
      (hl : g x (C.at s)=true) (hr : g x (C.at (s+d))=true) (od : d%2=1) : n≤d+2 := by
    have finish : g (C.at (s+d)) x=true := (symm _ _).trans hr
    apply short (d+2) (C.closeArcThrough sb dl dr x outside finish hl) (by omega)
    intro v hv
    obtain eq | mem := vertices_of_closeArcThrough C sb dl dr x outside finish hl v hv
    · exact eq.symm ▸ xW
    · exact sub v mem
  by_cases oa : a%2=1
  · have eq : g x (C.at (i+a))=true := ia ▸ ej
    have s := close i a inb (by omega) (by omega) ei eq oa
    omega
  · by_cases ob : b%2=1
    · have eq : g x (C.at (j+b))=true := jb ▸ ek
      have s := close j b jnb (by omega) (by omega) ej eq ob
      omega
    · have eq : g x (C.at (k+c))=true := by rw [kc,C.at_period]; exact ei
      have oc : c%2=1 := by omega
      have s := close k c kn (by omega) (by omega) ek eq oc
      omega

/-- Every outside vertex of a shortest odd cycle has at most two of its
vertices as neighbors. Three chosen neighbors would cut the cycle into
three gaps of length at least two; an odd gap closes through the outsider. -/
theorem TraceCycle.outsider_degree_le_two {n : Nat} (C : TraceCycle g n)
    (symm : Symmetric g) (triangle : TriangleFree g) {W : List V}
    (minOdd : C.ShortestOdd W) {x : V} (xW : x∈W) (outside : x∉C.vertices) :
    degree g x C.vertices ≤ 2 := by
  apply Classical.byContradiction
  intro bad
  let F := C.vertices.filter (g x)
  change ¬ F.length ≤ 2 at bad
  have m0 : 0 < F.length := by omega
  have m1 : 1 < F.length := by omega
  have m2 : 2 < F.length := by omega
  let v0 := F[0]'m0
  let v1 := F[1]'m1
  let v2 := F[2]'m2
  have fnd : F.Nodup := List.filter_sublist.nodup C.vertices_nodup
  have d01 : v0 ≠ v1 := by
    intro eq
    have h := (List.Nodup.getElem_inj fnd).mp eq
    omega
  have d02 : v0 ≠ v2 := by
    intro eq
    have h := (List.Nodup.getElem_inj fnd).mp eq
    omega
  have d12 : v1 ≠ v2 := by
    intro eq
    have h := (List.Nodup.getElem_inj fnd).mp eq
    omega
  have m (v : V) (vm : v∈F) : ∃ i : Fin n, C.at i.val = v ∧ g x (C.at i.val)=true := by
    obtain ⟨mv,adj⟩ := List.mem_filter.mp vm
    obtain ⟨i,eq⟩ := List.mem_ofFn.mp mv
    rw [← C.at_eq_trace i.isLt] at eq
    refine ⟨i,eq,?_⟩
    rw [eq]
    exact adj
  obtain ⟨i,ie,ia⟩ := m v0 (List.mem_of_getElem rfl)
  obtain ⟨j,je,ja⟩ := m v1 (List.mem_of_getElem rfl)
  obtain ⟨k,ke,ka⟩ := m v2 (List.mem_of_getElem rfl)
  have idj : i.val ≠ j.val := fun eq => d01 (ie.symm.trans ((congrArg C.at eq).trans je))
  have idk : i.val ≠ k.val := fun eq => d02 (ie.symm.trans ((congrArg C.at eq).trans ke))
  have jdk : j.val ≠ k.val := fun eq => d12 (je.symm.trans ((congrArg C.at eq).trans ke))
  have no {a b c : Fin n} (ab : a.val<b.val) (bc : b.val<c.val)
      (aa : g x (C.at a.val)=true) (ba : g x (C.at b.val)=true)
      (ca : g x (C.at c.val)=true) : False :=
    C.no_three_ordered_neighbors symm triangle minOdd xW outside ab bc c.isLt aa ba ca
  by_cases ij : i.val<j.val
  · by_cases jk : j.val<k.val
    · exact no ij jk ia ja ka
    · by_cases ik : i.val<k.val
      · exact no ik (by omega : k.val<j.val) ia ka ja
      · exact no (by omega : k.val<i.val) ij ka ia ja
  · by_cases ik : i.val<k.val
    · exact no (by omega : j.val<i.val) ik ja ia ka
    · by_cases jk : j.val<k.val
      · exact no jk (by omega : k.val<i.val) ja ka ia
      · exact no (by omega : k.val<j.val) (by omega : j.val<i.val) ka ja ia

private theorem TraceCycle.neighbor_values {n : Nat} (C : TraceCycle g n)
    (symm : Symmetric g) (loop : Loopless g) {W : List V}
    (minOdd : C.ShortestOdd W) (i : Fin n) (v : V) :
    v ∈ C.vertices.filter (g (C.at i.val)) ↔
      v = C.at (i.val+1) ∨ v = C.at (i.val+(n-1)) := by
  have nmin := C.length_ge_three
  constructor
  · intro vm
    obtain ⟨vc, edge⟩ := List.mem_filter.mp vm
    obtain ⟨j,hj⟩ := List.mem_ofFn.mp vc
    rw [← C.at_eq_trace j.isLt] at hj
    rw [← hj] at edge ⊢
    have iB := i.isLt
    have jB := j.isLt
    by_cases f : i.val < j.val
    · obtain succ | ⟨i0,last⟩ := C.shortest_edge_consecutive symm minOdd f jB edge
      · exact Or.inl (congrArg (fun k => C.at k) succ)
      · right
        rw [show j.val = i.val+(n-1) by omega]
    · by_cases rev : j.val < i.val
      · have edge' : g (C.at j.val) (C.at i.val)=true := (symm _ _).trans edge
        obtain pred | ⟨j0,last⟩ := C.shortest_edge_consecutive symm minOdd rev iB edge'
        · right
          rw [show i.val+(n-1)=j.val+n by omega, C.at_period]
        · left
          rw [j0]
          exact (C.at_period 0).symm.trans
            (congrArg (fun t => C.at t) (by omega : 0+n=i.val+1))
      · have eq : j.val=i.val := by omega
        rw [eq, loop] at edge
        contradiction
  · rintro (rfl | rfl)
    · exact List.mem_filter.mpr ⟨C.mem_at _, C.at_next _⟩
    · have e := C.at_next (i.val+(n-1))
      rw [show i.val+(n-1)+1=i.val+n by omega, C.at_period] at e
      exact List.mem_filter.mpr ⟨C.mem_at _, (symm _ _).trans e⟩

/-- Every vertex of the shortest odd cycle has precisely its two cyclic
neighbors within the cycle, by the no-chord theorem. -/
theorem TraceCycle.internal_degree_eq_two {n : Nat} (C : TraceCycle g n)
    (symm : Symmetric g) (loop : Loopless g) {W : List V}
    (minOdd : C.ShortestOdd W) {v : V} (vm : v ∈ C.vertices) :
    degree g v C.vertices = 2 := by
  obtain ⟨i,eq⟩ := List.mem_ofFn.mp vm
  rw [← C.at_eq_trace i.isLt] at eq
  rw [← eq]
  let F := C.vertices.filter (g (C.at i.val))
  let x := C.at (i.val+1)
  let y := C.at (i.val+(n-1))
  have fnd : F.Nodup := List.filter_sublist.nodup C.vertices_nodup
  have three := C.length_ge_three
  have ne : x ≠ y := by
    intro e
    have q : 1=n-1 := C.arc_injective i.isLt (by omega) (by omega) e
    omega
  have tn : ([x,y] : List V).Nodup := by simp [ne]
  have perm : F.Perm [x,y] := (List.perm_ext_iff_of_nodup fnd tn).mpr (by
    intro a
    simpa [F,x,y] using C.neighbor_values symm loop minOdd i a)
  exact perm.length_eq

private theorem cut_eq_length_mul {V : Type u} (g : V → V → Bool) (A B : List V)
    (k : Nat) (all : ∀ v∈A, degree g v B=k) :
    cut g A B = A.length*k := by
  induction A with
  | nil => simp [cut]
  | cons a A ih =>
    have aeq := all a List.mem_cons_self
    have rest := ih (fun v hv => all v (List.mem_cons_of_mem a hv))
    change degree g a B + cut g A B = (a::A).length*k
    rw [aeq,rest,List.length_cons,Nat.add_mul,Nat.one_mul,Nat.add_comm]

/-- The induced edge ledger of the shortest odd cycle is exactly its perimeter. -/
theorem TraceCycle.edge_perimeter {n : Nat} (C : TraceCycle g n)
    (symm : Symmetric g) (loop : Loopless g) {W : List V} (minOdd : C.ShortestOdd W) :
    edges g C.vertices = C.vertices.length := by
  have h := cut_eq_length_mul g C.vertices C.vertices 2
    (fun v hv => C.internal_degree_eq_two symm loop minOdd hv)
  rw [twice_edges g symm loop] at h
  omega

/-- Source-level cycle adapter: the caller supplies an actual shortest odd
cycle witness, but neither a perimeter assumption nor an outsider degree cap. -/
theorem TraceCycle.shortest_partition {n : Nat} (C : TraceCycle g n)
    (symm : Symmetric g) (loop : Loopless g) (triangle : TriangleFree g)
    (W O : List V) (r : Nat) (hr : 12 ≤ r) (perm : (C.vertices ++ O).Perm W)
    (nd : W.Nodup) (size : W.length = 2*r-1)
    (density : (r-1)*(r-1) ≤ edges g W) (minOdd : C.ShortestOdd W) :
    C.vertices.length = 5 ∧ ∃ A B : List V, (A ++ B).Perm O ∧
      (∀ x ∈ A, ∀ y ∈ A, g x y = false) ∧
      (∀ x ∈ B, ∀ y ∈ B, g x y = false) ∧
      let R := r - 3
      let missing := cut (fun x y => !g x y) A B
      let hits := cut g O C.vertices
      ((A.length = R ∧ B.length = R ∧ missing + (4 * R - hits) ≤ 1) ∨
       (((A.length + 1 = R ∧ B.length = R + 1) ∨
         (B.length + 1 = R ∧ A.length = R + 1)) ∧ missing = 0 ∧ hits = 4 * R)) := by
  have len : C.vertices.length=n := List.length_ofFn
  have odd : ∃ k : Nat, C.vertices.length=2*k+1 := by
    refine ⟨n/2,?_⟩
    have h := minOdd.1
    omega
  have ge5 : 5 ≤ C.vertices.length := by
    rw [len]
    exact C.odd_length_ge_five symm triangle minOdd.1
  have well := List.nodup_append.mp (perm.nodup_iff.mpr nd)
  have out : ∀ x∈O, degree g x C.vertices ≤ 2 := by
    intro x hx
    have m : x∈W := perm.mem_iff.mp (List.mem_append.mpr (Or.inr hx))
    exact C.outsider_degree_le_two symm triangle minOdd m (fun hc => well.2.2 x hc x hx rfl)
  exact pentagon_outside_partition g symm loop triangle W C.vertices O r hr perm
    size density odd ge5 (C.edge_perimeter symm loop minOdd) out

end ParallelMantel

#print axioms ParallelMantel.TraceCycle.shortest_edge_consecutive
#print axioms ParallelMantel.TraceCycle.outsider_degree_le_two
#print axioms ParallelMantel.TraceCycle.internal_degree_eq_two
#print axioms ParallelMantel.TraceCycle.edge_perimeter
#print axioms ParallelMantel.TraceCycle.shortest_partition
