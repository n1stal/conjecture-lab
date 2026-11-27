module

public import Palomar.Erdos617PairBound.Support.ShortestOdd
public import Lean.Elab.Tactic.Omega

@[expose] public section

namespace ParallelMantel

universe u
variable {V : Type u} {g : V → V → Bool} {W : List V}

structure GraphPath (g : V→V→Bool) (W : List V) (x y : V) (n : Nat) where
  point : Nat → V
  start : point 0=x
  finish : point n=y
  valid : ∀ i, i≤n → point i∈W
  edge : ∀ i, i<n → g (point i) (point (i+1))=true

def GraphPath.stay {x : V} (mem : x∈W) : GraphPath g W x x 0 where
  point := fun _ => x
  start := rfl
  finish := rfl
  valid := fun _ _ => mem
  edge := fun _ bad => False.elim (Nat.not_lt_zero _ bad)

def GraphPath.single {x y : V} (xm : x∈W) (ym : y∈W) (h : g x y=true) :
    GraphPath g W x y 1 where
  point := fun i=> if i=0 then x else y
  start := rfl
  finish := rfl
  valid i _ := by
    by_cases e : i=0
    · simpa [e] using xm
    · simpa [e] using ym
  edge i eq := by
    have p : i=0 := by omega
    simpa [p] using h

def GraphPath.reverse {x y : V} {n : Nat} (p : GraphPath g W x y n)
    (symm : Symmetric g) : GraphPath g W y x n where
  point := fun i => p.point (n-i)
  start := by simpa using p.finish
  finish := by simpa using p.start
  valid i _ := p.valid (n-i) (by omega)
  edge i lt := by
    have e := p.edge (n-(i+1)) (by omega)
    rw [show n-(i+1)+1=n-i by omega] at e
    exact (symm _ _).trans e

def GraphPath.join {x y z : V} {a b : Nat}
    (p : GraphPath g W x y a) (q : GraphPath g W y z b) :
    GraphPath g W x z (a+b) where
  point := fun i => if i≤a then p.point i else q.point (i-a)
  start := by simpa using p.start
  finish := by
    by_cases e : b=0
    · have h : q.point 0=z := by simpa [e] using q.finish
      simpa [e] using p.finish.trans (q.start.symm.trans h)
    · have lt : ¬ a+b≤a := by omega
      simpa [lt] using q.finish
  valid i bound := by
    by_cases e : i≤a
    · simp [e,p.valid i e]
    · have w := q.valid (i-a) (by omega)
      simpa [e] using w
  edge i bound := by
    by_cases e : i+1≤a
    · have e' : i≤a := by omega
      simpa [e,e'] using p.edge i (by omega)
    · by_cases f : i≤a
      · have eq : i=a := by omega
        have hp : p.point i = q.point (i-a) := by
          simpa [eq] using p.finish.trans q.start.symm
        rw [ite_eq_left f,ite_eq_right e,hp,show i+1-a=(i-a)+1 by omega]
        exact q.edge (i-a) (by omega)
      · rw [ite_eq_right f,ite_eq_right e,show i+1-a=(i-a)+1 by omega]
        exact q.edge (i-a) (by omega)

structure ClosedTrace (g : V→V→Bool) (W : List V) (n : Nat) where
  positive : 0<n
  trace : Fin n → V
  valid : ∀ i, trace i∈W
  step : ∀ i : Fin n, g (trace i) (trace ⟨(i.val+1)%n,Nat.mod_lt _ positive⟩)=true

def GraphPath.toClosedTrace {x : V} {n : Nat} (p : GraphPath g W x x n)
    (positive : 0<n) : ClosedTrace g W n where
  positive := positive
  trace i := p.point i.val
  valid i := p.valid _ (by have h:=i.isLt;omega)
  step i := by
    have k := i.isLt
    change g (p.point i.val) (p.point ((i.val+1)%n))=true
    by_cases e : i.val+1<n
    · rw [Nat.mod_eq_of_lt e]
      exact p.edge _ k
    · have eq : i.val+1=n := by omega
      rw [eq,Nat.mod_self,p.start.trans p.finish.symm]
      have h := p.edge _ k
      rw [eq] at h
      exact h

def ClosedTrace.at {n : Nat} (C : ClosedTrace g W n) (i : Nat) : V :=
  C.trace ⟨i%n,Nat.mod_lt _ C.positive⟩

theorem ClosedTrace.at_eq_trace {n : Nat} (C : ClosedTrace g W n) (i : Fin n) :
    C.at i.val=C.trace i := by
  unfold ClosedTrace.at
  congr 1
  exact Fin.eq_of_val_eq (Nat.mod_eq_of_lt i.isLt)

theorem ClosedTrace.at_period {n : Nat} (C : ClosedTrace g W n) (i : Nat) :
    C.at (i+n)=C.at i := by
  unfold ClosedTrace.at
  congr 1
  apply Fin.eq_of_val_eq
  change (i+n)%n=i%n
  simp

theorem ClosedTrace.at_next {n : Nat} (C : ClosedTrace g W n) (i : Nat) :
    g (C.at i) (C.at (i+1))=true := by
  unfold ClosedTrace.at
  have h := C.step ⟨i%n,Nat.mod_lt _ C.positive⟩
  have eq : (⟨(i%n+1)%n,Nat.mod_lt _ C.positive⟩ : Fin n)=
      ⟨(i+1)%n,Nat.mod_lt _ C.positive⟩ :=
    Fin.eq_of_val_eq (Nat.mod_add_mod i n 1)
  exact eq ▸ h

def ClosedTrace.cutAt {n : Nat} (C : ClosedTrace g W n) (s d : Nat) (dp : 0<d)
    (same : C.at (s+d)=C.at s) : ClosedTrace g W d where
  positive := dp
  trace i := C.at (s+i.val)
  valid i := C.valid _
  step i := by
    have bound := i.isLt
    change g (C.at (s+i.val)) (C.at (s+(i.val+1)%d))=true
    by_cases e : i.val+1<d
    · rw [Nat.mod_eq_of_lt e,←Nat.add_assoc]
      exact C.at_next _
    · have z : i.val+1=d := by omega
      rw [z,Nat.mod_self,Nat.add_zero,←same]
      have h := C.at_next (s+i.val)
      rwa [show s+i.val+1=s+d by omega] at h

private theorem least_of_exists (P : Nat→Prop) (ex : ∃ n, P n) :
    ∃ n, P n ∧ ∀ m, P m → n≤m := by
  obtain ⟨n,p⟩ := ex
  have aux (k : Nat) : P k → ∃ n, P n ∧ ∀ m, P m → n≤m := by
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro pk
      by_cases smaller : ∃ m, m<k ∧ P m
      · obtain ⟨m,lt,pm⟩ := smaller
        exact ih m lt pm
      · exact ⟨k,pk,fun m pm => by
          by_cases e : k≤m
          · exact e
          · exact False.elim (smaller ⟨m,by omega,pm⟩)⟩
  exact aux n p

/-- A shortest odd closed trace has no repeated vertex. Repetition would
cut it into two genuinely shorter closed traces, one of odd length. -/
theorem shortest_simple_cycle_of_odd_trace (loop : Loopless g)
    (ex : ∃ n, n%2=1 ∧ Nonempty (ClosedTrace g W n)) :
    ∃ n, ∃ C : TraceCycle g n, C.ShortestOdd W := by
  obtain ⟨n,⟨odd,⟨C⟩⟩,minimal⟩ := least_of_exists
    (fun n => n%2=1 ∧ Nonempty (ClosedTrace g W n)) ex
  have no1 : n≠1 := by
    intro one
    have h := C.at_next 0
    change g (C.at 0) (C.at 1)=true at h
    have eq : C.at 1=C.at 0 :=
      (congrArg (fun i=>C.at i) (by omega : 1=0+n)).trans (C.at_period 0)
    rw [eq,loop] at h
    contradiction
  have bound : 3≤n := by have h:=C.positive;omega
  have ordConflict {i j : Fin n} (ord : i.val<j.val) (eq : C.trace i=C.trace j) : False := by
    let d := j.val-i.val
    let e := n-d
    have ij : i.val+d=j.val := by dsimp [d];omega
    have je : j.val+e=i.val+n := by dsimp [d,e];omega
    have dpos : 0<d := by dsimp [d];omega
    have epos : 0<e := by dsimp [e];have h:=j.isLt;omega
    have dn : d<n := by have h:=j.isLt;dsimp [d];omega
    have en : e<n := by dsimp [e];omega
    have eq1 : C.at (i.val+d)=C.at i.val := by
      rw [ij,C.at_eq_trace j,C.at_eq_trace i,eq]
    have eq2 : C.at (j.val+e)=C.at j.val := by
      rw [je,C.at_period,C.at_eq_trace i,C.at_eq_trace j,eq]
    by_cases dOdd : d%2=1
    · have no := minimal d ⟨dOdd,⟨C.cutAt i.val d dpos eq1⟩⟩
      omega
    · have eo : e%2=1 := by dsimp [e];omega
      have no := minimal e ⟨eo,⟨C.cutAt j.val e epos eq2⟩⟩
      omega
  let D : TraceCycle g n :=
    ⟨bound,C.trace,(fun i j eq => by
      by_cases hl : i.val<j.val
      · exact False.elim (ordConflict hl eq)
      · by_cases hr : j.val<i.val
        · exact False.elim (ordConflict hr eq.symm)
        · exact Fin.eq_of_val_eq (by omega)),C.step⟩
  refine ⟨n,D,odd,?_,?_⟩
  · intro v vm
    obtain ⟨i,eq⟩ := List.mem_ofFn.mp vm
    exact eq ▸ C.valid i
  · intro m E eo inside
    exact minimal m ⟨eo,⟨⟨by have h:=E.length_ge_three;omega,E.trace,
      (fun i => inside _ (List.mem_ofFn.mpr ⟨i,rfl⟩)),E.step⟩⟩⟩

private def Reaches (g : V→V→Bool) (W : List V) (x z : V) : Prop :=
  ∃ n, Nonempty (GraphPath g W x z n)

private noncomputable def rootOpt (g : V→V→Bool) (W : List V) (x : V) : Option V :=
  open Classical in (W.filter (fun z=> decide (Reaches g W x z))).head?

private theorem root_reached (x : V) (xm : x∈W) :
    ∃ z, rootOpt g W x=some z ∧ Reaches g W x z := by
  classical
  unfold rootOpt
  have xx : Reaches g W x x := ⟨0,⟨GraphPath.stay xm⟩⟩
  have q : x∈W.filter (fun z=> decide (Reaches g W x z)) :=
    List.mem_filter.mpr ⟨xm,decide_eq_true xx⟩
  cases e : W.filter (fun z=> decide (Reaches g W x z)) with
  | nil => simp [e] at q
  | cons z Z =>
    have zm : z∈W.filter (fun z=> decide (Reaches g W x z)) := by rw [e];simp
    exact ⟨z,rfl,of_decide_eq_true ((List.mem_filter.mp zm).2)⟩

private theorem edge_common_root (symm : Symmetric g) {x y : V} (xm : x∈W)
    (ym : y∈W) (e : g x y=true) : rootOpt g W x = rootOpt g W y := by
  classical
  unfold rootOpt
  congr 1
  apply List.filter_congr
  intro z _
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro ⟨n,⟨p⟩⟩
    exact ⟨1+n,⟨(GraphPath.single ym xm ((symm _ _).trans e)).join p⟩⟩
  · intro ⟨n,⟨p⟩⟩
    exact ⟨1+n,⟨(GraphPath.single xm ym e).join p⟩⟩

private def EvenRoot (g : V→V→Bool) (W : List V) (x : V) : Prop :=
  ∃ z n, rootOpt g W x=some z ∧ n%2=0 ∧ Nonempty (GraphPath g W x z n)

private theorem edge_odd_trace_from_same_parity (symm : Symmetric g)
    {x y z : V} {a b : Nat} (xm : x∈W) (ym : y∈W) (e : g x y=true)
    (px : GraphPath g W x z a) (py : GraphPath g W y z b) (same : a%2=b%2) :
    ∃ n, n%2=1 ∧ Nonempty (ClosedTrace g W n) := by
  let w := ((GraphPath.single xm ym e).join py).join (px.reverse symm)
  exact ⟨1+b+a,by omega,⟨w.toClosedTrace (by omega)⟩⟩

/-- Every graph with no odd closed trace admits an actual bipartition of W.
The even/odd paths used are confined to W and share a component root. -/
theorem bipartition_of_no_odd_trace (symm : Symmetric g)
    (no : ¬ ∃ n, n%2=1 ∧ Nonempty (ClosedTrace g W n)) :
    ∃ A B : List V, (A++B).Perm W ∧
      (∀ x∈A, ∀ y∈A, g x y=false) ∧
      (∀ x∈B, ∀ y∈B, g x y=false) := by
  classical
  let A := W.filter (fun x=>decide (EvenRoot g W x))
  let B := W.filter (fun x=> !decide (EvenRoot g W x))
  refine ⟨A,B,List.filter_append_perm _ _,?_,?_⟩
  · intro x xm y ym
    obtain ⟨xw,ex⟩ := List.mem_filter.mp xm
    obtain ⟨yw,ey⟩ := List.mem_filter.mp ym
    have xev : EvenRoot g W x := of_decide_eq_true ex
    have yev : EvenRoot g W y := of_decide_eq_true ey
    cases e : g x y
    · rfl
    · exfalso
      have roots := edge_common_root symm xw yw e
      obtain ⟨s,a,rx,ap,⟨px⟩⟩ := xev
      obtain ⟨t,b,ry,bp,⟨py⟩⟩ := yev
      have st : s=t := Option.some.inj (rx.symm.trans (roots.trans ry))
      subst t
      exact no (edge_odd_trace_from_same_parity symm xw yw e px py (ap.trans bp.symm))
  · intro x xm y ym
    obtain ⟨xw,ex⟩ := List.mem_filter.mp xm
    obtain ⟨yw,ey⟩ := List.mem_filter.mp ym
    have xno : ¬EvenRoot g W x := by simpa using ex
    have yno : ¬EvenRoot g W y := by simpa using ey
    cases e : g x y
    · rfl
    · exfalso
      have roots := edge_common_root symm xw yw e
      obtain ⟨s,rx,a,⟨px⟩⟩ := root_reached x xw
      obtain ⟨t,ry,b,⟨py⟩⟩ := root_reached y yw
      have st : s=t := Option.some.inj (rx.symm.trans (roots.trans ry))
      subst t
      have na : a%2≠0 := fun zero => xno ⟨s,a,rx,zero,⟨px⟩⟩
      have nb : b%2≠0 := fun zero => yno ⟨s,b,ry,zero,⟨py⟩⟩
      exact no (edge_odd_trace_from_same_parity symm xw yw e px py (by omega))

/-- The usable non-bipartite-to-shortest-cycle bridge for the h=1
argument. At order 2r−1, the actual independence cap r−1 excludes any
bipartition; the finite graph therefore contains a shortest odd cycle. -/
theorem shortest_odd_of_tight_independence (symm : Symmetric g) (loop : Loopless g)
    (W : List V) (r : Nat) (hr : 1≤r) (nd : W.Nodup) (size : W.length=2*r-1)
    (cap : ∀ I : List V, I.Nodup → (∀ x∈I, x∈W) →
      (∀ x∈I, ∀ y∈I, g x y=false) → I.length≤r-1) :
    ∃ n, ∃ C : TraceCycle g n, C.ShortestOdd W := by
  apply shortest_simple_cycle_of_odd_trace loop
  apply Classical.byContradiction
  intro no
  obtain ⟨A,B,p,ia,ib⟩ := bipartition_of_no_odd_trace symm no
  have both := List.nodup_append.mp (p.nodup_iff.mpr nd)
  have ac := cap A both.1 (fun x xm => p.mem_iff.mp (List.mem_append_left _ xm)) ia
  have bc := cap B both.2.1 (fun x xm => p.mem_iff.mp (List.mem_append_right _ xm)) ib
  have diag := p.length_eq
  rw [List.length_append] at diag
  omega

end ParallelMantel

#print axioms ParallelMantel.shortest_simple_cycle_of_odd_trace
#print axioms ParallelMantel.bipartition_of_no_odd_trace
#print axioms ParallelMantel.shortest_odd_of_tight_independence
