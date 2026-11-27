module

public import Palomar.Erdos617PairStarDouble.Support.PairColoring
public import Palomar.Erdos617PairStarDouble.Support.NonbipartiteMantel
public import Lean.Elab.Tactic.Omega

@[expose] public section

namespace ParallelMantel.Pentagon

open Erdos617Geometry

universe u
variable {V : Type u} {r : Nat} {col : V → V → Fin r} {t : Fin r}

noncomputable abbrev NormalizedPair.miss (M : NormalizedPair col t) :=
  missingColor col t (M.vertices M.exceptions)

private theorem miss_true {W : List V} {x y : V} :
    missingColor col t W x y=true ↔ x∈W ∧ y∈W ∧ x≠y ∧ col x y≠t := by
  simp [missingColor]

private theorem miss_false {W : List V} {x y : V} (e : col x y=t) :
    missingColor col t W x y=false := by
  rw [← Bool.not_eq_true]
  exact fun h => (miss_true.mp h).2.2.2 e

private theorem left_in (M : NormalizedPair col t) {x : V} (h : x∈M.left) :
    x∈M.vertices M.exceptions := List.mem_append_left _ h

private theorem right_in (M : NormalizedPair col t) {x : V} (h : x∈M.right) :
    x∈M.vertices M.exceptions := List.mem_append_right _ (List.mem_append_left _ h)

private theorem ex_in (M : NormalizedPair col t) {x : V} (h : x∈M.exceptions) :
    x∈M.vertices M.exceptions := List.mem_append_right _ (List.mem_append_right _ h)

private theorem ex_anchors (M : NormalizedPair col t) {x : V} (h : x∈M.exceptions) :
    M.miss x M.p=false ∧ M.miss x M.q=false := by
  have d := M.double x h
  exact ⟨miss_false d.owner_adj,miss_false d.source_adj⟩

private theorem left_to_q (M : NormalizedPair col t) {x : V} (h : x∈M.left) :
    M.miss x M.q=true := by
  obtain ⟨ne,no⟩ := (M.privateLeft x h).away M.q M.q_mem (Ne.symm M.pq)
  exact miss_true.mpr ⟨left_in M h,right_in M M.q_right,ne,no⟩

private theorem right_to_p (M : NormalizedPair col t) {x : V} (h : x∈M.right) :
    M.miss x M.p=true := by
  obtain ⟨ne,no⟩ := (M.privateRight x h).away M.p M.p_mem M.pq
  exact miss_true.mpr ⟨right_in M h,left_in M M.p_left,ne,no⟩

private def five (a b c d e : V) (i : Fin 5) : V :=
  if i=0 then a else if i=1 then b else if i=2 then c else if i=3 then d else e

private theorem cases5 (i : Fin 5) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 :=
  (by decide : ∀ i : Fin 5, i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4) i

private theorem five_list (a b c d e : V) :
    List.ofFn (five a b c d e) = [a,b,c,d,e] := by
  rw [List.ofFn_succ,List.ofFn_succ,List.ofFn_succ,List.ofFn_succ,List.ofFn_succ,List.ofFn_zero]
  rfl

private def traceOfFive {g : V→V→Bool} {a b c d e : V}
    (nd : [a,b,c,d,e].Nodup) (ab : g a b=true) (bc : g b c=true) (cd : g c d=true)
    (de : g d e=true) (ea : g e a=true) : TraceCycle g 5 :=
  ⟨by decide, five a b c d e, (by
    intro i j eq
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at nd
    rcases cases5 i with h|h|h|h|h <;> subst i <;>
      rcases cases5 j with h|h|h|h|h <;> subst j <;>
      simp [five] at eq ⊢ <;> grind), (by
    intro i
    rcases cases5 i with h|h|h|h|h <;> subst i <;> first | exact ab | exact bc | exact cd | exact de | exact ea)⟩

private theorem traceOfFive_list {g : V→V→Bool} {a b c d e : V}
    (nd : [a,b,c,d,e].Nodup) (ab : g a b=true) (bc : g b c=true) (cd : g c d=true)
    (de : g d e=true) (ea : g e a=true) :
    (traceOfFive nd ab bc cd de ea).vertices=[a,b,c,d,e] :=
  five_list a b c d e

private theorem list_ne_left {A B : List V} (n : (A++B).Nodup)
    {x y : V} (xa : x∈A) (yb : y∈B) : x≠y :=
  (List.nodup_append.mp n).2.2 x xa y yb

/-- In an actual normalized color pair, a double-supported exception missing
at least one edge to each row forces the specific induced pentagon whose
only exceptional vertex is that very exception. -/
theorem NormalizedPair.canonical_five [BEq V] [LawfulBEq V] (M : NormalizedPair col t)
    (symm : ∀ x y, col x y=col y x) {x u v : V}
    (xm : x∈M.exceptions) (um : u∈M.left) (vm : v∈M.right)
    (xu : M.miss x u=true) (xv : M.miss x v=true) :
    ∃ C : TraceCycle M.miss 5, C.vertices=[M.p,M.q,u,x,v] ∧
      C.ShortestOdd (M.vertices M.exceptions) := by
  have sg := missingColor_symmetric col symm t (M.vertices M.exceptions)
  have hg := M.missing_triangle_free (List.Sublist.refl M.exceptions)
  have ab : M.miss M.p M.q=true := left_to_q M M.p_left
  have bc : M.miss M.q u=true := (sg _ _).trans (left_to_q M um)
  have cd : M.miss u x=true := (sg _ _).trans xu
  have ea : M.miss v M.p=true := right_to_p M vm
  have neP : M.p≠u := by
    intro e
    rw [← e,(ex_anchors M xm).1] at xu
    contradiction
  have neQ : M.q≠v := by
    intro e
    rw [← e,(ex_anchors M xm).2] at xv
    contradiction
  have nd := M.disjointLists
  have leftRight {a b : V} (am : a∈M.left) (bm : b∈M.right) : a≠b :=
    list_ne_left nd am (List.mem_append_left _ bm)
  have leftEx {a b : V} (am : a∈M.left) (bm : b∈M.exceptions) : a≠b :=
    list_ne_left nd am (List.mem_append_right _ bm)
  have rightEx {a b : V} (am : a∈M.right) (bm : b∈M.exceptions) : a≠b :=
    list_ne_left (List.nodup_append.mp nd).2.1 am bm
  have cycND : [M.p,M.q,u,x,v].Nodup := by
    simp [List.nodup_cons, M.pq,neP,neQ,leftEx M.p_left xm,leftRight M.p_left vm,
      Ne.symm (leftRight um M.q_right), rightEx M.q_right xm, leftEx um xm,
      leftRight um vm,Ne.symm (rightEx vm xm)]
  let C := traceOfFive cycND ab bc cd xv ea
  have main : C.vertices=[M.p,M.q,u,x,v] := traceOfFive_list cycND ab bc cd xv ea
  refine ⟨C,main, by decide,?_,?_⟩
  · intro w wm
    rw [main] at wm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at wm
    rcases wm with e|e|e|e|e <;> subst w
    · exact left_in M M.p_left
    · exact right_in M M.q_right
    · exact left_in M um
    · exact ex_in M xm
    · exact right_in M vm
  · intro n D odd _
    exact D.odd_length_ge_five sg hg odd


private theorem cut_sublist (g : V→V→Bool) {L A : List V}
    (s : L.Sublist A) (B : List V) : cut g L B ≤ cut g A B := by
  induction s with
  | slnil => exact Nat.le_refl _
  | cons a h ih =>
    change _ ≤ degree g a B + cut g _ B
    omega
  | cons_cons a h ih =>
    change degree g a B+cut g _ B ≤ degree g a B+cut g _ B
    omega

private theorem cut_lo (g : V→V→Bool) (A B : List V) (k : Nat)
    (lower : ∀ x∈A, k≤degree g x B) : A.length*k ≤ cut g A B := by
  induction A with
  | nil => simp [cut]
  | cons x A ih =>
    have tail := ih (fun y ym => lower y (List.mem_cons_of_mem _ ym))
    have head := lower x (by simp)
    change (A.length+1)*k ≤ degree g x B+cut g A B
    rw [Nat.add_mul,Nat.one_mul]
    omega

private theorem missing_rectangle {g : V→V→Bool} {L R A B : List V}
    (lnd : L.Nodup) (rnd : R.Nodup) (la : L ⊆ A) (rb : R ⊆ B)
    (holes : ∀ a∈L, ∀ b∈R, g a b=false) :
    L.length*R.length ≤ cut (fun x y => !g x y) A B := by
  classical
  let F := A.filter (fun x => decide (x∈L))
  have fs : F.Sublist A := List.filter_sublist
  have lf : L ⊆ F := by
    intro x xm
    exact List.mem_filter.mpr ⟨la xm,decide_eq_true xm⟩
  have llen := lnd.length_le_of_subset lf
  have lo : ∀ x∈F, R.length≤degree (fun x y => !g x y) x B := by
    intro x xm
    have l : x∈L := of_decide_eq_true (List.mem_filter.mp xm).2
    exact rnd.length_le_of_subset (fun y ym =>
      List.mem_filter.mpr ⟨rb ym,by simp [holes x l y ym]⟩)
  exact Nat.le_trans (Nat.mul_le_mul_right R.length llen)
    (Nat.le_trans (cut_lo _ F B R.length lo) (cut_sublist _ fs B))

private theorem pure_of_large_independent {g : V→V→Bool} {A B R : List V}
    (nd : (A++B).Nodup) (rND : R.Nodup) (rs : R ⊆ A++B)
    (ri : ∀ x∈R, ∀ y∈R, g x y=false)
    (S : Nat) (missing : cut (fun a b => !g a b) A B≤S)
    (large : S+1<R.length) : R ⊆ A ∨ R ⊆ B := by
  classical
  let L := A.filter (fun x => decide (x∈R))
  let H := B.filter (fun x => decide (x∈R))
  have lnd := (List.filter_sublist (p:=fun x => decide (x∈R)) (l:=A)).nodup (List.nodup_append.mp nd).1
  have hnd := (List.filter_sublist (p:=fun x => decide (x∈R)) (l:=B)).nodup (List.nodup_append.mp nd).2.1
  have lp : L ⊆ A := fun _ m => (List.mem_filter.mp m).1
  have hp : H ⊆ B := fun _ m => (List.mem_filter.mp m).1
  have lr : L ⊆ R := fun _ m => of_decide_eq_true (List.mem_filter.mp m).2
  have hr : H ⊆ R := fun _ m => of_decide_eq_true (List.mem_filter.mp m).2
  have lhn : (L++H).Nodup := by
    apply List.nodup_append.mpr
    exact ⟨lnd,hnd,fun a am b bm => (List.nodup_append.mp nd).2.2 a (lp am) b (hp bm)⟩
  have cover : (L++H).Perm R := by
    apply (List.perm_ext_iff_of_nodup lhn rND).mpr
    intro x
    constructor
    · intro xm
      exact (List.mem_append.mp xm).elim (fun m => lr m) (fun m => hr m)
    · intro xm
      rcases List.mem_append.mp (rs xm) with a|b
      · exact List.mem_append_left _ (List.mem_filter.mpr ⟨a,decide_eq_true xm⟩)
      · exact List.mem_append_right _ (List.mem_filter.mpr ⟨b,decide_eq_true xm⟩)
  by_cases l : L=[]
  · right
    intro x xm
    have h := cover.mem_iff.mpr xm
    rw [l,List.nil_append] at h
    exact hp h
  by_cases h : H=[]
  · left
    intro x xm
    have hh := cover.mem_iff.mpr xm
    rw [h,List.append_nil] at hh
    exact lp hh
  have ll : 0<L.length := List.length_pos_iff.mpr l
  have hh : 0<H.length := List.length_pos_iff.mpr h
  have rect := missing_rectangle lnd hnd lp hp (fun x xm y ym => ri x (lr xm) y (hr ym))
  change L.length*H.length ≤ cut (fun x y => !g x y) A B at rect
  have shape := cover.length_eq
  rw [List.length_append] at shape
  have arith (a b : Nat) : (a+1)*(b+1) = a*b+(a+b+1) := by
    rw [Nat.mul_add,Nat.add_mul,Nat.one_mul,Nat.mul_one]
    omega
  have q := arith (L.length-1) (H.length-1)
  rw [show L.length-1+1=L.length by omega,show H.length-1+1=H.length by omega] at q
  exact False.elim (by omega)

private theorem degree_cons_case (g : V→V→Bool) (x a : V) (A : List V) :
    degree g x (a::A) = (if g x a then 1 else 0) + degree g x A := by
  cases q : g x a <;> simp [degree,q] <;> omega

private theorem degree_eq_zero {g : V→V→Bool} {x : V} {A : List V}
    (no : ∀ y∈A, g x y=false) : degree g x A=0 := by
  have h : A.filter (g x)=[] := List.filter_eq_nil_iff.mpr (fun y ym => by simp [no y ym])
  simp [degree,h]

private theorem in_row_independent (M : NormalizedPair col t)
    (R : List V) (symm : ∀ x y, col x y=col y x)
    (cl : R.Pairwise (fun x y => col x y=t)) :
    ∀ x∈R, ∀ y∈R, M.miss x y=false := by
  intro x xm y ym
  have pf : R.Pairwise (fun a b=>M.miss a b=false) := cl.imp (fun h=>miss_false h)
  have pff : R.Pairwise (fun a b=>M.miss b a=false) := cl.imp (fun {a b} h=>by
    apply miss_false
    rw [symm b a]
    exact h)
  exact List.Pairwise.forall_of_forall_of_flip
    (fun a _=>missingColor_loopless col t (M.vertices M.exceptions) a) pf pff xm ym



private theorem remove_two [BEq V] [LawfulBEq V] {R : List V} {a b : V}
    (nd : R.Nodup) (am : a∈R) (bm : b∈R) (ab : a≠b) :
    (a::b::(R.erase a).erase b).Perm R := by
  have inE : b∈R.erase a := nd.mem_erase_iff.mpr ⟨Ne.symm ab,bm⟩
  exact ((List.perm_cons_erase inE).symm.cons a).trans (List.perm_cons_erase am).symm

private theorem row_hole_count {g : V→V→Bool} {R O : List V} {a b x : V}
    (p : (a::b::O).Perm R) (anch : g x a=false) :
    degree g x R ≤ 1+degree g x O := by
  have h : degree g x (a::b::O)=degree g x R := (p.filter (g x)).length_eq
  rw [degree_cons_case,anch,degree_cons_case] at h
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add] at h
  split at h <;> omega

private theorem degree_cap_of_rectangle {g : V→V→Bool} {A B P Q : List V}
    (tri : TriangleFree g) (ndP : P.Nodup) (ndQ : Q.Nodup)
    (p : P⊆A) (q : Q⊆B) (x : V) (S K : Nat)
    (budget : cut (fun a b=> !g a b) A B≤S)
    (sq : S<(K+1)*(K+1)) : degree g x P≤K ∨ degree g x Q≤K := by
  let U := P.filter (g x)
  let W := Q.filter (g x)
  have us : U.Sublist P := List.filter_sublist
  have ws : W.Sublist Q := List.filter_sublist
  have rect := missing_rectangle (us.nodup ndP) (ws.nodup ndQ)
    (fun _ m=>p (us.subset m)) (fun _ m=>q (ws.subset m))
    (fun a am b bm=>tri x a b (List.mem_filter.mp am).2 (List.mem_filter.mp bm).2)
  change degree g x P * degree g x Q≤cut (fun a b=> !g a b) A B at rect
  by_cases psmall : degree g x P≤K
  · exact Or.inl psmall
  · right
    apply Classical.byContradiction
    intro qlarge
    have m := Nat.mul_le_mul (by omega : K+1≤degree g x P) (by omega : K+1≤degree g x Q)
    omega

private theorem nodup_both_rows (M : NormalizedPair col t) : M.left.Nodup ∧ M.right.Nodup :=
  ⟨(List.nodup_append.mp M.disjointLists).1,
    (List.nodup_append.mp (List.nodup_append.mp M.disjointLists).2.1).1⟩

private theorem filtered_cycle_partition {g : V→V→Bool} {n : Nat}
    (C : TraceCycle g n) (W : List V) (nd : W.Nodup)
    (Csub : C.vertices⊆W) :
    ∃ O : List V, (C.vertices++O).Perm W ∧ ∀ z∈W, z∉C.vertices → z∈O := by
  classical
  let f (z : V) : Bool := decide (z∈C.vertices)
  let O := W.filter (fun z=> !f z)
  have eq : (W.filter f).Perm C.vertices := by
    apply (List.perm_ext_iff_of_nodup (List.filter_sublist.nodup nd) C.vertices_nodup).mpr
    intro x
    constructor
    · intro m
      exact of_decide_eq_true (List.mem_filter.mp m).2
    · intro m
      exact List.mem_filter.mpr ⟨Csub m,decide_eq_true m⟩
  refine ⟨O,(eq.symm.append_right O).trans (List.filter_append_perm f W),?_⟩
  intro z zw zn
  exact List.mem_filter.mpr ⟨zw,by simp [f,zn]⟩

private theorem pair_rows_apart (M : NormalizedPair col t)
    {L R A B : List V} (l : L.Sublist M.left) (rr : R.Sublist M.right)
    (psub : (A++B)⊆M.vertices M.exceptions)
    (ai : ∀ x∈A, ∀ y∈A, M.miss x y=false)
    (bi : ∀ x∈B, ∀ y∈B, M.miss x y=false)
    (ls : L ⊆ A ∨ L ⊆ B) (rs : R ⊆ A ∨ R ⊆ B)
    (large : r-1<L.length+R.length) :
    (L⊆A ∧ R⊆B) ∨ (L⊆B ∧ R⊆A) := by
  have both (D : List V) (ds : D⊆M.vertices M.exceptions)
      (di : ∀ x∈D, ∀ y∈D, M.miss x y=false) (la : L⊆D) (ra : R⊆D) : False := by
    have extra : (M.left++M.right).Sublist (M.vertices M.exceptions) := by
      rw [NormalizedPair.vertices,← List.append_assoc]
      exact List.sublist_append_left _ _
    have mergedSub := (l.append rr).trans extra
    have nd := mergedSub.nodup M.disjointLists
    have inside : (L++R)⊆D := fun _ hm => (List.mem_append.mp hm).elim (fun m=>la m) (fun m=>ra m)
    have cap := M.missing_independence_cap (List.Sublist.refl M.exceptions)
      (L++R) nd (fun _ hm=>ds (inside hm)) (fun x xm y ym=>di x (inside xm) y (inside ym))
    rw [List.length_append] at cap
    omega
  rcases ls with la|lb <;> rcases rs with ra|rb
  · exact False.elim (both A (fun _ m=>psub (List.mem_append_left B m)) ai la ra)
  · exact Or.inl ⟨la,rb⟩
  · exact Or.inr ⟨lb,ra⟩
  · exact False.elim (both B (fun _ m=>psub (List.mem_append_right A m)) bi lb rb)


private theorem neighbor_of_positive_degree {g : V→V→Bool} {x : V} {R : List V}
    (h : 0<degree g x R) : ∃ y∈R, g x y=true := by
  cases e : R.filter (g x) with
  | nil => simp [degree,e] at h
  | cons y Y =>
    have ym : y∈R.filter (g x) := by rw [e];simp
    exact ⟨y,(List.mem_filter.mp ym).1,(List.mem_filter.mp ym).2⟩

/-- Actual color pair with a simultaneously small private-row hole count for
every exception except at most one. The numerical premises are the exact
pentagon-exterior ledger/gap/row-size tests; the conclusion uses the original
private rows and all original shared exceptions. No partition is assumed. -/
theorem NormalizedPair.one_costly_exception_ledger [BEq V] [LawfulBEq V]
    (M : NormalizedPair col t) (symm : ∀ x y, col x y=col y x)
    (bal : Balanced col r)
    (leftClique : M.left.Pairwise (fun x y=>col x y=t))
    (rightClique : M.right.Pairwise (fun x y=>col x y=t))
    (S K : Nat)
    (gap : S+1<((M.vertices M.exceptions).length-5)/2)
    (ledger : mantelBound ((M.vertices M.exceptions).length-5) +
      2*((M.vertices M.exceptions).length-5) + 5 ≤
      (r-1)*((M.vertices M.exceptions).length-r)+S)
    (wideL : S+3<M.left.length) (wideR : S+3<M.right.length)
    (apart : r+3<M.left.length+M.right.length)
    (sq : S<(K+1)*(K+1)) :
    ∃ exceptional : Option V, ∃ routeLeft : V → Bool,
      ∀ x∈M.exceptions,
        let holes := if routeLeft x then degree M.miss x M.left else degree M.miss x M.right
        holes≤1 ∨ (exceptional=some x ∧ holes≤K+1) := by
  classical
  let W := M.vertices M.exceptions
  let g := M.miss
  have gs : Symmetric g := missingColor_symmetric col symm t W
  have gl : Loopless g := missingColor_loopless col t W
  have gt : TriangleFree g := M.missing_triangle_free (List.Sublist.refl M.exceptions)
  have ndW : W.Nodup := M.disjointLists
  have nd := nodup_both_rows M
  have lcl := in_row_independent M M.left symm leftClique
  have rcl := in_row_independent M M.right symm rightClique

  have routing (E : Option V)
      (h : ∀ y∈M.exceptions,
        let k := if E=some y then K+1 else 1
        degree g y M.left≤k ∨ degree g y M.right≤k) :
      ∃ routeLeft : V→Bool, ∀ y∈M.exceptions,
        let holes := if routeLeft y then degree g y M.left else degree g y M.right
        holes≤1 ∨ (E=some y ∧ holes≤K+1) := by
    let f (y : V) : Bool := decide (degree g y M.left ≤ if E=some y then K+1 else 1)
    refine ⟨f,?_⟩
    intro y ym
    have or := h y ym
    dsimp only at or
    by_cases he : E=some y
    · right
      refine ⟨he,?_⟩
      simp only [he, ite_true] at or
      dsimp only [f]
      simp only [he,ite_true,decide_eq_true_eq]
      split
      · assumption
      · exact or.resolve_left (by assumption)
    · left
      simp only [he, ite_false] at or
      dsimp only [f]
      simp only [he,ite_false,decide_eq_true_eq]
      split
      · assumption
      · exact or.resolve_left (by assumption)

  by_cases bad : ∃ x∈M.exceptions, 0<degree g x M.left ∧ 0<degree g x M.right
  · obtain ⟨x,xm,xl,xr⟩ := bad
    obtain ⟨u,um,xu⟩ := neighbor_of_positive_degree xl
    obtain ⟨v,vm,xv⟩ := neighbor_of_positive_degree xr
    obtain ⟨C,ceq,short⟩ := M.canonical_five symm xm um vm xu xv
    obtain ⟨O,part,exterior⟩ := filtered_cycle_partition C W ndW (fun _ m=>short.2.1 _ m)
    have ol := part.length_eq
    rw [List.length_append,show C.vertices.length=5 from List.length_ofFn] at ol
    have olen : O.length=W.length-5 := by omega
    have floor := missingColor_floor col t bal W ndW
    have gap' : S+1<O.length/2 := by rwa [olen]
    have dens : mantelBound O.length+2*O.length+5≤edges g W+S := by
      rw [olen]
      exact Nat.le_trans ledger (Nat.add_le_add_right floor S)
    obtain ⟨A,B,ab,ai,bi,res⟩ := C.dense_fiveExterior_split gs gl gt W O ndW part short S gap' dens
    change cut (fun a b=> !g a b) A B+(2*O.length-cut g O C.vertices)≤S at res
    have cross : cut (fun a b=> !g a b) A B≤S := by omega
    have abd := ab.nodup_iff.mpr (List.nodup_append.mp (part.nodup_iff.mpr ndW)).2.1
    have cover (z : V) (zm : z∈W) (zc : z∉C.vertices) : z∈A++B :=
      ab.mem_iff.mpr (exterior z zm zc)
    have noP : M.p≠u := by
      intro e
      change M.miss x u=true at xu
      rw [← e,(ex_anchors M xm).1] at xu
      contradiction
    have noQ : M.q≠v := by
      intro e
      change M.miss x v=true at xv
      rw [← e,(ex_anchors M xm).2] at xv
      contradiction
    let L := (M.left.erase M.p).erase u
    let R := (M.right.erase M.q).erase v
    have lsub : L.Sublist M.left := List.erase_sublist.trans List.erase_sublist
    have rsub : R.Sublist M.right := List.erase_sublist.trans List.erase_sublist
    have lp : (M.p::u::L).Perm M.left := remove_two nd.1 M.p_left um noP
    have rp : (M.q::v::R).Perm M.right := remove_two nd.2 M.q_right vm noQ
    have ll := lp.length_eq
    have rl := rp.length_eq
    simp only [List.length_cons] at ll rl

    have leftRight {a b : V} (am : a∈M.left) (bm : b∈M.right) : a≠b :=
      list_ne_left M.disjointLists am (List.mem_append_left _ bm)
    have leftEx {a b : V} (am : a∈M.left) (bm : b∈M.exceptions) : a≠b :=
      list_ne_left M.disjointLists am (List.mem_append_right _ bm)
    have rightEx {a b : V} (am : a∈M.right) (bm : b∈M.exceptions) : a≠b :=
      list_ne_left (List.nodup_append.mp M.disjointLists).2.1 am bm

    have la : L⊆A++B := by
      intro z zm
      have xl : z∈M.left := lsub.subset zm
      obtain ⟨nu,ze⟩ := (nd.1.erase M.p).mem_erase_iff.mp zm
      have np := (nd.1.mem_erase_iff.mp ze).1
      exact cover z (left_in M xl) (by simp [ceq,np,nu,leftRight xl M.q_right,leftEx xl xm,leftRight xl vm])
    have ra : R⊆A++B := by
      intro z zm
      have xr : z∈M.right := rsub.subset zm
      obtain ⟨nv,ze⟩ := (nd.2.erase M.q).mem_erase_iff.mp zm
      have nq := (nd.2.mem_erase_iff.mp ze).1
      exact cover z (right_in M xr) (by simp [ceq,nq,nv,Ne.symm (leftRight M.p_left xr),
        Ne.symm (leftRight um xr),rightEx xr xm])
    have exOut : ∀ y∈M.exceptions, y≠x → y∈A++B := by
      intro y ym ne
      exact cover y (ex_in M ym) (by simp [ceq,ne,Ne.symm (leftEx M.p_left ym),
        Ne.symm (rightEx M.q_right ym),Ne.symm (leftEx um ym),Ne.symm (rightEx vm ym)])
    have lpure := pure_of_large_independent abd (lsub.nodup nd.1) la
      (fun a am b bm=>lcl a (lsub.subset am) b (lsub.subset bm)) S cross (by omega)
    have rpure := pure_of_large_independent abd (rsub.nodup nd.2) ra
      (fun a am b bm=>rcl a (rsub.subset am) b (rsub.subset bm)) S cross (by omega)
    have both := pair_rows_apart M lsub rsub
      (fun _ m=>part.mem_iff.mp (List.mem_append_right _ (ab.mem_iff.mp m))) ai bi lpure rpure (by omega)
    have expensive : degree g x L≤K ∨ degree g x R≤K := by
      rcases both with ⟨la,rb⟩|⟨lb,ra⟩
      · exact degree_cap_of_rectangle gt (lsub.nodup nd.1) (rsub.nodup nd.2) la rb x S K cross sq
      · exact (degree_cap_of_rectangle gt (rsub.nodup nd.2) (lsub.nodup nd.1) ra lb x S K cross sq).symm
    have cheap : ∀ y∈M.exceptions, y≠x →
        degree g y L=0 ∨ degree g y R=0 := by
      intro y ym ne
      rcases both with ⟨la,rb⟩|⟨lb,ra⟩ <;> rcases List.mem_append.mp (exOut y ym ne) with a|b
      · exact Or.inl (degree_eq_zero (fun z zm=>ai y a z (la zm)))
      · exact Or.inr (degree_eq_zero (fun z zm=>bi y b z (rb zm)))
      · exact Or.inr (degree_eq_zero (fun z zm=>ai y a z (ra zm)))
      · exact Or.inl (degree_eq_zero (fun z zm=>bi y b z (lb zm)))
    refine ⟨some x,routing (some x) ?_⟩
    intro y ym
    have cl := row_hole_count lp (ex_anchors M ym).1
    have cr := row_hole_count rp (ex_anchors M ym).2
    change degree g y M.left≤1+degree g y L at cl
    change degree g y M.right≤1+degree g y R at cr
    by_cases same : y=x
    · subst y
      simp only [ite_true]
      exact expensive.elim (fun h=>Or.inl (by omega)) (fun h=>Or.inr (by omega))
    · simp only [Option.some.injEq,Ne.symm same,ite_false]
      exact (cheap y ym same).elim (fun h=>Or.inl (by omega)) (fun h=>Or.inr (by omega))
  · refine ⟨none,routing none ?_⟩
    intro y ym
    simp only [reduceCtorEq,ite_false]
    by_cases p : degree g y M.left≤1
    · exact Or.inl p
    · right
      apply Classical.byContradiction
      intro q
      exact bad ⟨y,ym,by omega,by omega⟩


/-- Exact exterior count identity for the actual pair residual. -/
theorem pair_exterior_arithmetic (r h : Nat) (hp : 2≤h) (rh : h+3≤r) :
    let m := 2*r-h-5
    mantelBound m+2*m+5 = (r-1)*(r-h)+(mantelBound (h-1)+1) := by
  dsimp only
  let a := r-h-3
  have defineR : r=a+h+3 := by dsimp [a];omega
  by_cases odd : h%2=1
  · let k := (h-1)/2
    have hk : h=2*k+1 := by dsimp [k];omega
    have m : 2*r-h-5=2*(a+k+1) := by omega
    have r1 : r-1=a+(k+k)+3 := by omega
    have rh' : r-h=a+3 := by omega
    have h1 : h-1=2*k := by omega
    rw [m,r1,rh',h1]
    unfold mantelBound
    rw [show (2*(a+k+1))/2=a+k+1 by omega,
      show (2*(a+k+1)+1)/2=a+k+1 by omega,
      show (2*k)/2=k by omega,show (2*k+1)/2=k by omega]
    simp only [Nat.mul_add,Nat.add_mul]
    rw [Nat.mul_comm k a]
    omega
  · let k := (h-2)/2
    have hk : h=2*k+2 := by dsimp [k];omega
    have m : 2*r-h-5=2*(a+k+1)+1 := by omega
    have r1 : r-1=a+(k+k)+4 := by omega
    have rh' : r-h=a+3 := by omega
    have h1 : h-1=2*k+1 := by omega
    rw [m,r1,rh',h1]
    unfold mantelBound
    rw [show (2*(a+k+1)+1)/2=a+k+1 by omega,
      show (2*(a+k+1)+1+1)/2=a+k+2 by omega,
      show (2*k+1)/2=k by omega,show (2*k+1+1)/2=k+1 by omega]
    simp only [Nat.mul_add,Nat.add_mul]
    rw [Nat.mul_comm k a]
    omega

def NormalizedPair.residual (M : NormalizedPair col t) : Nat :=
  M.ld + M.rd - M.exceptions.length

def NormalizedPair.exteriorBudget (M : NormalizedPair col t) : Nat :=
  mantelBound (M.residual-1)+1

/-- Source-matched internal bundle routing. Both rows are genuine cliques
of the target hue, and all exceptions satisfy their actual two-anchor words
inside a normalized pair. The deficit budget is computed from this pair,
not supplied as an abstract density hypothesis. -/
theorem NormalizedPair.one_costly_exception [BEq V] [LawfulBEq V]
    (M : NormalizedPair col t) (symm : ∀ x y, col x y=col y x)
    (bal : Balanced col r) (hr : 12≤r)
    (hd : 3≤M.ld) (he : 3≤M.rd)
    (leftClique : M.left.Pairwise (fun x y=>col x y=t))
    (rightClique : M.right.Pairwise (fun x y=>col x y=t))
    (K : Nat)
    (gap : M.exteriorBudget+1<(2*r-M.residual-5)/2)
    (wideL : M.exteriorBudget+3<M.left.length)
    (wideR : M.exteriorBudget+3<M.right.length)
    (apart : M.ld+M.rd+3<r)
    (sq : M.exteriorBudget<(K+1)*(K+1)) :
    ∃ exceptional : Option V, ∃ routeLeft : V → Bool,
      ∀ x∈M.exceptions,
        let holes := if routeLeft x then degree M.miss x M.left else degree M.miss x M.right
        holes≤1 ∨ (exceptional=some x ∧ holes≤K+1) := by
  let h := M.residual
  have mulBound := M.high_parallel_multiplicity_bound symm bal hr hd he
  have hEq : h=M.ld+M.rd-M.exceptions.length := rfl
  have hsmall := M.normalizedSum
  have wl := M.leftSize
  have wr := M.rightSize
  have hmin : 2≤h := by omega
  have hrh : h+3≤r := by omega
  have wEq : (M.vertices M.exceptions).length=2*r-h := by
    simp only [NormalizedPair.vertices,List.length_append]
    omega
  have expL : r+3<M.left.length+M.right.length := by omega
  have bill := pair_exterior_arithmetic r h hmin hrh
  have sumL : (M.vertices M.exceptions).length-r=r-h := by rw [wEq];omega
  have Sdef : M.exteriorBudget=mantelBound (h-1)+1 := rfl
  apply M.one_costly_exception_ledger symm bal leftClique rightClique M.exteriorBudget K
  · rw [wEq]; exact gap
  · rw [sumL,wEq,Sdef]
    exact Nat.le_of_eq bill
  · exact wideL
  · exact wideR
  · exact expL
  · exact sq

private theorem nonedge_list (g : V→V→Bool) (A : List V)
    (ind : ∀ x∈A, ∀ y∈A, g x y=false) : edges g A=0 := by
  induction A with
  | nil => rfl
  | cons x A ih =>
    have dz := degree_eq_zero (fun y (ym : y∈A)=>ind x (by simp) y (List.mem_cons_of_mem _ ym))
    rw [edges,dz,ih (fun y ym z zm=>ind y (List.mem_cons_of_mem _ ym) z (List.mem_cons_of_mem _ zm))]

private theorem cut_cap (g : V→V→Bool) (A B : List V) (c : Nat)
    (cap : ∀ x∈A, degree g x B≤c) :
    cut g A B≤A.length*c := by
  induction A with
  | nil => simp [cut]
  | cons x A ih =>
    have p := cap x (by simp)
    have q := ih (fun y ym=>cap y (List.mem_cons_of_mem _ ym))
    change degree g x B+cut g A B≤(A.length+1)*c
    rw [Nat.add_mul,Nat.one_mul]
    omega

private theorem cut_rev (g : V→V→Bool) (symm : Symmetric g) (loop : Loopless g) (A B : List V) :
    cut g A B=cut g B A := by
  have pe := edges_perm g symm loop (List.perm_append_comm : (A++B).Perm (B++A))
  have l := edges_append g A B
  have r := edges_append g B A
  omega

private theorem outsider_product_ceiling (r h a b : Nat) (rh : h+3≤r)
    (sizes : a+b=2*r-h-5) (small : a≤r-h-3) :
    a*b ≤ (r-h-3)*(r-2) := by
  let k := r-h-3-a
  have ak : a+k=r-h-3 := by dsimp [k];omega
  have bk : b=(r-2)+k := by dsimp [k];omega
  have ar : a≤r-2 := by omega
  have m := Nat.mul_le_mul_right k ar
  rw [←ak,bk,Nat.mul_add,Nat.add_mul,Nat.mul_comm k (r-2)]
  omega

private theorem outsider_product_strict (r h : Nat) (h2 : 2≤h) (rh : h+3≤r) :
    (r-h-3)*(r-2)+2*(2*r-h-5)+5 < (r-1)*(r-h) := by
  let a := r-h-3
  have shift : r=a+h+3 := by dsimp [a];omega
  have r1 : r-1=a+h+2 := by omega
  have r2 : r-2=a+h+1 := by omega
  have u : r-h=a+3 := by omega
  have m : 2*r-h-5=2*a+h+1 := by omega
  change a*(r-2)+2*(2*r-h-5)+5 < (r-1)*(r-h)
  rw [r1,r2,m,u]
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one]
  rw [Nat.mul_comm h a]
  omega

/-- If an actual pair has an exception with holes on both sides, its
canonical pentagon forces at least μ−rightDeficit exterior arrivals at the
left support, each with at most one hole. This is stronger than the
arbitrary-shortest-pentagon repair for leaf elimination. -/
theorem NormalizedPair.cheap_left_arrivals_of_two_holes [BEq V] [LawfulBEq V]
    (M : NormalizedPair col t) (symm : ∀ x y, col x y=col y x)
    (bal : Balanced col r) (hr : 12≤r)
    (hd : 3≤M.ld) (he : 3≤M.rd)
    (leftClique : M.left.Pairwise (fun x y=>col x y=t))
    (rightClique : M.right.Pairwise (fun x y=>col x y=t))
    (gap : M.exteriorBudget+1<(2*r-M.residual-5)/2)
    (wideL : M.exteriorBudget+3<M.left.length)
    (wideR : M.exteriorBudget+3<M.right.length)
    (apart : M.ld+M.rd+3<r)
    (sur : M.rd≤M.exceptions.length)
    (bad : ∃ x∈M.exceptions, 0<degree M.miss x M.left ∧ 0<degree M.miss x M.right) :
    ∃ Z : List V, Z.Sublist M.exceptions ∧ Z.length+M.rd=M.exceptions.length ∧
      ∀ z∈Z, degree M.miss z M.left≤1 := by
  classical
  let W := M.vertices M.exceptions
  let g := M.miss
  let h := M.residual
  let S := M.exteriorBudget
  have gs : Symmetric g := missingColor_symmetric col symm t W
  have gl : Loopless g := missingColor_loopless col t W
  have gt : TriangleFree g := M.missing_triangle_free (List.Sublist.refl M.exceptions)
  have ndW : W.Nodup := M.disjointLists
  have nd := nodup_both_rows M
  have lcl := in_row_independent M M.left symm leftClique
  have rcl := in_row_independent M M.right symm rightClique
  have hb := M.high_parallel_multiplicity_bound symm bal hr hd he
  have hdef : h=M.ld+M.rd-M.exceptions.length := rfl
  have hl : 2≤h := by omega
  have hsmall := M.normalizedSum
  have hrh : h+3≤r := by omega
  have wl := M.leftSize
  have wr := M.rightSize
  have wEq : W.length=2*r-h := by
    simp only [W,NormalizedPair.vertices,List.length_append]
    omega
  have expL : r+3<M.left.length+M.right.length := by omega
  have wdiff : W.length-r=r-h := by rw [wEq];omega
  have Sd : S=mantelBound (h-1)+1 := rfl
  have Sleft : S+3<M.left.length := wideL
  have Sright : S+3<M.right.length := wideR
  obtain ⟨x,xm,xl,xr⟩ := bad
  obtain ⟨u,um,xu⟩ := neighbor_of_positive_degree xl
  obtain ⟨v,vm,xv⟩ := neighbor_of_positive_degree xr
  obtain ⟨C,ceq,short⟩ := M.canonical_five symm xm um vm xu xv
  obtain ⟨O,part,exterior⟩ := filtered_cycle_partition C W ndW (fun _ m=>short.2.1 _ m)
  have ol := part.length_eq
  rw [List.length_append,show C.vertices.length=5 from List.length_ofFn] at ol
  have olen : O.length=W.length-5 := by omega
  have floor := missingColor_floor col t bal W ndW
  have gap' : S+1<O.length/2 := by
    rw [olen,wEq]
    exact gap
  have dens : mantelBound O.length+2*O.length+5≤edges g W+S := by
    rw [olen,wEq,pair_exterior_arithmetic r h hl hrh,← Sd,← wdiff]
    exact Nat.add_le_add_right floor S
  obtain ⟨A,B,ab,ai,bi,res⟩ := C.dense_fiveExterior_split gs gl gt W O ndW part short S gap' dens
  change cut (fun a b=> !g a b) A B+(2*O.length-cut g O C.vertices)≤S at res
  have cross : cut (fun a b=> !g a b) A B≤S := by omega
  have abd := ab.nodup_iff.mpr (List.nodup_append.mp (part.nodup_iff.mpr ndW)).2.1
  have cover (z : V) (zm : z∈W) (zc : z∉C.vertices) : z∈A++B :=
    ab.mem_iff.mpr (exterior z zm zc)
  have noP : M.p≠u := by
    intro e
    change M.miss x u=true at xu
    rw [← e,(ex_anchors M xm).1] at xu
    contradiction
  have noQ : M.q≠v := by
    intro e
    change M.miss x v=true at xv
    rw [← e,(ex_anchors M xm).2] at xv
    contradiction
  let L := (M.left.erase M.p).erase u
  let R := (M.right.erase M.q).erase v
  have lsub : L.Sublist M.left := List.erase_sublist.trans List.erase_sublist
  have rsub : R.Sublist M.right := List.erase_sublist.trans List.erase_sublist
  have lp : (M.p::u::L).Perm M.left := remove_two nd.1 M.p_left um noP
  have rp : (M.q::v::R).Perm M.right := remove_two nd.2 M.q_right vm noQ
  have ll := lp.length_eq
  have rl := rp.length_eq
  simp only [List.length_cons] at ll rl

  have leftRight {a b : V} (am : a∈M.left) (bm : b∈M.right) : a≠b :=
    list_ne_left M.disjointLists am (List.mem_append_left _ bm)
  have leftEx {a b : V} (am : a∈M.left) (bm : b∈M.exceptions) : a≠b :=
    list_ne_left M.disjointLists am (List.mem_append_right _ bm)
  have rightEx {a b : V} (am : a∈M.right) (bm : b∈M.exceptions) : a≠b :=
    list_ne_left (List.nodup_append.mp M.disjointLists).2.1 am bm

  have la : L⊆A++B := by
    intro z zm
    have xl : z∈M.left := lsub.subset zm
    obtain ⟨nu,ze⟩ := (nd.1.erase M.p).mem_erase_iff.mp zm
    have np := (nd.1.mem_erase_iff.mp ze).1
    exact cover z (left_in M xl) (by simp [ceq,np,nu,leftRight xl M.q_right,leftEx xl xm,leftRight xl vm])
  have ra : R⊆A++B := by
    intro z zm
    have xr : z∈M.right := rsub.subset zm
    obtain ⟨nv,ze⟩ := (nd.2.erase M.q).mem_erase_iff.mp zm
    have nq := (nd.2.mem_erase_iff.mp ze).1
    exact cover z (right_in M xr) (by simp [ceq,nq,nv,Ne.symm (leftRight M.p_left xr),
      Ne.symm (leftRight um xr),rightEx xr xm])
  have lpure := pure_of_large_independent abd (lsub.nodup nd.1) la
    (fun a am b bm=>lcl a (lsub.subset am) b (lsub.subset bm)) S cross (by omega)
  have rpure := pure_of_large_independent abd (rsub.nodup nd.2) ra
    (fun a am b bm=>rcl a (rsub.subset am) b (rsub.subset bm)) S cross (by omega)
  have both := pair_rows_apart M lsub rsub
    (fun _ m=>part.mem_iff.mp (List.mem_append_right _ (ab.mem_iff.mp m))) ai bi lpure rpure (by omega)

  have outside (z : V) (zm : z∈O) : z∉C.vertices :=
    fun c => (List.nodup_append.mp (part.nodup_iff.mpr ndW)).2.2 z c z zm rfl
  have cn : ∀ z∈O, degree g z C.vertices≤2 := by
    intro z zm
    exact C.outsider_degree_le_two gs gt short
      (part.mem_iff.mp (List.mem_append_right _ zm)) (outside z zm)
  have capC := cut_cap g O C.vertices 2 cn
  have splitE := edges_append g C.vertices O
  rw [edges_perm g gs gl part,C.edge_perimeter gs gl short,
    show C.vertices.length=5 from List.length_ofFn,cut_rev g gs gl C.vertices O] at splitE
  have eCut (U T : List V) (perm : (U++T).Perm O)
      (ui : ∀ z∈U, ∀ w∈U, g z w=false)
      (ti : ∀ z∈T, ∀ w∈T, g z w=false) :
      edges g O≤U.length*T.length := by
    have b := cut_cap g U T T.length (fun y _=>List.length_filter_le _ _)
    have e := edges_append g U T
    rw [edges_perm g gs gl perm,nonedge_list g U ui,nonedge_list g T ti] at e
    omega
  have finish (U T : List V) (perm : (U++T).Perm O)
      (ui : ∀ z∈U, ∀ w∈U, g z w=false)
      (ti : ∀ z∈T, ∀ w∈T, g z w=false)
      (lu : L⊆U) (rt : R⊆T) :
      ∃ Z : List V, Z.Sublist M.exceptions ∧ Z.length+M.rd=M.exceptions.length ∧
        ∀ z∈Z, degree g z M.left≤1 := by
    let Z := M.exceptions.filter (fun y=>decide (y∈U))
    have zs : Z.Sublist M.exceptions := List.filter_sublist
    have Uout (y : V) (ym : y∈U) : y∈O :=
      perm.mem_iff.mp (List.mem_append_left _ ym)
    have Uin (y : V) (ym : y∈U) : y∈W :=
      part.mem_iff.mp (List.mem_append_right _ (Uout y ym))
    have Udis : (U++T).Nodup :=
      perm.nodup_iff.mpr (List.nodup_append.mp (part.nodup_iff.mpr ndW)).2.1
    have zu : Z⊆U := fun _ zm=>of_decide_eq_true (List.mem_filter.mp zm).2
    have copies : (L++Z).Nodup := by
      apply List.nodup_append.mpr
      have Xnd := (List.nodup_append.mp (List.nodup_append.mp ndW).2.1).2.1
      exact ⟨lsub.nodup nd.1,zs.nodup Xnd,fun a am b bm=>leftEx (lsub.subset am) (zs.subset bm)⟩
    have pZ : (L++Z).Perm U := by
      apply (List.perm_ext_iff_of_nodup copies (List.nodup_append.mp Udis).1).mpr
      intro y
      constructor
      · intro ym
        exact (List.mem_append.mp ym).elim (fun ym=>lu ym) (fun ym=>zu ym)
      · intro ym
        have mid := Uin y ym
        change y∈M.left++(M.right++M.exceptions) at mid
        have no := outside y (Uout y ym)
        have neP : y≠M.p := fun e=>no (by simp [ceq,e])
        have neQ : y≠M.q := fun e=>no (by simp [ceq,e])
        have neU : y≠u := fun e=>no (by simp [ceq,e])
        have neV : y≠v := fun e=>no (by simp [ceq,e])
        rcases List.mem_append.mp mid with yl|tail
        · have inL : y∈L := (nd.1.erase M.p).mem_erase_iff.mpr
            ⟨neU,nd.1.mem_erase_iff.mpr ⟨neP,yl⟩⟩
          exact List.mem_append_left _ inL
        · rcases List.mem_append.mp tail with yr|ye
          · have inR : y∈R := (nd.2.erase M.q).mem_erase_iff.mpr
              ⟨neV,nd.2.mem_erase_iff.mpr ⟨neQ,yr⟩⟩
            exact False.elim ((List.nodup_append.mp Udis).2.2 y ym y (rt inR) rfl)
          · exact List.mem_append_right _ (List.mem_filter.mpr ⟨ye,decide_eq_true ym⟩)
    have sizeU := pZ.length_eq
    rw [List.length_append] at sizeU
    have sizeO := perm.length_eq
    rw [List.length_append,olen,wEq] at sizeO
    have exCount : M.exceptions.length-M.rd≤Z.length := by
      apply Classical.byContradiction
      intro nope
      have small : U.length≤r-h-3 := by omega
      have prod := outsider_product_ceiling r h U.length T.length hrh sizeO small
      have edgeU := eCut U T perm ui ti
      have strict := outsider_product_strict r h hl hrh
      have len : O.length=2*r-h-5 := by rw [olen,wEq]
      change (r-1)*(W.length-r)≤edges g W at floor
      rw [wdiff] at floor
      rw [len] at capC
      omega
    let J := Z.take (M.exceptions.length-M.rd)
    have subJ : J.Sublist Z := List.take_sublist _ _
    have lenJ : J.length=M.exceptions.length-M.rd := by simp [J,List.length_take,exCount]
    refine ⟨J,subJ.trans zs,by omega,?_⟩
    intro z zm
    have zZ := subJ.subset zm
    have no : degree g z L=0 :=
      degree_eq_zero (fun y ym=>ui z (zu zZ) y (lu ym))
    have mask := row_hole_count lp (ex_anchors M (zs.subset zZ)).1
    change degree g z M.left≤1+degree g z L at mask
    omega
  rcases both with ⟨lu,rt⟩|⟨lt,ru⟩
  · exact finish A B ab ai bi lu rt
  · exact finish B A (List.perm_append_comm.trans ab) bi ai lt ru



private theorem cuts_add (g : V→V→Bool) (A B : List V) :
    cut g A B+cut (fun x y => !g x y) A B=A.length*B.length := by
  have row (x : V) : degree g x B+degree (fun x y => !g x y) x B=B.length := by
    simpa only [degree,List.length_append] using (List.filter_append_perm (g x) B).length_eq
  induction A with
  | nil => simp [cut]
  | cons x A ih =>
    have hh := row x
    change degree g x B+cut g A B+(degree (fun x y=>!g x y) x B+cut (fun x y=>!g x y) A B)
      =(A.length+1)*B.length
    rw [Nat.add_mul,Nat.one_mul]
    omega

private theorem cut_rectangle_arithmetic (r d e : Nat) (hr : d+e+3≤r)
    (hd : 1≤d) (he : 1≤e) :
    (r-1)*(r-d-e+1)+(d-1)*(e-1)=(r-d)*(r-e) := by
  let a := r-d-e
  let p := d-1
  let q := e-1
  have r1 : r-1=a+p+q+1 := by dsimp [a,p,q];omega
  have rp : r-d=a+q+1 := by dsimp [a,q];omega
  have rq : r-e=a+p+1 := by dsimp [a,p];omega
  change (r-1)*(a+1)+p*q=(r-d)*(r-e)
  rw [r1,rp,rq]
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul]
  rw [Nat.mul_comm q p,Nat.mul_comm a p]
  omega

private theorem two_large_rule (d e p q : Nat) (dh : 3≤d) (eh : 3≤e)
    (cap : p*q≤(d-1)*(e-1)+p+q) : p≤d ∨ q≤e := by
  by_cases pl : p≤d
  · exact Or.inl pl
  · right
    apply Classical.byContradiction
    intro ql
    let D := d-1
    let E := e-1
    let P := p-d-1
    let Q := q-e-1
    have ps : p=D+P+2 := by dsimp [D,P];omega
    have qs : q=E+Q+2 := by dsimp [E,Q];omega
    change p*q≤D*E+p+q at cap
    rw [ps,qs] at cap
    simp only [Nat.mul_add,Nat.add_mul] at cap
    omega

/-- Earlier exact pointwise rectangle argument, rederived from an actual
normalized color pair. Every exception can be routed to one true support
with no more holes than the receiving deficit. -/
theorem NormalizedPair.deficit_hole_choice [BEq V] [LawfulBEq V]
    (M : NormalizedPair col t) (symm : ∀ x y, col x y=col y x) (bal : Balanced col r)
    (hd : 3≤M.ld) (he : 3≤M.rd)
    (leftClique : M.left.Pairwise (fun x y=>col x y=t))
    (rightClique : M.right.Pairwise (fun x y=>col x y=t))
    {x : V} (xm : x∈M.exceptions) :
    degree M.miss x M.left≤M.ld ∨ degree M.miss x M.right≤M.rd := by
  classical
  let W := M.vertices M.exceptions
  let g := M.miss
  let U := x::(M.left++M.right)
  let P := M.left.filter (g x)
  let Q := M.right.filter (g x)
  have ps : P.Sublist M.left := List.filter_sublist
  have qs : Q.Sublist M.right := List.filter_sublist
  have gt : TriangleFree g := M.missing_triangle_free (List.Sublist.refl M.exceptions)
  have rn := nodup_both_rows M
  have rect := missing_rectangle (ps.nodup rn.1) (qs.nodup rn.2)
    (fun _ m=>ps.subset m) (fun _ m=>qs.subset m)
    (fun z zm w wm=>gt x z w (List.mem_filter.mp zm).2 (List.mem_filter.mp wm).2)
  change degree g x M.left * degree g x M.right≤cut (fun z w=>!g z w) M.left M.right at rect
  have sumCut := cuts_add g M.left M.right
  have small : (M.vertices [x]).Sublist W :=
    (List.Sublist.refl M.left).append ((List.Sublist.refl M.right).append (List.singleton_sublist.mpr xm))
  have flip : U.Perm (M.vertices [x]) := by
    unfold U NormalizedPair.vertices
    rw [← List.append_assoc]
    change ([x]++(M.left++M.right)).Perm ((M.left++M.right)++[x])
    exact List.perm_append_comm
  have ndu := flip.nodup_iff.mpr (small.nodup M.disjointLists)
  have eu := missingColor_edges_eq_palette col t W U ndu (fun _ m=>small.subset (flip.mem_iff.mp m))
  have el := missingColor_edges_eq_palette col t U U ndu (fun _ m=>m)
  have low := missingColor_floor col t bal U ndu
  rw [el,← eu] at low
  change (r-1)*(U.length-r)≤edges g U at low
  have lz := nonedge_list g M.left (in_row_independent M M.left symm leftClique)
  have rz := nonedge_list g M.right (in_row_independent M M.right symm rightClique)
  have express : edges g U =
      degree g x M.left + degree g x M.right + cut g M.left M.right := by
    change degree g x (M.left++M.right)+edges g (M.left++M.right)=_
    rw [edges_append,lz,rz,Nat.zero_add]
    have de : degree g x (M.left++M.right)=degree g x M.left + degree g x M.right := by
      simp [degree,List.filter_append]
    rw [de]
  have l := M.leftSize
  have n := M.rightSize
  have cap := M.normalizedSum
  have sr : M.ld+M.rd+3≤r := by omega
  have clr := cut_rectangle_arithmetic r M.ld M.rd sr (by omega) (by omega)
  have us : U.length-r=r-M.ld-M.rd+1 := by simp only [U,List.length_cons,List.length_append];omega
  have side : M.left.length*M.right.length=(r-M.ld)*(r-M.rd) := by
    rw [show M.left.length=r-M.ld by omega,show M.right.length=r-M.rd by omega]
  rw [us,express] at low
  rw [side,←clr] at sumCut
  exact two_large_rule M.ld M.rd (degree g x M.left) (degree g x M.right) hd he (by omega)

end ParallelMantel.Pentagon

#print axioms ParallelMantel.Pentagon.NormalizedPair.canonical_five

#print axioms ParallelMantel.Pentagon.NormalizedPair.one_costly_exception_ledger

#print axioms ParallelMantel.Pentagon.pair_exterior_arithmetic
#print axioms ParallelMantel.Pentagon.NormalizedPair.one_costly_exception

#print axioms ParallelMantel.Pentagon.NormalizedPair.cheap_left_arrivals_of_two_holes

#print axioms ParallelMantel.Pentagon.NormalizedPair.deficit_hole_choice
