module

public import Palomar.Erdos617PairBound.Support.PentagonTypes
public import Lean.Elab.Tactic.Omega

@[expose] public section

namespace ParallelMantel.Pentagon

set_option maxHeartbeats 1000000
universe u
variable {V : Type u} {g : V → V → Bool}

private theorem cons_cut (f : V→V→Bool) (x : V) (A B : List V) :
    cut f (x::A) B = degree f x B + cut f A B := rfl

private theorem app_cut (f : V→V→Bool) (A B C : List V) :
    cut f (A++B) C = cut f A C + cut f B C := by simp [cut,List.sum_append]

private theorem perm_cut_left (f : V→V→Bool) {A B : List V} (p : A.Perm B) (C : List V) :
    cut f A C = cut f B C := by
  induction p with
  | nil => rfl
  | cons x _ ih => rw [cons_cut,cons_cut,ih]
  | swap x y T =>
    simp only [cons_cut]
    omega
  | trans _ _ p q => exact p.trans q

private theorem perm_cut_right (f : V→V→Bool) (A : List V) {B C : List V} (p : B.Perm C) :
    cut f A B = cut f A C := by
  induction A with
  | nil => rfl
  | cons x A ih =>
    have k : degree f x B = degree f x C := (p.filter (f x)).length_eq
    rw [cons_cut,cons_cut,k,ih]

private theorem degree_pos_of_edge (f : V→V→Bool) {x y : V} {B : List V}
    (ym : y∈B) (edge : f x y=true) : 0<degree f x B := by
  have mem : y∈B.filter (f x) := List.mem_filter.mpr ⟨ym,edge⟩
  cases p : B.filter (f x) with
  | nil => simp [p] at mem
  | cons a A => simp [degree,p]

private theorem row_zero (f : V→V→Bool) {x : V} {B : List V} (zero : degree f x B=0) :
    ∀ y∈B, f x y=false := by
  intro y ym
  cases e : f x y
  · rfl
  · have q := degree_pos_of_edge f ym e
    omega

private theorem cut_zero (f : V→V→Bool) {A B : List V} (zero : cut f A B=0) :
    ∀ x∈A, ∀ y∈B, f x y=false := by
  induction A with
  | nil => simp
  | cons x A ih =>
    rw [cons_cut] at zero
    intro a am
    rcases List.mem_cons.mp am with e | am
    · subst a
      exact row_zero f (by omega)
    · exact ih (by omega) a am

private theorem cut_pos_edge (f : V→V→Bool) {A B : List V} (pos : 0<cut f A B) :
    ∃ a∈A, ∃ b∈B, f a b=true := by
  apply Classical.byContradiction
  intro no
  have d : ∀ a∈A, degree f a B=0 := by
    intro a am
    cases eq : B.filter (f a) with
    | nil => simp [degree,eq]
    | cons b L =>
      have mem : b∈B.filter (f a) := by rw [eq];simp
      have ⟨bm,fe⟩ := List.mem_filter.mp mem
      exact False.elim (no ⟨a,am,b,bm,fe⟩)
  have kz (L : List V) (dL : ∀ a∈L, degree f a B=0) : cut f L B=0 := by
    induction L with
    | nil => rfl
    | cons a L ih =>
      rw [cons_cut,dL a (by simp),ih (fun x xm => dL x (List.mem_cons_of_mem _ xm))]
  have k := kz A d
  omega

private theorem move_head {A : List V} {a : V} (m : a∈A) :
    ∃ L : List V, (a::L).Perm A := by
  obtain ⟨l,r,eq⟩ := List.append_of_mem m
  refine ⟨l++r,?_⟩
  rw [eq]
  exact List.perm_middle.symm

private theorem cut_one (f : V→V→Bool) {A B : List V} (one : cut f A B=1) :
    ∃ a b L M, (a::L).Perm A ∧ (b::M).Perm B ∧
      (∀ x∈L, ∀ y∈b::M, f x y=false) ∧
      (∀ x∈a::L, ∀ y∈M, f x y=false) := by
  obtain ⟨a,am,b,bm,e⟩ := cut_pos_edge f (by omega : 0<cut f A B)
  obtain ⟨L,lp⟩ := move_head am
  obtain ⟨M,mp⟩ := move_head bm
  have k : cut f (a::L) (b::M) = 1 := by
    rw [perm_cut_left f lp,perm_cut_right f A mp,one]
  rw [cons_cut] at k
  have eq : degree f a (b::M) = degree f a M+1 := by simp [degree,e]
  have lc : cut f L (b::M)=0 := by omega
  have mr : degree f a M=0 := by omega
  refine ⟨a,b,L,M,lp,mp,cut_zero f lc,?_⟩
  intro x xm y ym
  rcases List.mem_cons.mp xm with ee | xm
  · subst x
    exact row_zero f mr y ym
  · exact cut_zero f lc x xm y (List.mem_cons_of_mem _ ym)

private def shortfall (g : V→V→Bool) (C X : List V) : Nat :=
  (X.map (fun x => 2 - degree g x C)).sum

private theorem shortfall_total (g : V→V→Bool) (C X : List V)
    (upper : ∀ x∈X, degree g x C≤2) :
    shortfall g C X+cut g X C=2*X.length := by
  induction X with
  | nil => rfl
  | cons x X ih =>
    have head := upper x (by simp)
    have rest := ih (fun y ym => upper y (List.mem_cons_of_mem _ ym))
    rw [cons_cut]
    change (2 - degree g x C) + shortfall g C X + (degree g x C + cut g X C) =
      2*(x::X).length
    simp only [List.length_cons]
    omega

private theorem full_on_gap_zero (g : V→V→Bool) (C X : List V)
    (upper : ∀ x∈X, degree g x C≤2) (zero : shortfall g C X=0) :
    ∀ x∈X, degree g x C=2 := by
  induction X with
  | nil => simp
  | cons x X ih =>
    have bound := upper x (by simp)
    change (2-degree g x C)+shortfall g C X=0 at zero
    intro v vm
    rcases List.mem_cons.mp vm with e | m
    · subst v
      omega
    · exact ih (fun w wm => upper w (List.mem_cons_of_mem _ wm)) (by omega) v m

private theorem gap_one (g : V→V→Bool) (C X : List V)
    (upper : ∀ x∈X, degree g x C≤2) (one : shortfall g C X=1) :
    ∃ x L, (x::L).Perm X ∧ degree g x C=1 ∧ ∀ y∈L, degree g y C=2 := by
  induction X with
  | nil => contradiction
  | cons x X ih =>
    have bound := upper x (by simp)
    have up : ∀ y∈X, degree g y C≤2 := fun y ym => upper y (List.mem_cons_of_mem _ ym)
    change (2-degree g x C)+shortfall g C X=1 at one
    by_cases f : degree g x C=2
    · obtain ⟨y,L,p,h,a⟩ := ih up (by omega)
      refine ⟨y,x::L,(List.Perm.swap x y L).trans (p.cons _),h,?_⟩
      intro z zm
      rcases List.mem_cons.mp zm with e | zm
      · rwa [e]
      · exact a z zm
    · exact ⟨x,X,List.Perm.refl _,by omega,full_on_gap_zero g C X up (by omega)⟩

private theorem Frame.permSides {W A B A' B' : List V} {c : Type5→V}
    (h : Frame g W A B c) (pa : A'.Perm A) (pb : B'.Perm B) :
    Frame g W A' B' c :=
  ⟨h.nodup,((pa.append pb).append_left _).trans h.partition,h.cycle,
    (fun x xm y ym => h.leftInd x (pa.mem_iff.mp xm) y (pa.mem_iff.mp ym)),
    (fun x xm y ym => h.rightInd x (pb.mem_iff.mp xm) y (pb.mem_iff.mp ym))⟩

private noncomputable def tagFor (g : V→V→Bool) (c : Type5→V) (x : V) : Type5 :=
  open Classical in
  if h : ∃ a : Type5, Full (g:=g) c x a then Classical.choose h else 0

private theorem tagFull {W A B : List V} {c : Type5→V}
    (h : Frame g W A B c) (symm : Symmetric g) (tri : TriangleFree g) {x : V}
    (two : degree g x (List.ofFn c)=2) :
    Full (g:=g) c x (tagFor g c x) := by
  unfold tagFor
  split
  · rename_i ex
    exact Classical.choose_spec ex
  · rename_i no
    exact False.elim (no (full_of_degree_two h symm tri two))

/-- On a balanced outer partition, the single joint deficit produces
exactly one of the three low-defect false-twin configurations. -/
theorem balanced_ledger_twins {W A B : List V} {c : Type5→V}
    (h : Frame g W A B c) (symm : Symmetric g) (tri : TriangleFree g)
    (R : Nat) (rp : 2≤R) (al : A.length=R) (bl : B.length=R)
    (upperA : ∀ x∈A, degree g x (List.ofFn c)≤2)
    (upperB : ∀ x∈B, degree g x (List.ofFn c)≤2)
    (budget : cut (fun x y => !g x y) A B + (4*R - cut g (A++B) (List.ofFn c))≤1) :
    TwinBlock g W R (R+2) := by
  let Cy := List.ofFn c
  let m := cut (fun x y => !g x y) A B
  let sa := shortfall g Cy A
  let sb := shortfall g Cy B
  have a := shortfall_total g Cy A upperA
  have b := shortfall_total g Cy B upperB
  rw [al] at a
  rw [bl] at b
  rw [app_cut] at budget
  change m+(4*R-(cut g A Cy+cut g B Cy))≤1 at budget
  change sa+cut g A Cy=2*R at a
  change sb+cut g B Cy=2*R at b
  have total : m+sa+sb≤1 := by omega
  by_cases m0 : m=0
  · have cross (x : V) (xm : x∈A) (y : V) (ym : y∈B) : g x y=true := by
      have e := cut_zero (fun x y => !g x y) m0 x xm y ym
      simpa using e
    by_cases sa0 : sa=0
    · have fa (x : V) (xm : x∈A) : Full (g:=g) c x (tagFor g c x) :=
        tagFull h symm tri (full_on_gap_zero g Cy A upperA sa0 x xm)
      by_cases sb0 : sb=0
      · have fb (x : V) (xm : x∈B) : Full (g:=g) c x (tagFor g c x) :=
          tagFull h symm tri (full_on_gap_zero g Cy B upperB sb0 x xm)
        obtain ⟨T,nd,sub,len,deg,tw⟩ :=
          no_defect_twins h symm tri (tagFor g c) fa fb cross R (by omega) al bl
        exact ⟨T,nd,sub,by omega,deg,tw⟩
      · obtain ⟨w,L,p,_,fu⟩ := gap_one g Cy B upperB (by omega : sb=1)
        have ln := p.length_eq
        have sim (x : V) (xm : x∈w::L) (y : V) (ym : y∈A) : g x y=true :=
          (symm _ _).trans (cross y ym x (p.mem_iff.mp xm))
        exact weak_vertex_twins (h.swap.permSides p (List.Perm.refl _)) symm tri
          (tagFor g c) (fun x xm => tagFull h symm tri (fu x xm)) fa sim R rp
          (by simpa [bl] using ln) al
    · obtain ⟨w,L,p,_,fu⟩ := gap_one g Cy A upperA (by omega : sa=1)
      have ln := p.length_eq
      have fb (x : V) (xm : x∈B) : Full (g:=g) c x (tagFor g c x) :=
        tagFull h symm tri (full_on_gap_zero g Cy B upperB (by omega : sb=0) x xm)
      exact weak_vertex_twins (h.permSides p (List.Perm.refl _)) symm tri
        (tagFor g c) (fun x xm => tagFull h symm tri (fu x xm)) fb
        (fun x xm => cross x (p.mem_iff.mp xm)) R rp (by simpa [al] using ln) bl
  · obtain ⟨u,v,L,M,pa,pb,ca,cb⟩ := cut_one (fun x y=> !g x y) (by omega : m=1)
    have fa (x : V) (xm : x∈u::L) : Full (g:=g) c x (tagFor g c x) :=
      tagFull h symm tri (full_on_gap_zero g Cy A upperA (by omega : sa=0) x (pa.mem_iff.mp xm))
    have fb (x : V) (xm : x∈v::M) : Full (g:=g) c x (tagFor g c x) :=
      tagFull h symm tri (full_on_gap_zero g Cy B upperB (by omega : sb=0) x (pb.mem_iff.mp xm))
    exact missing_cross_twins (h.permSides pa pb) symm tri (tagFor g c) fa fb
      (fun x xm y ym => by simpa using ca x xm y ym)
      (fun x xm y ym => by simpa using cb x xm y ym) R rp
      (by simpa [al] using pa.length_eq) (by simpa [bl] using pb.length_eq)

/-- Integrated C5 result. Starting with a shortest odd cycle in an induced
triangle-free graph on 2r−1 vertices and the actual edge and independence
bounds, this produces genuine false twins, with no assumed defect pattern. -/
theorem shortest_cycle_false_twins {n : Nat} (C : TraceCycle g n)
    (symm : Symmetric g) (loop : Loopless g) (tri : TriangleFree g)
    (W O : List V) (r : Nat) (hr : 12≤r) (part : (C.vertices++O).Perm W)
    (nd : W.Nodup) (size : W.length=2*r-1)
    (dense : (r-1)*(r-1)≤edges g W) (short : C.ShortestOdd W)
    (cap : ∀ I : List V, I.Nodup → (∀ x∈I, x∈W) →
      (∀ x∈I, ∀ y∈I, g x y=false) → I.length≤r-1) :
    TwinBlock g W (r-3) (r-1) := by
  obtain ⟨clen,A,B,outpart,indA,indB,budgets⟩ :=
    C.shortest_partition symm loop tri W O r hr part nd size dense short
  have ns : n=5 := (List.length_ofFn (f:=C.trace)).symm.trans clen
  subst n
  let R := r-3
  have rp : 2≤R := by dsimp [R];omega
  have rsub : R+2=r-1 := by dsimp [R];omega
  have frame := frame_of_shortest C symm loop short nd
    ((outpart.append_left C.vertices).trans part) indA indB
  have merged : (C.vertices++(A++B)).Nodup := frame.partition.nodup_iff.mpr nd
  have outer {x : V} (m : x∈A++B) : degree g x C.vertices≤2 :=
    C.outsider_degree_le_two symm tri short
      (frame.partition.mem_iff.mp (List.mem_append_right _ m))
      (fun xc => (List.nodup_append.mp merged).2.2 x xc x m rfl)
  have upA (x : V) (m : x∈A) : degree g x C.vertices≤2 :=
     outer (List.mem_append_left _ m)
  have upB (x : V) (m : x∈B) : degree g x C.vertices≤2 :=
     outer (List.mem_append_right _ m)
  rcases budgets with ⟨al,bl,bud⟩ | ⟨lengths,miss,hits⟩
  · have z := balanced_ledger_twins frame symm tri R rp al bl upA upB
      (by rw [perm_cut_left g outpart]; exact bud)
    rwa [rsub] at z
  · have sumlen : A.length+B.length=2*R := by
      rcases lengths with e | e <;> omega
    have all : ∀ x∈A++B, degree g x C.vertices=2 := by
      apply full_on_gap_zero g C.vertices (A++B) (fun _ => outer)
      have sh := shortfall_total g C.vertices (A++B) (fun _ => outer)
      rw [perm_cut_left g outpart,List.length_append, sumlen] at sh
      change cut g O C.vertices = 4*R at hits
      omega
    have fa (x : V) (m : x∈A) : Full (g:=g) C.trace x (tagFor g C.trace x) :=
      tagFull frame symm tri (all x (List.mem_append_left _ m))
    have fb (x : V) (m : x∈B) : Full (g:=g) C.trace x (tagFor g C.trace x) :=
      tagFull frame symm tri (all x (List.mem_append_right _ m))
    have cross (a : V) (am : a∈A) (b : V) (bm : b∈B) : g a b=true := by
      have q := cut_zero (fun x y=> !g x y) miss a am b bm
      simpa using q
    exfalso
    rcases lengths with ⟨al,bl⟩ | ⟨bl,al⟩
    · have ap : A≠[] := by
        intro z
        simp [z] at al
        omega
      obtain ⟨I,id,im,il,ii⟩ := imbalanced_obstruction frame symm tri (tagFor g C.trace)
        fa fb cross ap
      have q := cap I id im ii
      omega
    · have bp : B≠[] := by
        intro z
        simp [z] at bl
        omega
      obtain ⟨I,id,im,il,ii⟩ := imbalanced_obstruction frame.swap symm tri (tagFor g C.trace)
        fb fa (fun b bm a am => (symm _ _).trans (cross a am b bm)) bp
      have q := cap I id im ii
      omega

end ParallelMantel.Pentagon

#print axioms ParallelMantel.Pentagon.balanced_ledger_twins
#print axioms ParallelMantel.Pentagon.shortest_cycle_false_twins
