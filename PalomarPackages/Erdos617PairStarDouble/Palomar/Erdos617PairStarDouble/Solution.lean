module

public import Palomar.Erdos617PairStarDouble.Support.GlobalPalette
public import Palomar.Erdos617PairStarDouble.Support.NormalizedStar
public import Lean.Elab.Tactic.Omega

@[expose] public section

namespace ParallelMantel.Pentagon

open Erdos617Geometry
set_option maxHeartbeats 1200000
universe u
variable {V : Type u} {r : Nat} {col : V→V→Fin r} {t : Fin r}

/-- Actual normalized double star. The leaf removal capacity (strict surplus
of each spoke over its leaf deficit) is the exact consequence of the
usual proper-set capacity after deleting that leaf. -/
structure NormalizedDoubleStar (col : V→V→Fin r) (t : Fin r) where
  center : NormalizedPair col t
  leftSpokes : List (NormalizedPair col t)
  rightSpokes : List (NormalizedPair col t)
  sameLeft : ∀ M∈leftSpokes, M.p=center.p ∧ M.left=center.left ∧ M.ld=center.ld
  sameRight : ∀ M∈rightSpokes, M.p=center.q ∧ M.left=center.right ∧ M.ld=center.rd
  leftSurplus : ∀ M∈leftSpokes, M.rd<M.exceptions.length
  rightSurplus : ∀ M∈rightSpokes, M.rd<M.exceptions.length
  distinct : ((center.left++center.right)++
    ((leftSpokes.flatMap fun M=>M.exceptions)++
     ((rightSpokes.flatMap fun M=>M.exceptions)++center.exceptions))).Nodup
  overload : (leftSpokes.flatMap fun M=>M.exceptions).length+
    (rightSpokes.flatMap fun M=>M.exceptions).length+center.exceptions.length=
    center.ld+center.rd+
    (leftSpokes.map fun M=>M.rd).sum+(rightSpokes.map fun M=>M.rd).sum+1

/-- A single division of every actual central exception between the hubs.
The two debts are bounds on actual colored edges to the two private rows. -/
structure PairArrivals (M : NormalizedPair col t) (costL costR : Nat) where
  left : List V
  right : List V
  lsub : left.Sublist M.exceptions
  rsub : right.Sublist M.exceptions
  length_eq : left.length+right.length=M.exceptions.length
  leftDebt : arrivalDebt col t M.left left≤costL
  rightDebt : arrivalDebt col t M.right right≤costR

private theorem pair_ex_in (M : NormalizedPair col t) {x : V} (m : x∈M.exceptions) :
    x∈M.vertices M.exceptions :=
  List.mem_append_right _ (List.mem_append_right _ m)

private theorem complement_filter (M : NormalizedPair col t) (f : V→Bool) :
    let L := M.exceptions.filter f
    let R := M.exceptions.filter (fun x=>!f x)
    L.length+R.length=M.exceptions.length := by
  simpa only [List.length_append] using (List.filter_append_perm f M.exceptions).length_eq

/-- Refined central edge, with one costly exception. -/
theorem NormalizedPair.refined_arrivals [BEq V] [LawfulBEq V]
    (M : NormalizedPair col t) (symm : ∀ x y, col x y=col y x)
    (bal : Balanced col r) (hr : 12≤r) (hl : 3≤M.ld) (hq : 3≤M.rd)
    (leftClique : M.left.Pairwise (fun x y=>col x y=t))
    (rightClique : M.right.Pairwise (fun x y=>col x y=t))
    (K : Nat)
    (gap : M.exteriorBudget+1<(2*r-M.residual-5)/2)
    (wideL : M.exteriorBudget+3<M.left.length)
    (wideR : M.exteriorBudget+3<M.right.length)
    (apart : M.ld+M.rd+3<r) (sq : M.exteriorBudget<(K+1)*(K+1)) :
    Nonempty (PairArrivals M K K) := by
  obtain ⟨E,f,works⟩ := M.one_costly_exception symm bal hr hl hq leftClique rightClique K
    gap wideL wideR apart sq
  let L := M.exceptions.filter f
  let R := M.exceptions.filter (fun x=>!f x)
  have lsub : L.Sublist M.exceptions := List.filter_sublist
  have rsub : R.Sublist M.exceptions := List.filter_sublist
  have nd := (List.nodup_append.mp (List.nodup_append.mp M.disjointLists).2.1).2.1
  refine ⟨⟨L,R,lsub,rsub,complement_filter M f,?_,?_⟩⟩
  · apply arrivalDebt_single_cap col t M.left L E K (lsub.nodup nd)
    intro x xm
    rw [rowHoles_eq_degree col t (M.vertices M.exceptions) M.left x (pair_ex_in M (lsub.subset xm))
      (fun _ m=>List.mem_append_left _ m)]
    have ftrue : f x=true := (List.mem_filter.mp xm).2
    simpa only [ftrue,ite_true] using works x (lsub.subset xm)
  · apply arrivalDebt_single_cap col t M.right R E K (rsub.nodup nd)
    intro x xm
    rw [rowHoles_eq_degree col t (M.vertices M.exceptions) M.right x (pair_ex_in M (rsub.subset xm))
      (fun _ m=>List.mem_append_right _ (List.mem_append_left _ m))]
    have ff : f x=false := by
      have h : (!(f x))=true := (List.mem_filter.mp xm).2
      simpa only [Bool.not_eq_true'] using h
    simpa only [ff,Bool.false_eq_true,ite_false] using works x (rsub.subset xm)

/-- Rough central edge: every exception is oriented to its low-hole side. -/
theorem NormalizedPair.rough_arrivals [BEq V] [LawfulBEq V]
    (M : NormalizedPair col t) (symm : ∀ x y, col x y=col y x)
    (bal : Balanced col r) (hl : 3≤M.ld) (hq : 3≤M.rd)
    (leftClique : M.left.Pairwise (fun x y=>col x y=t))
    (rightClique : M.right.Pairwise (fun x y=>col x y=t)) :
    Nonempty (PairArrivals M (M.exceptions.length*(M.ld-1)) (M.exceptions.length*(M.rd-1))) := by
  classical
  let f (x : V) : Bool := decide (degree M.miss x M.left≤M.ld)
  let L := M.exceptions.filter f
  let R := M.exceptions.filter (fun x=>!f x)
  have lsub : L.Sublist M.exceptions := List.filter_sublist
  have rsub : R.Sublist M.exceptions := List.filter_sublist
  refine ⟨⟨L,R,lsub,rsub,complement_filter M f,?_,?_⟩⟩
  · refine Nat.le_trans (arrivalDebt_max_holes col t M.left L M.ld ?_)
      (Nat.mul_le_mul_right _ lsub.length_le)
    intro x xm
    rw [rowHoles_eq_degree col t (M.vertices M.exceptions) M.left x (pair_ex_in M (lsub.subset xm))
      (fun _ m=>List.mem_append_left _ m)]
    exact of_decide_eq_true (List.mem_filter.mp xm).2
  · refine Nat.le_trans (arrivalDebt_max_holes col t M.right R M.rd ?_)
      (Nat.mul_le_mul_right _ rsub.length_le)
    intro x xm
    rw [rowHoles_eq_degree col t (M.vertices M.exceptions) M.right x (pair_ex_in M (rsub.subset xm))
      (fun _ m=>List.mem_append_right _ (List.mem_append_left _ m))]
    have h : (!(f x))=true := (List.mem_filter.mp xm).2
    have no : ¬degree M.miss x M.left≤M.ld := by simpa [f] using h
    exact (M.deficit_hole_choice symm bal hl hq leftClique rightClique (rsub.subset xm)).resolve_left no

/-- A family of leaf bundles of the same actual hub, after stripping exactly
their leaf deficit from each without any incoming debt at the hub. -/
private theorem strip_spoke_list [BEq V] [LawfulBEq V]
    (B : List (NormalizedPair col t)) (P : List V)
    (symm : ∀ x y, col x y=col y x) (bal : Balanced col r) (hr : 12≤r)
    (hubClique : P.Pairwise (fun x y=>col x y=t))
    (conditions : ∀ M∈B, M.left=P ∧ 3≤M.ld ∧ 3≤M.rd ∧
      M.rd≤M.exceptions.length ∧ M.right.Pairwise (fun x y=>col x y=t) ∧
      M.exteriorBudget+1<(2*r-M.residual-5)/2 ∧
      M.exteriorBudget+3<M.left.length ∧ M.exteriorBudget+3<M.right.length ∧
      M.ld+M.rd+3<r ∧ pairSlots (M.rd+1)+(M.rd+1)<r-1) :
    ∃ Z : List V, Z.Sublist (B.flatMap fun M=>M.exceptions) ∧
      Z.length+(B.map fun M=>M.rd).sum=(B.flatMap fun M=>M.exceptions).length ∧
      arrivalDebt col t P Z=0 := by
  induction B with
  | nil => exact ⟨[],List.Sublist.refl _,rfl,rfl⟩
  | cons M B ih =>
    obtain ⟨same,hl,hright,sur,cl,gap,wideL,wideR,apart,cap⟩ := conditions M (by simp)
    have ch : M.left.Pairwise (fun x y=>col x y=t) := same.symm ▸ hubClique
    obtain ⟨Z,zs,zlen,zcap⟩ := M.strip_leaf symm bal hr hl hright ch cl gap wideL wideR apart sur cap
    obtain ⟨J,js,jlen,jcap⟩ := ih (fun W wm=>conditions W (List.mem_cons_of_mem _ wm))
    have nullZ : arrivalDebt col t P Z=0 := by
      have each (x : V) (xm : x∈Z) : rowHoles col t x P≤1 := by
        rw [←same];exact zcap x xm
      have drop := arrivalDebt_max_holes col t P Z 1 each
      simp only [Nat.sub_self,Nat.mul_zero] at drop
      omega
    refine ⟨Z++J,zs.append js,?_,?_⟩
    · simp only [List.flatMap_cons,List.length_append,List.map_cons,List.sum_cons]
      omega
    · rw [arrivalDebt_append,nullZ,jcap]

/-- End-to-end global overload contradiction for actual normalized double
stars. All spoke stripping is from actual balanced coloring. The explicit
pair arrivals are discharged by the refined or rough lemmas above. -/
theorem NormalizedDoubleStar.route_impossible [BEq V] [LawfulBEq V]
    (C : NormalizedDoubleStar col t) (symm : ∀ x y, col x y=col y x)
    (bal : Balanced col r) (hr : 12≤r) (hl : 3≤C.center.ld) (hq : 3≤C.center.rd)
    (leftClique : C.center.left.Pairwise (fun x y=>col x y=t))
    (rightClique : C.center.right.Pairwise (fun x y=>col x y=t))
    (bl br : Nat) (hubRoute : PairArrivals C.center bl br)
    (spokes : ∀ M∈C.leftSpokes++C.rightSpokes,
      3≤M.rd ∧ M.right.Pairwise (fun x y=>col x y=t) ∧
      M.exteriorBudget+1<(2*r-M.residual-5)/2 ∧
      M.exteriorBudget+3<M.left.length ∧ M.exteriorBudget+3<M.right.length ∧
      M.ld+M.rd+3<r ∧ pairSlots (M.rd+1)+(M.rd+1)<r-1)
    (capL : pairSlots (C.center.ld+1)+(C.center.ld+1)+bl<r-1)
    (capR : pairSlots (C.center.rd+1)+(C.center.rd+1)+br<r-1) :
    False := by
  obtain ⟨A,aSub,aLen,aDebt⟩ := strip_spoke_list C.leftSpokes C.center.left symm bal hr leftClique (by
    intro M hm
    obtain ⟨_,eq,de⟩ := C.sameLeft M hm
    obtain ⟨h,c,g,w,z,a,p⟩ := spokes M (List.mem_append_left _ hm)
    exact ⟨eq,de.symm ▸ hl,h,Nat.le_of_lt (C.leftSurplus M hm),c,g,w,z,a,p⟩)
  obtain ⟨B,bSub,bLen,bDebt⟩ := strip_spoke_list C.rightSpokes C.center.right symm bal hr rightClique (by
    intro M hm
    obtain ⟨_,eq,de⟩ := C.sameRight M hm
    obtain ⟨h,c,g,w,z,a,p⟩ := spokes M (List.mem_append_right _ hm)
    exact ⟨eq,de.symm ▸ hq,h,Nat.le_of_lt (C.rightSurplus M hm),c,g,w,z,a,p⟩)
  let EL := C.leftSpokes.flatMap fun M=>M.exceptions
  let ER := C.rightSpokes.flatMap fun M=>M.exceptions
  let X := C.center.exceptions
  have nt : ((C.center.left++C.center.right)++(EL++(ER++X))).Nodup := C.distinct
  have ax : (A++hubRoute.left).Sublist (EL++(ER++X)) :=
    aSub.append (hubRoute.lsub.trans (List.sublist_append_right _ _))
  have bx : (B++hubRoute.right).Sublist (EL++(ER++X)) :=
    (bSub.append hubRoute.rsub).trans (List.sublist_append_right _ _)
  have l0 : C.center.left.Sublist (C.center.left++C.center.right) :=
    List.sublist_append_left _ _
  have r0 : C.center.right.Sublist (C.center.left++C.center.right) :=
    List.sublist_append_right _ _
  have lNd : ((A++hubRoute.left)++C.center.left).Nodup :=
    List.perm_append_comm.nodup_iff.mp ((l0.append ax).nodup nt)
  have rNd : ((B++hubRoute.right)++C.center.right).Nodup :=
    List.perm_append_comm.nodup_iff.mp ((r0.append bx).nodup nt)
  have la := routed_row_capacity bal C.center.left (A++hubRoute.left) C.center.ld bl
    lNd leftClique C.center.leftSize (by
      rw [arrivalDebt_append,aDebt,Nat.zero_add]
      exact hubRoute.leftDebt) capL
  have ra := routed_row_capacity bal C.center.right (B++hubRoute.right) C.center.rd br
    rNd rightClique C.center.rightSize (by
      rw [arrivalDebt_append,bDebt,Nat.zero_add]
      exact hubRoute.rightDebt) capR
  have tall := C.overload
  have nc := hubRoute.length_eq
  rw [List.length_append] at la ra
  omega
private theorem slots_twice (n : Nat) : 2*pairSlots (n+1)=(n+1)*n := by
  induction n with
  | zero => decide
  | succ n ih =>
    change 2*(pairSlots (n+1)+(n+1))=(n+1+1)*(n+1)
    simp only [Nat.mul_add,Nat.add_mul,Nat.one_mul,Nat.mul_one] at ih ⊢
    omega

private theorem slots_mono {a b : Nat} (le : a≤b) : pairSlots a≤pairSlots b := by
  induction b with
  | zero =>
    have e : a=0 := by omega
    simp [e]
  | succ b ih =>
    by_cases e : a=b+1
    · rw [e]; exact Nat.le_refl _
    · have h := ih (by omega)
      change pairSlots a≤pairSlots b+b
      omega



private theorem scaled_budget (D h : Nat) (high : 2≤h) (limit : 4*h≤7*D) :
    64*(mantelBound (h-1)+1)≤49*(D*D)+64 := by
  let A := (h-1)/2
  let B := (h-1+1)/2
  have am : 8*A≤7*D := by dsimp [A];omega
  have bm : 8*B≤7*D := by dsimp [B];omega
  have b := Nat.mul_le_mul am bm
  have lef : (8*A)*(8*B)=64*(A*B) := by
    calc
      _ = (8*8)*(A*B) := by ac_rfl
      _ = _ := rfl
  have rig : (7*D)*(7*D)=49*(D*D) := by
    calc
      _ = (7*7)*(D*D) := by ac_rfl
      _ = _ := rfl
  rw [lef,rig] at b
  change 64*(A*B+1)≤49*(D*D)+64
  rw [Nat.mul_add,Nat.mul_one]
  omega

private theorem local_numbers
    (M : NormalizedPair col t) (D : Nat)
    (radius : 49*(D*D)+64*(6*D+10)≤64*r) (dh : 3≤D)
    (dl : M.ld≤D) (dr : M.rd≤D)
    (hmin : 2≤M.residual) (_hmax : M.residual≤2*D-1)
    (small : 4*M.residual≤7*D) :
    M.exteriorBudget+1<(2*r-M.residual-5)/2 ∧
    M.exteriorBudget+3<M.left.length ∧
    M.exteriorBudget+3<M.right.length ∧
    M.ld+M.rd+3<r ∧ M.exteriorBudget<(D+1)*(D+1) := by
  have sx := scaled_budget D M.residual hmin small
  change 64*M.exteriorBudget≤49*(D*D)+64 at sx
  have space : M.exteriorBudget+6*D+9≤r := by omega
  have wideL := M.leftSize
  have wideR := M.rightSize
  have sl : (M.residual-1)/2≤D-1 := by omega
  have sr : (M.residual-1+1)/2≤D-1 := by omega
  have sd := Nat.mul_le_mul sl sr
  have larger : (D-1)*(D-1)+1<(D+1)*(D+1) := by
    let a := D-1
    have eq : D+1=a+2 := by dsimp [a];omega
    change a*a+1<(D+1)*(D+1)
    rw [eq]
    simp only [Nat.mul_add,Nat.add_mul]
    omega
  refine ⟨by omega,by omega,by omega,by omega,?_⟩
  change (M.residual-1)/2*((M.residual-1+1)/2)+1<(D+1)*(D+1)
  omega

private theorem general_palette_numbers (D r : Nat)
    (radius : 49*(D*D)+64*(6*D+10)≤64*r) :
    pairSlots (D+1)+(D+1)+D<r-1 := by
  have sl := slots_twice D
  rw [Nat.add_mul,Nat.one_mul] at sl
  omega

private theorem rough_palette_numbers (D r mu : Nat)
    (radius : 49*(D*D)+64*(6*D+10)≤64*r) (small : 4*mu≤D) :
    pairSlots (D+1)+(D+1)+mu*D<r-1 := by
  have sl := slots_twice D
  rw [Nat.add_mul,Nat.one_mul] at sl
  have cap := Nat.mul_le_mul_right D small
  rw [Nat.mul_assoc] at cap
  omega

/-- Full uniform conditional double-star exclusion. All rows have deficit
between 3 and D. Each true leaf spoke satisfies the deletion capacity in
the normalized data. The integer radius is equivalent to
r ≥ ceil(49 D² / 64) + 6D + 10. No geometric coloring partitions or row
routes are assumed. -/
theorem NormalizedDoubleStar.uniform_impossible [BEq V] [LawfulBEq V]
    (C : NormalizedDoubleStar col t) (symm : ∀ x y, col x y=col y x)
    (bal : Balanced col r)
    (D : Nat) (radius : 49*(D*D)+64*(6*D+10)≤64*r)
    (leftHigh : 3≤C.center.ld) (leftSmall : C.center.ld≤D)
    (rightHigh : 3≤C.center.rd) (rightSmall : C.center.rd≤D)
    (leftClique : C.center.left.Pairwise (fun x y=>col x y=t))
    (rightClique : C.center.right.Pairwise (fun x y=>col x y=t))
    (leaves : ∀ M∈C.leftSpokes++C.rightSpokes,
      3≤M.rd ∧ M.rd≤D ∧ M.right.Pairwise (fun x y=>col x y=t)) :
    False := by
  have dh : 3≤D := by omega
  have hr : 12≤r := by omega
  have palette := general_palette_numbers D r radius
  have sp (M : NormalizedPair col t) (hm : M∈C.leftSpokes++C.rightSpokes) :
      3≤M.rd ∧ M.right.Pairwise (fun x y=>col x y=t) ∧
      M.exteriorBudget+1<(2*r-M.residual-5)/2 ∧
      M.exteriorBudget+3<M.left.length ∧ M.exteriorBudget+3<M.right.length ∧
      M.ld+M.rd+3<r ∧ pairSlots (M.rd+1)+(M.rd+1)<r-1 := by
    obtain ⟨rh,rs,cl⟩ := leaves M hm
    have hub (M) (hm : M∈C.leftSpokes++C.rightSpokes) :
        3≤M.ld ∧ M.ld≤D ∧ M.rd<M.exceptions.length ∧
        M.left.Pairwise (fun x y=>col x y=t) := by
      rcases List.mem_append.mp hm with l|q
      · obtain ⟨_,eq,de⟩ := C.sameLeft M l
        exact ⟨de.symm ▸ leftHigh,de.symm ▸ leftSmall,C.leftSurplus M l,eq.symm ▸ leftClique⟩
      · obtain ⟨_,eq,de⟩ := C.sameRight M q
        exact ⟨de.symm ▸ rightHigh,de.symm ▸ rightSmall,C.rightSurplus M q,eq.symm ▸ rightClique⟩
    obtain ⟨lh,ls,sur,ch⟩ := hub M hm
    have bound := M.high_parallel_multiplicity_bound symm bal hr lh rh
    have residual : M.residual=M.ld+M.rd-M.exceptions.length := rfl
    have ⟨g,w,v,a,_⟩ := local_numbers M D radius dh ls rs
      (by omega) (by omega) (by omega)
    have sm := slots_mono (by omega : M.rd+1≤D+1)
    exact ⟨rh,cl,g,w,v,a,by omega⟩
  let M := C.center
  let mu := M.exceptions.length
  by_cases short : 4*mu≤D
  · obtain ⟨routing⟩ := M.rough_arrivals symm bal leftHigh rightHigh leftClique rightClique
    have whole := rough_palette_numbers D r mu radius short
    have l := slots_mono (by omega : C.center.ld+1≤D+1)
    have q := slots_mono (by omega : C.center.rd+1≤D+1)
    have lc : mu*(C.center.ld-1)≤mu*D := Nat.mul_le_mul_left mu (by omega)
    have rc : mu*(C.center.rd-1)≤mu*D := Nat.mul_le_mul_left mu (by omega)
    apply C.route_impossible symm bal hr leftHigh rightHigh leftClique rightClique
      (mu*(C.center.ld-1)) (mu*(C.center.rd-1)) routing sp
    · omega
    · omega
  · have highBound := M.high_parallel_multiplicity_bound symm bal hr leftHigh rightHigh
    have res : M.residual=M.ld+M.rd-mu := rfl
    have lh : M.ld≤D := leftSmall
    have rh : M.rd≤D := rightSmall
    change mu≤M.ld+M.rd-2 at highBound
    obtain ⟨g,w,v,a,k⟩ := local_numbers M D radius dh lh rh (by omega) (by omega) (by omega)
    obtain ⟨routing⟩ := M.refined_arrivals symm bal hr leftHigh rightHigh leftClique rightClique D g w v a k
    have l := slots_mono (by omega : C.center.ld+1≤D+1)
    have q := slots_mono (by omega : C.center.rd+1≤D+1)
    exact C.route_impossible symm bal hr leftHigh rightHigh leftClique rightClique D D routing sp
      (by omega) (by omega)

end ParallelMantel.Pentagon
#print axioms ParallelMantel.Pentagon.NormalizedPair.refined_arrivals
#print axioms ParallelMantel.Pentagon.NormalizedPair.rough_arrivals
#print axioms ParallelMantel.Pentagon.NormalizedDoubleStar.route_impossible

#print axioms ParallelMantel.Pentagon.NormalizedDoubleStar.uniform_impossible
