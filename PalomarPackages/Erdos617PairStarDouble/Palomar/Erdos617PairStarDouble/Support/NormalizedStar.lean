module

public import Palomar.Erdos617PairStarDouble.Support.GlobalPalette
public import Lean.Elab.Tactic.Omega

@[expose] public section

namespace ParallelMantel.Pentagon

open Erdos617Geometry

set_option maxHeartbeats 1000000

universe u
variable {V : Type u} {r : Nat} {col : V→V→Fin r} {t : Fin r}

/-- A matching-free star configuration on actual rows in the conditional
two-supported normalized core. Every exception is in one bundle incident
to the common hub. Row/multiplicity normalization is input, not inferred
for arbitrary counterexamples to Erdős #617. -/
structure NormalizedStar (col : V→V→Fin r) (t : Fin r) where
  hubAnchor : V
  hub : List V
  deficit : Nat
  branches : List (NormalizedPair col t)
  sameHub : ∀ M∈branches, M.p=hubAnchor ∧ M.left=hub ∧ M.ld=deficit
  hubSize : hub.length+deficit=r
  hubClique : hub.Pairwise (fun x y=>col x y=t)
  allDistinct : (hub++(branches.flatMap fun M=>M.exceptions)).Nodup
  overload : (branches.flatMap fun M=>M.exceptions).length =
    deficit+(branches.map fun M=>M.rd).sum+1

private theorem flatMap_sublist_of {A : Type u} {f h : A→List V} (B : List A)
    (sub : ∀ a∈B,(f a).Sublist (h a)) :
    (B.flatMap f).Sublist (B.flatMap h) := by
  induction B with
  | nil => exact List.Sublist.refl _
  | cons a B ih =>
    exact (sub a (by simp)).append (ih (fun x xm=>sub x (List.mem_cons_of_mem _ xm)))

private theorem flatMap_debt_le {A : Type u} (B : List A) (f : A→List V) (K : A→Nat)
    (P : List V) (each : ∀ a∈B,arrivalDebt col t P (f a)≤K a) :
    arrivalDebt col t P (B.flatMap f)≤(B.map K).sum := by
  induction B with
  | nil => exact Nat.le_refl _
  | cons a B ih =>
    rw [List.flatMap_cons,arrivalDebt_append,List.map_cons,List.sum_cons]
    exact Nat.add_le_add (each a (by simp)) (ih (fun x xm=>each x (List.mem_cons_of_mem _ xm)))

private theorem flatMap_length_le {A : Type u} (B : List A) (f : A→List V) (n : A→Nat)
    (each : ∀ a∈B,(f a).length≤n a) :
    (B.flatMap f).length≤(B.map n).sum := by
  induction B with
  | nil => exact Nat.le_refl _
  | cons a B ih =>
    rw [List.flatMap_cons,List.length_append,List.map_cons,List.sum_cons]
    exact Nat.add_le_add (each a (by simp)) (ih (fun x xm=>each x (List.mem_cons_of_mem _ xm)))

private theorem flatMap_partition_length {A : Type u} (B : List A) (f g h : A→List V)
    (each : ∀ a∈B,(f a).length+(g a).length=(h a).length) :
    (B.flatMap f).length+(B.flatMap g).length=(B.flatMap h).length := by
  induction B with
  | nil => rfl
  | cons a B ih =>
    simp only [List.flatMap_cons,List.length_append]
    have p := each a (by simp)
    have q := ih (fun x xm=>each x (List.mem_cons_of_mem _ xm))
    omega

private theorem whole_exception_in (M : NormalizedPair col t) {x : V} (m : x∈M.exceptions) :
    x∈M.vertices M.exceptions :=
  List.mem_append_right _ (List.mem_append_right _ m)

private theorem whole_left_in (M : NormalizedPair col t) :
    M.left⊆M.vertices M.exceptions := fun _ m=>List.mem_append_left _ m

private theorem whole_right_in (M : NormalizedPair col t) :
    M.right⊆M.vertices M.exceptions := fun _ m=>List.mem_append_right _ (List.mem_append_left _ m)

/-- Full conditional star contradiction, using actual per-bundle row routing,
all exceptions exactly once, and balance on the overfull reached row. No
external partition or palette inequality is assumed; the stated numerical
strict upper bounds are tests on the supplied row deficits and routing costs. -/
theorem NormalizedStar.refined_star_impossible [BEq V] [LawfulBEq V]
    (C : NormalizedStar col t) (symm : ∀ x y, col x y=col y x)
    (bal : Balanced col r) (hr : 12≤r) (hd : 3≤C.deficit)
    (K : NormalizedPair col t → Nat)
    (branches : ∀ M∈C.branches,
      3≤M.rd ∧ M.right.Pairwise (fun x y=>col x y=t) ∧
      M.exteriorBudget+1<(2*r-M.residual-5)/2 ∧
      M.exteriorBudget+3<M.left.length ∧ M.exteriorBudget+3<M.right.length ∧
      M.ld+M.rd+3<r ∧ M.exteriorBudget<(K M+1)*(K M+1) ∧
      pairSlots (M.rd+1)+(M.rd+1)+K M<r-1)
    (hubBudget : pairSlots (C.deficit+1)+(C.deficit+1)+(C.branches.map K).sum<r-1) :
    False := by
  classical
  let Per (M : NormalizedPair col t) (E : Option V) (route : V→Bool) : Prop :=
    ∀ x∈M.exceptions,
      let holes := if route x then degree M.miss x M.left else degree M.miss x M.right
      holes≤1 ∨ (E=some x ∧ holes≤K M+1)
  have ex (M : NormalizedPair col t) (hm : M∈C.branches) : ∃ E route, Per M E route := by
    obtain ⟨high,cl,gap,wideL,wideR,apart,sq,_⟩ := branches M hm
    have leftHigh : 3≤M.ld := by rw [(C.sameHub M hm).2.2];exact hd
    have leftClique : M.left.Pairwise (fun x y=>col x y=t) := by
      rw [(C.sameHub M hm).2.1]
      exact C.hubClique
    exact M.one_costly_exception symm bal hr leftHigh high leftClique cl (K M) gap wideL wideR apart sq
  let E (M : NormalizedPair col t) : Option V :=
    if hm : M∈C.branches then Classical.choose (ex M hm) else none
  let route (M : NormalizedPair col t) : V→Bool :=
    if hm : M∈C.branches then Classical.choose (Classical.choose_spec (ex M hm)) else (fun _=>false)
  have works (M : NormalizedPair col t) (hm : M∈C.branches) : Per M (E M) (route M) := by
    simpa only [E,route,dite_eq_left hm] using Classical.choose_spec (Classical.choose_spec (ex M hm))
  let toHub (M : NormalizedPair col t) := M.exceptions.filter (route M)
  let toLeaf (M : NormalizedPair col t) := M.exceptions.filter (fun x=>!route M x)
  have subH (M : NormalizedPair col t) : (toHub M).Sublist M.exceptions := List.filter_sublist
  have subL (M : NormalizedPair col t) : (toLeaf M).Sublist M.exceptions := List.filter_sublist
  have ndEx (M : NormalizedPair col t) : M.exceptions.Nodup :=
    (List.nodup_append.mp (List.nodup_append.mp M.disjointLists).2.1).2.1
  have hubDebt (M : NormalizedPair col t) (hm : M∈C.branches) :
      arrivalDebt col t C.hub (toHub M)≤K M := by
    rw [← (C.sameHub M hm).2.1]
    apply arrivalDebt_single_cap col t M.left (toHub M) (E M) (K M) ((subH M).nodup (ndEx M))
    intro x xm
    have xE := (subH M).subset xm
    have rule := works M hm x xE
    have routeL : route M x=true := (List.mem_filter.mp xm).2
    have compat := rowHoles_eq_degree col t (M.vertices M.exceptions) M.left x
      (whole_exception_in M xE) (whole_left_in M)
    rw [compat]
    simpa only [routeL,ite_true] using rule
  have leafDebt (M : NormalizedPair col t) (hm : M∈C.branches) :
      arrivalDebt col t M.right (toLeaf M)≤K M := by
    apply arrivalDebt_single_cap col t M.right (toLeaf M) (E M) (K M) ((subL M).nodup (ndEx M))
    intro x xm
    have xE := (subL M).subset xm
    have rule := works M hm x xE
    have routeR : route M x=false := by
      have h : (!(route M x))=true := (List.mem_filter.mp xm).2
      simpa only [Bool.not_eq_true'] using h
    have compat := rowHoles_eq_degree col t (M.vertices M.exceptions) M.right x
      (whole_exception_in M xE) (whole_right_in M)
    rw [compat]
    simpa only [routeR,Bool.false_eq_true,ite_false] using rule
  have leafCount (M : NormalizedPair col t) (hm : M∈C.branches) :
      (toLeaf M).length≤M.rd := by
    have dis : (M.right++M.exceptions).Nodup := (List.nodup_append.mp M.disjointLists).2.1
    have ds : (M.right++toLeaf M).Nodup :=
      ((List.Sublist.refl M.right).append (subL M)).nodup dis
    have joint : (toLeaf M++M.right).Nodup := List.perm_append_comm.nodup_iff.mp ds
    rcases branches M hm with ⟨_,cl,_,_,_,_,_,budget⟩
    exact routed_row_capacity bal M.right (toLeaf M) M.rd (K M) joint cl M.rightSize
      (leafDebt M hm) budget
  let H := C.branches.flatMap toHub
  let L := C.branches.flatMap toLeaf
  have counted : H.length+L.length=(C.branches.flatMap fun M=>M.exceptions).length := by
    exact flatMap_partition_length C.branches toHub toLeaf (fun M=>M.exceptions)
      (fun M _=>by simpa only [List.length_append] using (List.filter_append_perm (route M) M.exceptions).length_eq)
  have leafAll : L.length<=(C.branches.map fun M=>M.rd).sum :=
    flatMap_length_le C.branches toLeaf (fun M=>M.rd) leafCount
  have hubSub : H.Sublist (C.branches.flatMap fun M=>M.exceptions) :=
    flatMap_sublist_of C.branches (fun M _=>subH M)
  have hubNd : (C.hub++H).Nodup :=
    ((List.Sublist.refl C.hub).append hubSub).nodup C.allDistinct
  have hubAll : H.length≤C.deficit :=
    routed_row_capacity bal C.hub H C.deficit (C.branches.map K).sum
      (List.perm_append_comm.nodup_iff.mp hubNd) C.hubClique C.hubSize
      (flatMap_debt_le C.branches toHub K C.hub hubDebt) hubBudget
  have surplus := C.overload
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

private theorem all_one_surplus {A : Type u} (B : List A) (f : A→List V) (d : A→Nat)
    (each : ∀ a∈B,(f a).length=d a+1) :
    (B.flatMap f).length=(B.map d).sum+B.length := by
  induction B with
  | nil => rfl
  | cons a B ih =>
    simp only [List.flatMap_cons,List.length_append,List.map_cons,List.sum_cons,List.length_cons]
    rw [each a (by simp),ih (fun x xm=>each x (List.mem_cons_of_mem _ xm))]
    omega

private theorem sum_constant {A : Type u} (B : List A) (K : Nat) :
    (B.map fun _=>K).sum=B.length*K := by
  induction B with
  | nil => simp
  | cons a B ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons,ih,Nat.add_mul,Nat.one_mul]
    omega

private theorem unit_margin_numbers (D r : Nat) (hd : 3≤D) (many : (D+1)*(D+1)≤r) :
    let K := (D-1)/2
    let S := mantelBound (D-2)+1
    S<(K+1)*(K+1) ∧
    S+1<(2*r-(D-1)-5)/2 ∧
    S+D+3<r ∧ 2*D+3<r ∧
    pairSlots (D+1)+(D+1)+(D+1)*K<r-1 := by
  dsimp only
  let K := (D-1)/2
  let S := mantelBound (D-2)+1
  have KD : 2*K+1≤D := by dsimp [K];omega
  have K1 : K+1≤D := by omega
  have kpos : 1≤K := by dsimp [K];omega
  have sq : S<(K+1)*(K+1) := by
    have f : (D-2)/2≤K := by dsimp [K];omega
    have c : (D-2+1)/2=K := by dsimp [K];omega
    have prod := Nat.mul_le_mul f (Nat.le_refl K)
    change mantelBound (D-2)+1<(K+1)*(K+1)
    unfold mantelBound
    rw [c]
    simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul]
    omega
  have Sd := (Nat.lt_of_lt_of_le sq (Nat.mul_le_mul K1 K1))
  have room : D*D+2*D+1≤r := by
    simp only [Nat.mul_add,Nat.add_mul,Nat.one_mul,Nat.mul_one] at many
    omega
  have sizeD : 2*D+3<r := by
    have lm : 3*3≤D*D := Nat.mul_le_mul hd hd
    omega
  have swide : S+D+3<r := by omega
  have split : S+1<(2*r-(D-1)-5)/2 := by omega
  have p := slots_twice D
  rw [Nat.add_mul,Nat.one_mul] at p
  have bill := Nat.mul_le_mul_right (D+1) KD
  rw [Nat.add_mul,Nat.one_mul,Nat.mul_assoc,Nat.mul_comm K (D+1),Nat.mul_add,Nat.mul_one] at bill
  have pe : pairSlots (D+1)+(D+1)+(D+1)*K<r-1 := by omega
  exact ⟨sq,split,swide,sizeD,pe⟩

/-- Explicit unbounded family: every branch has one more exception than
its leaf deficit, all leaves are high and at most the hub deficit, and
r ≥ (hub deficit + 1)^2. The one-overload normalization forces exactly
hub deficit+1 distinct branches; no all-leaves-equal premise is needed. -/
theorem NormalizedStar.unit_margin_star_impossible [BEq V] [LawfulBEq V]
    (C : NormalizedStar col t) (symm : ∀ x y, col x y=col y x)
    (bal : Balanced col r) (hd : 3≤C.deficit)
    (many : (C.deficit+1)*(C.deficit+1)≤r)
    (branches : ∀ M∈C.branches,
      3≤M.rd ∧ M.rd≤C.deficit ∧ M.exceptions.length=M.rd+1 ∧
      M.right.Pairwise (fun x y=>col x y=t)) :
    False := by
  let D := C.deficit
  let K := (D-1)/2
  let S := mantelBound (D-2)+1
  obtain ⟨sq,gap,width,apart,hub⟩ := unit_margin_numbers D r hd many
  change S<(K+1)*(K+1) at sq
  change S+1<(2*r-(D-1)-5)/2 at gap
  change S+D+3<r at width
  change pairSlots (D+1)+(D+1)+(D+1)*K<r-1 at hub
  have hr : 12≤r :=
    Nat.le_trans (by decide : 12≤4*4) (Nat.le_trans
      (Nat.mul_le_mul (by omega : 4≤C.deficit+1) (by omega : 4≤C.deficit+1)) many)
  have n : C.branches.length=D+1 := by
    have exactSum := all_one_surplus C.branches (fun M=>M.exceptions) (fun M=>M.rd)
      (fun M hm=>(branches M hm).2.2.1)
    have over := C.overload
    change _ = D+(C.branches.map fun M=>M.rd).sum+1 at over
    omega
  apply C.refined_star_impossible symm bal hr hd (fun _=>K)
  · intro M hm
    obtain ⟨high,small,exlen,cl⟩ := branches M hm
    have left := (C.sameHub M hm).2.2
    change M.ld=D at left
    have mres : M.residual=D-1 := by
      unfold NormalizedPair.residual
      omega
    have mb : M.exteriorBudget=S := by
      unfold NormalizedPair.exteriorBudget S
      rw [mres,show D-1-1=D-2 by omega]
    have xl := M.leftSize
    have xr := M.rightSize
    have cap := slots_mono (by omega : M.rd+1≤D+1)
    have smallK : K≤(D+1)*K := by
      have zero := Nat.mul_le_mul_right K (by omega : 1≤D+1)
      simpa only [Nat.one_mul] using zero
    exact ⟨high,cl,by rw [mb,mres];exact gap,by rw [mb];omega,
      by rw [mb];omega,by omega,by rwa [mb],by omega⟩
  · change pairSlots (D+1)+(D+1)+(C.branches.map fun _=>K).sum<r-1
    simpa only [sum_constant C.branches K,n] using hub

end ParallelMantel.Pentagon

#print axioms ParallelMantel.Pentagon.NormalizedStar.refined_star_impossible

#print axioms ParallelMantel.Pentagon.NormalizedStar.unit_margin_star_impossible
