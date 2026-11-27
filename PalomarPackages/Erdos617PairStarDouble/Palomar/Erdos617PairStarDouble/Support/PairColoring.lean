module

public import Palomar.Erdos617PairStarDouble.Support.ParallelBoundary
public import Palomar.Erdos617PairStarDouble.Support.EvenBoundary
public import Palomar.Erdos617PairStarDouble.Support.FromColoring
public import Lean.Elab.Tactic.Omega

@[expose] public section

namespace ParallelMantel.Pentagon

open Erdos617Geometry

universe u

variable {V : Type u} {r : Nat}

noncomputable def missingColor (col : V→V→Fin r) (t : Fin r) (W : List V) : V→V→Bool :=
  open Classical in
  fun x y=>decide (x∈W ∧ y∈W ∧ x≠y ∧ col x y≠t)

private theorem missingColor_true {col : V→V→Fin r} {t : Fin r} {W : List V} {x y : V} :
    missingColor col t W x y=true ↔ x∈W ∧ y∈W ∧ x≠y ∧ col x y≠t := by
  simp [missingColor]

private theorem missingColor_false_of {col : V→V→Fin r} {t : Fin r} {W : List V} {x y : V}
    (h : x=y ∨ col x y=t) : missingColor col t W x y=false := by
  rw [←Bool.not_eq_true]
  intro equal
  obtain ⟨_,_,ne,nt⟩ := missingColor_true.mp equal
  exact h.elim ne nt

theorem missingColor_symmetric (col : V→V→Fin r) (symm : ∀ x y, col x y=col y x)
    (t : Fin r) (W : List V) : Symmetric (missingColor col t W) := by
  intro x y
  apply Bool.eq_iff_iff.mpr
  rw [missingColor_true,missingColor_true,symm x y]
  constructor <;> rintro ⟨a,b,c,d⟩ <;> exact ⟨b,a,Ne.symm c,d⟩

theorem missingColor_loopless (col : V→V→Fin r) (t : Fin r) (W : List V) :
    Loopless (missingColor col t W) :=
  fun x => missingColor_false_of (x:=x) (Or.inl rfl)

theorem missingColor_edges_eq_palette (col : V→V→Fin r) (t : Fin r)
    (W U : List V) (nd : U.Nodup) (inside : ∀ x∈U, x∈W) :
    edges (missingColor col t W) U =
      ((orderedColors col U).filter (fun h => !(h==t))).length := by
  induction U with
  | nil => rfl
  | cons x U ih =>
    have nds := List.nodup_cons.mp nd
    have fw : U.filter (missingColor col t W x) =
        U.filter (fun y => !((col x y)==t)) := by
      apply List.filter_congr
      intro y ym
      apply Bool.eq_iff_iff.mpr
      rw [missingColor_true]
      have xw := inside x (by simp)
      have yw := inside y (List.mem_cons_of_mem x ym)
      have xy : x≠y := fun eq => nds.1 (eq.symm ▸ ym)
      simp [xw,yw,xy]
    have tail := ih nds.2 (fun y ym => inside y (List.mem_cons_of_mem x ym))
    rw [edges,tail,orderedColors,List.filter_append,List.length_append]
    congr 1
    unfold degree
    rw [fw,List.filter_map,List.length_map]
    rfl

/-- Actual hue ledger gives the full complement density used in the odd
and even graph boundaries, with no abstract density premise to assume. -/
theorem missingColor_floor (col : V→V→Fin r) (t : Fin r) (bal : Balanced col r)
    (W : List V) (nd : W.Nodup) :
    (r-1)*(W.length-r)≤edges (missingColor col t W) W := by
  let E := orderedColors col W
  let F := E.filter (fun h=> !(h==t))
  obtain ⟨palND,palNot,palLen⟩ := exceptPalette_specs t
  have quota (h : Fin r) (hm : h∈exceptPalette t) : W.length-r ≤ F.count h := by
    have hne : h≠t := fun e => palNot (e ▸ hm)
    have edge := hue_edge_floor col h r (balanced_independenceCap col r bal h) W nd
    change W.length-r ≤ (E.filter (fun x => !(x==t))).count h
    rw [List.count_filter (a:=h) (p:=fun x : Fin r => !(x==t)) (show (!(h==t))=true by simp [hne])]
    change W.length ≤ r+E.count h at edge
    omega
  have bound := hue_quota_mul_le_length (exceptPalette t) palND (W.length-r) F quota
  rw [palLen] at bound
  rw [missingColor_edges_eq_palette col t W W nd (fun _ m=>m)]
  exact bound

/-- Data inherited by any pair of rows and its shared-support exceptions in
the bounded-exception normalized core. The two caps are scoped to the actual
core vertex list, not claimed for all ambient vertices. -/
structure NormalizedPair (col : V→V→Fin r) (t : Fin r) where
  core : List V
  anchors : List V
  p : V
  q : V
  left : List V
  right : List V
  exceptions : List V
  ld : Nat
  rd : Nat
  anchorInd : anchors.Pairwise (Compatible (fun x y=>col x y=t))
  p_mem : p∈anchors
  q_mem : q∈anchors
  pq : p≠q
  p_left : p∈left
  q_right : q∈right
  anchorCore : ∀ a∈anchors, a∈core
  verticesCore : ∀ x∈left++(right++exceptions), x∈core
  disjointLists : (left++(right++exceptions)).Nodup
  privateLeft : ∀ x∈left, Private (fun x y=>col x y=t) anchors p x
  privateRight : ∀ x∈right, Private (fun x y=>col x y=t) anchors q x
  double : ∀ x∈exceptions, Double (fun x y=>col x y=t) anchors p q x
  coreInd : ∀ I : List V, (∀ x∈I, x∈core) →
    I.Pairwise (Compatible (fun x y=>col x y=t)) → I.length≤anchors.length
  coreClique : ∀ I : List V, I.Nodup → (∀ x∈I, x∈core) →
    I.Pairwise (fun x y=>col x y=t) → I.length≤r-1
  leftSize : left.length+ld=r
  rightSize : right.length+rd=r
  normalizedSum : ld+rd≤r-3

variable {col : V→V→Fin r} {t : Fin r}

def NormalizedPair.vertices (M : NormalizedPair col t) (X : List V) : List V :=
  M.left++(M.right++X)

private theorem pair_mem_split (M : NormalizedPair col t) (X : List V)
    {x : V} (m : x∈M.vertices X) : x∈M.left ∨ x∈M.right ∨ x∈X := by
  unfold NormalizedPair.vertices at m
  simpa only [List.mem_append] using m

private theorem pair_core (M : NormalizedPair col t) {X : List V}
    (sub : X.Sublist M.exceptions) (x : V) (xm : x∈M.vertices X) : x∈M.core :=
  M.verticesCore x
    ((List.Sublist.refl M.left |>.append ((List.Sublist.refl M.right).append sub)).subset xm)

theorem NormalizedPair.missing_independence_cap (M : NormalizedPair col t) {X : List V}
    (sub : X.Sublist M.exceptions) :
    InducedIndependenceCap (missingColor col t (M.vertices X)) (M.vertices X) (r-1) := by
  intro I nd inc indep
  apply M.coreClique I nd (fun x xm=>pair_core M sub x (inc x xm))
  apply (List.nodup_iff_pairwise_ne.mp nd).imp_of_mem
  intro x y xm ym ne
  apply Classical.byContradiction
  intro no
  have edge := missingColor_true.mpr ⟨inc x xm,inc y ym,ne,no⟩
  have bad := indep x xm y ym
  rw [edge] at bad
  contradiction

theorem NormalizedPair.missing_triangle_free [BEq V] [LawfulBEq V]
    (M : NormalizedPair col t) {X : List V} (sub : X.Sublist M.exceptions) :
    TriangleFree (missingColor col t (M.vertices X)) := by
  intro x y z xy xz
  rw [←Bool.not_eq_true]
  intro yz
  obtain ⟨xW,yW,nxy,hxy⟩ := missingColor_true.mp xy
  obtain ⟨_,zW,nxz,hxz⟩ := missingColor_true.mp xz
  obtain ⟨_,_,nyz,hyz⟩ := missingColor_true.mp yz
  let D := eraseAnchors M.anchors [M.p,M.q]
  have rm := eraseAnchors_spec (fun a b=>col a b=t) M.anchors [M.p,M.q]
    M.anchorInd (by simp [M.pq]) (by
      intro a am
      simp only [List.mem_cons,List.not_mem_nil,or_false] at am
      exact am.elim (fun e=>e.symm ▸ M.p_mem) (fun e=>e.symm ▸ M.q_mem))
  have fromD (v : V) (vm : v∈M.vertices X) (a : V) (am : a∈D) :
      Compatible (fun x y=>col x y=t) v a := by
    have ⟨ac,ano⟩ := rm.2.2 a am
    have ap : a≠M.p := fun e => ano (by simp [e])
    have aq : a≠M.q := fun e => ano (by simp [e])
    rcases pair_mem_split M X vm with pl | qr | ex
    · exact (M.privateLeft v pl).away a ac ap
    · exact (M.privateRight v qr).away a ac aq
    · exact (M.double v (sub.subset ex)).compatible_away ac ap aq
  have ge := M.coreInd ([x,y,z]++D) (by
    intro v vm
    rcases List.mem_append.mp vm with vl | vd
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at vl
      rcases vl with eq | eq | eq
      · exact eq.symm ▸ pair_core M sub x xW
      · exact eq.symm ▸ pair_core M sub y yW
      · exact eq.symm ▸ pair_core M sub z zW
    · exact M.anchorCore v (rm.2.2 v vd).1) (by
      apply List.pairwise_append.mpr
      refine ⟨?_,rm.2.1,?_⟩
      · simp [Compatible,nxy,nxz,nyz,hxy,hxz,hyz]
      · intro v vm a am
        simp only [List.mem_cons,List.not_mem_nil,or_false] at vm
        rcases vm with eq | eq | eq
        · exact eq.symm ▸ fromD x xW a am
        · exact eq.symm ▸ fromD y yW a am
        · exact eq.symm ▸ fromD z zW a am)
  have len := rm.1
  change D.length+[M.p,M.q].length=M.anchors.length at len
  simp only [List.length_append,List.length_cons,List.length_nil] at ge len
  omega

private theorem NormalizedPair.missing_words (M : NormalizedPair col t) {X : List V}
    (sub : X.Sublist M.exceptions) :
    let g := missingColor col t (M.vertices X)
    (∀ x∈M.left, anchorWord g M.p M.q x=(false,true)) ∧
    (∀ x∈M.right, anchorWord g M.p M.q x=(true,false)) ∧
    (∀ x∈X, anchorWord g M.p M.q x=(false,false)) := by
  let W := M.vertices X
  let g := missingColor col t W
  have inL (x : V) (m : x∈M.left) : x∈W := List.mem_append_left _ m
  have inR (x : V) (m : x∈M.right) : x∈W :=
    List.mem_append_right _ (List.mem_append_left _ m)
  have pW := inL M.p M.p_left
  have qW := inR M.q M.q_right
  change (∀ x∈M.left, anchorWord g M.p M.q x=(false,true)) ∧
    (∀ x∈M.right, anchorWord g M.p M.q x=(true,false)) ∧
    (∀ x∈X, anchorWord g M.p M.q x=(false,false))
  refine ⟨?_,?_,?_⟩
  · intro x xm
    have y := M.privateLeft x xm
    have absent : g x M.p=false := missingColor_false_of y.own
    have away := y.away M.q M.q_mem (Ne.symm M.pq)
    have edge : g x M.q=true := missingColor_true.mpr ⟨inL x xm,qW,away.1,away.2⟩
    simp [anchorWord,absent,edge]
  · intro x xm
    have y := M.privateRight x xm
    have absent : g x M.q=false := missingColor_false_of y.own
    have away := y.away M.p M.p_mem M.pq
    have edge : g x M.p=true := missingColor_true.mpr ⟨inR x xm,pW,away.1,away.2⟩
    simp [anchorWord,absent,edge]
  · intro x xm
    have y := M.double x (sub.subset xm)
    have a : g x M.p=false := missingColor_false_of (Or.inr y.owner_adj)
    have b : g x M.q=false := missingColor_false_of (Or.inr y.source_adj)
    simp [anchorWord,a,b]

private theorem NormalizedPair.trim_nodup (M : NormalizedPair col t) {X : List V}
    (sub : X.Sublist M.exceptions) : (M.vertices X).Nodup :=
  ((List.Sublist.refl M.left).append ((List.Sublist.refl M.right).append sub)).nodup
    M.disjointLists

/-- Prior known pair bound, reverified directly from actual balanced colors
plus the normalized-core pair hypotheses. It does not use the new h=1 theorem. -/
theorem NormalizedPair.prior_multiplicity_bound [BEq V] [LawfulBEq V]
    (M : NormalizedPair col t) (symm : ∀ x y, col x y=col y x)
    (bal : Balanced col r) (hr : 6≤r) (positive : 1≤M.ld+M.rd) :
    M.exceptions.length ≤ M.ld+M.rd-1 := by
  apply Classical.byContradiction
  intro no
  let X := M.exceptions.take (M.ld+M.rd)
  let W := M.vertices X
  have sub : X.Sublist M.exceptions := List.take_sublist _ _
  have nd := M.trim_nodup sub
  have xlen : X.length=M.ld+M.rd := by
    unfold X
    rw [List.length_take,Nat.min_eq_left]
    omega
  have pl := M.leftSize
  have ql := M.rightSize
  have size : W.length=2*r := by
    dsimp [W,NormalizedPair.vertices]
    rw [List.length_append,List.length_append,xlen]
    omega
  have dense := missingColor_floor col t bal W nd
  have s : W.length-r=r := by omega
  rw [s,Nat.mul_comm (r-1) r] at dense
  exact even_boundary_impossible (missingColor_symmetric col symm t W)
    (missingColor_loopless col t W) (M.missing_triangle_free sub)
    W r hr nd size dense (M.missing_independence_cap sub)

/-- High-deficit parallel pair theorem, from the actual finite hue palette
and exact two-support source geometry. This excludes one boundary
multiplicity beyond the previously checked pair cap, not every high-high
configuration nor the Erdős–Gyárfás conjecture. -/
theorem NormalizedPair.high_parallel_multiplicity_bound [BEq V] [LawfulBEq V]
    (M : NormalizedPair col t) (symm : ∀ x y, col x y=col y x)
    (bal : Balanced col r) (hr : 12≤r) (hl : 3≤M.ld) (hq : 3≤M.rd) :
    M.exceptions.length ≤ M.ld+M.rd-2 := by
  have prior := M.prior_multiplicity_bound symm bal (by omega) (by omega)
  apply Classical.byContradiction
  intro no
  have xlen : M.exceptions.length=M.ld+M.rd-1 := by omega
  let X := M.exceptions
  let W := M.vertices X
  have sub : X.Sublist M.exceptions := List.Sublist.refl _
  have nd := M.trim_nodup sub
  have pl := M.leftSize
  have ql := M.rightSize
  have norms := M.normalizedSum
  have size : W.length=2*r-1 := by
    dsimp [W,NormalizedPair.vertices,X]
    rw [List.length_append,List.length_append,xlen]
    omega
  have dens := missingColor_floor col t bal W nd
  have wt : W.length-r=r-1 := by omega
  rw [wt] at dens
  obtain ⟨wb,wc,wd⟩ := M.missing_words sub
  exact parallel_boundary_impossible (missingColor_symmetric col symm t W)
    (missingColor_loopless col t W) (M.missing_triangle_free sub)
    W M.left M.right X r hr nd size dens (M.missing_independence_cap sub)
    M.p M.q M.p_left M.q_right (List.Perm.refl _)
    (by omega) (by omega) (by dsimp [X]; omega) wb wc wd

end ParallelMantel.Pentagon

#print axioms ParallelMantel.Pentagon.missingColor_floor
#print axioms ParallelMantel.Pentagon.NormalizedPair.missing_independence_cap
#print axioms ParallelMantel.Pentagon.NormalizedPair.missing_triangle_free
#print axioms ParallelMantel.Pentagon.NormalizedPair.prior_multiplicity_bound
#print axioms ParallelMantel.Pentagon.NormalizedPair.high_parallel_multiplicity_bound
