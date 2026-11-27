module

public import Palomar.Erdos617PairStarDouble.Support.ShortestOdd
public import Lean.Elab.Tactic.Omega

@[expose] public section

namespace ParallelMantel.Pentagon
set_option maxRecDepth 20000
set_option maxHeartbeats 500000

abbrev Type5 := Fin 5

/-- The two neighbors of a vertex in the canonical five-cycle. -/
def near (a b : Type5) : Bool :=
  decide (((a.val + 1) % 5 = b.val) ∨ ((b.val + 1) % 5 = a.val))

theorem near_symm : ∀ a b : Type5, near a b = near b a := by decide

theorem near_irrefl : ∀ a : Type5, near a a = false := by decide

theorem disjoint_iff_near : ∀ a b : Type5,
    (∀ t : Type5, near a t = true → near b t = false) ↔ near a b = true := by decide

theorem two_types_at_most_one_common : ∀ a b x y : Type5,
    a ≠ b → near a x = true → near b x = true →
    near a y = true → near b y = true → x = y := by decide

/-- Type-level description when the single missing cross edge has
incompatible endpoint types. The hypotheses name the two exceptional
types u,v, an ordinary type a opposite v, and an ordinary type b opposite u. -/
theorem exceptional_type_signature : ∀ u v a b : Type5,
    near u v = false → near a v = true → near u b = true → near a b = true →
    near a u = false ∧ near b v = false ∧
      (∀ x : Type5, near x v = true → near x b = true → x = a) ∧
      (∀ y : Type5, near u y = true → near a y = true → y = b) := by decide

/-- Adjacent types have the advertised two common non-neighbor cycle vertices
on the larger side in the imbalanced split. -/
theorem near_type_avoid_own_adjacent_types : ∀ u a b : Type5,
    near u a = true → near u b = true → near a b = false := by decide

/-- The pair of cyclic neighbors itself is a nonadjacent distinct pair. -/
def next (a : Type5) : Type5 := ⟨(a.val+1)%5, Nat.mod_lt _ (by decide)⟩
def prev (a : Type5) : Type5 := ⟨(a.val+4)%5, Nat.mod_lt _ (by decide)⟩

theorem near_pair : ∀ a : Type5,
    near a (next a) = true ∧ near a (prev a) = true ∧ next a ≠ prev a := by decide

def hits (f : Type5 → Bool) : Nat :=
  (if f 0 then 1 else 0) + (if f 1 then 1 else 0) + (if f 2 then 1 else 0) +
    (if f 3 then 1 else 0) + (if f 4 then 1 else 0)

private def idx (a b c d e : Bool) (j : Type5) : Bool :=
  if j = 0 then a else if j = 1 then b else if j = 2 then c else if j = 3 then d else e

private theorem two_hit_support_kernel : ∀ a b c d e : Bool,
    hits (idx a b c d e) = 2 →
    (∀ u v : Type5, near u v = true → idx a b c d e u = true →
      idx a b c d e v = false) →
    ∃ t : Type5, ∀ j : Type5, idx a b c d e j = near t j := by decide

private theorem idx_last : ∀ j : Type5, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 3 → j = 4 := by decide

theorem two_hit_support (f : Type5 → Bool) (num : hits f = 2)
    (ind : ∀ u v : Type5, near u v = true → f u = true → f v = false) :
    ∃ t : Type5, ∀ j : Type5, f j = near t j := by
  have repr : f = idx (f 0) (f 1) (f 2) (f 3) (f 4) := by
    funext j
    by_cases a : j=0
    · simp [a,idx]
    by_cases b : j=1
    · subst j
      rfl
    by_cases c : j=2
    · subst j
      rfl
    by_cases d : j=3
    · subst j
      rfl
    · have e := idx_last j a b c d
      subst j
      rfl
  rw [repr] at num ind ⊢
  exact two_hit_support_kernel _ _ _ _ _ num ind

universe u
variable {V : Type u}

/-- A nonempty pair of full sides whose every cross pair is present has
at least one side with a unique pentagon type. -/
theorem uniform_side (type : V → Type5) (A B : List V)
    (anon : A ≠ []) (bnon : B ≠ [])
    (cross : ∀ a ∈ A, ∀ b ∈ B, near (type a) (type b) = true) :
    (∃ t : Type5, ∀ a ∈ A, type a = t) ∨
    (∃ t : Type5, ∀ b ∈ B, type b = t) := by
  cases A with
  | nil => contradiction
  | cons a A =>
    cases B with
    | nil => contradiction
    | cons b B =>
      by_cases uni : ∀ x ∈ a::A, type x = type a
      · exact Or.inl ⟨_,uni⟩
      · have witness : ∃ a' ∈ a::A, type a ≠ type a' := by
          apply Classical.byContradiction
          intro no
          exact uni (by
            intro a' ha'
            by_cases e : type a = type a'
            · exact e.symm
            · exact False.elim (no ⟨a',ha',e⟩))
        obtain ⟨a',ma',different⟩ := witness
        right
        refine ⟨type b,?_⟩
        intro b' mb'
        exact two_types_at_most_one_common _ _ _ _ different
          (cross a (by simp) b' mb') (cross a' ma' b' mb')
          (cross a (by simp) b (by simp)) (cross a' ma' b (by simp))

variable {g : V → V → Bool}

/-- Exact two-hit label of an outside graph vertex. -/
def Full (c : Type5 → V) (x : V) (t : Type5) : Prop :=
  ∀ j : Type5, g x (c j) = near t j

structure Frame (g : V → V → Bool) (W A B : List V) (c : Type5 → V) : Prop where
  nodup : W.Nodup
  partition : (List.ofFn c ++ (A ++ B)).Perm W
  cycle : ∀ i j, g (c i) (c j) = near i j
  leftInd : ∀ x∈A, ∀ y∈A, g x y = false
  rightInd : ∀ x∈B, ∀ y∈B, g x y = false

def TwinBlock (g : V → V → Bool) (W : List V) (lower deg : Nat) : Prop :=
  ∃ T : List V, T.Nodup ∧ (∀ x∈T, x∈W) ∧ lower ≤ T.length ∧
    (∀ x∈T, degree g x W = deg) ∧
    (∀ x∈T, ∀ y∈T, ∀ z∈W, g x z = g y z)

theorem cross_type {c : Type5 → V} (triangle : TriangleFree g)
    {x y : V} {a b : Type5} (xa : Full (g:=g) c x a) (yb : Full (g:=g) c y b)
    (edge : g x y = true) : near a b = true := by
  apply (disjoint_iff_near a b).mp
  intro j h
  have hx : g x (c j)=true := (xa j).trans h
  have no := triangle x y (c j) edge hx
  rw [yb j] at no
  exact no

theorem cycle_to_full {c : Type5 → V} (symm : Symmetric g)
    {x : V} {t : Type5} (full : Full (g:=g) c x t) (j : Type5) :
    g (c j) x = near j t := by
  rw [symm (c j),full j,near_symm t j]

theorem Frame.swap {W A B : List V} {c : Type5 → V}
    (h : Frame g W A B c) : Frame g W B A c where
  nodup := h.nodup
  partition := (List.perm_append_comm (l₁ := B) (l₂ := A)).append_left _ |>.trans h.partition
  cycle := h.cycle
  leftInd := h.rightInd
  rightInd := h.leftInd

private theorem Frame.reduceNodup {W A B : List V} {c : Type5 → V}
    (h : Frame g W A B c) : (List.ofFn c).Nodup ∧ A.Nodup :=
  let hn := List.nodup_append.mp (h.partition.nodup_iff.mpr h.nodup)
  ⟨hn.1,(List.nodup_append.mp hn.2.1).1⟩

private theorem Frame.cycle_outside {W A B : List V} {c : Type5 → V}
    (h : Frame g W A B c) (t : Type5) : c t ∉ A := by
  intro a
  have d := (List.nodup_append.mp (h.partition.nodup_iff.mpr h.nodup)).2.2
  exact d (c t) (List.mem_ofFn.mpr ⟨t,rfl⟩) (c t) (List.mem_append_left _ a) rfl

private theorem any_label_mem {W A B : List V} {c : Type5 → V} (h : Frame g W A B c)
    (t : Type5) : c t ∈ W :=
  h.partition.mem_iff.mp (List.mem_append_left _ (List.mem_ofFn.mpr ⟨t,rfl⟩))

private theorem left_mem {W A B : List V} {c : Type5 → V} (h : Frame g W A B c)
    {x : V} (a : x∈A) : x∈W :=
  h.partition.mem_iff.mp (List.mem_append_right _ (List.mem_append_left _ a))

private theorem Frame.cycle_mem_cases {W A B : List V} {c : Type5 → V} (h : Frame g W A B c)
    {z : V} (hz : z∈W) : z∈A ∨ z∈B ∨ ∃ i, c i=z := by
  obtain cy | out := List.mem_append.mp (h.partition.mem_iff.mpr hz)
  · exact Or.inr (Or.inr (List.mem_ofFn.mp cy))
  · obtain a | b := List.mem_append.mp out
    · exact Or.inl a
    · exact Or.inr (Or.inl b)

private theorem degree_left_uniform_cases {W A B : List V} {c : Type5 → V}
    (h : Frame g W A B c) (t : Type5) (x : V)
    (toA : ∀ a∈A, g x a = false) (toB : ∀ b∈B, g x b = true)
    (toC : ∀ i, g x (c i) = near t i) :
    degree g x W = B.length+2 := by
  have lfilter : A.filter (g x)=[] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro a ha
    obtain ⟨am,ae⟩ := List.mem_filter.mp ha
    rw [toA a am] at ae
    contradiction
  have rfilter : B.filter (g x)=B := List.filter_eq_self.mpr toB
  have cf : ((List.ofFn c).filter (g x)).Perm [c (next t), c (prev t)] := by
    have nd : ((List.ofFn c).filter (g x)).Nodup := List.filter_sublist.nodup h.reduceNodup.1
    have np := (near_pair t).2.2
    have ninj : ∀ a b : Type5, c a = c b → a=b := by
      intro a b ab
      have get (j : Type5) : (List.ofFn c)[j.val]'(by simp) = c j := by
        rw [List.getElem_ofFn]
      have eq := (get a).trans (ab.trans (get b).symm)
      exact Fin.eq_of_val_eq ((List.Nodup.getElem_inj h.reduceNodup.1).mp eq)
    have nt : ([c (next t),c (prev t)] : List V).Nodup := by
      simp [show c (next t) ≠ c (prev t) from fun e => np (ninj _ _ e)]
    apply (List.perm_ext_iff_of_nodup nd nt).mpr
    intro z
    constructor
    · intro zm
      obtain ⟨zcycle,edge⟩ := List.mem_filter.mp zm
      obtain ⟨j,eq⟩ := List.mem_ofFn.mp zcycle
      rw [← eq, toC j] at edge
      have f : j = next t ∨ j = prev t := by
        have closed : ∀ a b : Type5, near a b=true → b=next a ∨ b=prev a := by decide
        exact closed t j edge
      rcases f with fj | fj <;> simp [← eq,fj]
    · intro hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with e | e
      · exact List.mem_filter.mpr ⟨List.mem_ofFn.mpr ⟨next t,e.symm⟩,
          by rw [e,toC]; exact (near_pair t).1⟩
      · exact List.mem_filter.mpr ⟨List.mem_ofFn.mpr ⟨prev t,e.symm⟩,
          by rw [e,toC]; exact (near_pair t).2.1⟩
  have d := (h.partition.filter (g x)).length_eq
  simp only [List.filter_append, List.length_append, lfilter, rfilter, cf.length_eq,
    List.length_cons, List.length_nil, Nat.zero_add] at d
  unfold degree
  omega

/-- Any uniform ordinary left sublist with full crossings already gives
a false-twin block. No control on the special vertices' types is needed. -/
theorem left_uniform_block {W A B U : List V} {c : Type5 → V}
    (h : Frame g W A B c) (t : Type5) (sub : U.Sublist A)
    (uniform : ∀ x∈U, Full (g:=g) c x t)
    (cross : ∀ x∈U, ∀ y∈B, g x y=true) :
    TwinBlock g W U.length (B.length+2) := by
  refine ⟨U,sub.nodup h.reduceNodup.2,(fun x m => left_mem h (sub.subset m)),Nat.le_refl _,?_,?_⟩
  · intro x xm
    exact degree_left_uniform_cases h t x (h.leftInd x (sub.subset xm))
      (cross x xm) (uniform x xm)
  · intro x xm y ym z zm
    rcases h.cycle_mem_cases zm with a | b | ⟨j,e⟩
    · rw [h.leftInd x (sub.subset xm) z a,h.leftInd y (sub.subset ym) z a]
    · rw [cross x xm z b,cross y ym z b]
    · rw [← e,uniform x xm j,uniform y ym j]

/-- Add the cycle vertex of the uniform type, when it has the matching
cross and internal-side adjacency words. -/
theorem left_uniform_add_cycle {W A B U : List V} {c : Type5 → V}
    (h : Frame g W A B c) (t : Type5) (sub : U.Sublist A)
    (uniform : ∀ x∈U, Full (g:=g) c x t)
    (cross : ∀ x∈U, ∀ y∈B, g x y=true)
    (cycleA : ∀ x∈A, g (c t) x = false) (cycleB : ∀ y∈B, g (c t) y = true) :
    TwinBlock g W (U.length+1) (B.length+2) := by
  have dn : (c t::U).Nodup :=
    List.nodup_cons.mpr ⟨fun m => h.cycle_outside t (sub.subset m),sub.nodup h.reduceNodup.2⟩
  have toA (x : V) (mem : x∈c t::U) : ∀ a∈A, g x a = false := by
    rcases List.mem_cons.mp mem with eq | xm
    · exact eq.symm ▸ cycleA
    · exact h.leftInd x (sub.subset xm)
  have toB (x : V) (mem : x∈c t::U) : ∀ b∈B, g x b = true := by
    rcases List.mem_cons.mp mem with eq | xm
    · exact eq.symm ▸ cycleB
    · exact cross x xm
  have toC (x : V) (mem : x∈c t::U) : ∀ j, g x (c j) = near t j := by
    rcases List.mem_cons.mp mem with eq | xm
    · exact eq.symm ▸ h.cycle t
    · exact uniform x xm
  refine ⟨c t::U,dn,?_,by simp,?_,?_⟩
  · intro x m
    rcases List.mem_cons.mp m with eq | xm
    · exact eq.symm ▸ any_label_mem h t
    · exact left_mem h (sub.subset xm)
  · intro x m
    exact degree_left_uniform_cases h t x (toA x m) (toB x m) (toC x m)
  · intro x xm y ym z zm
    rcases h.cycle_mem_cases zm with a | b | ⟨j,e⟩
    · rw [toA x xm z a,toA y ym z a]
    · rw [toB x xm z b,toB y ym z b]
    · rw [← e,toC x xm j,toC y ym j]

private theorem TwinBlock.weaken {W : List V} {n k d : Nat}
    (h : TwinBlock g W n d) (le : k≤n) : TwinBlock g W k d := by
  obtain ⟨T,nd,sub,len,deg,tw⟩ := h
  exact ⟨T,nd,sub,Nat.le_trans le len,deg,tw⟩

private theorem nonempty_of_positive {A : List V} (h : 0<A.length) : A ≠ [] := by
  intro empty
  simp [empty] at h

private theorem pick_mem {A : List V} (h : A ≠ []) : ∃ x, x∈A := by
  cases A with
  | nil => contradiction
  | cons x X => exact ⟨x,by simp⟩

private theorem uniform_adjacency {W A B : List V} {c : Type5 → V}
    (h : Frame g W A B c) (symm : Symmetric g) (triangle : TriangleFree g)
    (type : V → Type5) (fullA : ∀ x∈A, Full (g:=g) c x (type x))
    (fullB : ∀ x∈B, Full (g:=g) c x (type x))
    (cross : ∀ x∈A, ∀ y∈B, g x y = true) (t : Type5)
    (uniform : ∀ a∈A, type a=t) (non : A≠[]) :
    TwinBlock g W (A.length+1) (B.length+2) := by
  obtain ⟨a,am⟩ := pick_mem non
  apply left_uniform_add_cycle h t (List.Sublist.refl A)
  · intro x xm j
    rw [fullA x xm j,uniform x xm]
  · exact cross
  · intro x xm
    rw [cycle_to_full symm (fullA x xm) t,uniform x xm]
    exact near_irrefl t
  · intro x xm
    rw [cycle_to_full symm (fullB x xm) t]
    have ab := cross_type triangle (fullA a am) (fullB x xm) (cross a am x xm)
    rwa [uniform a am] at ab

/-- No defects: a balanced pair of full sides gives at least R+1 twins. -/
theorem no_defect_twins {W A B : List V} {c : Type5 → V}
    (h : Frame g W A B c) (symm : Symmetric g) (triangle : TriangleFree g)
    (type : V → Type5) (fullA : ∀ x∈A, Full (g:=g) c x (type x))
    (fullB : ∀ x∈B, Full (g:=g) c x (type x))
    (cross : ∀ x∈A, ∀ y∈B, g x y = true)
    (R : Nat) (rp : 0<R) (al : A.length=R) (bl : B.length=R) :
    TwinBlock g W (R+1) (R+2) := by
  have ap := nonempty_of_positive (al ▸ rp)
  have bp := nonempty_of_positive (bl ▸ rp)
  have uc := uniform_side type A B ap bp (fun a am b bm =>
    cross_type triangle (fullA a am) (fullB b bm) (cross a am b bm))
  rcases uc with ⟨t,tu⟩ | ⟨t,tu⟩
  · have tw := uniform_adjacency h symm triangle type fullA fullB cross t tu ap
    simpa [al,bl] using tw
  · have rev (b : V) (bm : b∈B) (a : V) (am : a∈A) : g b a=true :=
      (symm _ _).trans (cross a am b bm)
    have tw := uniform_adjacency h.swap symm triangle type fullB fullA rev t tu bp
    simpa [al,bl] using tw

/-- One weak vertex w on the left. All other vertices are full and all
crossings are present. The proof does not need w's particular cycle bit. -/
theorem weak_vertex_twins {W A B : List V} {c : Type5 → V} {w : V}
    (h : Frame g W (w::A) B c) (symm : Symmetric g) (triangle : TriangleFree g)
    (type : V → Type5) (fullA : ∀ x∈A, Full (g:=g) c x (type x))
    (fullB : ∀ x∈B, Full (g:=g) c x (type x))
    (cross : ∀ x∈w::A, ∀ y∈B, g x y = true)
    (R : Nat) (rp : 2≤R) (al : A.length+1=R) (bl : B.length=R) :
    TwinBlock g W R (R+2) := by
  have apos : 0<A.length := by omega
  have bpos : 0<B.length := by omega
  have ap := nonempty_of_positive apos
  have bp := nonempty_of_positive bpos
  obtain uni | uni := uniform_side type A B ap bp (fun a am b bm =>
    cross_type triangle (fullA a am) (fullB b bm) (cross a (List.mem_cons_of_mem _ am) b bm))
  · obtain ⟨t,tu⟩ := uni
    obtain ⟨a,am⟩ := pick_mem ap
    obtain ⟨b,bm⟩ := pick_mem bp
    have adjB (y : V) (ym : y∈B) : g (c t) y=true := by
      rw [cycle_to_full symm (fullB y ym) t]
      have word := cross_type triangle (fullA a am) (fullB y ym)
        (cross a (List.mem_cons_of_mem _ am) y ym)
      rwa [tu a am] at word
    have adjA (x : V) (xm : x∈w::A) : g (c t) x = false := by
      rcases List.mem_cons.mp xm with eq | mm
      · rw [eq]
        have ww := cross w (by simp) b bm
        exact triangle b (c t) w ((symm _ _).trans (adjB b bm)) ((symm _ _).trans ww)
      · rw [cycle_to_full symm (fullA x mm) t,tu x mm]
        exact near_irrefl t
    have tw := left_uniform_add_cycle h t (List.Sublist.cons _ (List.Sublist.refl A))
      (fun x xm j => (fullA x xm j).trans (congrArg (fun z => near z j) (tu x xm)))
      (fun x xm => cross x (List.mem_cons_of_mem _ xm)) adjA adjB
    simpa [al,bl] using tw
  · obtain ⟨t,tu⟩ := uni
    have tw := left_uniform_block h.swap t (List.Sublist.refl B)
      (fun x xm j => (fullB x xm j).trans (congrArg (fun z => near z j) (tu x xm)))
      (fun x xm y ym => (symm _ _).trans (cross y ym x xm))
    simpa [al,bl] using tw

private theorem missing_left_lift {W A B : List V} {c : Type5 → V} {u v : V}
    (h : Frame g W (u::A) (v::B) c) (symm : Symmetric g)
    (type : V → Type5) (fa : ∀ x∈u::A, Full (g:=g) c x (type x))
    (fb : ∀ x∈v::B, Full (g:=g) c x (type x))
    (crossA : ∀ a∈A, ∀ b∈v::B, g a b=true)
    (t : Type5) (reg : ∀ a∈A, type a=t)
    (special : near t (type u)=false) (opp : ∀ b∈v::B, near t (type b)=true) :
    TwinBlock g W (A.length+1) ((v::B).length+2) := by
  refine left_uniform_add_cycle h t (List.Sublist.cons _ (List.Sublist.refl A))
    (fun x xm j => (fa x (List.mem_cons_of_mem _ xm) j).trans
      (congrArg (fun z => near z j) (reg x xm))) crossA ?_ ?_
  · intro x xm
    rw [cycle_to_full symm (fa x xm) t]
    rcases List.mem_cons.mp xm with e | p
    · simpa [e] using special
    · rw [reg x p]
      exact near_irrefl t
  · intro y ym
    rw [cycle_to_full symm (fb y ym) t]
    exact opp y ym

/-- One missing crossing at u,v, all vertices full. The two structural
possibilities for their types both give at least R graph-level twins. -/
theorem missing_cross_twins {W A B : List V} {c : Type5 → V} {u v : V}
    (h : Frame g W (u::A) (v::B) c) (symm : Symmetric g) (triangle : TriangleFree g)
    (type : V → Type5) (fa : ∀ x∈u::A, Full (g:=g) c x (type x))
    (fb : ∀ x∈v::B, Full (g:=g) c x (type x))
    (crossA : ∀ a∈A, ∀ b∈v::B, g a b=true)
    (crossB : ∀ a∈u::A, ∀ b∈B, g a b=true)
    (R : Nat) (rp : 2≤R) (al : A.length+1=R) (bl : B.length+1=R) :
    TwinBlock g W R (R+2) := by
  have atop : A≠[] := nonempty_of_positive (by omega)
  have btop : B≠[] := nonempty_of_positive (by omega)
  have atype (a : V) (am : a∈A) (b : V) (bm : b∈v::B) : near (type a) (type b)=true :=
    cross_type triangle (fa a (List.mem_cons_of_mem _ am)) (fb b bm) (crossA a am b bm)
  have btype (a : V) (am : a∈u::A) (b : V) (bm : b∈B) : near (type a) (type b)=true :=
    cross_type triangle (fa a am) (fb b (List.mem_cons_of_mem _ bm)) (crossB a am b bm)
  by_cases yes : near (type u) (type v)=true
  · have whole (a : V) (am : a∈u::A) (b : V) (bm : b∈v::B) : near (type a) (type b)=true := by
      rcases List.mem_cons.mp am with ae | ap
      · rcases List.mem_cons.mp bm with be | bp
        · simpa [ae,be] using yes
        · exact btype a am b bp
      · exact atype a ap b bm
    rcases uniform_side type (u::A) (v::B) (by simp) (by simp) whole with ⟨t,uni⟩ | ⟨t,uni⟩
    · have self := uni u (by simp)
      have tw := missing_left_lift h symm type fa fb crossA t
        (fun x xm => uni x (List.mem_cons_of_mem _ xm)) (self ▸ near_irrefl (type u))
        (fun y ym => self ▸ whole u (by simp) y ym)
      simpa [List.length_cons,al,bl] using tw
    · have self := uni v (by simp)
      have rev (b : V) (bm : b∈B) (a : V) (am : a∈u::A) : g b a=true :=
        (symm _ _).trans (crossB a am b bm)
      have tw := missing_left_lift h.swap symm type fb fa rev t
        (fun x xm => uni x (List.mem_cons_of_mem _ xm)) (self ▸ near_irrefl (type v))
        (fun y ym => self ▸ (near_symm _ _).trans (whole y ym v (by simp)))
      simpa [List.length_cons,al,bl] using tw
  · have no : near (type u) (type v)=false := by
      cases e : near (type u) (type v) <;> simp_all
    obtain ⟨a,am⟩ := pick_mem atop
    obtain ⟨b,bm⟩ := pick_mem btop
    have sign := exceptional_type_signature _ _ _ _ no (atype a am v (by simp))
      (btype u (by simp) b bm) (atype a am b (List.mem_cons_of_mem _ bm))
    have uni (x : V) (xm : x∈A) : type x = type a :=
      sign.2.2.1 _ (atype x xm v (by simp)) (atype x xm b (List.mem_cons_of_mem _ bm))
    have tw := missing_left_lift h symm type fa fb crossA (type a) uni sign.1
      (fun y ym => atype a am y ym)
    simpa [List.length_cons,al,bl] using tw

private theorem near_increasing : ∀ i j : Type5, i.val<j.val →
    (near i j=true ↔ j.val=i.val+1 ∨ (i.val=0 ∧ j.val+1=5)) := by decide

private theorem shortest_trace_pattern {W : List V} (C : TraceCycle g 5)
    (symm : Symmetric g) (loop : Loopless g) (short : C.ShortestOdd W) (i j : Type5) :
    g (C.trace i) (C.trace j) = near i j := by
  have smaller (a b : Type5) (ord : a.val<b.val) :
      g (C.at a.val) (C.at b.val) = near a b := by
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro e
      exact (near_increasing a b ord).mpr (C.shortest_edge_consecutive symm short ord b.isLt e)
    · intro e
      obtain adjacent | ⟨first,last⟩ := (near_increasing a b ord).mp e
      · rw [adjacent]
        exact C.at_next _
      · rw [first]
        have close := C.at_next b.val
        rw [last] at close
        have ep : C.at 5 = C.at 0 := C.at_period 0
        rw [ep] at close
        exact (symm _ _).trans close
  rw [← C.at_eq_trace i.isLt, ← C.at_eq_trace j.isLt]
  by_cases ij : i.val<j.val
  · exact smaller i j ij
  · by_cases ji : j.val<i.val
    · rw [symm (C.at i.val),near_symm i j]
      exact smaller j i ji
    · have e : i=j := Fin.eq_of_val_eq (by omega)
      subst j
      rw [loop,near_irrefl]

/-- Convert the verified shortest cycle representation to the exact
labelled finite pentagon used by the three false-twin cases. -/
theorem frame_of_shortest {W A B : List V} (C : TraceCycle g 5)
    (symm : Symmetric g) (loop : Loopless g) (short : C.ShortestOdd W)
    (nd : W.Nodup) (part : (C.vertices ++ (A++B)).Perm W)
    (Aind : ∀ x∈A, ∀ y∈A, g x y=false) (Bind : ∀ x∈B, ∀ y∈B, g x y=false) :
    Frame g W A B C.trace :=
  ⟨nd,part,shortest_trace_pattern C symm loop short,Aind,Bind⟩

private theorem ofFn_five (c : Type5 → V) : List.ofFn c = [c 0,c 1,c 2,c 3,c 4] := by
  simp only [List.ofFn_succ,List.ofFn_zero]
  rfl

theorem full_of_degree_two {W A B : List V} {c : Type5 → V}
    (h : Frame g W A B c) (symm : Symmetric g) (triangle : TriangleFree g) {x : V}
    (d : degree g x (List.ofFn c)=2) : ∃ t : Type5, Full (g:=g) c x t := by
  have num : hits (fun j => g x (c j))=2 := by
    unfold degree at d
    rw [ofFn_five] at d
    unfold hits
    cases ha : g x (c 0) <;> cases hb : g x (c 1) <;> cases hc : g x (c 2) <;>
      cases hd : g x (c 3) <;> cases he : g x (c 4) <;>
      simp_all
  exact two_hit_support _ num (fun u v nearUV xu => triangle (c u) x (c v)
    ((symm _ _).trans xu) ((h.cycle u v).trans nearUV))

/-- If all crossings are present and all outside vertices are full, the
larger side can be extended by two cycle vertices. This excludes the
unbalanced outside case under the global independence cap R+2. -/
theorem imbalanced_obstruction {W A B : List V} {c : Type5 → V}
    (h : Frame g W A B c) (symm : Symmetric g) (triangle : TriangleFree g)
    (type : V → Type5) (fullA : ∀ a∈A, Full (g:=g) c a (type a))
    (fullB : ∀ b∈B, Full (g:=g) c b (type b))
    (cross : ∀ a∈A, ∀ b∈B, g a b=true) (ap : A≠[]) :
    ∃ I : List V, I.Nodup ∧ (∀ x∈I, x∈W) ∧ I.length=B.length+2 ∧
      (∀ x∈I, ∀ y∈I, g x y=false) := by
  obtain ⟨a,am⟩ := pick_mem ap
  let t := type a
  let u := next t
  let v := prev t
  have tu : near t u=true := (near_pair t).1
  have tv : near t v=true := (near_pair t).2.1
  have uv : near u v=false := near_type_avoid_own_adjacent_types t u v tu tv
  have ne := (near_pair t).2.2
  have cuv : c u ≠ c v := by
    intro e
    have nth (j : Type5) : (List.ofFn c)[j.val]'(by simp) = c j := by
      rw [List.getElem_ofFn]
    have eq := (nth u).trans (e.trans (nth v).symm)
    exact ne (Fin.eq_of_val_eq ((List.Nodup.getElem_inj h.reduceNodup.1).mp eq))
  have nd : (c u :: c v :: B).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,List.nodup_cons.mpr ⟨h.swap.cycle_outside v,h.swap.reduceNodup.2⟩⟩
    intro m
    rcases List.mem_cons.mp m with eq | mm
    · exact cuv eq
    · exact h.swap.cycle_outside u mm
  have noB (b : V) (bm : b∈B) (s : Type5) (ns : near t s=true) : g b (c s)=false := by
    have ab := cross_type triangle (fullA a am) (fullB b bm) (cross a am b bm)
    have eq := fullB b bm s
    rw [eq]
    exact near_type_avoid_own_adjacent_types t (type b) s ab ns
  refine ⟨c u :: c v :: B,nd,?_,by simp,?_⟩
  · intro x xm
    simp only [List.mem_cons] at xm
    rcases xm with eq | eq | bm
    · exact eq.symm ▸ any_label_mem h u
    · exact eq.symm ▸ any_label_mem h v
    · exact left_mem h.swap bm
  · intro x xm y ym
    simp only [List.mem_cons] at xm ym
    rcases xm with e | e | xb <;> rcases ym with f | f | yb
    · rw [e,f,h.cycle,near_irrefl]
    · rw [e,f,h.cycle,uv]
    · rw [e,symm (c u)]
      exact noB y yb u tu
    · rw [e,f,h.cycle,near_symm v u,uv]
    · rw [e,f,h.cycle,near_irrefl]
    · rw [e,symm (c v)]
      exact noB y yb v tv
    · rw [f]
      exact noB x xb u tu
    · rw [f]
      exact noB x xb v tv
    · exact h.rightInd x xb y yb

end ParallelMantel.Pentagon

#print axioms ParallelMantel.Pentagon.two_hit_support
#print axioms ParallelMantel.Pentagon.exceptional_type_signature
#print axioms ParallelMantel.Pentagon.uniform_side
#print axioms ParallelMantel.Pentagon.left_uniform_add_cycle
#print axioms ParallelMantel.Pentagon.no_defect_twins
#print axioms ParallelMantel.Pentagon.weak_vertex_twins
#print axioms ParallelMantel.Pentagon.missing_cross_twins
#print axioms ParallelMantel.Pentagon.frame_of_shortest
#print axioms ParallelMantel.Pentagon.full_of_degree_two
#print axioms ParallelMantel.Pentagon.imbalanced_obstruction
