module

public import Palomar.Erdos617PairStarDouble.Support.PentagonLedger
public import Lean.Elab.Tactic.Omega

@[expose] public section

namespace ParallelMantel.Pentagon

universe u
variable {V : Type u} {g : V → V → Bool}

def anchorWord (g : V → V → Bool) (p q x : V) : Bool × Bool :=
  (g x p, g x q)

private theorem subset_length {S T : List V} (sn : S.Nodup) (tn : T.Nodup)
    (sub : ∀ x∈S, x∈T) : S.length ≤ T.length := by
  classical
  let U := T.filter (fun x => decide (x∈S))
  have un : U.Nodup := List.filter_sublist.nodup tn
  have bymem (x : V) : x∈S ↔ x∈U := by
    constructor
    · intro m
      exact List.mem_filter.mpr ⟨sub x m,decide_eq_true m⟩
    · intro m
      exact of_decide_eq_true (List.mem_filter.mp m).2
  have p := (List.perm_ext_iff_of_nodup sn un).mpr bymem
  exact p.length_eq ▸ List.length_filter_le _ _

private theorem subset_equal_of_length {S T : List V} (sn : S.Nodup) (tn : T.Nodup)
    (sub : ∀ x∈S, x∈T) (same : S.length=T.length) : S.Perm T := by
  classical
  let U := T.filter (fun x => decide (x∈S))
  have un : U.Nodup := List.filter_sublist.nodup tn
  have bymem (x : V) : x∈S ↔ x∈U := by
    constructor
    · intro m
      exact List.mem_filter.mpr ⟨sub x m,decide_eq_true m⟩
    · intro m
      exact of_decide_eq_true (List.mem_filter.mp m).2
  have p := (List.perm_ext_iff_of_nodup sn un).mpr bymem
  have eq : U = T := List.filter_sublist.eq_of_length (p.length_eq.symm.trans same)
  exact eq ▸ p

/-- Transfer of the verified false-twin block to the actual two-support
anchor words of the missing-target graph at boundary h=1. The two private
rows have size at most r−3, and the exceptional class is strictly smaller.
If a twin block lies in a row, it equals it, forcing that row's anchor
to see r−1 vertices in the opposite private row, a contradiction. -/
theorem anchor_words_exclude_twins (symm : Symmetric g)
    (W P Q X : List V) (p q : V) (pP : p∈P) (qQ : q∈Q)
    (nd : W.Nodup) (cover : (P++(Q++X)).Perm W) (r : Nat) (hr : 4≤r)
    (pl : P.length≤r-3) (ql : Q.length≤r-3) (xl : X.length<r-3)
    (pw : ∀ x∈P, anchorWord g p q x=(false,true))
    (qw : ∀ x∈Q, anchorWord g p q x=(true,false))
    (xw : ∀ x∈X, anchorWord g p q x=(false,false))
    (twins : TwinBlock g W (r-3) (r-1)) :
    False := by
  have allND := List.nodup_append.mp (cover.nodup_iff.mpr nd)
  have pnd := allND.1
  have qnd := (List.nodup_append.mp allND.2.1).1
  have xnd := (List.nodup_append.mp allND.2.1).2.1
  have bits (x : V) (xW : x∈W) : x∈P ∨ x∈Q ∨ x∈X := by
    rcases List.mem_append.mp (cover.mem_iff.mpr xW) with yes | rest
    · exact Or.inl yes
    · exact Or.inr (List.mem_append.mp rest)
  have pW : p∈W := cover.mem_iff.mp (List.mem_append_left _ pP)
  have qW : q∈W := cover.mem_iff.mp (List.mem_append_right _ (List.mem_append_left _ qQ))
  have pDegree : degree g p W=Q.length := by
    have e (x : V) : x∈W.filter (g p) ↔ x∈Q := by
      constructor
      · intro xm
        obtain ⟨xW,edge⟩ := List.mem_filter.mp xm
        rw [symm p] at edge
        rcases bits x xW with a | b | c
        · have ne := congrArg Prod.fst (pw x a)
          change g x p=false at ne
          rw [ne] at edge
          contradiction
        · exact b
        · have ne := congrArg Prod.fst (xw x c)
          change g x p=false at ne
          rw [ne] at edge
          contradiction
      · intro xQ
        have h := congrArg Prod.fst (qw x xQ)
        exact List.mem_filter.mpr ⟨cover.mem_iff.mp
          (List.mem_append_right _ (List.mem_append_left _ xQ)), (symm _ _).trans h⟩
    exact ((List.perm_ext_iff_of_nodup (List.filter_sublist.nodup nd) qnd).mpr e).length_eq
  have qDegree : degree g q W=P.length := by
    have e (x : V) : x∈W.filter (g q) ↔ x∈P := by
      constructor
      · intro xm
        obtain ⟨xW,edge⟩ := List.mem_filter.mp xm
        rw [symm q] at edge
        rcases bits x xW with a | b | c
        · exact a
        · have ne := congrArg Prod.snd (qw x b)
          change g x q=false at ne
          rw [ne] at edge
          contradiction
        · have ne := congrArg Prod.snd (xw x c)
          change g x q=false at ne
          rw [ne] at edge
          contradiction
      · intro xP
        have h := congrArg Prod.snd (pw x xP)
        exact List.mem_filter.mpr ⟨cover.mem_iff.mp
          (List.mem_append_left _ xP), (symm _ _).trans h⟩
    exact ((List.perm_ext_iff_of_nodup (List.filter_sublist.nodup nd) pnd).mpr e).length_eq
  obtain ⟨T,tn,sub,tl,td,tw⟩ := twins
  have non : T≠[] := by
    intro no
    simp [no] at tl
    omega
  have sameWord (x : V) (xm : x∈T) (y : V) (ym : y∈T) :
      anchorWord g p q x=anchorWord g p q y := by
    unfold anchorWord
    rw [tw x xm y ym p pW,tw x xm y ym q qW]
  have mem : ∃ t, t∈T := by
    cases T with
    | nil => contradiction
    | cons t T => exact ⟨t,by simp⟩
  obtain ⟨t,tm⟩ := mem
  rcases bits t (sub t tm) with hp | hq | hx
  · have TP : ∀ y∈T, y∈P := by
      intro y ym
      have b := sameWord t tm y ym
      rw [pw t hp] at b
      rcases bits y (sub y ym) with py | qy | xy
      · exact py
      · rw [qw y qy] at b
        contradiction
      · rw [xw y xy] at b
        contradiction
    have card := subset_length tn pnd TP
    have eq : T.length=P.length := by omega
    have pT := (subset_equal_of_length tn pnd TP eq).mem_iff.mpr pP
    have pd := td p pT
    omega
  · have TQ : ∀ y∈T, y∈Q := by
      intro y ym
      have b := sameWord t tm y ym
      rw [qw t hq] at b
      rcases bits y (sub y ym) with py | qy | xy
      · rw [pw y py] at b
        contradiction
      · exact qy
      · rw [xw y xy] at b
        contradiction
    have card := subset_length tn qnd TQ
    have eq : T.length=Q.length := by omega
    have qT := (subset_equal_of_length tn qnd TQ eq).mem_iff.mpr qQ
    have qd := td q qT
    omega
  · have TX : ∀ y∈T, y∈X := by
      intro y ym
      have b := sameWord t tm y ym
      rw [xw t hx] at b
      rcases bits y (sub y ym) with py | qy | xy
      · rw [pw y py] at b
        contradiction
      · rw [qw y qy] at b
        contradiction
      · exact xy
    have card := subset_length tn xnd TX
    omega

theorem shortest_parallel_boundary_impossible {n : Nat} (C : TraceCycle g n)
    (symm : Symmetric g) (loop : Loopless g) (tri : TriangleFree g)
    (W O P Q X : List V) (r : Nat) (hr : 12≤r)
    (part : (C.vertices++O).Perm W) (nd : W.Nodup) (size : W.length=2*r-1)
    (dense : (r-1)*(r-1)≤edges g W) (short : C.ShortestOdd W)
    (cap : ∀ I : List V, I.Nodup → (∀ x∈I, x∈W) →
      (∀ x∈I, ∀ y∈I, g x y=false) → I.length≤r-1)
    (p q : V) (pP : p∈P) (qQ : q∈Q) (cover : (P++(Q++X)).Perm W)
    (pl : P.length≤r-3) (ql : Q.length≤r-3) (xl : X.length<r-3)
    (pw : ∀ x∈P, anchorWord g p q x=(false,true))
    (qw : ∀ x∈Q, anchorWord g p q x=(true,false))
    (xw : ∀ x∈X, anchorWord g p q x=(false,false)) :
    False := by
  exact anchor_words_exclude_twins symm W P Q X p q pP qQ nd cover r (by omega)
    pl ql xl pw qw xw (shortest_cycle_false_twins C symm loop tri W O r hr part nd size dense short cap)

end ParallelMantel.Pentagon

#print axioms ParallelMantel.Pentagon.anchor_words_exclude_twins
#print axioms ParallelMantel.Pentagon.shortest_parallel_boundary_impossible
