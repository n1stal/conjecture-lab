module

public import Palomar.Erdos617PairBound.Support.AnchorTransfer
public import Palomar.Erdos617PairBound.Support.OddExistence
public import Lean.Elab.Tactic.Omega

@[expose] public section

namespace ParallelMantel.Pentagon

universe u
variable {V : Type u} {g : V → V → Bool}

/-- End-to-end h=1 exclusion for a graph on the actual pair rows and
exceptions. No supplied cycle or defect classification. The color-to-graph
inputs are the complement's edge floor and independence cap, and its
triangle-freeness. The row sizes and three anchor words are explicit. -/
theorem parallel_boundary_impossible (symm : Symmetric g) (loop : Loopless g)
    (tri : TriangleFree g) (W P Q X : List V) (r : Nat) (hr : 12≤r)
    (nd : W.Nodup) (size : W.length=2*r-1)
    (dense : (r-1)*(r-1)≤edges g W)
    (cap : ∀ I : List V, I.Nodup → (∀ x∈I, x∈W) →
      (∀ x∈I, ∀ y∈I, g x y=false) → I.length≤r-1)
    (p q : V) (pP : p∈P) (qQ : q∈Q) (cover : (P++(Q++X)).Perm W)
    (pl : P.length≤r-3) (ql : Q.length≤r-3) (xl : X.length<r-3)
    (pw : ∀ x∈P, anchorWord g p q x=(false,true))
    (qw : ∀ x∈Q, anchorWord g p q x=(true,false))
    (xw : ∀ x∈X, anchorWord g p q x=(false,false)) :
    False := by
  classical
  obtain ⟨n,C,short⟩ := shortest_odd_of_tight_independence symm loop W r (by omega) nd size cap
  let marked (v : V) : Bool := decide (v∈C.vertices)
  let O := W.filter (fun v => !marked v)
  have cyclefilter : (W.filter marked).Perm C.vertices := by
    have fn : (W.filter marked).Nodup := List.filter_sublist.nodup nd
    apply (List.perm_ext_iff_of_nodup fn C.vertices_nodup).mpr
    intro v
    constructor
    · intro vmem
      exact of_decide_eq_true (List.mem_filter.mp vmem).2
    · intro vm
      exact List.mem_filter.mpr ⟨short.2.1 v vm,decide_eq_true vm⟩
  have part : (C.vertices++O).Perm W :=
    (cyclefilter.symm.append_right O).trans (List.filter_append_perm marked W)
  exact shortest_parallel_boundary_impossible C symm loop tri W O P Q X r hr part
    nd size dense short cap p q pP qQ cover pl ql xl pw qw xw

end ParallelMantel.Pentagon

#print axioms ParallelMantel.Pentagon.parallel_boundary_impossible
