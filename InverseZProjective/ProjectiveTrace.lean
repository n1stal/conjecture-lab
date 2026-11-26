module
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import InverseZProofs.Algebra
@[expose] public section
set_option autoImplicit false
namespace InverseZProjective.ProjectiveTrace
open Module Submodule
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
def LinePreserving (S : Set V) : Prop :=
  ∀ U : Submodule K V, finrank K U = 2 →
    ∃ x ∈ S, ∃ y ∈ S, x ∈ U ∧ y ∈ U ∧ x ≠ 0 ∧ y ∉ span K ({x} : Set V)
private theorem span_pair_finrank (x y : V) (hx : x ≠ 0)
    (hy : y ∉ span K ({x} : Set V)) :
    finrank K (span K ({x,y} : Set V)) = 2 := by
  classical
  have hl : span K ({x} : Set V) < span K ({x,y} : Set V) := by
    apply lt_of_le_of_ne (span_mono (by simp))
    intro he
    exact hy (he ▸ (subset_span (Set.mem_insert_of_mem x (Set.mem_singleton y)) :
      y ∈ span K ({x,y} : Set V)))
  have hlt := Submodule.finrank_lt_finrank_of_lt hl
  rw [finrank_span_singleton hx] at hlt
  have hle := finrank_span_le_card (R:=K) ({x,y} : Set V)
  have hne : x ≠ y := fun h => hy (h ▸ mem_span_singleton_self x)
  have hc : ({x,y} : Set V).toFinset.card = 2 := by
    rw [← Set.ncard_eq_toFinset_card']
    exact Set.ncard_pair hne
  omega
theorem span_trace_eq_of_linePreserving (S : Set V) (hS : LinePreserving (K:=K) S)
    (P : Submodule K V) (hP : 2 ≤ finrank K P) :
    span K (S ∩ (P : Set V)) = P := by
  apply le_antisymm (span_le.mpr Set.inter_subset_right)
  intro x hx
  by_cases hx₀ : x = 0
  · subst x; exact zero_mem _
  have hnot : ¬ P ≤ span K ({x} : Set V) := by
    intro hle
    have hf := Submodule.finrank_mono hle
    rw [finrank_span_singleton hx₀] at hf
    omega
  obtain ⟨y, hy, hyn⟩ : ∃ y ∈ P, y ∉ span K ({x} : Set V) := by
    by_contra hn
    apply hnot
    intro v hv
    by_contra hnv
    exact hn ⟨v,hv,hnv⟩
  let U := span K ({x,y} : Set V)
  have hU : finrank K U = 2 := span_pair_finrank x y hx₀ hyn
  have hUP : U ≤ P := span_le.mpr (by
    intro v hv
    rcases Set.mem_insert_iff.mp hv with hv | hv
    · subst v; exact hx
    · have hEq := Set.mem_singleton_iff.mp hv
      subst v; exact hy)
  obtain ⟨a, haS, b, hbS, haU, hbU, ha₀, hbn⟩ := hS U hU
  have hW : span K ({a,b} : Set V) = U := by
    apply Submodule.eq_of_le_of_finrank_le
    · apply span_le.mpr
      intro v hv
      rcases Set.mem_insert_iff.mp hv with h | h
      · subst v; exact haU
      · have hEq := Set.mem_singleton_iff.mp h
        subst v; exact hbU
    · rw [hU,span_pair_finrank a b ha₀ hbn]
  have hm : ({a,b} : Set V) ⊆ S ∩ (P : Set V) := by
    intro v hv
    rcases Set.mem_insert_iff.mp hv with h | h
    · exact h.symm ▸ ⟨haS, hUP haU⟩
    · exact (Set.mem_singleton_iff.mp h).symm ▸ ⟨hbS,hUP hbU⟩
  apply span_mono (R:=K) hm
  rw [hW]
  exact subset_span (Set.mem_insert x _)
abbrev Surviving (S : Set V) := {P : Submodule K V // span K (S ∩ (P : Set V)) = P}
def traceOrderEmbedding (S : Set V) : Surviving (K:=K) S ↪o Set V :=
  OrderEmbedding.ofMapLEIff (fun P => S ∩ (P.val : Set V)) (by
    intro P Q
    constructor
    · intro h
      have hspan := span_mono (R:=K) h
      rw [P.property, Q.property] at hspan
      exact hspan
    · intro h x hx
      exact ⟨hx.1, h hx.2⟩)
abbrev ClosedTrace (S : Set V) := {T : Set V // T ⊆ S ∧ S ∩ (span K T : Set V) = T}
def traceOrderIso (S : Set V) : Surviving (K:=K) S ≃o ClosedTrace (K:=K) S where
  toFun P := ⟨S ∩ (P.val : Set V), Set.inter_subset_left, by rw [P.property]⟩
  invFun T := ⟨span K T.val, by rw [T.property.2]⟩
  left_inv P := Subtype.ext P.property
  right_inv T := Subtype.ext T.property.2
  map_rel_iff' := (traceOrderEmbedding (K:=K) S).map_rel_iff
def matroidFlatTraceOrderIso (M : Matroid V) (S : Set V)
    (hground : M.E = S)
    (hclosure : ∀ T ⊆ S, M.closure T = S ∩ (span K T : Set V)) :
    InverseZ.Algebra.Flats M ≃o ClosedTrace (K:=K) S where
  toFun F :=
    let hsub : F.val ⊆ S := hground ▸ F.property.subset_ground
    ⟨F.val, hsub, (hclosure F.val hsub).symm.trans F.property.closure⟩
  invFun T := ⟨T.val, Matroid.isFlat_iff_closure_eq.mpr
    ((hclosure T.val T.property.1).trans T.property.2)⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_rel_iff' := Iff.rfl
def traceMatroidFlatOrderIso (M : Matroid V) (S : Set V)
    (hground : M.E = S)
    (hclosure : ∀ T ⊆ S, M.closure T = S ∩ (span K T : Set V)) :
    Surviving (K:=K) S ≃o InverseZ.Algebra.Flats M :=
  (traceOrderIso (K:=K) S).trans (matroidFlatTraceOrderIso M S hground hclosure).symm
#print axioms span_trace_eq_of_linePreserving
#print axioms traceMatroidFlatOrderIso
end InverseZProjective.ProjectiveTrace
