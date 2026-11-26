module
public import InverseZProjective.ProjectiveTrace
@[expose] public section
set_option autoImplicit false
namespace InverseZProjective.ProjectiveTrace
open Module Submodule Matroid
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V] [Finite V]
omit [FiniteDimensional K V] in
private theorem span_finrank_of_indep {I : Set V} (hI : LinearIndepOn K id I) :
    finrank K (span K I) = I.ncard := by
  classical
  let : Fintype I := Fintype.ofFinite I
  have he : Set.range (fun x : I => (x : V)) = I := Subtype.range_coe
  have hli : LinearIndependent K (fun x : I => (x : V)) := hI
  rw [← he, finrank_span_eq_card hli, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, he]
private theorem linear_augment {I J : Set V}
    (hI : LinearIndepOn K id I) (hJ : LinearIndepOn K id J) (h : I.ncard < J.ncard) :
    ∃ e ∈ J, e ∉ I ∧ LinearIndepOn K id (insert e I) := by
  have hn : ¬ J ⊆ (span K I : Set V) := by
    intro hJI
    have hd := Submodule.finrank_mono (span_le.mpr hJI)
    rw [span_finrank_of_indep hI, span_finrank_of_indep hJ] at hd
    omega
  obtain ⟨e, heJ, heI⟩ := Set.not_subset.mp hn
  have he : e ∉ I := fun h => heI (subset_span h)
  exact ⟨e, heJ, he, (linearIndepOn_id_insert he).2 ⟨hI, heI⟩⟩
def representedMatroid (S : Set V) : Matroid V :=
  (IndepMatroid.ofFinite (Set.toFinite S)
    (fun I => I ⊆ S ∧ LinearIndepOn K id I)
    ⟨Set.empty_subset _, linearIndepOn_empty K id⟩
    (by intro I J h hIJ; exact ⟨hIJ.trans h.1, h.2.mono hIJ⟩)
    (by
      intro I J hI hJ hIJ
      obtain ⟨e, heJ, heI, h⟩ := linear_augment hI.2 hJ.2 hIJ
      exact ⟨e, heJ, heI, Set.insert_subset (hJ.1 heJ) hI.1, h⟩)
    (by intro I h; exact h.1)).matroid
@[simp] theorem representedMatroid_ground (S : Set V) : (representedMatroid (K:=K) S).E = S := rfl
@[simp] theorem representedMatroid_indep (S I : Set V) :
    (representedMatroid (K:=K) S).Indep I ↔ I ⊆ S ∧ LinearIndepOn K id I := by
  unfold representedMatroid
  exact IndepMatroid.matroid_indep_iff
private theorem represented_closure_of_indep (S : Set V) {I : Set V}
    (hI : (representedMatroid (K:=K) S).Indep I) :
    (representedMatroid (K:=K) S).closure I = S ∩ (span K I : Set V) := by
  let M := representedMatroid (K:=K) S
  have hI' := (representedMatroid_indep S I).mp hI
  ext e
  by_cases heS : e ∈ S
  · by_cases heI : e ∈ I
    · exact ⟨fun _ => ⟨heS,subset_span heI⟩, fun _ => M.mem_closure_of_mem heI hI.subset_ground⟩
    · have hEq : e ∉ M.closure I ↔ e ∉ span K I := by
        rw [hI.notMem_closure_iff_of_notMem heI heS, representedMatroid_indep,
          linearIndepOn_id_insert heI]
        exact ⟨fun h => h.2.2, fun he => ⟨Set.insert_subset heS hI'.1,hI'.2,he⟩⟩
      constructor
      · intro he
        exact ⟨heS, by by_contra hn; exact (hEq.mpr hn) he⟩
      · intro he
        by_contra hn
        exact (hEq.mp hn) he.2
  · exact ⟨fun h => (heS (M.closure_subset_ground _ h)).elim, fun h => (heS h.1).elim⟩
theorem representedMatroid_closure (S : Set V) (X : Set V) (hXS : X ⊆ S) :
    (representedMatroid (K:=K) S).closure X = S ∩ (span K X : Set V) := by
  let M := representedMatroid (K:=K) S
  obtain ⟨I,hI⟩ := M.exists_isBasis X hXS
  have hc := represented_closure_of_indep S hI.indep
  have hsp : span K I = span K X := span_eq_span
    (hI.subset.trans subset_span) (by
      intro x hx
      have hm := hI.subset_closure hx
      rw [hc] at hm
      exact hm.2)
  rw [← hI.closure_eq_closure, hc, hsp]
theorem representedMatroid_rank (S X : Set V) (hXS : X ⊆ S) :
    ((representedMatroid (K:=K) S).eRk X).toNat = finrank K (span K X) := by
  let M := representedMatroid (K:=K) S
  obtain ⟨I,hI⟩ := M.exists_isBasis X hXS
  have hiS : I ⊆ S := hI.subset.trans hXS
  have hc := representedMatroid_closure (K:=K) S I hiS
  have hsp : span K I = span K X := span_eq_span
    (hI.subset.trans subset_span) (by
      intro x hx
      have hm := hI.subset_closure hx
      rw [hc] at hm
      exact hm.2)
  rw [hI.eRk_eq_encard, ← Set.ncard_def, ← hsp,
    span_finrank_of_indep ((representedMatroid_indep S I).mp hI.indep).2]
def representedFlatIso (S : Set V) :
    Surviving (K:=K) S ≃o InverseZ.Algebra.Flats (representedMatroid (K:=K) S) :=
  traceMatroidFlatOrderIso _ S (representedMatroid_ground S) (representedMatroid_closure S)
theorem representedFlatIso_rank (S : Set V) (P : Surviving (K:=K) S) :
    InverseZ.Algebra.flatRank (representedMatroid (K:=K) S) (representedFlatIso S P) =
      finrank K P.val := by
  have hsub : S ∩ (P.val : Set V) ⊆ S := Set.inter_subset_left
  change ((representedMatroid (K:=K) S).eRk (S ∩ (P.val : Set V))).toNat = _
  rw [representedMatroid_rank S _ hsub, P.property]
#print axioms representedMatroid_closure
#print axioms representedMatroid_rank
#print axioms representedFlatIso_rank
end InverseZProjective.ProjectiveTrace
