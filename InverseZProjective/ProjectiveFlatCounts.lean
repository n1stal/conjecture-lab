module
public import InverseZProjective.ProjectiveUpperMobius
@[expose] public section
set_option autoImplicit false
namespace InverseZProjective.GaussianIncidence
open Module Submodule InverseZ.Algebra InverseZProjective.ProjectiveTrace
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V] [Finite V]
noncomputable def actualFlatAboveEquiv (S : Set V) (hS : LinePreserving (K:=K) S)
    (b : Flats (representedMatroid (K:=K) S)) (U : Submodule K V)
    (j : ℕ) (hj : 2 ≤ j) :
    {x : Set.Iic b // flatRank (representedMatroid (K:=K) S) x.val = j ∧
      U ≤ flatSubspaceEmbedding S x.val} ≃
    {y : Set.Icc U (flatSubspaceEmbedding S b) // finrank K y.val = j} := by
  let e := flatSubspaceEmbedding (K:=K) S
  refine Equiv.ofBijective (fun x =>
    ⟨⟨e x.val.val,x.property.2,e.monotone x.val.property⟩,
      (flatSubspaceEmbedding_rank S x.val.val).symm.trans x.property.1⟩) ⟨?_,?_⟩
  · intro x y h
    apply Subtype.ext
    apply Subtype.ext
    apply e.injective
    exact congrArg (fun z : {y : Set.Icc U (flatSubspaceEmbedding S b) //
      finrank K y.val = j} => z.val.val) h
  · intro y
    let Y : Surviving (K:=K) S := ⟨y.val.val,
      span_trace_eq_of_linePreserving S hS _ (by rw [y.property]; exact hj)⟩
    let x := representedFlatIso S Y
    have he : e x = y.val.val := by
      change (((representedFlatIso (K:=K) S).symm) (representedFlatIso S Y)).val = _
      rw [OrderIso.symm_apply_apply]
    have hxb : x ≤ b := e.le_iff_le.mp (he.symm ▸ y.val.property.2)
    have hxj : flatRank (representedMatroid (K:=K) S) x = j :=
      (flatSubspaceEmbedding_rank S x).trans (he.symm ▸ y.property)
    have hUx : U ≤ e x := he.symm ▸ y.val.property.1
    refine ⟨⟨⟨x,hxb⟩, hxj,hUx⟩, ?_⟩
    exact Subtype.ext (Subtype.ext he)
theorem card_actualFlats_above_subspace (S : Set V) (hS : LinePreserving (K:=K) S)
    (b : Flats (representedMatroid (K:=K) S)) (U : Submodule K V)
    (hub : U ≤ flatSubspaceEmbedding S b)
    (j : ℕ) (hj : 2 ≤ j) (hUj : finrank K U ≤ j) :
    Nat.card {x : Set.Iic b // flatRank (representedMatroid (K:=K) S) x.val = j ∧
      U ≤ flatSubspaceEmbedding S x.val} =
      gaussianCount K (flatRank (representedMatroid (K:=K) S) b - finrank K U)
        (j-finrank K U) := by
  rw [Nat.card_congr (actualFlatAboveEquiv S hS b U j hj)]
  let e := Equiv.subtypeEquivRight (α := Set.Icc U (flatSubspaceEmbedding S b))
    (p := fun y => finrank K y.val = j)
    (q := fun y => finrank K y.val - finrank K U = j-finrank K U)
    (fun y => by
      have h := Submodule.finrank_mono y.property.1
      omega)
  rw [Nat.card_congr e, card_subspace_interval_layer U _ hub,
    ← flatSubspaceEmbedding_rank S b]
theorem card_actualFlats_above_point (S : Set V) (hS : LinePreserving (K:=K) S)
    (b : Flats (representedMatroid (K:=K) S)) (P : Submodule K V)
    (hp : finrank K P = 1) (hpb : P ≤ flatSubspaceEmbedding S b)
    (j : ℕ) (hj : 2 ≤ j) :
    Nat.card {x : Set.Iic b // flatRank (representedMatroid (K:=K) S) x.val = j ∧
      P ≤ flatSubspaceEmbedding S x.val} =
      gaussianCount K (flatRank (representedMatroid (K:=K) S) b - 1) (j-1) := by
  rw [card_actualFlats_above_subspace S hS b P hpb j hj (by omega), hp]
#print axioms card_actualFlats_above_point
end InverseZProjective.GaussianIncidence
