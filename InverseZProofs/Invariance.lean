module

public import InverseZProofs.Simplify

@[expose] public section

set_option autoImplicit false
namespace InverseZ
open Finset Polynomial
open InverseZ.Algebra

section Orders
variable {A B : Type*} [PartialOrder A] [PartialOrder B]
  [LocallyFiniteOrder A] [LocallyFiniteOrder B] [DecidableEq A] [DecidableEq B]
variable (e : A ≃o B) (rA : A → ℕ) (rB : B → ℕ)

omit [DecidableEq A] [DecidableEq B] in
theorem interval_Ico_sum {R : Type*} [AddCommMonoid R] (a b : A) (f : B → R) :
    (∑ x ∈ Ico (e a) (e b), f x) = ∑ x ∈ Ico a b, f (e x) := by
  symm
  exact Finset.sum_equiv e.toEquiv (by simp [mem_Ico]) (by simp)

omit [DecidableEq A] [DecidableEq B] in
theorem interval_Icc_sum {R : Type*} [AddCommMonoid R] (a b : A) (f : B → R) :
    (∑ x ∈ Icc (e a) (e b), f x) = ∑ x ∈ Icc a b, f (e x) := by
  symm
  exact Finset.sum_equiv e.toEquiv (by simp [mem_Icc]) (by simp)

theorem mu_orderIso (strict : StrictMono rA) (a b : A) :
    IncidenceAlgebra.mu ℤ (e a) (e b) = IncidenceAlgebra.mu ℤ a b := by
  generalize hn : rA b = n
  induction n using Nat.strong_induction_on generalizing b with
  | h n ih =>
    rw [IncidenceAlgebra.mu_apply (e a) (e b),IncidenceAlgebra.mu_apply a b]
    by_cases hab : a=b
    · subst b
      simp
    have he : e a ≠ e b := fun h => hab (e.injective h)
    rw [ite_eq_right hab,ite_eq_right he,interval_Ico_sum]
    congr 1
    apply sum_congr rfl
    intro x hx
    have hr := strict (mem_Ico.mp hx).2
    exact ih _ (hn ▸ hr) x rfl

theorem signedMu_orderIso (strict : StrictMono rA) (rankEq : ∀ x, rB (e x) = rA x)
    (a b : A) : signedMu rB (e a) (e b) = signedMu rA a b := by
  rw [signedMu,signedMu,rankEq,rankEq,mu_orderIso e rA strict]

theorem inverseKL_orderIso (strictA : StrictMono rA) (strictB : StrictMono rB)
    (rankEq : ∀ x, rB (e x) = rA x) (a b : A) :
    inverseKL rB strictB (e a) (e b) = inverseKL rA strictA a b := by
  generalize hn : rA b = n
  induction n using Nat.strong_induction_on generalizing b with
  | h n ih =>
    rw [inverseKL_eq,inverseKL_eq]
    by_cases hab : a=b
    · subst b
      simp
    have he : e a ≠ e b := fun h => hab (e.injective h)
    rw [ite_eq_right hab,ite_eq_right he,rankEq,rankEq]
    congr 1
    unfold properSum
    rw [interval_Ico_sum]
    apply sum_congr rfl
    intro x hx
    have hr := strictA (mem_Ico.mp hx).2
    rw [rankEq,rankEq,signedMu_orderIso e rA rB strictA rankEq x b,
      ih _ (hn ▸ hr) x rfl]

theorem inverseZ_orderIso (strictA : StrictMono rA) (strictB : StrictMono rB)
    (rankEq : ∀ x, rB (e x) = rA x) (a b : A) :
    inverseZ rB (inverseKL rB strictB) (e a) (e b) =
      inverseZ rA (inverseKL rA strictA) a b := by
  unfold inverseZ
  rw [interval_Icc_sum]
  apply sum_congr rfl
  intro x _
  rw [rankEq,rankEq,signedMu_orderIso e rA rB strictA rankEq x b,
    inverseKL_orderIso e rA rB strictA strictB rankEq a x]
end Orders

section Matroids
open Set Matroid

variable {α : Type*} (M : Matroid α)

theorem simplFlatOrderIso_bottom :
    simplFlatOrderIso M (bottomFlat (M ↾ simplGround M)) = bottomFlat M := by
  apply Subtype.ext
  change M.closure ((M ↾ simplGround M).closure ∅) = M.closure ∅
  rw [M.restrict_closure_eq (Set.empty_subset _) (simpl_ground_subset M)]
  exact simpl_spans_flat M (bottomFlat M)

theorem simplFlatOrderIso_top :
    simplFlatOrderIso M (topFlat (M ↾ simplGround M)) = topFlat M := by
  apply Subtype.ext
  change M.closure (simplGround M) = M.E
  have hh := simpl_spans_flat M (topFlat M)
  change M.closure (M.E ∩ simplGround M) = M.E at hh
  rwa [Set.inter_eq_right.mpr (simpl_ground_subset M)] at hh

variable [Finite α]

/-- Restrict to one point of every rank-one flat; the polynomial is unchanged. -/
theorem matroidInverseZ_simplification :
    matroidInverseZ (M ↾ simplGround M) = matroidInverseZ M := by
  classical
  have h := inverseZ_orderIso (simplFlatOrderIso M)
    (flatRank (M ↾ simplGround M)) (flatRank M)
    (flatRank_strict (M ↾ simplGround M)) (flatRank_strict M)
    (simplFlatOrderIso_rank M)
    (bottomFlat (M ↾ simplGround M)) (topFlat (M ↾ simplGround M))
  rw [simplFlatOrderIso_bottom,simplFlatOrderIso_top] at h
  exact h.symm

end Matroids

#print axioms mu_orderIso
#print axioms inverseZ_orderIso
#print axioms matroidInverseZ_simplification
end InverseZ
