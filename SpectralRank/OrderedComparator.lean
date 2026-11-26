module

public import SpectralRank.FrobeniusBridge
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Trace

@[expose] public section

open Finset Matrix
open scoped BigOperators
namespace SpectralRank

theorem sqFrob_trace {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℝ) :
    sqFrob A = (A * Aᵀ).trace := by
  simp [sqFrob, Matrix.trace, Matrix.diag, Matrix.mul_apply, pow_two]

theorem sqFrob_orthogonal_conj {m : Type*} [Fintype m] [DecidableEq m]
    (Q X : Matrix m m ℝ) (hq : Qᵀ*Q=1) : sqFrob (Q*X*Qᵀ) = sqFrob X := by
  rw [sqFrob_trace,sqFrob_trace]
  have mulEq : (Q*X*Qᵀ)*(Q*X*Qᵀ)ᵀ = (Q*(X*Xᵀ))*Qᵀ := by
    rw [transpose_mul,transpose_mul,transpose_transpose]
    calc
      _ = Q*X*(Qᵀ*Q)*Xᵀ*Qᵀ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hq,Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [mulEq, trace_mul_comm, ← Matrix.mul_assoc, hq, Matrix.one_mul]

theorem sqFrob_diagonal {m : Type*} [Fintype m] [DecidableEq m] (d : m → ℝ) :
    sqFrob (diagonal d) = ∑ i, (d i)^2 := by
  classical
  simp [sqFrob, diagonal_apply, ite_pow]

theorem ordered_eigenvalue_comparator {m : Type*} [Fintype m] [DecidableEq m]
    (H : Matrix m m ℝ) (hH : H.IsHermitian)
    (b : Fin (Fintype.card m) → ℝ)
    (hb : Fintype.card {i // b i ≠ 0} ≤ 3) :
    ∃ C : Matrix m m ℝ, C.rank ≤ 3 ∧
      sqFrob (H-C) = ∑ i, (hH.eigenvalues₀ i-b i)^2 := by
  classical
  let Q : Matrix m m ℝ := hH.eigenvectorUnitary
  have qt : star Q = Qᵀ := by rw [star_eq_conjTranspose,conjTranspose_eq_transpose_of_trivial]
  have hq : Qᵀ*Q=1 := by
    rw [← qt]
    exact Unitary.coe_star_mul_self hH.eigenvectorUnitary
  have he : H = Q * diagonal hH.eigenvalues * Qᵀ := by
    have s := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star] at s
    change H = Q * diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star Q at s
    rw [qt] at s
    simpa using s
  let e : Fin (Fintype.card m) ≃ m := Fintype.equivOfCardEq (Fintype.card_fin _)
  let d : m → ℝ := fun i => b (e.symm i)
  let C := Q * diagonal d * Qᵀ
  have hd : Fintype.card {i // d i ≠ 0} = Fintype.card {i // b i ≠ 0} := by
    apply Fintype.card_congr (Equiv.subtypeEquiv e.symm _)
    intro i
    rfl
  refine ⟨C,?_,?_⟩
  · exact (rank_mul_le_left _ _).trans ((rank_mul_le_right _ _).trans (by simpa [rank_diagonal,hd] using hb))
  · calc
      sqFrob (H-C) = sqFrob ((Q * diagonal hH.eigenvalues * Qᵀ)-C) :=
        congrArg (fun A => sqFrob (A-C)) he
      _ = _ := ?_
    change sqFrob (Q * diagonal hH.eigenvalues * Qᵀ - Q * diagonal d * Qᵀ) = _
    rw [← sub_mul,← mul_sub,diagonal_sub,sqFrob_orthogonal_conj _ _ hq,sqFrob_diagonal]
    exact (Equiv.sum_comp e.symm (fun i => (hH.eigenvalues₀ i - b i)^2))

theorem sqFrob_submatrix_le {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m m ℝ) (e : n ↪ m) : (sqFrob (A.submatrix e e)) ≤ sqFrob A := by
  classical
  let E : Finset m := Finset.univ.map e
  have index_le (x : m → ℝ) (hx : ∀ i, 0≤x i) : (∑ i, x (e i)) ≤ ∑ i, x i := by
    calc
      (∑ i, x (e i)) = ∑ i ∈ E, x i := by simp [E]
      _ ≤ ∑ i, x i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ E) (fun i _ _ => hx i)
  change (∑ i, ∑ j, (A (e i) (e j))^2) ≤ ∑ i, ∑ j, (A i j)^2
  calc
    (∑ i, ∑ j, (A (e i) (e j))^2) ≤ ∑ i, ∑ j, (A (e i) j)^2 :=
      Finset.sum_le_sum (fun i _ => index_le (fun j => (A (e i) j)^2) (fun _ => sq_nonneg _))
    _ ≤ ∑ i, ∑ j, (A i j)^2 :=
      index_le (fun i => ∑ j, (A i j)^2) (fun i => Finset.sum_nonneg (fun j _ => sq_nonneg _))

theorem extend_minor_lowrank_lower_bound {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m m ℝ) (e : n ↪ m) (t : ℝ)
    (h : ∀ C : Matrix n n ℝ, C.rank ≤ 3 → t ≤ sqFrob ((A.submatrix e e)-C)) :
    ∀ C : Matrix m m ℝ, C.rank ≤ 3 → t ≤ sqFrob (A-C) := by
  intro C hc
  have hh := h (C.submatrix e e) ((rank_submatrix_le C e e).trans hc)
  change t ≤ sqFrob ((A-C).submatrix e e) at hh
  exact hh.trans (sqFrob_submatrix_le (A-C) e)

theorem ordered_distance_ge_of_minor {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (A : Matrix m m ℝ) (hA : A.IsHermitian) (e : n ↪ m) (q : ℝ)
    (hminor : ∀ C : Matrix n n ℝ, C.rank ≤ 3 → q ≤ sqFrob ((A.submatrix e e)-C))
    (v : Fin (Fintype.card m) → ℝ) (hv : Fintype.card {i // v i ≠ 0} ≤ 3) :
    q ≤ ∑ i, (hA.eigenvalues₀ i-v i)^2 := by
  obtain ⟨C,hC,heq⟩ := ordered_eigenvalue_comparator A hA v hv
  rw [← heq]
  exact extend_minor_lowrank_lower_bound A e q hminor C hC

#print axioms SpectralRank.ordered_distance_ge_of_minor
end SpectralRank
