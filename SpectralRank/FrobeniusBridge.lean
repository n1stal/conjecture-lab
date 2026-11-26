module

public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.Rank

@[expose] public section

open scoped InnerProductSpace
open Matrix
open scoped BigOperators
open Module
namespace SpectralRank

theorem find_unit_in_two_spaces_orthogonal_to_prior
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (P K : Submodule ℝ E) (i : Nat) (u : Fin i → E)
    (h : finrank ℝ E + i < finrank ℝ P + finrank ℝ K) :
    ∃ w, w ∈ P ∧ w ∈ K ∧ ‖w‖ = 1 ∧ ∀ j, ⟪u j,w⟫_ℝ = 0 := by
  classical
  let S := Submodule.span ℝ (Set.range u)
  let W := (P ⊓ K) ⊓ Sᗮ
  have hS : finrank ℝ S ≤ i := by
    refine (finrank_span_le_card (R := ℝ) (Set.range u)).trans ?_
    rw [Set.toFinset_card]
    exact (Fintype.card_range_le u).trans_eq (Fintype.card_fin _)
  have hPK := Submodule.finrank_sup_add_finrank_inf_eq P K
  have hPKsup : finrank ℝ ↥(P ⊔ K) ≤ finrank ℝ E := Submodule.finrank_le _
  have hSS := Submodule.finrank_add_finrank_orthogonal S
  have hW := Submodule.finrank_sup_add_finrank_inf_eq (P ⊓ K) Sᗮ
  have hWsup : finrank ℝ ↥((P ⊓ K) ⊔ Sᗮ) ≤ finrank ℝ E := Submodule.finrank_le _
  have hpos : 0 < finrank ℝ W := by
    change 0 < finrank ℝ ↥((P ⊓ K) ⊓ Sᗮ)
    omega
  have hn : W ≠ ⊥ := by
    intro h
    rw [h,finrank_bot] at hpos
    exact (Nat.lt_irrefl _) hpos
  obtain ⟨v,hv,hz⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  let w : E := ‖v‖⁻¹ • v
  have hw : w ∈ W := W.smul_mem _ hv
  have hnorm : ‖w‖ = 1 := by
    simp [w,norm_smul,inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]
  refine ⟨w,hw.1.1,hw.1.2,hnorm,fun j => ?_⟩
  exact (Submodule.mem_orthogonal S w).mp hw.2 (u j) (Submodule.subset_span ⟨j,rfl⟩)

theorem select_orthonormal_directions
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (k : Nat) (P : Nat → Submodule ℝ E) (K : Submodule ℝ E)
    (h : ∀ i<k, finrank ℝ E + i < finrank ℝ (P i) + finrank ℝ K) :
    ∃ u : Fin k → E, Orthonormal ℝ u ∧ ∀ i, u i ∈ P i.val ∧ u i ∈ K := by
  induction k with
  | zero =>
    refine ⟨Fin.elim0, ?_, fun i => Fin.elim0 i⟩
    exact orthonormal_iff_ite.mpr (fun i => Fin.elim0 i)
  | succ k ih =>
    obtain ⟨u,hu,hm⟩ := ih (fun i hi => h i (by omega))
    obtain ⟨w,hP,hK,hn,ho⟩ := find_unit_in_two_spaces_orthogonal_to_prior
      (P k) K k u (h k (by omega))
    let v : Fin (k+1) → E := Fin.snoc u w
    refine ⟨v, orthonormal_iff_ite.mpr ?_, fun i => ?_⟩
    · intro i j
      refine Fin.lastCases ?_ (fun i' => ?_) i
      · refine Fin.lastCases ?_ (fun j' => ?_) j
        · simp [v,hn]
        · simpa [v,real_inner_comm,Ne.symm (Fin.castSucc_ne_last j')] using ho j'
      · refine Fin.lastCases ?_ (fun j' => ?_) j
        · simpa [v] using ho i'
        · simpa [v] using (orthonormal_iff_ite.mp hu) i' j'
    · refine Fin.lastCases ?_ (fun i' => ?_) i
      · simpa [v] using And.intro hP hK
      · simpa [v] using hm i'

noncomputable def sqFrob {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℝ) : ℝ :=
  ∑ i, ∑ j, (A i j)^2

theorem bessel_matrix {m n ι : Type*} [Fintype m] [Fintype n] [Fintype ι]
    (A : Matrix m n ℝ) (u : ι → EuclideanSpace ℝ n) (hu : Orthonormal ℝ u) :
    (∑ i, ∑ j, (A.mulVec (WithLp.ofLp (u i)) j)^2) ≤ sqFrob A := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro j _
  have h := hu.sum_inner_products_le (WithLp.toLp 2 (fun l => A j l)) (s:=Finset.univ)
  simpa only [EuclideanSpace.inner_eq_star_dotProduct,WithLp.ofLp_toLp,Matrix.mulVec,
    star_trivial,dotProduct_comm,PiLp.norm_sq_eq_of_L2,Real.norm_eq_abs,sq_abs] using h

theorem frobenius_ge_thresholds
    {m : Type*} [Fintype m] [DecidableEq m]
    (B C : Matrix m m ℝ) (r k : Nat) (hc : C.rank≤r)
    (q : Fin k → ℝ) (P : Nat → Submodule ℝ (EuclideanSpace ℝ m))
    (hdim : ∀ i : Fin k, r+i.val+1 ≤ Module.finrank ℝ (P i.val))
    (hP : ∀ (i : Fin k) (x : EuclideanSpace ℝ m), x∈P i.val →
        q i ^ 2 * ‖x‖^2 ≤ ‖B.toEuclideanLin x‖^2) :
    (∑ i, q i ^ 2) ≤ sqFrob (B-C) := by
  let T := C.toEuclideanLin
  let K := LinearMap.ker T
  have hr : Module.finrank ℝ (LinearMap.range T) = C.rank := by
    change Module.finrank ℝ (LinearMap.range C.toEuclideanLin) = C.rank
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
    exact (C.rank_eq_finrank_range_toLin _ _).symm
  have hdimT : Module.finrank ℝ (LinearMap.range T) + Module.finrank ℝ K =
      Module.finrank ℝ (EuclideanSpace ℝ m) := LinearMap.finrank_range_add_finrank_ker T
  have hd : ∀ i<k, Module.finrank ℝ (EuclideanSpace ℝ m) + i <
          Module.finrank ℝ (P i) + Module.finrank ℝ K := by
    intro i hi
    have h := hdim ⟨i,hi⟩
    change r+i+1 ≤ Module.finrank ℝ (P i) at h
    omega
  obtain ⟨u,hu,hmem⟩ := select_orthonormal_directions k P K hd
  have ev (i : Fin k) : (C *ᵥ WithLp.ofLp (u i)) = 0 := by
    have e := LinearMap.mem_ker.mp (hmem i).2
    exact congrArg WithLp.ofLp e
  have contribution (i : Fin k) :
      q i ^ 2 ≤ ∑ j, ((B-C).mulVec (WithLp.ofLp (u i)) j)^2 := by
    have e := hP i (u i) (hmem i).1
    rw [hu.norm_eq_one i,one_pow,mul_one] at e
    rw [Matrix.sub_mulVec,ev i,sub_zero]
    simpa only [PiLp.norm_sq_eq_of_L2,Real.norm_eq_abs,sq_abs,Matrix.toLpLin_apply,
      WithLp.ofLp_toLp] using e
  exact (Finset.sum_le_sum (fun i _ => contribution i)).trans (bessel_matrix (B-C) u hu)

#print axioms SpectralRank.frobenius_ge_thresholds
end SpectralRank
