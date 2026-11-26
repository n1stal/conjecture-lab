module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.ByContra
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

open Matrix Finset
namespace SpectralRank

theorem gram_form {m n : Type*} [Fintype m] [Fintype n]
    (B : Matrix m m ℝ) (P : Matrix m n ℝ) (z : n → ℝ) :
    z ⬝ᵥ ((Pᵀ * B * P) *ᵥ z) = (P *ᵥ z) ⬝ᵥ (B *ᵥ (P *ᵥ z)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_transpose_mulVec,
    dotProduct_comm]

theorem gram_positive_subspace {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (B : Matrix m m ℝ) (P : Matrix m n ℝ) (d : n → ℝ)
    (hg : Pᵀ * B * P = diagonal d) (hd : ∀ i, 0 < d i) :
    ∃ V : Submodule ℝ (m → ℝ), Module.finrank ℝ V = Fintype.card n ∧
      ∀ x ∈ V, x ≠ 0 → 0 < x ⬝ᵥ (B *ᵥ x) := by
  have pos (z : n → ℝ) (hz : z ≠ 0) : 0 < z ⬝ᵥ ((Pᵀ * B * P) *ᵥ z) := by
    have hNz : ∃ i, z i ≠ 0 := by
      by_contra! hn
      apply hz
      funext i
      exact hn i
    obtain ⟨i,hi⟩ := hNz
    have hnon (j : n) : 0 ≤ d j * z j ^ 2 := mul_nonneg (hd j).le (sq_nonneg _)
    have hterm : 0 < d i * z i ^ 2 := mul_pos (hd i) (sq_pos_of_ne_zero hi)
    rw [hg, dotProduct]
    simp only [mulVec_diagonal]
    calc
      0 < d i * z i ^ 2 := hterm
      _ ≤ ∑ j, d j * z j ^ 2 := single_le_sum (fun j _ => hnon j) (mem_univ i)
      _ = ∑ j, z j * (d j * z j) := by congr 1; funext j; ring
  let T := P.mulVecLin
  have hinj : Function.Injective T := by
    apply LinearMap.ker_eq_bot.mp
    change LinearMap.ker P.mulVecLin = ⊥
    rw [Matrix.ker_mulVecLin_eq_bot_iff]
    intro z hz
    by_contra! hn
    have h := pos z hn
    change P *ᵥ z = 0 at hz
    rw [gram_form,hz] at h
    simp at h
  refine ⟨LinearMap.range T, ?_,?_⟩
  · rw [LinearMap.finrank_range_of_inj hinj]
    simp
  · intro x hx hne
    obtain ⟨z,rfl⟩ := hx
    change P *ᵥ z ≠ 0 at hne
    have hz : z ≠ 0 := fun hz => hne (by simp [hz])
    change 0 < (P *ᵥ z) ⬝ᵥ (B *ᵥ (P *ᵥ z))
    rw [← gram_form]
    exact pos z hz
theorem int_gram_positive_subspace {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (B : Matrix m m ℤ) (P : Matrix m n ℤ) (d : n → ℤ)
    (hg : Pᵀ * B * P = diagonal d) (hd : ∀ i, 0 < d i) :
    ∃ V : Submodule ℝ (m → ℝ), Module.finrank ℝ V = Fintype.card n ∧
      ∀ x ∈ V, x ≠ 0 → 0 < x ⬝ᵥ ((B.map (Int.castRingHom ℝ)) *ᵥ x) := by
  refine gram_positive_subspace (B.map (Int.castRingHom ℝ))
    (P.map (Int.castRingHom ℝ)) (fun i => (d i : ℝ)) ?_ ?_
  · have h := congrArg (fun A : Matrix n n ℤ => A.map (Int.castRingHom ℝ)) hg
    rw [Matrix.map_mul, Matrix.map_mul] at h
    have e : Pᵀ.map (Int.castRingHom ℝ) = (P.map (Int.castRingHom ℝ))ᵀ := by
      ext i j
      rfl
    rw [e] at h
    simpa using h
  · intro i
    exact_mod_cast hd i

noncomputable def squareCut {m : Type*} [Fintype m] [DecidableEq m]
    (B : Matrix m m ℝ) (q : ℝ) : Matrix m m ℝ :=
  Bᵀ * B - q^2 • (1 : Matrix m m ℝ)

theorem sq_norm_toLp_dot {m : Type*} [Fintype m] (x : m → ℝ) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℝ m)‖^2 = x ⬝ᵥ x := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp [dotProduct, pow_two]

theorem squareCut_form {m : Type*} [Fintype m] [DecidableEq m]
    (B : Matrix m m ℝ) (q : ℝ) (x : m → ℝ) :
    x ⬝ᵥ (squareCut B q *ᵥ x) =
      ‖B.toEuclideanLin (WithLp.toLp 2 x)‖^2 -
        q^2 * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ m)‖^2 := by
  rw [squareCut, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul]
  rw [← mulVec_mulVec, dotProduct_transpose_mulVec]
  change _ = ‖(WithLp.toLp 2 (B *ᵥ x) : EuclideanSpace ℝ m)‖^2 -
    q^2 * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ m)‖^2
  rw [sq_norm_toLp_dot,sq_norm_toLp_dot,smul_eq_mul]

theorem integer_square_cut_positive {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n]
    (B : Matrix m m ℤ) (P : Matrix m n ℤ) (d : n → ℤ) (j : ℤ)
    (hg : Pᵀ * ((100 : ℤ) • (Bᵀ * B) - j^2 • (1 : Matrix m m ℤ)) * P = diagonal d)
    (hd : ∀ i, 0 < d i) :
    ∃ V : Submodule ℝ (EuclideanSpace ℝ m), Module.finrank ℝ V = Fintype.card n ∧
      ∀ x ∈ V, ((j : ℝ)/10)^2 * ‖x‖^2 ≤
        ‖(B.map (Int.castRingHom ℝ)).toEuclideanLin x‖^2 := by
  let q : ℝ := (j : ℝ)/10
  let f := Int.castRingHom ℝ
  obtain ⟨V,hV,hn⟩ := int_gram_positive_subspace _ P d hg hd
  have hEq : (((100 : ℤ) • (Bᵀ * B) - j^2 • (1 : Matrix m m ℤ)).map f)
      = (100 : ℝ) • squareCut (B.map f) q := by
    have hT : Bᵀ.map f = (B.map f)ᵀ := by rfl
    have hM : (Bᵀ * B).map f = (B.map f)ᵀ * (B.map f) := by
      rw [Matrix.map_mul,hT]
    ext i k
    have hMk := congrFun (congrFun hM i) k
    change f ((Bᵀ * B) i k) = _ at hMk
    change f ((100 : ℤ) * (Bᵀ * B) i k - j^2 * (1 : Matrix m m ℤ) i k) = _
    rw [map_sub,map_mul,map_mul,map_pow,hMk]
    simp only [Matrix.smul_apply, squareCut, Matrix.sub_apply, smul_eq_mul, map_ofNat]
    by_cases hik : i=k
    · subst k
      simp [q,f]
      ring
    · simp [Matrix.one_apply_ne hik,q,f]
  let e := (WithLp.linearEquiv 2 ℝ (m → ℝ)).symm
  refine ⟨V.map e.toLinearMap,(LinearEquiv.finrank_map_eq e V).trans hV,?_⟩
  intro x hx
  obtain ⟨u,hu,rfl⟩ := Submodule.mem_map.mp hx
  change q^2 * ‖(WithLp.toLp 2 u : EuclideanSpace ℝ m)‖^2 ≤
    ‖(B.map f).toEuclideanLin (WithLp.toLp 2 u)‖^2
  by_cases h : u=0
  · simp [h]
  · have hp := hn u hu h
    change 0 < u ⬝ᵥ ((((100 : ℤ) • (Bᵀ * B) - j^2 • (1 : Matrix m m ℤ)).map f) *ᵥ u) at hp
    rw [hEq,smul_mulVec,dotProduct_smul,smul_eq_mul,squareCut_form] at hp
    linarith

#print axioms SpectralRank.integer_square_cut_positive
end SpectralRank
