module
public import InverseZProjective.GaussianRatios
public import Mathlib.Tactic.Ring
@[expose] public section
set_option autoImplicit false
namespace InverseZProjective.GaussianIncidence
open Module Submodule Finset
theorem gaussianCount_zero (K : Type*) [Field K] (n : ℕ) :
    gaussianCount K n 0 = 1 := by
  let : Unique (RankSubspaces K (Fin n → K) 0) :=
    { default := ⟨⊥, finrank_bot _ _⟩
      uniq := fun U => Subtype.ext (Submodule.finrank_eq_zero.mp U.property) }
  exact Nat.card_unique
theorem gaussianCount_diag (K : Type*) [Field K] (n : ℕ) :
    gaussianCount K n n = 1 := by
  rw [gaussianCount_symm_canonical K n n le_rfl, Nat.sub_self, gaussianCount_zero]
theorem gaussianCount_above_diag (K : Type*) [Field K] (n k : ℕ) (h : n < k) :
    gaussianCount K n k = 0 := by
  let : IsEmpty (RankSubspaces K (Fin n → K) k) := ⟨fun U => by
    have hle := Submodule.finrank_le U.val
    rw [Module.finrank_fin_fun,U.property] at hle
    omega⟩
  exact Nat.card_of_isEmpty
noncomputable def qInteger (q n : ℕ) : ℕ := ∑ i ∈ range n, q^i
theorem qInteger_add (q m n : ℕ) :
    qInteger q (m+n) = qInteger q m + q^m*qInteger q n := by
  rw [qInteger, sum_range_add, qInteger, qInteger, mul_sum]
  congr 1
  apply sum_congr rfl
  intro i _
  rw [pow_add, mul_comm]
theorem qInteger_pos (q n : ℕ) (hn : 0 < n) : 0 < qInteger q n := by
  unfold qInteger
  have hh := single_le_sum (f:=fun i => q^i) (fun _ _ => Nat.zero_le _) (mem_range.mpr hn)
  rw [pow_zero] at hh
  omega
theorem gaussian_pascal (K : Type*) [Field K] [Finite K] (n i : ℕ) (hi : i ≤ n) :
    gaussianCount K (n+1) (i+1) =
      gaussianCount K n i + (Nat.card K)^(i+1)*gaussianCount K n (i+1) := by
  by_cases hx : i = n
  · subst i
    rw [gaussianCount_diag, gaussianCount_diag,
      gaussianCount_above_diag K n (n+1) (by omega), mul_zero, add_zero]
  · have hp := gaussian_point_ratio_canonical K (n+1) i
    have hc := gaussian_codim_ratio_canonical K (n+1) (i+1) (by omega)
    simp only [show n+1-1=n by omega, show n+1-(i+1)=n-i by omega,
      gaussianCount_one_canonical] at hp hc
    apply Nat.mul_left_cancel (qInteger_pos (Nat.card K) (n+1) (by omega))
    calc
      _ = gaussianCount K (n+1) (i+1)*qInteger (Nat.card K) ((i+1)+(n-i)) := by
        rw [show (i+1)+(n-i)=n+1 by omega, mul_comm]
      _ = gaussianCount K (n+1) (i+1)*qInteger (Nat.card K) (i+1) +
          (Nat.card K)^(i+1)*(gaussianCount K (n+1) (i+1)*qInteger (Nat.card K) (n-i)) := by
        rw [qInteger_add]
        ring
      _ = _ := by unfold qInteger; rw [hp,hc]; ring
def mobiusWeight (q : ℤ) : ℕ → ℤ
  | 0 => 1
  | n+1 => -(q^n * mobiusWeight q n)
theorem mobiusWeight_succ (q : ℤ) (n : ℕ) :
    mobiusWeight q (n+1) = -(q^n*mobiusWeight q n) := rfl
theorem gaussian_mobius_sum (K : Type*) [Field K] [Finite K] (n : ℕ) :
    ∑ i ∈ range (n+2), (gaussianCount K (n+1) i : ℤ)*mobiusWeight (Nat.card K) i = 0 := by
  let q : ℤ := Nat.card K
  let w := mobiusWeight q
  let a : ℕ → ℤ := fun i => (gaussianCount K n i : ℤ)*(q^i*w i)
  have hstep (i : ℕ) (hi : i < n+1) :
      (gaussianCount K (n+1) (i+1) : ℤ)*w (i+1) = a (i+1) - a i := by
    rw [gaussian_pascal K n i (by omega), Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
    unfold a
    rw [show w (i+1) = -(q^i*w i) by rfl]
    change (_ + q^(i+1)*_)*_ = _
    ring
  change ∑ i ∈ range (n+2), (gaussianCount K (n+1) i : ℤ)*w i = 0
  rw [sum_range_succ']
  have he : (∑ i ∈ range (n+1), (gaussianCount K (n+1) (i+1) : ℤ)*w (i+1)) =
      ∑ i ∈ range (n+1), (a (i+1)-a i) :=
    sum_congr rfl (fun i hi => hstep i (mem_range.mp hi))
  rw [he, sum_range_sub]
  have hlast : a (n+1) = 0 := by
    simp [a,gaussianCount_above_diag K n (n+1) (by omega)]
  have hzero : a 0 = 1 := by simp [a,w,mobiusWeight,gaussianCount_zero]
  rw [hlast,hzero,gaussianCount_zero]
  simp [w,mobiusWeight]
#print axioms gaussian_pascal
#print axioms gaussian_mobius_sum
end InverseZProjective.GaussianIncidence
