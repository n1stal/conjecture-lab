module

public import InverseZProofs.DoubleCount

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace InverseZ.Algebra
open Finset Polynomial
open scoped BigOperators

section Ranked
variable {L : Type*} [PartialOrder L] [LocallyFiniteOrder L] [DecidableEq L]
variable (rk : L → ℕ) (strict : StrictMono rk)
variable {a b : L}
include strict

/-- The two contributing rank slices at the middle coefficient of rank four. -/
theorem inverseZ_rank_four_middle_split (_hab : a ≤ b) (h : rk b-rk a=4) :
    (inverseZ rk (inverseKL rk strict) a b).coeff 2 =
      (∑ x ∈ layer rk a b 2, (W rk a x 1-1)*(W rk x b 1-1)) +
      (∑ x ∈ layer rk a b 3, (W rk a x 2-W rk a x 1)) := by
  classical
  rw [coeff_inverseZ]
  simp only [layer, sum_filter]
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro x hx
  obtain ⟨hax,hxb⟩ := mem_Icc.mp hx
  have ha := strict.monotone hax
  have hb := strict.monotone hxb
  by_cases hr2 : rk x-rk a=2
  · have hdif : rk b-rk x=2 := by omega
    rw [ite_eq_left hr2, ite_eq_right (show ¬ rk x-rk a=3 by omega), add_zero, hdif, ite_eq_left le_rfl, Nat.sub_self,
      inverseKL_constant rk strict hax, signedMu_two rk strict hax hr2,
      signedMu_two rk strict hxb hdif, mul_comm]
  · rw [ite_eq_right hr2, zero_add]
    by_cases hr3 : rk x-rk a=3
    · have hdif : rk b-rk x=1 := by omega
      rw [ite_eq_left hr3, hdif, ite_eq_left (by decide : 1 ≤ 2), show 2-1=1 by decide,
        inverseKL_rank_three_linear rk strict hax hr3, signedMu_one rk strict hxb hdif, one_mul]
    · rw [ite_eq_right hr3]
      by_cases hr4 : rk x-rk a=4
      · have hdif : rk b-rk x=0 := by omega
        have hne : a ≠ x := by rintro rfl; omega
        rw [hdif, ite_eq_left (Nat.zero_le _), Nat.sub_zero,
          inverseKL_high_coeff rk strict hne _ (by omega), mul_zero]
      · rw [ite_eq_right (by omega),mul_zero]

theorem sum_rank_four_products (i j k : ℕ) :
    (∑ x ∈ layer rk a b (i+j), W rk a x i * W rk x b k) = T rk a b i (i+j) (i+j+k) := by
  have hh := sum_upper_lower rk strict (a:=a) (b:=b) (i+j) k
    (fun x _ => W rk a x i)
  simp only [sum_const, nsmul_eq_mul] at hh
  calc
    _ = ∑ x ∈ layer rk a b (i+j), W rk x b k * W rk a x i :=
      sum_congr rfl (fun x _ => mul_comm (W rk a x i) (W rk x b k))
    _ = _ := hh

theorem inverseZ_rank_four_C (hab : a ≤ b) (h : rk b-rk a=4) :
    (inverseZ rk (inverseKL rk strict) a b).coeff 2 =
      T rk a b 1 2 3 - I rk a b 1 2 + W rk a b 2 - I rk a b 1 3 := by
  rw [inverseZ_rank_four_middle_split rk strict hab h]
  have hp : (∑ x ∈ layer rk a b 2, W rk a x 1 * W rk x b 1) = T rk a b 1 2 3 :=
    sum_rank_four_products rk strict 1 1 1
  have hW : (∑ x ∈ layer rk a b 2, W rk x b 1) = I rk a b 2 3 :=
    sum_W_one rk strict 2 1
  have exp : ∀ u v : ℤ, (u-1)*(v-1) = u*v-u-v+1 := by intros; ring
  simp_rw [exp]
  rw [sum_add_distrib, sum_sub_distrib, sum_sub_distrib, sum_sub_distrib, hp, hW]
  have hc : (∑ _x ∈ layer rk a b 2, (1:ℤ)) = W rk a b 2 := by simp [W]
  rw [hc]
  change T rk a b 1 2 3-I rk a b 1 2-I rk a b 2 3+W rk a b 2+
    (I rk a b 2 3-I rk a b 1 3) = _
  ring

end Ranked

#print axioms inverseZ_rank_four_middle_split
#print axioms inverseZ_rank_four_C
end InverseZ.Algebra
