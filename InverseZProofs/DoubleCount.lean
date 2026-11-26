module

public import InverseZProofs.Coefficients
public import Mathlib.Tactic.NormNum

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
noncomputable local instance : DecidableLE L := Classical.decRel _
include strict

theorem upper_layer_filter {x : L} (hax : a ≤ x) {i j : ℕ} (hi : rk x-rk a=i) :
    layer rk x b j = (layer rk a b (i+j)).filter (fun y => x ≤ y) := by
  classical
  ext y
  simp only [mem_layer, mem_filter]
  constructor
  · intro h
    obtain ⟨⟨hxy,hyb⟩,hr⟩ := h
    have h₁ := strict.monotone hax
    have h₂ := strict.monotone hxy
    exact ⟨⟨⟨hax.trans hxy,hyb⟩,by omega⟩,hxy⟩
  · rintro ⟨⟨⟨_,hyb⟩,hr⟩,hxy⟩
    have h₁ := strict.monotone hax
    have h₂ := strict.monotone hxy
    exact ⟨⟨hxy,hyb⟩,by omega⟩

theorem lower_layer_filter {y : L} (hyb : y ≤ b) (i : ℕ) :
    layer rk a y i = (layer rk a b i).filter (fun x => x ≤ y) := by
  classical
  ext x
  simp only [mem_layer, mem_filter]
  exact ⟨fun ⟨⟨hax,hxy⟩,hr⟩ => ⟨⟨⟨hax,hxy.trans hyb⟩,hr⟩,hxy⟩,
    fun ⟨⟨⟨hax,_⟩,hr⟩,hxy⟩ => ⟨⟨hax,hxy⟩,hr⟩⟩

/-- Double-count incidences with arbitrary weights, by upper/lower layers. -/
theorem sum_upper_lower {G : Type*} [AddCommMonoid G] (i j : ℕ) (f : L → L → G) :
    (∑ x ∈ layer rk a b i, ∑ y ∈ layer rk x b j, f x y) =
      ∑ y ∈ layer rk a b (i+j), ∑ x ∈ layer rk a y i, f x y := by
  classical
  calc
    _ = ∑ x ∈ layer rk a b i, ∑ y ∈ layer rk a b (i+j),
        if x ≤ y then f x y else 0 := by
      apply sum_congr rfl
      intro x hx
      obtain ⟨⟨hax,_⟩,hr⟩ := (mem_layer rk).mp hx
      rw [upper_layer_filter rk strict hax hr, sum_filter]
    _ = ∑ y ∈ layer rk a b (i+j), ∑ x ∈ layer rk a b i,
        if x ≤ y then f x y else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro y hy
      rw [lower_layer_filter rk strict ((mem_layer rk).mp hy).1.2, sum_filter]

theorem sum_W_one (i j : ℕ) :
    (∑ x ∈ layer rk a b i, W rk x b j) = I rk a b i (i+j) := by
  change (∑ x ∈ layer rk a b i, W rk x b j) =
    ∑ y ∈ layer rk a b (i+j), W rk a y i
  simpa only [W, sum_const, nsmul_eq_mul, mul_one] using
    sum_upper_lower rk strict (a:=a) (b:=b) i j (fun _ _ => (1:ℤ))

theorem inverseZ_rank_zero (hab : a ≤ b) (h : rk b-rk a=0) :
    inverseZ rk (inverseKL rk strict) a b = 1 := by
  have e : a=b := by
    by_contra hn
    have hh := strict (lt_of_le_of_ne hab hn)
    omega
  subst b
  rw [inverseZ_self, inverseKL_self]

theorem inverseZ_rank_one (hab : a ≤ b) (h : rk b-rk a=1) :
    (inverseZ rk (inverseKL rk strict) a b).coeff 0 = 1 ∧
    (inverseZ rk (inverseKL rk strict) a b).coeff 1 = 1 := by
  have htop := inverseZ_top_coeff rk strict hab
  rw [h, signedMu_one rk strict hab h] at htop
  refine ⟨?_, htop⟩
  have hpal := inverseZ_coeff_palindromic rk strict hab 0 (by omega)
  simpa only [h,Nat.sub_zero,htop] using hpal.symm

theorem inverseZ_rank_two (hab : a ≤ b) (h : rk b-rk a=2) :
    (inverseZ rk (inverseKL rk strict) a b).coeff 2 = W rk a b 1 - 1 ∧
    (inverseZ rk (inverseKL rk strict) a b).coeff 1 = W rk a b 1 := by
  have htop := inverseZ_top_coeff rk strict hab
  rw [h, signedMu_two rk strict hab h] at htop
  refine ⟨htop, ?_⟩
  have hnext := inverseZ_penultimate rk strict hab (by omega)
  norm_num [h] at hnext
  rw [hnext, W]
  have hex : ∑ x ∈ layer rk a b 1, signedMu rk x b = ∑ _x ∈ layer rk a b 1, (1:ℤ) := by
    apply sum_congr rfl
    intro x hx
    obtain ⟨⟨hax,hxb⟩,hr⟩ := (mem_layer rk).mp hx
    apply signedMu_one rk strict hxb
    omega
  simp [hex]

theorem inverseZ_rank_three (hab : a ≤ b) (h : rk b-rk a=3) :
    (inverseZ rk (inverseKL rk strict) a b).coeff 3 =
      I rk a b 1 2-W rk a b 2-W rk a b 1+1 ∧
    (inverseZ rk (inverseKL rk strict) a b).coeff 2 = I rk a b 1 2-W rk a b 1 := by
  have htop := inverseZ_top_coeff rk strict hab
  rw [h, signedMu_three rk strict hab h] at htop
  refine ⟨htop, ?_⟩
  have hnext := inverseZ_penultimate rk strict hab (by omega)
  norm_num [h] at hnext
  rw [hnext]
  have hex : ∑ x ∈ layer rk a b 1, signedMu rk x b =
      ∑ x ∈ layer rk a b 1, (W rk x b 1 - 1) := by
    apply sum_congr rfl
    intro x hx
    obtain ⟨⟨hax,hxb⟩,hr⟩ := (mem_layer rk).mp hx
    apply signedMu_two rk strict hxb
    omega
  rw [hex, sum_sub_distrib, sum_W_one rk strict (a:=a) (b:=b) 1 1]
  simp [W]

theorem inverseKL_rank_three_linear (hab : a ≤ b) (h : rk b-rk a=3) :
    (inverseKL rk strict a b).coeff 1 = W rk a b 2-W rk a b 1 := by
  have hnext := (inverseZ_rank_three rk strict hab h).2
  have hpal := inverseZ_coeff_palindromic rk strict hab 1 (by omega)
  have hlin := inverseZ_linear rk strict hab (by omega)
  norm_num [h] at hpal hlin
  rw [← hpal,hnext] at hlin
  have hex : ∑ x ∈ layer rk a b 2, signedMu rk a x = I rk a b 1 2-W rk a b 2 := by
    unfold I
    have hc : W rk a b 2 = ∑ _x ∈ layer rk a b 2, (1:ℤ) := by simp [W]
    rw [hc, ← sum_sub_distrib]
    exact sum_congr rfl fun x hx =>
      signedMu_two rk strict ((mem_layer rk).mp hx).1.1 ((mem_layer rk).mp hx).2
  rw [hex] at hlin
  omega

theorem sum_I_upper (i j k : ℕ) :
    (∑ x ∈ layer rk a b i, I rk x b j (j+k)) = T rk a b i (i+j) (i+(j+k)) := by
  change (∑ x ∈ layer rk a b i, ∑ y ∈ layer rk x b (j+k), W rk x y j) =
    ∑ y ∈ layer rk a b (i+(j+k)), I rk a y i (i+j)
  rw [sum_upper_lower rk strict i (j+k)]
  apply sum_congr rfl
  intro y _
  exact sum_W_one rk strict i j

theorem inverseZ_rank_four_A (hab : a ≤ b) (h : rk b-rk a=4) :
    (inverseZ rk (inverseKL rk strict) a b).coeff 4 =
      T rk a b 1 2 3 - I rk a b 2 3 - I rk a b 1 3 + W rk a b 3
      - I rk a b 1 2 + W rk a b 2 + W rk a b 1 - 1 := by
  have htop := inverseZ_top_coeff rk strict hab
  rw [h, signedMu_four rk strict hab h] at htop
  exact htop

theorem inverseZ_rank_four_B (hab : a ≤ b) (h : rk b-rk a=4) :
    (inverseZ rk (inverseKL rk strict) a b).coeff 3 =
      T rk a b 1 2 3-I rk a b 1 3-I rk a b 1 2+W rk a b 1 := by
  have hnext := inverseZ_penultimate rk strict hab (by omega)
  norm_num [h] at hnext
  rw [hnext]
  have hex : ∑ x ∈ layer rk a b 1, signedMu rk x b =
      ∑ x ∈ layer rk a b 1, (I rk x b 1 (1+1)-W rk x b 2-W rk x b 1+1) := by
    apply sum_congr rfl
    intro x hx
    obtain ⟨⟨hax,hxb⟩,hr⟩ := (mem_layer rk).mp hx
    apply signedMu_three rk strict hxb
    omega
  rw [hex, sum_add_distrib, sum_sub_distrib, sum_sub_distrib, sum_I_upper rk strict,
    sum_W_one rk strict, sum_W_one rk strict]
  simp [W]

end Ranked

#print axioms inverseZ_rank_zero
#print axioms inverseZ_rank_one
#print axioms inverseZ_rank_two
#print axioms inverseZ_rank_three
#print axioms inverseKL_rank_three_linear
#print axioms inverseZ_rank_four_A
#print axioms inverseZ_rank_four_B
end InverseZ.Algebra
