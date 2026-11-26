module

public import InverseZProofs.Algebra
public import Mathlib.Tactic.Ring

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace InverseZ.Algebra
open Finset Polynomial
open scoped BigOperators

section Ranked
variable {L : Type*} [PartialOrder L] [LocallyFiniteOrder L] [DecidableEq L]
variable (rk : L → ℕ) (strict : StrictMono rk)
variable {a b : L}

/-- Rank j relative to the bottom of the interval. -/
def layer (a b : L) (j : ℕ) : Finset L :=
  (Icc a b).filter fun x => rk x - rk a = j

@[simp] theorem mem_layer {x : L} {j : ℕ} :
    x ∈ layer rk a b j ↔ (a ≤ x ∧ x ≤ b) ∧ rk x-rk a=j := by
  simp [layer]

include strict
theorem layer_zero (hab : a ≤ b) : layer rk a b 0 = {a} := by
  ext x
  simp only [mem_layer, mem_singleton]
  constructor
  · rintro ⟨⟨hax,hxb⟩,hr⟩
    by_contra e
    have h := strict (lt_of_le_of_ne hax (Ne.symm e))
    omega
  · rintro rfl
    exact ⟨⟨le_rfl,hab⟩,Nat.sub_self _⟩

theorem layer_top (hab : a ≤ b) :
    layer rk a b (rk b-rk a) = {b} := by
  ext x
  simp only [mem_layer, mem_singleton]
  constructor
  · rintro ⟨⟨hax,hxb⟩,hr⟩
    by_contra e
    have h := strict (lt_of_le_of_ne hxb e)
    have hax' := strict.monotone hax
    omega
  · rintro rfl
    exact ⟨⟨hab,le_rfl⟩,rfl⟩

theorem closed_sum_layers {G : Type*} [AddCommMonoid G] (f : L → G) {d : ℕ}
    (h : rk b-rk a = d) :
    ∑ x ∈ Icc a b, f x = ∑ j ∈ range (d+1), ∑ x ∈ layer rk a b j, f x := by
  symm
  apply sum_fiberwise_of_maps_to (g := fun x => rk x-rk a)
  intro x hx
  have hh := strict.monotone (mem_Icc.mp hx).2
  exact mem_range.mpr (by omega)

theorem open_sum_layers {G : Type*} [AddCommMonoid G] (f : L → G) {d : ℕ}
    (h : rk b-rk a = d+1) :
    ∑ x ∈ Ioo a b, f x = ∑ j ∈ range d, ∑ x ∈ layer rk a b (j+1), f x := by
  classical
  have hpart : ∑ j ∈ range d, ∑ x ∈ (Ioo a b).filter (fun x => rk x-rk a-1=j), f x =
      ∑ x ∈ Ioo a b, f x := by
    apply sum_fiberwise_of_maps_to (g := fun x => rk x-rk a-1)
    intro x hx
    obtain ⟨hax,hxb⟩ := mem_Ioo.mp hx
    have h1 := strict hax
    have h2 := strict hxb
    exact mem_range.mpr (by omega)
  rw [← hpart]
  apply sum_congr rfl
  intro j hj
  apply sum_congr _ (fun _ _ => rfl)
  ext x
  simp only [mem_filter, mem_Ioo, mem_layer]
  have hj' := mem_range.mp hj
  constructor
  · rintro ⟨⟨hax,hxb⟩, e⟩
    have hh := strict hax
    exact ⟨⟨hax.le,hxb.le⟩,by omega⟩
  · rintro ⟨⟨hax,hxb⟩, e⟩
    refine ⟨⟨?_,?_⟩,by omega⟩
    · apply lt_of_le_of_ne hax
      rintro rfl
      omega
    · apply lt_of_le_of_ne hxb
      rintro rfl
      omega

/-- Möbius recurrence with the bottom separated off. -/
theorem signedMu_recurrence {d : ℕ} (hab : a ≤ b) (h : rk b-rk a=d+1) :
    signedMu rk a b = (-1)^(d+1) *
      (-(1 + ∑ j ∈ range d, ∑ x ∈ layer rk a b (j+1), IncidenceAlgebra.mu ℤ a x)) := by
  classical
  have hne : a ≠ b := by rintro rfl; omega
  unfold signedMu
  rw [h, IncidenceAlgebra.mu_eq_neg_sum_Ico_of_ne hne,
    Ico_eq_cons_Ioo (lt_of_le_of_ne hab hne), sum_cons, IncidenceAlgebra.mu_self,
    open_sum_layers rk strict (IncidenceAlgebra.mu ℤ a) h]

theorem signedMu_one (hab : a ≤ b) (h : rk b-rk a=1) :
    signedMu rk a b = 1 := by
  simpa using signedMu_recurrence rk strict hab (d:=0) h

theorem unsignedMu_one (hab : a ≤ b) (h : rk b-rk a=1) :
    IncidenceAlgebra.mu ℤ a b = -1 := by
  have hh := signedMu_one rk strict hab h
  simp only [signedMu, h, pow_one, neg_mul, one_mul] at hh
  omega

noncomputable def W (a b : L) (i : ℕ) : ℤ := (layer rk a b i).card

theorem signedMu_two (hab : a ≤ b) (h : rk b-rk a=2) :
    signedMu rk a b = W rk a b 1 - 1 := by
  rw [signedMu_recurrence rk strict hab (d:=1) h]
  simp only [sum_range_one, Nat.zero_add]
  have e : (∑ x ∈ layer rk a b 1, IncidenceAlgebra.mu ℤ a x) = -W rk a b 1 := by
    unfold W
    rw [show (∑ x ∈ layer rk a b 1, IncidenceAlgebra.mu ℤ a x) =
      ∑ _x ∈ layer rk a b 1, (-1:ℤ) from
      sum_congr rfl (fun x hx => unsignedMu_one rk strict ((mem_layer rk).mp hx).1.1
        ((mem_layer rk).mp hx).2)]
    simp
  rw [e]
  ring

theorem unsignedMu_two (hab : a ≤ b) (h : rk b-rk a=2) :
    IncidenceAlgebra.mu ℤ a b = W rk a b 1 - 1 := by
  simpa [signedMu,h] using signedMu_two rk strict hab h

/-- Counts comparable pairs in increasing rank order, by summing lower slices. -/
noncomputable def I (a b : L) (i j : ℕ) : ℤ :=
  ∑ x ∈ layer rk a b j, W rk a x i

theorem signedMu_three (hab : a ≤ b) (h : rk b-rk a=3) :
    signedMu rk a b = I rk a b 1 2 - W rk a b 2 - W rk a b 1 + 1 := by
  rw [signedMu_recurrence rk strict hab (d:=2) h]
  simp only [show 2 = 1+1 by rfl, sum_range_succ, range_zero, sum_empty, zero_add]
  have e1 : (∑ x ∈ layer rk a b 1, IncidenceAlgebra.mu ℤ a x) = -W rk a b 1 := by
    unfold W
    rw [show (∑ x ∈ layer rk a b 1, IncidenceAlgebra.mu ℤ a x) =
      ∑ _x ∈ layer rk a b 1, (-1:ℤ) from
      sum_congr rfl (fun x hx => unsignedMu_one rk strict ((mem_layer rk).mp hx).1.1
        ((mem_layer rk).mp hx).2)]
    simp
  have e2 : (∑ x ∈ layer rk a b 2, IncidenceAlgebra.mu ℤ a x) = I rk a b 1 2 - W rk a b 2 := by
    unfold I
    have hconst : W rk a b 2 = ∑ _x ∈ layer rk a b 2, (1:ℤ) := by simp [W]
    rw [hconst, ← sum_sub_distrib]
    exact sum_congr rfl (fun x hx => unsignedMu_two rk strict ((mem_layer rk).mp hx).1.1
      ((mem_layer rk).mp hx).2)
  rw [e1, e2]
  ring

theorem unsignedMu_three (hab : a ≤ b) (h : rk b-rk a=3) :
    IncidenceAlgebra.mu ℤ a b = -(I rk a b 1 2 - W rk a b 2 - W rk a b 1 + 1) := by
  have hh := signedMu_three rk strict hab h
  simp only [signedMu,h,show (-1:ℤ)^3 = -1 by decide,neg_mul,one_mul] at hh
  omega

noncomputable def T (a b : L) (i j k : ℕ) : ℤ :=
  ∑ x ∈ layer rk a b k, I rk a x i j

theorem signedMu_four (hab : a ≤ b) (h : rk b-rk a=4) :
    signedMu rk a b = T rk a b 1 2 3 - I rk a b 2 3 - I rk a b 1 3 + W rk a b 3
      - I rk a b 1 2 + W rk a b 2 + W rk a b 1 - 1 := by
  rw [signedMu_recurrence rk strict hab (d:=3) h]
  simp only [show 3 = 2+1 by rfl, show 2 = 1+1 by rfl,
    sum_range_succ, range_zero, sum_empty, zero_add]
  have e1 : (∑ x ∈ layer rk a b 1, IncidenceAlgebra.mu ℤ a x) = -W rk a b 1 := by
    unfold W
    rw [show (∑ x ∈ layer rk a b 1, IncidenceAlgebra.mu ℤ a x) =
      ∑ _x ∈ layer rk a b 1, (-1:ℤ) from
      sum_congr rfl (fun x hx => unsignedMu_one rk strict ((mem_layer rk).mp hx).1.1
        ((mem_layer rk).mp hx).2)]
    simp
  have e2 : (∑ x ∈ layer rk a b 2, IncidenceAlgebra.mu ℤ a x) = I rk a b 1 2 - W rk a b 2 := by
    unfold I
    have hconst : W rk a b 2 = ∑ _x ∈ layer rk a b 2, (1:ℤ) := by simp [W]
    rw [hconst, ← sum_sub_distrib]
    exact sum_congr rfl (fun x hx => unsignedMu_two rk strict ((mem_layer rk).mp hx).1.1
      ((mem_layer rk).mp hx).2)
  have e3 : (∑ x ∈ layer rk a b 3, IncidenceAlgebra.mu ℤ a x) =
      -(T rk a b 1 2 3-I rk a b 2 3-I rk a b 1 3+W rk a b 3) := by
    unfold T I
    rw [← sum_sub_distrib, ← sum_sub_distrib]
    have hconst : W rk a b 3 = ∑ _x ∈ layer rk a b 3, (1:ℤ) := by simp [W]
    rw [hconst, ← sum_add_distrib, ← sum_neg_distrib]
    exact sum_congr rfl (fun x hx => unsignedMu_three rk strict ((mem_layer rk).mp hx).1.1
      ((mem_layer rk).mp hx).2)
  rw [e1,e2,e3]
  ring

/-- Only the rank-one slice contributes just below the top coefficient. -/
theorem inverseZ_penultimate (hab : a ≤ b) (hd : 0 < rk b-rk a) :
    (inverseZ rk (inverseKL rk strict) a b).coeff (rk b-rk a-1) =
      ∑ x ∈ layer rk a b 1, signedMu rk x b := by
  classical
  rw [coeff_inverseZ, layer, sum_filter]
  apply sum_congr rfl
  intro x hx
  obtain ⟨ha,hb⟩ := mem_Icc.mp hx
  have ha' := strict.monotone ha
  have hb' := strict.monotone hb
  by_cases hr : rk x-rk a=1
  · rw [ite_eq_left hr, ite_eq_left (by omega), show rk b-rk a-1-(rk b-rk x)=0 by omega,
      inverseKL_constant rk strict ha, signedMu_one rk strict ha hr, mul_one]
  · rw [ite_eq_right hr]
    by_cases hax : a=x
    · subst x
      rw [ite_eq_right (by omega), mul_zero]
    · have hl := strict (lt_of_le_of_ne ha hax)
      rw [ite_eq_left (by omega), inverseKL_high_coeff rk strict hax _ (by omega), mul_zero]

/-- The linear coefficient splits into the top interval's inverse KL term
    plus the constant inverse KL contributions of the layer just below the top. -/
theorem inverseZ_linear (hab : a ≤ b) (hd : 0 < rk b-rk a) :
    (inverseZ rk (inverseKL rk strict) a b).coeff 1 =
      (inverseKL rk strict a b).coeff 1 +
      ∑ x ∈ layer rk a b (rk b-rk a-1), signedMu rk a x := by
  classical
  rw [inverseZ_eq_proper_add rk _ hab, coeff_add, add_comm, properSum,
    finsetSum_coeff, layer, sum_filter]
  have hh : Ico a b ⊆ Icc a b := fun _ hx =>
    ⟨(mem_Ico.mp hx).1,(mem_Ico.mp hx).2.le⟩ |> mem_Icc.mpr
  rw [← sum_subset hh (fun x hx hnot => ?_)]
  · congr 1
    apply sum_congr rfl
    intro x hx
    obtain ⟨ha,hb⟩ := mem_Ico.mp hx
    have ha' := strict.monotone ha
    have hb' := strict hb
    simp only [coeff_C_mul, coeff_X_pow_mul']
    by_cases hr : rk x-rk a = rk b-rk a-1
    · have hdif : rk b-rk x=1 := by omega
      rw [ite_eq_left hr, hdif, ite_eq_left le_rfl, Nat.sub_self, inverseKL_constant rk strict ha,
        signedMu_one rk strict hb.le hdif, one_mul]
    · rw [ite_eq_right hr, ite_eq_right (by omega), mul_zero]
  · have he : x=b := by
      obtain ⟨ha,hb⟩ := mem_Icc.mp hx
      exact (eq_or_lt_of_le hb).resolve_right (fun hlt => hnot (mem_Ico.mpr ⟨ha,hlt⟩))
    subst x
    rw [ite_eq_right (by omega)]

end Ranked

#print axioms signedMu_four
#print axioms inverseZ_penultimate
#print axioms inverseZ_linear
end InverseZ.Algebra
