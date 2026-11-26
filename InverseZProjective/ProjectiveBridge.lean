module
public import InverseZProofs.Algebra
@[expose] public section
set_option autoImplicit false
namespace InverseZProjective.ProjectiveBridge
open Finset Polynomial InverseZ.Algebra
open scoped BigOperators
variable {L : Type*} [PartialOrder L] [LocallyFiniteOrder L] [DecidableEq L]
variable (rk : L → ℕ)
noncomputable def linearCandidate (A B : L → ℤ) (_ f : L) : ℤ[X] :=
  monomial 0 (A f) + monomial 1 (B f)
noncomputable def layerCoefficient (A B : L → ℤ) (o f : L) (i : ℕ) : ℤ :=
    (∑ x ∈ (Icc o f).filter (fun x => rk f - rk x = i), signedMu rk x f * A x) +
    (∑ x ∈ (Icc o f).filter (fun x => rk f - rk x + 1 = i), signedMu rk x f * B x)
theorem coeff_inverseZ_linearCandidate (A B : L → ℤ) (o f : L) (i : ℕ) :
    (inverseZ rk (linearCandidate A B) o f).coeff i =
      layerCoefficient rk A B o f i := by
  classical
  rw [coeff_inverseZ, layerCoefficient, sum_filter, sum_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro x hx
  simp only [linearCandidate, coeff_add, coeff_monomial]
  by_cases h₀ : rk f-rk x = i
  · simp [h₀]
  · by_cases h₁ : rk f-rk x+1 = i
    · have hle : rk f-rk x ≤ i := by omega
      have hsub : i-(rk f-rk x) = 1 := by omega
      simp [h₀, h₁, hle, hsub]
    · by_cases hle : rk f-rk x ≤ i
      · have hsub₀ : i-(rk f-rk x) ≠ 0 := by omega
        have hsub₁ : i-(rk f-rk x) ≠ 1 := by omega
        simp [h₀, h₁, hle, Ne.symm hsub₀, Ne.symm hsub₁]
      · simp [h₀, h₁, hle]
theorem inverseKL_unique_from_bottom (strict : StrictMono rk) (o : L)
    (q : L → L → ℤ[X]) (base : q o o = 1)
    (high : ∀ f, o < f → ∀ i, rk f-rk o ≤ 2*i → (q o f).coeff i = 0)
    (pal : ∀ f, o ≤ f → ∀ i, i ≤ rk f-rk o →
      (inverseZ rk q o f).coeff (rk f-rk o-i) = (inverseZ rk q o f).coeff i)
    {f : L} (hof : o ≤ f) :
    q o f = inverseKL rk strict o f := by
  classical
  let q' : L → L → ℤ[X] := fun a b => if a = o then q o b else inverseKL rk strict a b
  have same (f : L) : inverseZ rk q' o f = inverseZ rk q o f := by
    unfold inverseZ q'
    simp
  have hq' : q' o f = inverseKL rk strict o f :=
    inverseKL_unique rk strict q'
      (by
        intro a
        by_cases e : a = o
        · subst a; simpa [q'] using base
        · simp [q', e, inverseKL_self])
      (by
        intro a b hab i hi
        by_cases e : a = o
        · subst a; simp only [q', ite_eq_left rfl]; exact high b hab i hi
        · simp only [q', ite_eq_right e]
          exact inverseKL_high_coeff rk strict (ne_of_lt hab) i hi)
      (by
        intro a b hab i hi
        by_cases e : a = o
        · subst a; rw [same]; exact pal b hab i hi
        · have heq : inverseZ rk q' a b = inverseZ rk (inverseKL rk strict) a b := by
            unfold inverseZ q'
            simp [e]
          rw [heq]
          exact inverseZ_coeff_palindromic rk strict hab i hi)
      hof
  simpa [q'] using hq'
theorem source_coeff_of_layer_symmetry (strict : StrictMono rk) (A B : L → ℤ) (o : L)
    (hA : A o = 1) (hB : B o = 0)
    (hsmall : ∀ f, o < f → rk f-rk o ≤ 2 → B f = 0)
    (hsymm : ∀ f, o ≤ f → ∀ i, i ≤ rk f-rk o →
      layerCoefficient rk A B o f (rk f-rk o-i) = layerCoefficient rk A B o f i)
    {f : L} (i : ℕ) :
    (inverseZ rk (inverseKL rk strict) o f).coeff i =
      layerCoefficient rk A B o f i := by
  have heq {x : L} (hox : o ≤ x) : linearCandidate A B o x = inverseKL rk strict o x := by
    apply inverseKL_unique_from_bottom rk strict o (linearCandidate A B) ?_ ?_ ?_ hox
    · simp [linearCandidate, hA, hB]
    · intro b hob j hj
      have hr := strict hob
      have hn : j ≠ 0 := by omega
      by_cases hj1 : j = 1
      · subst j
        simp only [linearCandidate, coeff_add, coeff_monomial, ite_eq_right (by decide : (0:ℕ) ≠ 1),
          hsmall b hob (by omega), ite_self, add_zero]
      · simp only [linearCandidate, coeff_add, coeff_monomial, ite_eq_right (Ne.symm hn),
          ite_eq_right (Ne.symm hj1), add_zero]
    · intro b hob j hj
      rw [coeff_inverseZ_linearCandidate, coeff_inverseZ_linearCandidate]
      exact hsymm b hob j hj
  calc
    _ = (inverseZ rk (linearCandidate A B) o f).coeff i := by
      simp only [coeff_inverseZ]
      apply sum_congr rfl
      intro x hx
      rw [heq (mem_Icc.mp hx).1]
    _ = _ := coeff_inverseZ_linearCandidate rk A B o f i
section Matroid
variable {α : Type*} [Finite α] (M : Matroid α)
noncomputable def matroidLayerCoefficient (A B : Flats M → ℤ) (f : Flats M) (i : ℕ) : ℤ := by
  classical
  exact layerCoefficient (flatRank M) A B (bottomFlat M) f i
theorem matroidInverseZ_coeff_of_layer_symmetry (A B : Flats M → ℤ)
    (hA : A (bottomFlat M) = 1) (hB : B (bottomFlat M) = 0)
    (hsmall : ∀ f, bottomFlat M < f → flatRank M f ≤ 2 → B f = 0)
    (hsymm : ∀ f i, i ≤ flatRank M f →
      matroidLayerCoefficient M A B f (flatRank M f-i) = matroidLayerCoefficient M A B f i)
    (i : ℕ) :
    (matroidInverseZ M).coeff i = matroidLayerCoefficient M A B (topFlat M) i := by
  classical
  delta matroidInverseZ matroidInverseKL matroidLayerCoefficient
  exact source_coeff_of_layer_symmetry (flatRank M) (flatRank_strict M) A B
    (bottomFlat M) hA hB
    (by intro f hf hfr; exact hsmall f hf (by simpa only [flatRank_bottom, Nat.sub_zero] using hfr))
    (by
      intro f _ j hj
      have h := hsymm f j (by simpa only [flatRank_bottom, Nat.sub_zero] using hj)
      unfold matroidLayerCoefficient at h
      simpa only [flatRank_bottom, Nat.sub_zero] using h)
    i
end Matroid
#print axioms matroidInverseZ_coeff_of_layer_symmetry
end InverseZProjective.ProjectiveBridge
