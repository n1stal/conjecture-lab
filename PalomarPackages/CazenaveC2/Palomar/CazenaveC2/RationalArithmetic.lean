module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section

/-! Exact rational sum-of-squares and Rayleigh arithmetic for the
11-vertex Cazenave #20829 witness. Source-only draft; no Lean receipt.
The semantic graph-to-quadratic-form and eigenvalue adapters are separate. -/
namespace CazenaveC2

noncomputable def diamondForm (a b c d p : ℝ) : ℝ :=
  (13/8)*(a^2+b^2+c^2)+(21/8)*d^2+
    2*(a*b+a*c+b*c+b*d+c*d+a*p)

noncomputable def diamondSq (a b c d p : ℝ) : ℝ :=
  (21/4)*((b+c)/2+(8/21)*(a+d))^2+
  (5/4)*((b-c)/2)^2+
  (313/168)*(d-(128/313)*a)^2+
  (1381/2504)*(a+(2504/1381)*p)^2

theorem diamond_eq (a b c d p : ℝ) :
    diamondForm a b c d p = diamondSq a b c d p - (2504/1381)*p^2 := by
  unfold diamondForm diamondSq
  ring

theorem diamondSq_nonneg (a b c d p : ℝ) : 0 ≤ diamondSq a b c d p := by
  unfold diamondSq
  positivity

noncomputable def pathSq (p q r : ℝ) : ℝ :=
  (8969/11048)*(p+(11048/8969)*q)^2+
  (8969/11048)*(r+(11048/8969)*q)^2+
  (11581/71752)*q^2

theorem pathSq_eq (p q r : ℝ) :
    pathSq p q r =
      (8969/11048)*(p^2+r^2)+(21/8)*q^2+2*p*q+2*q*r := by
  unfold pathSq
  ring

theorem pathSq_nonneg (p q r : ℝ) : 0 ≤ pathSq p q r := by
  unfold pathSq
  positivity

noncomputable def lapShiftForm (x : Fin 11 → ℝ) : ℝ :=
  diamondForm (x 0) (x 1) (x 2) (x 3) (x 8)+
  diamondForm (x 4) (x 5) (x 6) (x 7) (x 10)+
  (21/8)*((x 8)^2+(x 9)^2+(x 10)^2)+2*(x 8)*(x 9)+2*(x 9)*(x 10)

theorem lapShiftForm_nonnegative (x : Fin 11 → ℝ) : 0 ≤ lapShiftForm x := by
  have h₁ := diamondSq_nonneg (x 0) (x 1) (x 2) (x 3) (x 8)
  have h₂ := diamondSq_nonneg (x 4) (x 5) (x 6) (x 7) (x 10)
  have h₃ := pathSq_nonneg (x 8) (x 9) (x 10)
  have he : lapShiftForm x =
      diamondSq (x 0) (x 1) (x 2) (x 3) (x 8) +
      diamondSq (x 4) (x 5) (x 6) (x 7) (x 10) + pathSq (x 8) (x 9) (x 10) := by
    unfold lapShiftForm
    rw [diamond_eq, diamond_eq, pathSq_eq]
    ring
  rw [he]
  exact add_nonneg (add_nonneg h₁ h₂) h₃

/-- Actual Rayleigh form once support orthogonality and qf are evaluated. -/
theorem twoSupport_strict (a b : ℝ) (h : a ≠ 0 ∨ b ≠ 0) :
    (21/8)*(422*(a^2+b^2)) < 1114*(a^2+b^2) := by
  have hp : 0 < a^2+b^2 := by
    rcases h with ha | hb
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero ha) (sq_nonneg b)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg a) (sq_pos_of_ne_zero hb)
  nlinarith only [hp]

end CazenaveC2
