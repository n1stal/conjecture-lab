import Std

namespace ConjectureLab

/-- No positive smaller member divides the sum of two distinct larger members. -/
def propertyP (xs : List Nat) : Bool :=
  xs.all fun a => xs.all fun b => xs.all fun c =>
    !(decide (0 < a ∧ a < b ∧ b < c ∧ (b + c) % a = 0))

/-- The two-element witness is admissible. No optimality is claimed. -/
theorem baseline_valid : propertyP [1, 2] = true := by decide

/-- The reciprocal sum, scaled by the common denominator 2, is 3. -/
theorem baseline_weight :
    (2 / (1 : Nat)) + (2 / (2 : Nat)) = 3 := by decide

end ConjectureLab
