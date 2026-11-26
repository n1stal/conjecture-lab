import Std

namespace ConjectureLab

/-- A finite list has Property P iff no increasing triple in it is forbidden.
    The implication only considers positive smaller elements. -/
def propertyP (xs : List Nat) : Bool :=
  xs.all fun a => xs.all fun b => xs.all fun c =>
    !(decide (0 < a ∧ a < b ∧ b < c ∧ (b + c) % a = 0))

/-- This statement verifies only the exhibited finite witness. -/
theorem baseline_valid : propertyP [1, 2] = true := by decide

theorem baseline_weight :
    (2 / (1 : Nat)) + (2 / (2 : Nat)) = 3 := by decide

def withoutOne : List Nat := [3, 5, 6, 8, 11, 20, 23, 26, 56, 71, 143, 146]

set_option maxRecDepth 16384 in
theorem withoutOne_valid : propertyP withoutOne = true := by decide

/-- D is a common multiple, so the scaled sum is exact (not rounded division). -/
def D : Nat := 14319385080

theorem denominator_exact : withoutOne.all (fun a => D % a == 0) = true := by decide

theorem withoutOne_weight :
    (withoutOne.map (fun a => D / a)).sum = 15660150090 := by decide

theorem improves_without_one_candidate : 15660150090 * 12 > 13 * D := by decide

#print axioms baseline_valid
#print axioms baseline_weight
#print axioms withoutOne_valid
#print axioms denominator_exact
#print axioms withoutOne_weight
#print axioms improves_without_one_candidate

end ConjectureLab
