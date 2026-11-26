module

public import InverseZProofs.RankFour

@[expose] public section

set_option autoImplicit false
namespace InverseZ

theorem positive_lookup {xs : List Int} (h : Positive xs)
    (i : Nat) (hi : i < xs.length) : 0 < xs[i] := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a as ih =>
    cases i with
    | zero => exact h.1
    | succ j =>
      change 0 < as[j]'(by simp at hi <;> omega)
      exact ih h.2 j (by simp at hi <;> omega)

theorem logconcave_lookup {xs : List Int} (h : LogConcave xs)
    (i : Nat) (hi : i+2 < xs.length) :
    xs[i]'(by omega) * xs[i+2] ≤ xs[i+1]'(by omega) * xs[i+1]'(by omega) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a as ih =>
    cases as with
    | nil => simp at hi <;> omega
    | cons b bs =>
      cases bs with
      | nil => simp at hi <;> omega
      | cons c cs =>
        cases i with
        | zero => exact h.1
        | succ j =>
          change
            (b :: c :: cs)[j]'(by simp at hi ⊢ <;> omega) *
              (b :: c :: cs)[j+2]'(by simp at hi ⊢ <;> omega) ≤
              (b :: c :: cs)[j+1]'(by simp at hi ⊢ <;> omega) *
              (b :: c :: cs)[j+1]'(by simp at hi ⊢ <;> omega)
          exact ih h.2 j (by simp at hi ⊢ <;> omega)

#print axioms positive_lookup
#print axioms logconcave_lookup
end InverseZ
