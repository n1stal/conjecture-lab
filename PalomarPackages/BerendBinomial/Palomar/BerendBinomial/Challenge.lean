module

public import Mathlib

@[expose] public section

/- Comparator statement only. The proof is in the separately compiled Solution. -/
namespace BerendBinomial
open Polynomial Finset
open scoped BigOperators

abbrev Nodes (m : Nat) := Fin (m+1)
abbrev Poly := Polynomial ℝ

def x {m : Nat} (i : Nodes m) : ℝ := i.val

def bin (m : Nat) (p : ℝ) (i : Nodes m) : ℝ :=
  (m.choose i.val : ℝ) * p^i.val * (1-p)^(m-i.val)

def moment {m : Nat} (u : Nodes m → ℝ) (f : Poly) : ℝ :=
  ∑ i, u i * f.eval (x i)

def Quadrature {m : Nat} (d : Nat) (p : ℝ) (u : Nodes m → ℝ) : Prop :=
  ∀ f : Poly, f.natDegree ≤ d → moment u f = moment (bin m p) f

def Paired (m k : Nat) (J : Finset (Nodes m)) : Prop :=
  J.card = k ∧ ∃ T : Finset Nat, 2*T.card=k ∧
    (∀ a ∈ T, a+1 ≤ m) ∧
    (∀ a ∈ T, ∀ b ∈ T, a < b → a+2 ≤ b) ∧
    ∀ i : Nodes m, i∈J ↔ ∃ a∈T, i.val=a ∨ i.val=a+1

def Feasible (m k : Nat) (J : Finset (Nodes m)) (p : ℝ) : Prop :=
  Paired m k J ∧ ∃ v : Nodes (m+1) → ℝ,
    Quadrature k p v ∧ (∀ j, 0≤v j) ∧ ∀ i : Nodes m, i∉J → v i.castSucc=0

def LeftActive (m k : Nat) (J : Finset (Nodes m)) (p : ℝ) : Prop :=
  ∃ ε : ℝ, 0<ε ∧ ∀ q : ℝ, 0<q → q<1 → p-ε<q → q<p → Feasible m k J q

def RightActive (m k : Nat) (J : Finset (Nodes m)) (p : ℝ) : Prop :=
  ∃ ε : ℝ, 0<ε ∧ ∀ q : ℝ, 0<q → q<1 → p<q → q<p+ε → Feasible m k J q

/-- Source Sect. 5.2: an exceptional point is an internal transition
with at least two departing indices. n = m+1, the fixed endpoint n is
omitted from both lower support sets, and thus from their difference. -/
def Exceptional (m k : Nat) (p : ℝ) : Prop :=
  0<p ∧ p<1 ∧ ∃ J K : Finset (Nodes m),
    Feasible m k J p ∧ Feasible m k K p ∧
    LeftActive m k J p ∧ RightActive m k K p ∧ 2≤(J\K).card

abbrev SourceExceptional (n k : Nat) (p : ℝ) : Prop := Exceptional (n-1) k p

theorem source_exceptional_reflect {n k : Nat} {p : ℝ}
    (hk : 2 ≤ k) (hle : k ≤ n - 1) (he : Even k)
    (h : SourceExceptional n k p) : SourceExceptional n k (1-p) :=
  sorry

end BerendBinomial
