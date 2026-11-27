module

public import Std

@[expose] public section

namespace InverseZ.TriangleCycle
def choose : Nat → Nat → Nat :=
  Nat.rec (fun k => Nat.casesOn k 1 (fun _ => 0))
    (fun _ prev k => Nat.casesOn k 1 (fun j => prev j + prev (j+1)))

def cycleRow (r i : Nat) : Nat :=
  if i≤r then
    let j := min i (r-i)
    choose (r+1) j*(r-j)
  else 0

def dent (m : Nat) : Nat := choose (2*m) m-choose (2*m) (m+1)
end InverseZ.TriangleCycle

namespace InverseZ.RatioDefect
abbrev Row := Nat → Int

def conv (a b : Row) (k : Nat) : Int :=
  Nat.rec (fun a : Row => a 0*b 0)
    (fun j prev a => a 0*b (j+1)+prev (fun i => a (i+1))) k a
end InverseZ.RatioDefect

namespace InverseZ.GluedCycleBounds
open TriangleCycle RatioDefect

def A (r i : Nat) : Int := (cycleRow r i : Int)

def U : Row := fun j=> if j=0 ∨ j=1 then 1 else 0

def halfPenalty (r i : Nat) : Int :=
  if r%2=1 ∧ i=(r+1)/2 then (dent ((r+1)/2):Int) else 0

def sourceCoeff (r s k : Nat) : Int :=
  A (r+s+1) k+conv U (conv (A r) (A s)) k
    - conv (halfPenalty r) (A s) k-conv (A r) (halfPenalty s) k
end InverseZ.GluedCycleBounds

namespace InverseZ.GluedCycleBounds
theorem sourceCoeff_strict_and_positive :
    (∀ r s i : Nat, 1≤r → 1≤s → i≤r+s+1 → 0<sourceCoeff r s i) ∧
    (∀ r s k : Nat, 1≤r → 1≤s → 1≤k → k<r+s+1 →
      sourceCoeff r s (k-1)*sourceCoeff r s (k+1)<sourceCoeff r s k*sourceCoeff r s k) := by sorry
end InverseZ.GluedCycleBounds
