module

public import Std

@[expose] public section

/-!
# The exact Maple quartic for a nondeterministic-excursion series

In de Panafieu and Wallner, Combinatorics of nondeterministic walks,
arXiv:2311.03234v2, §6.2 asks for a proof of an equation of degree four
in the authors' Maple companion. This file states that exact equation
for the original three nondeterministic steps, at every length.

A word consists of letters A={−1}, B={−1,+1}, C={−2,+1}. It counts once
if it has at least one realization with all partial sums nonnegative
and final sum zero. The recursion below reads the most recent letter
first; chronological words are reversed once in the membership test.

The integer polynomial coefficient lists are low-degree first and come
from algEE in PythonExample_m1_m1p1_m2p1.mw, GitLab blob
62f9f05364094361e768ace519a10aec3772d345. This is a quartic identity,
not a claim about the minimal algebraic degree, weighted extensions,
or the paper's separate general Conjecture 6.7.
-/


namespace WalkQuarticWord
inductive Letter where | A | B | C
  deriving DecidableEq

end WalkQuarticWord

namespace WalkQuarticSeries
structure Series where
  coeff : Nat → Rat
end WalkQuarticSeries

namespace WalkQuarticArithmetic
abbrev Poly := List Int

def c4 : Poly := [0, 0, 0, 0, 0, 0, 0, 0, 4, -24, -44, 448, 136, -3728, -120, 18208, 2484, -56216, -23004, 105952, 82624, -99968, -136832, 4608, 83968, 49152, 9216]
def c3 : Poly := [0, 0, 0, 0, 0, 0, 2, -8, -66, 318, 572, -3928, -1588, 24132, -3110, -87024, 35238, 199982, -127032, -315424, 286448, 399296, -407808, -472064, 277504, 402944, 2048, -122880, -36864]
def c2 : Poly := [-1, 2, 42, -74, -775, 1143, 8286, -9420, -56875, 42707, 261575, -86979, -807387, -75318, 1591536, 810509, -1708162, -1591734, 458477, 633356, 332364, 1602176, 1138360, -1559232, -1849024, 34304, 403840, -150016, -4096, 190464, 73728]
def c1 : Poly := [2, -4, -70, 148, 1006, -2356, -7564, 21360, 30760, -123824, -58286, 492616, 6930, -1400744, 52564, 2799150, 536136, -3465494, -1894224, 1721750, 1629810, 614406, 1171032, 251072, -1984304, -1576608, 396288, 566272, -6912, 77824, 40960, -135168, -73728]
def c0 : Poly := [-1, 2, 28, -74, -271, 1157, 564, -10264, 8649, 59127, -74013, -239645, 248181, 697650, -355798, -1379731, 6256, 1624262, 573455, -811202, -588678, -389454, -171788, 771500, 1257532, 286712, -705692, -583264, -186048, 65152, 318720, 304128, 160768, 86016, 36864]

end WalkQuarticArithmetic

namespace PalomarWalkQuartic
open WalkQuarticWord WalkQuarticSeries WalkQuarticArithmetic
open Letter

/-- Reachability for the most recent letter first, by explicit recursors. -/
def literalReach (w : List Letter) : Int → Prop :=
  List.rec (motive := fun _ => Int → Prop) (fun x => x = 0)
    (fun k _ previous x =>
      Letter.rec (motive := fun _ => Prop)
        (0 ≤ x ∧ previous (x+1))
        (0 ≤ x ∧ (previous (x-1) ∨ previous (x+1)))
        (0 ≤ x ∧ (previous (x-1) ∨ previous (x+2))) k) w

def literalAlphabet : List Letter := [A,B,C]

/-- Lists each source word of exactly the stated length. -/
def literalWords (n : Nat) : List (List Letter) :=
  Nat.rec (motive := fun _ => List (List Letter)) [[]]
    (fun _ previous =>
      literalAlphabet.flatMap (fun k => previous.map (fun w => k::w))) n

noncomputable def literalExcursions (n : Nat) : List (List Letter) := by
  classical
  exact (literalWords n).filter (fun w => decide (literalReach w.reverse 0))

/-- Full rational series of distinct source excursions, not realizing paths. -/
noncomputable def countSeries : Series :=
  ⟨fun n => ((literalExcursions n).length : Rat)⟩

def literalAdd (f g : Series) : Series := ⟨fun n => f.coeff n + g.coeff n⟩

def literalDelta (a : Rat) : Series :=
  ⟨Nat.rec (motive := fun _ => Rat) a (fun _ _ => 0)⟩

def literalTail (f : Series) : Series := ⟨fun n => f.coeff (n+1)⟩

def literalShift (f : Series) : Series :=
  ⟨Nat.rec (motive := fun _ => Rat) 0 (fun k _ => f.coeff k)⟩

/-- Coefficient n of the Cauchy product, without equation compiler helpers. -/
def literalCauchy (n : Nat) : Series → Series → Rat :=
  Nat.rec (motive := fun _ => Series → Series → Rat)
    (fun f g => f.coeff 0 * g.coeff 0)
    (fun k previous f g =>
      f.coeff 0 * g.coeff (k+1) + previous (literalTail f) g) n

def literalMul (f g : Series) : Series := ⟨fun n => literalCauchy n f g⟩
def literalT : Series := literalShift (literalDelta 1)

/-- Integer coefficient lists are low-degree first; use only List.foldr. -/
def evalPolynomial (p : Poly) : Series :=
  p.foldr (fun (a : Int) q => literalAdd (literalDelta (a : Rat)) (literalMul literalT q))
    (literalDelta 0)

/-- The exact author quartic in Y, with full rational-series operations. -/
def mapleQuarticAt (Y : Series) : Series :=
  let a := literalAdd (literalMul (evalPolynomial c4) Y) (evalPolynomial c3)
  let b := literalAdd (literalMul a Y) (evalPolynomial c2)
  let c := literalAdd (literalMul b Y) (evalPolynomial c1)
  literalAdd (literalMul c Y) (evalPolynomial c0)

/-- The literal full source word-count series satisfies the companion quartic. -/
theorem exact_quartic : mapleQuarticAt countSeries = literalDelta 0 := by
  sorry

end PalomarWalkQuartic
