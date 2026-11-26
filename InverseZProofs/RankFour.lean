module

public import Std

@[expose] public section

set_option autoImplicit false
namespace InverseZ

/-- In ascending degree order, check every adjacent coefficient triple. -/
def LogConcave : List Int → Prop
  | a :: b :: c :: xs => a * c ≤ b * b ∧ LogConcave (b :: c :: xs)
  | _ => True

def Positive : List Int → Prop
  | [] => True
  | a :: as => 0 < a ∧ Positive as

theorem square_gap (a x y : Int) :
    (a + x) * (a + x) - a * (a + x + y) =
      a * (x - y) + x * x := by
  simp only [Int.add_mul, Int.mul_add, Int.mul_sub]
  rw [Int.mul_comm x a]
  omega

theorem outer_inequality (a b c : Int) (ha : 0 ≤ a)
    (h : b - a ≥ c - b) : a * c ≤ b * b := by
  have hmul : 0 ≤ a * ((b - a) - (c - b)) :=
    Int.mul_nonneg ha (by omega)
  have hsq_nonneg : 0 ≤ (b - a) * (b - a) := by
    by_cases hba : 0 ≤ b - a
    · exact Int.mul_nonneg hba hba
    · exact Int.mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
  have he := square_gap a (b - a) (c - b)
  have hab : a + (b - a) = b := by omega
  have hbc : b + (c - b) = c := by omega
  rw [hab, hbc] at he
  omega

theorem rank_four_arithmetic (a b c : Int) (ha : 0 < a)
    (hmid : b ≤ c) (hgap : b - a ≥ c - b) :
    LogConcave [a,b,c,b,a] ∧ Positive [a,b,c,b,a] := by
  have hb : 0 < b := by omega
  have hc : 0 < c := by omega
  have hout := outer_inequality a b c (by omega) hgap
  have hm₁ := Int.mul_le_mul_of_nonneg_right hmid (show 0 ≤ b by omega)
  have hm₂ := Int.mul_le_mul_of_nonneg_left hmid (show 0 ≤ c by omega)
  have hmiddle : b*b ≤ c*c :=
    calc
      b*b ≤ c*b := hm₁
      _ ≤ c*c := hm₂
  have houtr : c*a ≤ b*b := by simpa only [Int.mul_comm c a] using hout
  simp [LogConcave, Positive, ha, hb, hc, hout, hmiddle, houtr]

theorem rank_two_arithmetic (n : Int) (hn : 2 ≤ n) :
    LogConcave [n-1,n,n-1] ∧ Positive [n-1,n,n-1] := by
  have hp : 0 < n-1 := by omega
  have hnp : 0 < n := by omega
  have h₁ : (n-1)*(n-1) ≤ n*(n-1) :=
    Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
  have h₂ : n*(n-1) ≤ n*n :=
    Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
  exact ⟨⟨Int.le_trans h₁ h₂, trivial⟩, hp, hnp, hp, trivial⟩

theorem rank_three_arithmetic (a b : Int) (ha : 0 < a) (hab : a ≤ b) :
    LogConcave [a,b,b,a] ∧ Positive [a,b,b,a] := by
  have hb : 0 < b := by omega
  have h₁ : a*b ≤ b*b := Int.mul_le_mul_of_nonneg_right hab (by omega)
  have h₂ : b*a ≤ b*b := Int.mul_le_mul_of_nonneg_left hab (by omega)
  exact ⟨⟨h₁, h₂, trivial⟩, ha, hb, hb, ha, trivial⟩

theorem rank_zero_one_arithmetic :
    (LogConcave [1] ∧ Positive [1]) ∧
      (LogConcave [1,1] ∧ Positive [1,1]) := by simp [LogConcave, Positive]

structure FlagCounts where
  points : Int
  lines : Int
  planes : Int
  pointLine : Int
  pointPlane : Int
  linePlane : Int
  pointLinePlane : Int
deriving Repr

def FlagCounts.outer (w : FlagCounts) : Int :=
  w.pointLinePlane - w.linePlane - w.pointPlane + w.planes -
    w.pointLine + w.lines + w.points - 1

def FlagCounts.inner (w : FlagCounts) : Int :=
  w.pointLinePlane - w.pointPlane - w.pointLine + w.points

def FlagCounts.middle (w : FlagCounts) : Int :=
  w.pointLinePlane - w.pointLine + w.lines - w.pointPlane

def FlagCounts.curvature (w : FlagCounts) : Int :=
  w.linePlane - 2*w.lines - w.planes + w.points + 1

theorem middle_gap (w : FlagCounts) : w.middle - w.inner = w.lines - w.points := by
  simp only [FlagCounts.middle, FlagCounts.inner]
  omega

theorem curvature_eq (w : FlagCounts) :
    (w.inner-w.outer)-(w.middle-w.inner) = w.curvature := by
  simp only [FlagCounts.outer, FlagCounts.inner, FlagCounts.middle, FlagCounts.curvature]
  omega

def boolean4 : FlagCounts := ⟨4,6,4,12,12,12,24⟩

/-- An abstract certificate for the numerical changes in a rank-preserving
    deletion of a point in a simple rank-four matroid. The geometric proof
    of this certificate is a separate obligation. -/
structure PointExtension (old new : FlagCounts) where
  heights : List Int
  newPlanes : Int
  enoughPlanes : ∀ h ∈ heights, 2 ≤ h
  points_eq : new.points = old.points + 1
  lines_eq : new.lines = old.lines + Int.ofNat heights.length
  planes_eq : new.planes = old.planes + newPlanes
  flags_eq : new.linePlane = old.linePlane + heights.sum + newPlanes

theorem heights_bound (heights : List Int)
    (enough : ∀ h ∈ heights, 2 ≤ h) : 2 * Int.ofNat heights.length ≤ heights.sum := by
  induction heights with
  | nil => decide
  | cons h hs ih =>
    have hh := enough h (by simp)
    have ht := ih (fun g hg => enough g (by simp [hg]))
    simp only [List.length_cons, List.sum_cons]
    have he : Int.ofNat (hs.length + 1) = Int.ofNat hs.length + 1 := by rfl
    rw [he]
    omega

theorem curvature_increases {old new : FlagCounts} (s : PointExtension old new) :
    new.curvature ≥ old.curvature + 1 := by
  have hh := heights_bound s.heights s.enoughPlanes
  simp only [FlagCounts.curvature]
  rw [s.points_eq, s.lines_eq, s.planes_eq, s.flags_eq]
  omega

inductive DeletionHistory : FlagCounts → Prop
  | basis : DeletionHistory boolean4
  | add {old new : FlagCounts} : DeletionHistory old →
      PointExtension old new → DeletionHistory new

theorem curvature_at_least_points_minus_three {w : FlagCounts}
    (h : DeletionHistory w) : w.points ≥ 4 ∧ w.curvature ≥ w.points - 3 := by
  induction h with
  | basis => decide
  | @add old new _ step ih =>
    have hinc := curvature_increases step
    have hpt := step.points_eq
    have h4 := ih.1
    have hcv := ih.2
    constructor <;> omega

/-- Kernel target for the algebra + finite deletion induction, conditional
    on the numerical deletion certificates and the point--line bound. -/
theorem rank_four_from_flags {w : FlagCounts} (h : DeletionHistory w)
    (point_line : w.points ≤ w.lines) (positive_mobius : 0 < w.outer) :
    LogConcave [w.outer,w.inner,w.middle,w.inner,w.outer] ∧
      Positive [w.outer,w.inner,w.middle,w.inner,w.outer] := by
  obtain ⟨hpts, hcurv⟩ := curvature_at_least_points_minus_three h
  have hm := middle_gap w
  have hd := curvature_eq w
  exact rank_four_arithmetic _ _ _ positive_mobius (by omega) (by omega)

#print axioms rank_two_arithmetic
#print axioms rank_three_arithmetic
#print axioms curvature_increases
#print axioms curvature_at_least_points_minus_three
#print axioms rank_four_from_flags

end InverseZ
