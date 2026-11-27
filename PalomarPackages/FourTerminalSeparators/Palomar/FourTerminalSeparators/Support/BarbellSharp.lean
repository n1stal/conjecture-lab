module

public import Palomar.FourTerminalSeparators.Support.BarbellUpper
public import Palomar.FourTerminalSeparators.Support.FourEdgeLower

@[expose] public section

namespace HakKozerenkoEdgeSeparator
open TriameterQ3Graph HakKozerenkoSeparatorGraph

inductive CapKind where
  | triangle | pentagon | single
  deriving DecidableEq

def capLen : CapKind → Nat
  | .triangle => 3 | .pentagon => 5 | .single => 2

def capOffset : CapKind → Nat
  | .triangle => 2 | .pentagon => 3 | .single => 0

def capPairDistance : CapKind → Nat
  | .pentagon => 2 | _ => 1

def capRadius : CapKind → Nat
  | .triangle => 1 | .pentagon => 2 | .single => 0

theorem cap_len_le (C : CapKind) : 2≤capLen C := by cases C <;> decide
theorem cap_offset_le (C : CapKind) : capOffset C<capLen C := by cases C <;> decide
theorem cap_offset_ne_one (C : CapKind) : capOffset C≠1 := by cases C <;> decide

def capLeft (C D : CapKind) (L z : Nat) : Fin (barOrder (capLen C) (capLen D) L) :=
  ⟨leftRoot (capLen C)-z,by
    have := cap_len_le C
    have := cap_len_le D
    unfold leftRoot barOrder
    omega⟩

def capRight (C D : CapKind) (L z : Nat) (hz : z<capLen D) :
    Fin (barOrder (capLen C) (capLen D) L) :=
  ⟨rightRoot (capLen C) L+z,by
    have := cap_len_le C
    unfold rightRoot barOrder
    omega⟩

theorem bar_dist_eq_one {p q L : Nat} {a b : Fin (barOrder p q L)}
    (h : (barGraph p q L).adj a b) : (barMetric p q L).dist a b=1 := by
  let M := barMetric p q L
  have u := M.minimal a b 1 (unitWalk h)
  have ne : M.dist a b≠0 := fun z => (barGraph p q L).loopless a
    ((M.dist_eq_zero_iff a b).mp z ▸ h)
  change M.dist a b=1
  omega

theorem bar_dist_eq_two {p q L : Nat} {a b c : Fin (barOrder p q L)}
    (ne : a≠c) (no : ¬ (barGraph p q L).adj a c)
    (h : (barGraph p q L).adj a b) (k : (barGraph p q L).adj b c) :
    (barMetric p q L).dist a c=2 := by
  let M := barMetric p q L
  have u := M.dist_triangle a b c
  rw [bar_dist_eq_one h,bar_dist_eq_one k] at u
  have nz := fun z => ne ((M.dist_eq_zero_iff a c).mp z)
  have noone : M.dist a c≠1 := by
    intro e
    let W := M.geodesic a c
    have w := W.step 0 (by omega)
    rw [W.first] at w
    change (barGraph p q L).adj a (W.point 1) at w
    have hl : W.point 1=c := (congrArg W.point e).symm.trans W.last
    exact no (hl ▸ w)
  have p : 1≤M.dist a c := Nat.pos_of_ne_zero nz
  have lo : 2≤M.dist a c := Nat.lt_of_le_of_ne p noone.symm
  exact Nat.le_antisymm u lo

theorem cap_left_pair (C D : CapKind) (L : Nat) :
    (barMetric (capLen C) (capLen D) L).dist
      (capLeft C D L (capOffset C)) (capLeft C D L 1) = capPairDistance C := by
  have hD := cap_len_le D
  cases C
  · apply bar_dist_eq_one
    exact Or.inl (Or.inl rfl)
  · apply bar_dist_eq_two (b := capLeft .pentagon D L 2)
    · intro e
      have eq := congrArg Fin.val e
      simp [capLeft,capLen,capOffset,leftRoot] at eq
    · intro E
      simp only [barGraph,capLeft,capLen,capOffset,leftRoot,stepBetween,endpoints,rightRoot,barOrder] at E
      omega
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (Or.inl rfl)
  · apply bar_dist_eq_one
    exact Or.inl (Or.inr rfl)

theorem cap_right_pair (C D : CapKind) (L : Nat) :
    (barMetric (capLen C) (capLen D) L).dist
      (capRight C D L (capOffset D) (cap_offset_le D))
      (capRight C D L 1 (cap_len_le D)) = capPairDistance D := by
  have hC := cap_len_le C
  cases D
  · apply bar_dist_eq_one
    exact Or.inl (Or.inr rfl)
  · apply bar_dist_eq_two (b := capRight C .pentagon L 2 (by decide))
    · intro e
      have eq := congrArg Fin.val e
      simp [capRight,capOffset] at eq
    · intro E
      simp only [barGraph,capRight,capLen,capOffset,leftRoot,stepBetween,endpoints,rightRoot,barOrder] at E
      omega
    · exact Or.inl (Or.inr rfl)
    · exact Or.inl (Or.inr rfl)
  · apply bar_dist_eq_one
    exact Or.inl (Or.inl rfl)

theorem cap_left_radA (C D : CapKind) (L : Nat) :
    (barMetric (capLen C) (capLen D) L).dist (capLeft C D L (capOffset C))
      (rootLeft (capLen C) (capLen D) L (cap_len_le C) (cap_len_le D)) = capRadius C := by
  have hD := cap_len_le D
  cases C
  · apply bar_dist_eq_one
    exact Or.inr (Or.inl ⟨by decide, Or.inl ⟨rfl,rfl⟩⟩)
  · apply bar_dist_eq_two (b := capLeft .pentagon D L 4)
    · intro e
      have eq := congrArg Fin.val e
      simp [rootLeft,capLeft,capLen,capOffset,leftRoot] at eq
    · intro E
      simp only [barGraph,capLeft,capLen,capOffset,rootLeft,leftRoot,stepBetween,endpoints,rightRoot,barOrder] at E
      omega
    · exact Or.inl (Or.inr rfl)
    · exact Or.inr (Or.inl ⟨by decide,Or.inl ⟨rfl,rfl⟩⟩)
  · exact (barMetric _ _ _).dist_self _

theorem cap_right_radA (C D : CapKind) (L : Nat) :
    (barMetric (capLen C) (capLen D) L).dist
      (rootRight (capLen C) (capLen D) L (cap_len_le C) (cap_len_le D))
      (capRight C D L (capOffset D) (cap_offset_le D)) = capRadius D := by
  have hC := cap_len_le C
  cases D
  · apply bar_dist_eq_one
    refine Or.inr (Or.inr ⟨by decide,Or.inl ⟨rfl,?_⟩⟩)
    cases C <;> simp [capRight,capOffset,rightRoot,barOrder,capLen] <;> omega
  · apply bar_dist_eq_two (b := capRight C .pentagon L 4 (by decide))
    · intro e
      have eq := congrArg Fin.val e
      simp [rootRight,capRight,capOffset] at eq
    · intro E
      cases C <;> simp only [barGraph,capRight,capLen,capOffset,rootRight,leftRoot,stepBetween,endpoints,rightRoot,barOrder] at E <;> omega
    · refine Or.inr (Or.inr ⟨by decide,Or.inl ⟨rfl,?_⟩⟩)
      cases C <;> simp [capRight,rightRoot,barOrder,capLen] <;> omega
    · exact Or.inl (Or.inr rfl)
  · exact (barMetric _ _ _).dist_self _

theorem cap_left_radB (C D : CapKind) (L : Nat) :
    (barMetric (capLen C) (capLen D) L).dist (capLeft C D L 1)
      (rootLeft (capLen C) (capLen D) L (cap_len_le C) (cap_len_le D)) = 1 := by
  apply bar_dist_eq_one
  refine Or.inl (Or.inl ?_)
  have := cap_len_le C
  simp only [capLeft,rootLeft,leftRoot]
  omega

theorem cap_right_radB (C D : CapKind) (L : Nat) :
    (barMetric (capLen C) (capLen D) L).dist
      (rootRight (capLen C) (capLen D) L (cap_len_le C) (cap_len_le D))
      (capRight C D L 1 (cap_len_le D)) = 1 := by
  apply bar_dist_eq_one
  exact Or.inl (Or.inl rfl)

def EdgeAttains (S : Nat) : Prop :=
  ∃ n : Nat, ∃ G : SimpleGraph (Fin n), ∃ M : ShortestDistances G,
    ∃ a b c d : Fin n, FourApart a b c d ∧ fourSumEdge M a b c d=S ∧
      EdgeCap G (markFourEdge a b c d) ((S+1)/4)

def capSum (C D : CapKind) (L : Nat) : Nat :=
  4*L+capPairDistance C+capPairDistance D+2*(capRadius C+capRadius D+2)

theorem bar_attains (C D : CapKind) (L : Nat) (leftNonsingle : C≠.single)
    (capCheck : L+capBudget (capLen C)+capBudget (capLen D) ≤ (capSum C D L+1)/4) :
    EdgeAttains (capSum C D L) := by
  let p := capLen C
  let q := capLen D
  let M := barMetric p q L
  let a := capLeft C D L (capOffset C)
  let b := capLeft C D L 1
  let c := capRight C D L (capOffset D) (cap_offset_le D)
  let d := capRight C D L 1 (cap_len_le D)
  have ha : a.val<leftRoot p := by cases C <;> simp [a,p,capLeft,leftRoot,capLen,capOffset] at *
  have hb : b.val<leftRoot p := by
    have := cap_len_le C
    simp only [b,p,capLeft,leftRoot]
    omega
  have hc : rightRoot p L≤c.val := Nat.le_add_right _ _
  have hd : rightRoot p L≤d.val := Nat.le_add_right _ _
  have hr : leftRoot p≤rightRoot p L := Nat.le_add_right _ _
  have ne : FourApart a b c d := by
    constructor <;> intro e <;> have eq := congrArg Fin.val e
    · cases C <;> simp [a,b,capLeft,capLen,capOffset,leftRoot] at *
    · omega
    · omega
    · omega
    · omega
    · have h := cap_offset_ne_one D
      simp only [c,d,capRight] at eq
      omega
  refine ⟨_,barGraph p q L,M,a,b,c,d,ne,?_,?_⟩
  · have ac := bar_cross_distance (cap_len_le C) (cap_len_le D) a c (Nat.le_of_lt ha) hc
    have bd := bar_cross_distance (cap_len_le C) (cap_len_le D) b d (Nat.le_of_lt hb) hd
    have ad := bar_cross_distance (cap_len_le C) (cap_len_le D) a d (Nat.le_of_lt ha) hd
    have bc := bar_cross_distance (cap_len_le C) (cap_len_le D) b c (Nat.le_of_lt hb) hc
    unfold fourSumEdge capSum
    change (barMetric p q L).dist a b+(barMetric p q L).dist c d+
      (barMetric p q L).dist a c+(barMetric p q L).dist b d+
      (barMetric p q L).dist a d+(barMetric p q L).dist b c=_
    rw [ac,bd,ad,bc]
    rw [show (barMetric p q L).dist a b=capPairDistance C from cap_left_pair C D L]
    rw [show (barMetric p q L).dist c d=capPairDistance D from cap_right_pair C D L]
    rw [show (barMetric p q L).dist a _=capRadius C from cap_left_radA C D L]
    rw [show (barMetric p q L).dist b _=1 from cap_left_radB C D L]
    rw [show (barMetric p q L).dist _ c=capRadius D from cap_right_radA C D L]
    rw [show (barMetric p q L).dist _ d=1 from cap_right_radB C D L]
    omega
  · have h := bar_edge_cap p q L (cap_len_le C) (cap_len_le D) (T:=markFourEdge a b c d) (by
      intro x hx
      rcases hx with rfl|rfl|rfl|rfl
      · exact Or.inl (by omega)
      · exact Or.inl (by omega)
      · exact Or.inr hc
      · exact Or.inr hd)
    intro v F
    exact Nat.le_trans (h v F) capCheck

theorem bar_large_attains (S : Nat) (h : 11≤S) : EdgeAttains S := by
  let e := (S+1)/4
  have he : 3≤e := by dsimp [e]; omega
  have casesS : S=4*e+2 ∨ S=4*e+1 ∨ S=4*e ∨ S+1=4*e := by dsimp [e]; omega
  rcases casesS with H|H|H|H
  · have r : capSum .triangle .triangle (e-2)=S := by
      simp [capSum,capPairDistance,capRadius]; omega
    rw [←r]
    apply bar_attains _ _ _ (by decide)
    simp [capSum,capPairDistance,capRadius,capBudget,capLen]
    omega
  · have r : capSum .triangle .pentagon (e-3)=S := by
      simp [capSum,capPairDistance,capRadius]; omega
    rw [←r]
    apply bar_attains _ _ _ (by decide)
    simp [capSum,capPairDistance,capRadius,capBudget,capLen]
    omega
  · have r : capSum .triangle .single (e-2)=S := by
      simp [capSum,capPairDistance,capRadius]; omega
    rw [←r]
    apply bar_attains _ _ _ (by decide)
    simp [capSum,capPairDistance,capRadius,capBudget,capLen]
    omega
  · have r : capSum .pentagon .single (e-3)=S := by
      simp [capSum,capPairDistance,capRadius]; omega
    rw [←r]
    apply bar_attains _ _ _ (by decide)
    simp [capSum,capPairDistance,capRadius,capBudget,capLen]
    omega

end HakKozerenkoEdgeSeparator

#print axioms HakKozerenkoEdgeSeparator.bar_attains
#print axioms HakKozerenkoEdgeSeparator.bar_large_attains
