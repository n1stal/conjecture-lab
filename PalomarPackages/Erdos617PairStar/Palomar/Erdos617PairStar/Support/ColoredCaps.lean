module

public import Palomar.Erdos617PairStar.Support.AnchorGeometry
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-! Exact edge ledger for the two inherited colored caps in #617.
A symmetric edge coloring on distinct vertices is supplied as col.
The proofs use one fixed order for the listed distinct vertices, so only
one copy of each edge is counted. No counting claim is checked by search. -/

namespace Erdos617Geometry

universe u v

def orderedColors {V : Type u} {H : Type v} (col : V → V → H) : List V → List H
  | [] => []
  | x :: W => W.map (col x) ++ orderedColors col W

def crossColors {V : Type u} {H : Type v} (col : V → V → H) (X Y : List V) : List H :=
  X.flatMap (fun x => Y.map (col x))

theorem length_crossColors {V : Type u} {H : Type v} (col : V → V → H)
    (X Y : List V) : (crossColors col X Y).length = X.length * Y.length := by
  induction X with
  | nil => simp [crossColors]
  | cons x X ih =>
    have h : crossColors col (x :: X) Y = Y.map (col x) ++ crossColors col X Y := rfl
    rw [h, List.length_append, List.length_map, ih, List.length_cons, Nat.succ_mul]
    omega

theorem orderedColors_count_append {V : Type u} {H : Type v} [BEq H]
    (col : V → V → H) (c : H) (X Y : List V) :
    (orderedColors col (X ++ Y)).count c =
      (orderedColors col X).count c + (orderedColors col Y).count c +
        (crossColors col X Y).count c := by
  induction X with
  | nil => simp [orderedColors, crossColors]
  | cons x X ih =>
    have h : crossColors col (x :: X) Y = Y.map (col x) ++ crossColors col X Y := rfl
    simp only [List.cons_append, orderedColors, List.map_append, List.count_append, h] at *
    omega

theorem orderedColors_count_eq_zero_of_clique {V : Type u} {H : Type v}
    [BEq H] [LawfulBEq H] (col : V → V → H) {t c : H} (hne : c ≠ t)
    (R : List V) (clique : R.Pairwise (fun a b => col a b = t)) :
    (orderedColors col R).count c = 0 := by
  induction R with
  | nil => simp [orderedColors]
  | cons x R ih =>
    obtain ⟨hx, ht⟩ := List.pairwise_cons.mp clique
    have hc : c ∉ R.map (col x) := by
      intro hm
      obtain ⟨y, hy, hcol⟩ := List.mem_map.mp hm
      exact hne (hcol.symm.trans (hx y hy))
    simp [orderedColors, List.count_eq_zero_of_not_mem hc, ih ht]

/-- An elementary independent sublist with one possible loss per hue-c edge. -/
theorem exists_independent_sublist {V : Type u} {H : Type v} [BEq H] [LawfulBEq H]
    (col : V → V → H) (c : H) (W : List V) (nd : W.Nodup) :
    ∃ I : List V, I.Sublist W ∧ I.Pairwise (Compatible (fun a b => col a b = c)) ∧
        W.length ≤ I.length + (orderedColors col W).count c := by
  classical
  induction W with
  | nil => exact ⟨[], List.Sublist.slnil, List.Pairwise.nil, by simp [orderedColors]⟩
  | cons x W ih =>
    obtain ⟨hx, hnd⟩ := List.nodup_cons.mp nd
    obtain ⟨I, sI, iI, lI⟩ := ih hnd
    by_cases h : c ∈ W.map (col x)
    · refine ⟨I, List.Sublist.cons x sI, iI, ?_⟩
      have p : 0 < (W.map (col x)).count c := List.count_pos_iff.mpr h
      simp only [orderedColors, List.length_cons, List.count_append]
      omega
    · refine ⟨x :: I, List.Sublist.cons_cons x sI, List.pairwise_cons.mpr ⟨?_, iI⟩, ?_⟩
      · intro y hy
        have hyW := sI.subset hy
        refine ⟨fun he => hx (he ▸ hyW), ?_⟩
        intro he
        exact h (List.mem_map.mpr ⟨y, hyW, he⟩)
      · simp only [orderedColors, List.length_cons, List.count_append]
        omega

/-- In every listed induced vertex set the number of hue-c edges is at
least its order minus the independence cap of that hue. -/
theorem hue_edge_floor {V : Type u} {H : Type v} [BEq H] [LawfulBEq H]
    (col : V → V → H) (c : H) (r : Nat)
    (cap : IndependenceCap (fun a b => col a b = c) r)
    (W : List V) (nd : W.Nodup) :
    W.length ≤ r + (orderedColors col W).count c := by
  obtain ⟨I, _, iI, lI⟩ := exists_independent_sublist col c W nd
  have b := cap I iI
  omega

theorem count_add_filter_ne_length {H : Type v} [BEq H] [LawfulBEq H]
    (c : H) (E : List H) :
    E.count c + (E.filter (fun x => !(x == c))).length = E.length := by
  induction E with
  | nil => simp
  | cons x E ih =>
    classical
    by_cases h : x = c
    · subst x
      simp only [List.count_cons_self, List.filter_cons, beq_self_eq_true, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte, List.length_cons]
      omega
    · have neq : (x == c) = false := by simp [h]
      simp only [List.count_cons_of_ne h, List.filter_cons, neq, Bool.not_false,
        ↓reduceIte, List.length_cons]
      omega

/-- Disjoint hue classes consume disjoint slots in a single palette ledger. -/
theorem hue_quota_mul_le_length {H : Type v} [BEq H] [LawfulBEq H]
    (C : List H) (nd : C.Nodup) (t : Nat) (E : List H)
    (lower : ∀ c ∈ C, t ≤ E.count c) : C.length * t ≤ E.length := by
  induction C generalizing E with
  | nil => simp
  | cons c C ih =>
    obtain ⟨hc, hnd⟩ := List.nodup_cons.mp nd
    have cur := lower c (by simp)
    have lower' : ∀ d ∈ C, t ≤ (E.filter (fun x => !(x == c))).count d := by
      intro d hd
      have hne : d ≠ c := fun h => hc (h ▸ hd)
      rw [List.count_filter (a := d) (p := fun x : H => !(x == c)) (show (!(d == c)) = true by simp [hne])]
      exact lower d (List.mem_cons_of_mem c hd)
    have prev := ih hnd (E.filter (fun x => !(x == c))) lower'
    have hsum := count_add_filter_ne_length c E
    rw [List.length_cons, Nat.succ_mul]
    omega

theorem target_add_hue_quota_le_length {H : Type v} [BEq H] [LawfulBEq H]
    (target : H) (C : List H) (nd : C.Nodup) (ht : target ∉ C) (t : Nat) (E : List H)
    (lower : ∀ c ∈ C, t ≤ E.count c) :
    E.count target + C.length * t ≤ E.length := by
  have lower' : ∀ c ∈ C, t ≤ (E.filter (fun x => !(x == target))).count c := by
    intro c hc
    have hne : c ≠ target := fun h => ht (h ▸ hc)
    rw [List.count_filter (a := c) (p := fun x : H => !(x == target)) (show (!(c == target)) = true by simp [hne])]
    exact lower c hc
  have ht' := hue_quota_mul_le_length C nd t _ lower'
  have hsum := count_add_filter_ne_length target E
  omega

/-- Exact upper bound on target hue crossing edges between two unit rows. -/
theorem unit_crossing_cap {V : Type u} {H : Type v} [BEq H] [LawfulBEq H]
    (col : V → V → H) (r : Nat) (hr : 2 ≤ r) (target : H)
    (others : List H) (nd : others.Nodup) (hother : target ∉ others)
    (palette : others.length = r - 1)
    (cap : ∀ c ∈ others, IndependenceCap (fun x y => col x y = c) r)
    (R S : List V) (hR : R.length = r-1) (hS : S.length = r-1)
    (hnd : (R ++ S).Nodup)
    (rcl : R.Pairwise (fun x y => col x y = target))
    (scl : S.Pairwise (fun x y => col x y = target)) :
    (crossColors col R S).count target ≤ r - 1 := by
  have lower : ∀ c ∈ others, r-2 ≤ (crossColors col R S).count c := by
    intro c hc
    have hne : c ≠ target := fun e => hother (e ▸ hc)
    have floor := hue_edge_floor col c r (cap c hc) (R ++ S) hnd
    rw [orderedColors_count_append,
      orderedColors_count_eq_zero_of_clique col hne R rcl,
      orderedColors_count_eq_zero_of_clique col hne S scl,
      List.length_append, hR, hS] at floor
    omega
  have budget := target_add_hue_quota_le_length target others nd hother (r-2) _ lower
  rw [palette, length_crossColors, hR, hS] at budget
  have scale : (r-1)*(r-1) = (r-1)*(r-2)+(r-1) := by
    calc
      (r-1)*(r-1) = (r-1)*((r-2)+1) := congrArg (fun n => (r-1)*n) (by omega)
      _ = (r-1)*(r-2)+(r-1) := by rw [Nat.mul_add, Nat.mul_one]
  rw [scale] at budget
  omega

/-- Exact upper bound on the total target-hue degrees of three distinct
outsiders into one unit row. Assumes the actual full palette of other
hues and their inherited global independence cap. -/
theorem unit_triple_degree_cap {V : Type u} {H : Type v} [BEq H] [LawfulBEq H]
    (col : V → V → H) (r : Nat) (hr : 1 ≤ r) (target : H)
    (others : List H) (nd : others.Nodup) (hother : target ∉ others)
    (palette : others.length = r - 1)
    (cap : ∀ c ∈ others, IndependenceCap (fun x y => col x y = c) r)
    (R : List V) (x y z : V) (hR : R.length = r-1)
    (hnd : ([x,y,z] ++ R).Nodup)
    (rcl : R.Pairwise (fun a b => col a b = target)) :
    (R.map (col x)).count target + (R.map (col y)).count target +
      (R.map (col z)).count target ≤ r + 2 := by
  let X := ([x,y,z] : List V)
  let E := orderedColors col X ++ crossColors col X R
  have lower : ∀ c ∈ others, 2 ≤ E.count c := by
    intro c hc
    have hne : c ≠ target := fun e => hother (e ▸ hc)
    have floor := hue_edge_floor col c r (cap c hc) (X ++ R) hnd
    rw [orderedColors_count_append,
      orderedColors_count_eq_zero_of_clique col hne R rcl,
      List.length_append, hR] at floor
    have lx : X.length = 3 := rfl
    rw [lx] at floor
    simp only [E, List.count_append]
    omega
  have budget := target_add_hue_quota_le_length target others nd hother 2 E lower
  have eLen : E.length = 3 + 3*(r-1) := by
    have lx : X.length = 3 := rfl
    have le : (orderedColors col X).length = 3 := rfl
    simp [E, List.length_append, le, length_crossColors, lx, hR]
  rw [palette, eLen] at budget
  have hcount : (crossColors col X R).count target =
      (R.map (col x)).count target + (R.map (col y)).count target +
      (R.map (col z)).count target := by
    simp [X, crossColors]
    omega
  have final : E.count target = (orderedColors col X).count target +
      ((R.map (col x)).count target + (R.map (col y)).count target +
      (R.map (col z)).count target) := by
    simp only [E, List.count_append, hcount]
  rw [final] at budget
  omega

end Erdos617Geometry

#print axioms Erdos617Geometry.hue_edge_floor
#print axioms Erdos617Geometry.target_add_hue_quota_le_length
#print axioms Erdos617Geometry.unit_crossing_cap
#print axioms Erdos617Geometry.unit_triple_degree_cap
