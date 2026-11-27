module

public import Palomar.Erdos617PairStarDouble.Support.ColoredCaps
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-! Adapter from a balanced complete-graph coloring with an exact
two-support anchor model into the numerical long-hole hypotheses.
The component verification is independent of any Mathlib cache. -/

namespace Erdos617Geometry

universe u v

def Balanced {V : Type u} {H : Type v} [BEq H]
    (col : V → V → H) (r : Nat) : Prop :=
  ∀ W : List V, W.Nodup → W.length = r+1 →
    ∀ c : H, 0 < (orderedColors col W).count c

theorem orderedColors_zero_of_indep {V : Type u} {H : Type v}
    [BEq H] [LawfulBEq H] (col : V → V → H) (c : H) (W : List V)
    (hi : W.Pairwise (Compatible (fun x y => col x y = c))) :
    (orderedColors col W).count c = 0 := by
  induction W with
  | nil => simp [orderedColors]
  | cons x W ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hi
    have hn : c ∉ W.map (col x) := by
      intro h
      obtain ⟨y, hy, hcol⟩ := List.mem_map.mp h
      exact (hhead y hy).2 hcol
    simp [orderedColors, List.count_eq_zero_of_not_mem hn, ih htail]

theorem balanced_independenceCap {V : Type u} {H : Type v}
    [BEq H] [LawfulBEq H] (col : V → V → H) (r : Nat)
    (bal : Balanced col r) (c : H) :
    IndependenceCap (fun x y => col x y = c) r := by
  intro W hW
  apply Classical.byContradiction
  intro hbad
  let T := W.take (r+1)
  have hT : T.Pairwise (Compatible (fun x y => col x y = c)) :=
    hW.sublist (List.take_sublist _ _)
  have len : T.length = r+1 := by
    rw [List.length_take, Nat.min_eq_left]
    omega
  have nd : T.Nodup := List.nodup_iff_pairwise_ne.mpr (hT.imp (fun h => h.1))
  have yes := bal T nd len c
  have no := orderedColors_zero_of_indep col c T hT
  omega

def holesList {V : Type u} {H : Type v} [BEq H]
    (col : V → V → H) (c : H) (R : List V) (x y : V) : List V :=
  R.filter (fun u => !(col x u == c) && !(col y u == c))

theorem mem_holesList {V : Type u} {H : Type v} [BEq H] [LawfulBEq H]
    (col : V → V → H) (c : H) (R : List V) (x y u : V) :
    u ∈ holesList col c R x y ↔ u ∈ R ∧ col x u ≠ c ∧ col y u ≠ c := by
  simp [holesList, List.mem_filter]

theorem holesList_sublist {V : Type u} {H : Type v} [BEq H]
    (col : V → V → H) (c : H) (R : List V) (x y : V) :
    (holesList col c R x y).Sublist R :=
  List.filter_sublist

theorem crossColors_sublist {V : Type u} {H : Type v}
    (col : V → V → H) {R R' S S' : List V}
    (hR : R.Sublist R') (hS : S.Sublist S') :
    (crossColors col R S).Sublist (crossColors col R' S') := by
  induction hR with
  | slnil => exact List.Sublist.slnil
  | cons a _ ih =>
    exact (List.nil_sublist _).append ih
  | cons_cons a _ ih =>
    exact (hS.map (col a)).append ih

theorem mul_len_le_cross_count_of_complete {V : Type u} {H : Type v}
    [BEq H] [LawfulBEq H] (col : V → V → H) (c : H)
    {U W R S : List V} (hU : U.Sublist R) (hW : W.Sublist S)
    (complete : ∀ u ∈ U, ∀ w ∈ W, col u w = c) :
    U.length*W.length ≤ (crossColors col R S).count c := by
  have full : (crossColors col U W).count c = (crossColors col U W).length := by
    apply List.count_eq_length.mpr
    intro t ht
    obtain ⟨u, hu, ht'⟩ := List.mem_flatMap.mp ht
    obtain ⟨w, hw, htw⟩ := List.mem_map.mp ht'
    exact (complete u hu w hw).symm.trans htw
  rw [← length_crossColors col U W, ← full]
  exact (crossColors_sublist col hU hW).count_le c

/-- Represents precisely the portion of the two-supported anchor core used
by the charging step. All exceptions use a fixed receiver b and their own
unit source s(x). The smaller core's independence cap is explicit. -/
structure UnitSourceSystem {V : Type u} {H : Type v} [BEq H]
    (col : V → V → H) (t : H) (r : Nat) where
  C : List V
  b : V
  J : List V
  s : V → V
  P : V → List V
  anchors : C.Pairwise (Compatible (fun x y => col x y = t))
  targetCap : IndependenceCap (fun x y => col x y = t) C.length
  support : ∀ x ∈ J, Double (fun x y => col x y = t) C b (s x) x
  privateRow : ∀ x ∈ J, ∀ a ∈ P (s x), Private (fun x y => col x y = t) C (s x) a
  rowNodup : ∀ x ∈ J, (P (s x)).Nodup
  rowClique : ∀ x ∈ J, (P (s x)).Pairwise (fun a b => col a b = t)
  unitSize : ∀ x ∈ J, (P (s x)).length = r-1

/-- Exact product hypothesis of the previously Lean-verified charging
theorem, derived here from source coloring and support geometry. -/
theorem source_supplies_productCap {V : Type u} {H : Type v}
    [BEq V] [LawfulBEq V] [BEq H] [LawfulBEq H]
    (col : V → V → H) (r : Nat) (hr : 2 ≤ r) (t : H)
    (others : List H) (nd : others.Nodup) (hother : t ∉ others)
    (palette : others.length = r-1) (bal : Balanced col r)
    (M : UnitSourceSystem col t r) {x y : V} (hx : x ∈ M.J) (hy : y ∈ M.J)
    (miss : Compatible (fun a b => col a b = t) x y) :
    (holesList col t (M.P (M.s x)) x y).length *
      (holesList col t (M.P (M.s y)) y x).length ≤ r-1 := by
  by_cases hs : M.s x = M.s y
  · let L := holesList col t (M.P (M.s x)) x y
    have no : L = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro u hu
      obtain ⟨hr, hxu, hyu⟩ := (mem_holesList _ _ _ _ _ _).mp hu
      have hy' := M.support y hy
      rw [← hs] at hy'
      exact same_source_no_common_hole M.anchors M.targetCap (M.support x hx) hy'
        miss (M.privateRow x hx u hr) hxu hyu
    change L.length * _ ≤ _
    rw [no, List.length_nil, Nat.zero_mul]
    exact Nat.zero_le _
  · have hd : (M.P (M.s x) ++ M.P (M.s y)).Nodup := by
      rw [List.nodup_iff_pairwise_ne, List.pairwise_append]
      refine ⟨List.nodup_iff_pairwise_ne.mp (M.rowNodup x hx),
        List.nodup_iff_pairwise_ne.mp (M.rowNodup y hy), ?_⟩
      intro u hu v hv
      exact (M.privateRow x hx u hu).ne_of_anchor_ne (M.privateRow y hy v hv) hs
    have crossing := unit_crossing_cap col r hr t others nd hother palette
      (fun c _ => balanced_independenceCap col r bal c)
      (M.P (M.s x)) (M.P (M.s y)) (M.unitSize x hx) (M.unitSize y hy)
      hd (M.rowClique x hx) (M.rowClique y hy)
    refine Nat.le_trans (mul_len_le_cross_count_of_complete col t
      (holesList_sublist col t (M.P (M.s x)) x y)
      (holesList_sublist col t (M.P (M.s y)) y x) ?_) crossing
    intro u hu v hv
    obtain ⟨hur, hxu, hyu⟩ := (mem_holesList _ _ _ _ _ _).mp hu
    obtain ⟨hvr, hyv, hxv⟩ := (mem_holesList _ _ _ _ _ _).mp hv
    exact distinct_sources_common_holes_adjacent (adj := fun a b => col a b = t) M.anchors M.targetCap
      (M.support x hx) (M.support y hy) hs miss
      (M.privateRow x hx u hur) (M.privateRow y hy v hvr) hxu hyu hxv hyv

/-- Exact triple hypothesis of the charging theorem, with disjointness of
the outsiders from the row derived from their genuine supports. -/
theorem source_supplies_tripleCap {V : Type u} {H : Type v}
    [BEq H] [LawfulBEq H]
    (col : V → V → H) (r : Nat) (hr : 1 ≤ r) (t : H)
    (others : List H) (nd : others.Nodup) (hother : t ∉ others)
    (palette : others.length = r-1) (bal : Balanced col r)
    (M : UnitSourceSystem col t r) {x y z : V}
    (hx : x ∈ M.J) (hy : y ∈ M.J) (hz : z ∈ M.J)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ((M.P (M.s x)).map (col x)).count t +
      ((M.P (M.s x)).map (col y)).count t +
      ((M.P (M.s x)).map (col z)).count t ≤ r+2 := by
  let R := M.P (M.s x)
  have hd : ([x,y,z] ++ R).Nodup := by
    rw [List.nodup_iff_pairwise_ne, List.pairwise_append]
    refine ⟨?_, List.nodup_iff_pairwise_ne.mp (M.rowNodup x hx), ?_⟩
    · simp [List.pairwise_cons, hxy, hxz, hyz]
    · intro a ha u hu
      have hup := M.privateRow x hx u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · exact (M.support _ hx).ne_private hup
      · exact (M.support _ hy).ne_private hup
      · exact (M.support _ hz).ne_private hup
  exact unit_triple_degree_cap col r hr t others nd hother palette
    (fun c _ => balanced_independenceCap col r bal c)
    R x y z (M.unitSize x hx) hd (M.rowClique x hx)

def exceptPalette {r : Nat} (t : Fin r) : List (Fin r) :=
  (List.finRange r).erase t

theorem exceptPalette_specs {r : Nat} (t : Fin r) :
    (exceptPalette t).Nodup ∧ t ∉ exceptPalette t ∧
      (exceptPalette t).length = r-1 := by
  have hn := List.nodup_finRange r
  refine ⟨hn.erase t, hn.not_mem_erase, ?_⟩
  simp [exceptPalette]

/-- Source specialization to the exact palette of r hues. -/
theorem source_fin_productCap {V : Type u}
    [BEq V] [LawfulBEq V] (r : Nat) (hr : 2 ≤ r) (t : Fin r)
    (col : V → V → Fin r) (bal : Balanced col r)
    (M : UnitSourceSystem col t r) {x y : V} (hx : x ∈ M.J) (hy : y ∈ M.J)
    (miss : Compatible (fun a b => col a b = t) x y) :
    (holesList col t (M.P (M.s x)) x y).length *
      (holesList col t (M.P (M.s y)) y x).length ≤ r-1 := by
  obtain ⟨nd, ne, len⟩ := exceptPalette_specs t
  exact source_supplies_productCap col r hr t (exceptPalette t) nd ne len bal M hx hy miss

theorem source_fin_tripleCap {V : Type u}
    (r : Nat) (hr : 1 ≤ r) (t : Fin r) (col : V → V → Fin r)
    (bal : Balanced col r) (M : UnitSourceSystem col t r) {x y z : V}
    (hx : x ∈ M.J) (hy : y ∈ M.J) (hz : z ∈ M.J)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ((M.P (M.s x)).map (col x)).count t +
      ((M.P (M.s x)).map (col y)).count t +
      ((M.P (M.s x)).map (col z)).count t ≤ r+2 := by
  obtain ⟨nd, ne, len⟩ := exceptPalette_specs t
  exact source_supplies_tripleCap col r hr t (exceptPalette t) nd ne len bal M hx hy hz
    hxy hxz hyz

/-- The starting anchor model really does have one or two supports in
each nonanchor hue. This is the first step, before making a smaller
overloaded core and recognizing its unit rows. -/
theorem initial_one_or_two_supports {V : Type u} (r : Nat) (hr : 2 ≤ r)
    (base t : Fin r) (hnt : t ≠ base) (col : V → V → Fin r)
    (bal : Balanced col r) (C : List V) (hC : C.Nodup)
    (len : C.length = r) (clique : C.Pairwise (fun x y => col x y = base))
    {x : V} (out : x ∉ C) :
    1 ≤ (C.map (col x)).count t ∧ (C.map (col x)).count t ≤ 2 := by
  let E := C.map (col x)
  let P := exceptPalette base
  have hcl : (x :: C).Nodup := List.nodup_cons.mpr ⟨out,hC⟩
  have hlen : (x :: C).length = r+1 := by simp [len]
  have all : ∀ c ∈ P, 1 ≤ E.count c := by
    intro c hc
    have hcne : c ≠ base :=
      ((List.nodup_finRange r).mem_erase_iff.mp hc).1
    have yes := bal (x :: C) hcl hlen c
    simpa [orderedColors, orderedColors_count_eq_zero_of_clique col hcne C clique, E] using yes
  obtain ⟨nd, _, plen⟩ := exceptPalette_specs base
  have ht : t ∈ P := (List.mem_erase_of_ne hnt).mpr (List.mem_finRange t)
  have lo := all t ht
  let Q := P.erase t
  have ndQ : Q.Nodup := nd.erase t
  have notQ : t ∉ Q := nd.not_mem_erase
  have qlen : Q.length = r-2 := by
    have h := List.length_erase_of_mem ht
    change (P.erase t).length = _
    rw [h, plen]
    omega
  have tot := target_add_hue_quota_le_length t Q ndQ notQ 1 E
    (fun c hc => all c (List.erase_subset hc))
  rw [qlen, Nat.mul_one] at tot
  have eLen : E.length = r := by simp [E, len]
  rw [eLen] at tot
  change 1 ≤ E.count t ∧ E.count t ≤ 2
  exact ⟨lo, by omega⟩

end Erdos617Geometry

#print axioms Erdos617Geometry.balanced_independenceCap
#print axioms Erdos617Geometry.source_supplies_productCap
#print axioms Erdos617Geometry.source_supplies_tripleCap

#print axioms Erdos617Geometry.source_fin_productCap
#print axioms Erdos617Geometry.source_fin_tripleCap
#print axioms Erdos617Geometry.initial_one_or_two_supports
