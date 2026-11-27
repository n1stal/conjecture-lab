module

public import Std
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-! The exact independent-set witnesses that supply the common-hole geometry
in the two-support model for Erdős #617. Uses only pinned Lean's Std.
A list satisfying Compatible pairwise has distinct vertices. No graph
adjacencies or cardinalities are delegated to an external solver. -/

namespace Erdos617Geometry

universe u

def Compatible {V : Type u} (adj : V → V → Prop) (x y : V) : Prop :=
  x ≠ y ∧ ¬adj x y

def IndependenceCap {V : Type u} (adj : V → V → Prop) (n : Nat) : Prop :=
  ∀ S : List V, S.Pairwise (Compatible adj) → S.length ≤ n

/-- A private vertex is its anchor, or sees that anchor, and is distinct
from and nonadjacent to every other anchor. -/
structure Private {V : Type u} (adj : V → V → Prop) (C : List V) (a u : V) : Prop where
  anchor_mem : a ∈ C
  own : u = a ∨ adj u a
  away : ∀ c ∈ C, c ≠ a → Compatible adj u c

/-- The exact two-support neighborhood on the anchor list. -/
structure Double {V : Type u} (adj : V → V → Prop) (C : List V) (b i x : V) : Prop where
  owner_mem : b ∈ C
  source_mem : i ∈ C
  distinct : b ≠ i
  outside : x ∉ C
  owner_adj : adj x b
  source_adj : adj x i
  away : ∀ c ∈ C, c ≠ b → c ≠ i → ¬adj x c

theorem Double.compatible_away {V : Type u} {adj : V → V → Prop} {C : List V}
    {b i x c : V} (hx : Double adj C b i x) (hc : c ∈ C)
    (hb : c ≠ b) (hi : c ≠ i) : Compatible adj x c :=
  ⟨fun e => hx.outside (e ▸ hc), hx.away c hc hb hi⟩

theorem Double.ne_private {V : Type u} {adj : V → V → Prop} {C : List V}
    {b i x a u : V} (hx : Double adj C b i x) (hu : Private adj C a u) : x ≠ u := by
  intro e
  subst u
  by_cases hb : b = a
  · have hi : i ≠ a := fun e => hx.distinct (hb.trans e.symm)
    exact (hu.away i hx.source_mem hi).2 hx.source_adj
  · exact (hu.away b hx.owner_mem hb).2 hx.owner_adj

theorem Private.ne_of_anchor_ne {V : Type u} {adj : V → V → Prop} {C : List V}
    {i j u v : V} (hu : Private adj C i u) (hv : Private adj C j v)
    (hij : i ≠ j) : u ≠ v := by
  intro e
  subst v
  rcases hu.own with hs | ha
  · exact (hv.away i hu.anchor_mem hij).1 hs
  · exact (hv.away i hu.anchor_mem hij).2 ha

def eraseAnchors {V : Type u} [BEq V] (C : List V) : List V → List V
  | [] => C
  | a :: D => eraseAnchors (C.erase a) D

/-- Removing a distinct list of specified anchors preserves independence,
removes exactly that many anchors, and removes all the named anchors. -/
theorem eraseAnchors_spec {V : Type u} [BEq V] [LawfulBEq V]
    (adj : V → V → Prop) (C D : List V)
    (hi : C.Pairwise (Compatible adj)) (hd : D.Nodup)
    (hsub : ∀ a ∈ D, a ∈ C) :
    (eraseAnchors C D).length + D.length = C.length ∧
    (eraseAnchors C D).Pairwise (Compatible adj) ∧
    ∀ a ∈ eraseAnchors C D, a ∈ C ∧ a ∉ D := by
  induction D generalizing C with
  | nil =>
    simp only [eraseAnchors, List.length_nil, Nat.add_zero, true_and]
    exact ⟨hi, fun _ ha => ⟨ha, List.not_mem_nil⟩⟩
  | cons d D ih =>
    have hdn := List.nodup_cons.mp hd
    have hin : d ∈ C := hsub d (by simp)
    have nd : C.Nodup := List.nodup_iff_pairwise_ne.mpr (hi.imp (fun h => h.1))
    have hsub' : ∀ a ∈ D, a ∈ C.erase d := by
      intro a ha
      have hn : a ≠ d := by
        intro he
        subst a
        exact hdn.1 ha
      apply (List.mem_erase_of_ne hn).mpr
      exact hsub a (List.mem_cons_of_mem d ha)
    obtain ⟨hlen, hrest, hmem⟩ := ih (C.erase d) (hi.erase d) hdn.2 hsub'
    have erlen := List.length_erase_of_mem hin
    have pos : 0 < C.length := by
      cases C with
      | nil => simp at hin
      | cons a l => simp
    change (eraseAnchors (C.erase d) D).length + (d :: D).length = C.length ∧
      (eraseAnchors (C.erase d) D).Pairwise (Compatible adj) ∧
      ∀ a ∈ eraseAnchors (C.erase d) D, a ∈ C ∧ a ∉ d :: D
    refine ⟨?_, hrest, ?_⟩
    · rw [List.length_cons]
      omega
    · intro a ha
      obtain ⟨hc, hnot⟩ := hmem a ha
      obtain ⟨hne, hc'⟩ := nd.mem_erase_iff.mp hc
      exact ⟨hc', fun h => (List.mem_cons.mp h).elim hne hnot⟩

/-- Exact anchor replacement: an independent replacement disjoint and
anticomplete to the retained anchors cannot be larger than the dropped list. -/
theorem replacement_length_le {V : Type u} [BEq V] [LawfulBEq V]
    (adj : V → V → Prop) (C D W : List V)
    (hi : C.Pairwise (Compatible adj)) (cap : IndependenceCap adj C.length)
    (hd : D.Nodup) (hsub : ∀ a ∈ D, a ∈ C)
    (hw : W.Pairwise (Compatible adj))
    (hcross : ∀ u ∈ W, ∀ a ∈ C, a ∉ D → Compatible adj u a) :
    W.length ≤ D.length := by
  obtain ⟨hlen, hind, hmem⟩ := eraseAnchors_spec adj C D hi hd hsub
  have allind : (W ++ eraseAnchors C D).Pairwise (Compatible adj) := by
    refine List.pairwise_append.mpr ⟨hw, hind, ?_⟩
    intro u hu a ha
    exact hcross u hu a (hmem a ha).1 (hmem a ha).2
  have bound := cap _ allind
  rw [List.length_append] at bound
  omega

/-- Same source: two missing-edge exceptions cannot have a common hole
in their source row. -/
theorem same_source_no_common_hole {V : Type u} [BEq V] [LawfulBEq V]
    {adj : V → V → Prop} {C : List V} {b i x y u : V}
    (hi : C.Pairwise (Compatible adj)) (cap : IndependenceCap adj C.length)
    (hx : Double adj C b i x) (hy : Double adj C b i y)
    (hxy : Compatible adj x y) (hu : Private adj C i u)
    (hxu : ¬adj x u) (hyu : ¬adj y u) : False := by
  have xu := hx.ne_private hu
  have yu := hy.ne_private hu
  have hw : ([x,y,u] : List V).Pairwise (Compatible adj) := by
    simp [List.pairwise_cons, hxy, show Compatible adj x u from ⟨xu, hxu⟩,
      show Compatible adj y u from ⟨yu, hyu⟩]
  have hd : ([b,i] : List V).Nodup := by simp [hx.distinct]
  have sub : ∀ a ∈ ([b,i] : List V), a ∈ C := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact hx.owner_mem
    · exact hx.source_mem
  have bound := replacement_length_le adj C [b,i] [x,y,u] hi cap hd sub hw (by
    intro z hz a ha hnot
    have hb : a ≠ b := fun e => hnot (e ▸ List.mem_cons_self)
    have ha_i : a ≠ i := fun e => hnot (e ▸ List.mem_cons_of_mem _ List.mem_cons_self)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · exact hx.compatible_away ha hb ha_i
    · exact hy.compatible_away ha hb ha_i
    · exact hu.away a ha ha_i)
  exact (by decide : ¬(3 : Nat) ≤ 2) bound

/-- Distinct sources: common holes in their two rows are completely joined
in the target hue. This is stated one pair of holes at a time. -/
theorem distinct_sources_common_holes_adjacent {V : Type u} [BEq V] [LawfulBEq V]
    {adj : V → V → Prop} {C : List V} {b i j x y u v : V}
    (hi : C.Pairwise (Compatible adj)) (cap : IndependenceCap adj C.length)
    (hx : Double adj C b i x) (hy : Double adj C b j y) (hij : i ≠ j)
    (hxy : Compatible adj x y) (hu : Private adj C i u) (hv : Private adj C j v)
    (hxu : ¬adj x u) (hyu : ¬adj y u) (hxv : ¬adj x v) (hyv : ¬adj y v) :
    adj u v := by
  classical
  apply Classical.byContradiction
  intro huv
  have xu := hx.ne_private hu
  have xv := hx.ne_private hv
  have yu := hy.ne_private hu
  have yv := hy.ne_private hv
  have uv := hu.ne_of_anchor_ne hv hij
  have hw : ([x,y,u,v] : List V).Pairwise (Compatible adj) := by
    simp [List.pairwise_cons, hxy, show Compatible adj x u from ⟨xu, hxu⟩,
      show Compatible adj x v from ⟨xv, hxv⟩,
      show Compatible adj y u from ⟨yu, hyu⟩,
      show Compatible adj y v from ⟨yv, hyv⟩, show Compatible adj u v from ⟨uv, huv⟩]
  have hd : ([b,i,j] : List V).Nodup := by simp [hx.distinct, hy.distinct, hij]
  have sub : ∀ a ∈ ([b,i,j] : List V), a ∈ C := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact hx.owner_mem
    · exact hx.source_mem
    · exact hy.source_mem
  have bound := replacement_length_le adj C [b,i,j] [x,y,u,v] hi cap hd sub hw (by
    intro z hz a ha hnot
    have hb : a ≠ b := fun e => hnot (e ▸ List.mem_cons_self)
    have ha_i : a ≠ i := fun e => hnot (e ▸ List.mem_cons_of_mem _ List.mem_cons_self)
    have ha_j : a ≠ j := fun e =>
      hnot (e ▸ List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact hx.compatible_away ha hb ha_i
    · exact hy.compatible_away ha hb ha_j
    · exact hu.away a ha ha_i
    · exact hv.away a ha ha_j)
  exact (by decide : ¬(4 : Nat) ≤ 3) bound

end Erdos617Geometry

#print axioms Erdos617Geometry.eraseAnchors_spec
#print axioms Erdos617Geometry.replacement_length_le
#print axioms Erdos617Geometry.same_source_no_common_hole
#print axioms Erdos617Geometry.distinct_sources_common_holes_adjacent
