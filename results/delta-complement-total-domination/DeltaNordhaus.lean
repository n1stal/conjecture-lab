module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith

@[expose] public section
namespace DeltaNordhaus
open Finset
open scoped BigOperators

def IsSymmetric {V : Type*} (A : V → V → Prop) := ∀ ⦃i j⦄, A i j → A j i
def IsLoopless {V : Type*} (A : V → V → Prop) := ∀ i, ¬ A i i

def OpenCovers {V : Type*} (A : V → V → Prop) (C D : Finset V) :=
  ∀ i ∈ C, ∃ j ∈ D, A i j

def NoIsolates {V : Type*} (A : V → V → Prop) := ∀ i, ∃ j, A i j

def compAdj {V : Type*} (A : V → V → Prop) (i j : V) := i ≠ j ∧ ¬ A i j

noncomputable def degree {V : Type*} [Fintype V] (A : V → V → Prop) (i : V) : Nat :=
  open Classical in (Finset.univ.filter (A i)).card

private theorem comp_symm {V : Type*} {A : V → V → Prop} (hs : IsSymmetric A) :
    IsSymmetric (compAdj A) :=
  fun _ _ h => ⟨h.1.symm,fun ha => h.2 (hs ha)⟩

private theorem comp_irrefl {V : Type*} {A : V → V → Prop} :
    IsLoopless (compAdj A) := fun _ h => h.1 rfl

private theorem degree_comp {V : Type*} [Fintype V] (A : V → V → Prop)
    (hi : IsLoopless A) (v : V) :
    degree A v + degree (compAdj A) v + 1 = Fintype.card V := by
  classical
  let U : Finset V := Finset.univ.erase v
  have hG : (U.filter (A v)) = Finset.univ.filter (A v) := by
    ext i
    simp only [U,Finset.mem_filter,Finset.mem_erase,Finset.mem_univ,and_true,true_and]
    exact ⟨And.right,fun h => ⟨fun e => hi v (e ▸ h),h⟩⟩
  have hC : U.filter (fun i => ¬ A v i) = Finset.univ.filter (compAdj A v) := by
    ext i
    simp [U,compAdj,ne_comm]
  rw [degree,degree,←hG,←hC,Finset.card_filter_add_card_filter_not]
  exact Finset.card_erase_add_one (Finset.mem_univ v)

private theorem root_cover {V : Type*} [Fintype V] (A : V → V → Prop)
    (hs : IsSymmetric A) (hN : NoIsolates A) (v : V) :
    ∃ D : Finset V, OpenCovers A Finset.univ D ∧ D.card+degree A v≤Fintype.card V+1 := by
  classical
  let B := Finset.univ.filter (fun w => ¬ A v w)
  let f (w : V) := Classical.choose (hN w)
  let D := insert v (B.image f)
  have hB : B.card+degree A v=Fintype.card V := by
    dsimp only [B,degree]
    rw [add_comm,Finset.card_filter_add_card_filter_not,Finset.card_univ]
  refine ⟨D,?_,?_⟩
  · intro w _
    by_cases h : A v w
    · exact ⟨v,Finset.mem_insert_self _ _,hs h⟩
    · have hm : w∈B := Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩
      exact ⟨f w,Finset.mem_insert_of_mem (Finset.mem_image_of_mem f hm),Classical.choose_spec (hN w)⟩
  · have hD : D.card ≤ B.card+1 := (Finset.card_insert_le _ _).trans
      (Nat.add_le_add_right Finset.card_image_le 1)
    omega

private theorem root_cover_save {V : Type*} [Fintype V] (A : V → V → Prop)
    (hs : IsSymmetric A) (hi : IsLoopless A) (hN : NoIsolates A)
    (v u w : V) (hv : v ≠ w) (hvu : A v u) (hwu : A w u) (hvw : ¬A v w) :
    ∃ D : Finset V, OpenCovers A Finset.univ D ∧ D.card+degree A v≤Fintype.card V := by
  classical
  let B := Finset.univ.filter (fun j => ¬ A v j)
  let f (j : V) := if j=v then u else Classical.choose (hN j)
  let D := insert v ((B.erase w).image f)
  have hvB : v∈B.erase w := Finset.mem_erase.mpr ⟨hv,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi v⟩⟩
  have huD : u∈D := by
    have h : f v ∈ D := Finset.mem_insert_of_mem (Finset.mem_image_of_mem f hvB)
    simpa [f] using h
  have hwB : w∈B := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hvw⟩
  have hB : B.card+degree A v=Fintype.card V := by
    dsimp only [B,degree]
    rw [add_comm,Finset.card_filter_add_card_filter_not,Finset.card_univ]
  refine ⟨D,?_,?_⟩
  · intro j _
    by_cases hj : A v j
    · exact ⟨v,Finset.mem_insert_self _ _,hs hj⟩
    by_cases hW : j=w
    · subst j; exact ⟨u,huD,hwu⟩
    have hm : j∈B.erase w := Finset.mem_erase.mpr ⟨hW,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩⟩
    refine ⟨f j,Finset.mem_insert_of_mem (Finset.mem_image_of_mem f hm),?_⟩
    by_cases hV : j=v
    · subst j; simpa [f] using hvu
    · simpa [f,hV] using Classical.choose_spec (hN j)
  · have hD : D.card ≤ (B.erase w).card+1 := (Finset.card_insert_le _ _).trans
      (Nat.add_le_add_right Finset.card_image_le 1)
    have hw := Finset.card_erase_add_one hwB
    omega

/-- Ordinary-complement total domination sum bound. This proof uses explicit neighborhoods,
not a black-box bound or an external axiom. -/
theorem ordinary_bound {V : Type*} [Fintype V] (A : V → V → Prop)
    (hs : IsSymmetric A) (hi : IsLoopless A) (hN : NoIsolates A)
    (hC : NoIsolates (compAdj A)) (hne : Nonempty V) :
    ∃ D E : Finset V, OpenCovers A Finset.univ D ∧
      OpenCovers (compAdj A) Finset.univ E ∧ D.card+E.card≤Fintype.card V+2 := by
  classical
  obtain ⟨v⟩ := hne
  obtain ⟨w,hvw⟩ := hC v
  obtain ⟨u,hvu⟩ := hN v
  by_cases hw : A w u
  · obtain ⟨D,hD,hd⟩ := root_cover_save A hs hi hN v u w hvw.1 hvu hw hvw.2
    obtain ⟨E,hE,he⟩ := root_cover (compAdj A) (comp_symm hs) hC v
    refine ⟨D,E,hD,hE,?_⟩
    have hc := degree_comp A hi v
    omega
  · have hvu' : v≠u := fun e => hi v (e.symm ▸ hvu)
    have huw' : u≠w := fun e => hvw.2 (e ▸ hvu)
    obtain ⟨E,hE,he⟩ := root_cover_save (compAdj A) (comp_symm hs) comp_irrefl hC
      v w u hvu' hvw ⟨huw',fun e => hw (hs e)⟩ (fun e => e.2 hvu)
    obtain ⟨D,hD,hd⟩ := root_cover A hs hN v
    refine ⟨D,E,hD,hE,?_⟩
    have hc := degree_comp A hi v
    omega

#print axioms ordinary_bound
end DeltaNordhaus
