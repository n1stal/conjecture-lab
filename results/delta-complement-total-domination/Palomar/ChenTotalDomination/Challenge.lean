module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Nat.Find

@[expose] public section

namespace DeltaNordhaus

def IsSymmetric {V : Type*} (A : V → V → Prop) := ∀ ⦃i j⦄, A i j → A j i
def IsLoopless {V : Type*} (A : V → V → Prop) := ∀ i, ¬ A i i

def OpenCovers {V : Type*} (A : V → V → Prop) (C D : Finset V) :=
  ∀ i ∈ C, ∃ j ∈ D, A i j

def NoIsolates {V : Type*} (A : V → V → Prop) := ∀ i, ∃ j, A i j

def compAdj {V : Type*} (A : V → V → Prop) (i j : V) := i ≠ j ∧ ¬ A i j

noncomputable def degree {V : Type*} [Fintype V] (A : V → V → Prop) (i : V) : Nat :=
  open Classical in (Finset.univ.filter (A i)).card

noncomputable def deltaAdj {V : Type*} [Fintype V] (A : V → V → Prop) (i j : V) : Prop :=
  if degree A i=degree A j then compAdj A i j else A i j

noncomputable def degreeClassCount {V : Type*} [Fintype V] (A : V → V → Prop) : ℕ :=
  (Finset.univ.image (degree A)).card

theorem coveringSizeExists {V : Type*} [Fintype V] (A : V → V → Prop)
    (h : NoIsolates A) :
    ∃ s : ℕ, ∃ D : Finset V, OpenCovers A Finset.univ D ∧ D.card=s := by
  refine ⟨Fintype.card V,Finset.univ,?_,Finset.card_univ⟩
  intro i _
  obtain ⟨j,hj⟩ := h i
  exact ⟨j,Finset.mem_univ _,hj⟩

/-- The minimum cardinality of a set giving every vertex a selected neighbor. -/
noncomputable def totalDominationNumber {V : Type*} [Fintype V] (A : V → V → Prop)
    (h : NoIsolates A) : ℕ := open Classical in Nat.find (coveringSizeExists A h)

theorem conjecture4 {V : Type*} [Fintype V] (A : V → V → Prop)
    (hs : IsSymmetric A) (hi : IsLoopless A)
    (hA : NoIsolates A) (hB : NoIsolates (deltaAdj A)) :
    totalDominationNumber A hA + totalDominationNumber (deltaAdj A) hB ≤
      Fintype.card V + 2 * degreeClassCount A := by
  sorry

end DeltaNordhaus
