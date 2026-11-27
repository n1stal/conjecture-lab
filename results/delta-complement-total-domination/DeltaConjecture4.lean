import DeltaClasses

namespace DeltaNordhaus
open Finset

noncomputable def deltaAdj {V : Type*} [Fintype V] (A : V → V → Prop) (i j : V) : Prop :=
  if degree A i=degree A j then compAdj A i j else A i j

noncomputable def degreeClassCount {V : Type*} [Fintype V] (A : V → V → Prop) : ℕ :=
  (Finset.univ.image (degree A)).card

theorem delta_adj_spec {V : Type*} [Fintype V] (A : V → V → Prop) (i j : V) :
    deltaAdj A i j ↔
      (i≠j ∧ degree A i=degree A j ∧ ¬ A i j) ∨
      (degree A i≠degree A j ∧ A i j) := by
  by_cases h : degree A i=degree A j <;> simp [deltaAdj,compAdj,h]

private theorem deltaSymm {V : Type*} [Fintype V] (A : V → V → Prop) (hs : IsSymmetric A) :
    IsSymmetric (deltaAdj A) := by
  intro i j h
  rcases (delta_adj_spec A i j).mp h with h | h
  · exact (delta_adj_spec A j i).mpr (Or.inl ⟨h.1.symm,h.2.1.symm,fun e => h.2.2 (hs e)⟩)
  · exact (delta_adj_spec A j i).mpr (Or.inr ⟨h.1.symm,hs h.2⟩)

private theorem coveringSizeExists {V : Type*} [Fintype V] (A : V → V → Prop)
    (h : NoIsolates A) :
    ∃ s : ℕ, ∃ D : Finset V, OpenCovers A Finset.univ D ∧ D.card=s := by
  refine ⟨Fintype.card V,Finset.univ,?_,Finset.card_univ⟩
  intro i _
  obtain ⟨j,hj⟩ := h i
  exact ⟨j,Finset.mem_univ _,hj⟩

/-- The minimum cardinality of a set giving every vertex a selected neighbor. -/
noncomputable def totalDominationNumber {V : Type*} [Fintype V] (A : V → V → Prop)
    (h : NoIsolates A) : ℕ := open Classical in Nat.find (coveringSizeExists A h)

theorem minimumTotalDominationRealized {V : Type*} [Fintype V] (A : V → V → Prop)
    (h : NoIsolates A) :
    ∃ D : Finset V, OpenCovers A Finset.univ D ∧ D.card=totalDominationNumber A h := by
  classical
  exact Nat.find_spec (coveringSizeExists A h)

theorem minimumTotalDomination_le {V : Type*} [Fintype V] (A : V → V → Prop)
    (h : NoIsolates A) (D : Finset V) (hD : OpenCovers A Finset.univ D) :
    totalDominationNumber A h≤D.card := by
  classical
  exact Nat.find_min' (coveringSizeExists A h) ⟨D,hD,rfl⟩

/-- Conjecture 4 (Mathematics 14(11), 1797, 2026) for every finite simple
graph whose graph and δ-complement are both without isolated vertices. -/
theorem conjecture4 {V : Type*} [Fintype V] (A : V → V → Prop)
    (hs : IsSymmetric A) (hi : IsLoopless A)
    (hA : NoIsolates A) (hB : NoIsolates (deltaAdj A)) :
    totalDominationNumber A hA + totalDominationNumber (deltaAdj A) hB ≤
      Fintype.card V + 2 * degreeClassCount A := by
  have hf : ∀ i j, degree A i=degree A j → (deltaAdj A i j ↔ compAdj A i j) := by
    intro i j hij
    simp [deltaAdj,hij]
  obtain ⟨D,E,hD,hE,hC⟩ := partition_total_domination A (deltaAdj A) (degree A)
    hs hi hA (deltaSymm A hs) hB hf
  exact (Nat.add_le_add (minimumTotalDomination_le A hA D hD)
    (minimumTotalDomination_le (deltaAdj A) hB E hE)).trans hC

#print axioms conjecture4
end DeltaNordhaus
