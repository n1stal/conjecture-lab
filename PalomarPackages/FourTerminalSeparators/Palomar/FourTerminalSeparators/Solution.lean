module

public import Palomar.FourTerminalSeparators.Support.SmallSharpWitnesses
public import Palomar.FourTerminalSeparators.Support.EdgeSmallDenseWitnesses

@[expose] public section

namespace HakKozerenkoSeparatorGraph
open TriameterQ3Graph

theorem vertex_attains_all (S : Nat) (hS : 6≤S) : VertexAttains S := by
  by_cases big : 16≤S
  · let q := (S-7)/4
    let j := 4*q+10-S
    have j3 : j≤3 := by dsimp [j,q]; omega
    have jq : j≤q := by dsimp [j,q]; omega
    have key : 4*q+10-j=S := by dsimp [j,q]; omega
    rw [←key]
    exact path_attains_vertex q j jq j3
  · have low : S=6 ∨ S=7 ∨ S=8 ∨ S=9 ∨ S=10 ∨ S=11 ∨
      S=12 ∨ S=13 ∨ S=14 ∨ S=15 := by omega
    rcases low with e|e|e|e|e|e|e|e|e|e <;> subst S
    · exact low_attains_6
    · exact low_attains_7
    · exact low_attains_8
    · exact low_attains_9
    · exact low_attains_10
    · exact low_attains_11
    · exact low_attains_12
    · exact low_attains_13
    · exact low_attains_14
    · exact low_attains_15

/-- Given any natural terminal sum at least six, the exact universal
minimum number of disjoint four-terminal vertex separators is
(S-7)/4 in natural arithmetic, equivalently max(0, ceil((S-10)/4)).
The first conjunct gives a family in every actual finite graph with
that sum, and the second supplies an actual realization whose every
family has size at most the displayed number. -/
theorem sharp_four_vertex_separator_bound (S : Nat) (hS : 6≤S) :
    (∀ (n : Nat) (G : SimpleGraph (Fin n)) (M : ShortestDistances G)
      (a b c d : Fin n), FourApart a b c d → fourSum M a b c d=S →
       Nonempty (VertexFamily G (markFour a b c d) ((S-7)/4))) ∧
    VertexAttains S := by
  refine ⟨?_,vertex_attains_all S hS⟩
  intro n G M a b c d neq score
  have h := four_vertex_separators M a b c d neq
  rwa [score] at h

end HakKozerenkoSeparatorGraph

#print axioms HakKozerenkoSeparatorGraph.vertex_attains_all
#print axioms HakKozerenkoSeparatorGraph.sharp_four_vertex_separator_bound

namespace HakKozerenkoEdgeSeparator
open TriameterQ3Graph HakKozerenkoSeparatorGraph

theorem edge_attains_all (S : Nat) (hS : 6≤S) : EdgeAttains S := by
  by_cases h : 11≤S
  · exact bar_large_attains S h
  · have low : S=6 ∨ S=7 ∨ S=8 ∨ S=9 ∨ S=10 := by omega
    rcases low with e|e|e|e|e <;> subst S
    · exact edge_attains_six
    · exact edge_attains_7
    · exact edge_attains_8
    · exact edge_attains_9
    · exact edge_attains_ten

/-- Exact universal minimum for families of pairwise edge-disjoint edge
separators of four distinct terminals, given the sum S of six
graph distances. Every S≥6 occurs in a finite connected simple graph. -/
theorem sharp_four_edge_separator_bound (S : Nat) (hS : 6≤S) :
    (∀ (n : Nat) (G : SimpleGraph (Fin n)) (M : ShortestDistances G)
      (a b c d : Fin n), FourApart a b c d → fourSumEdge M a b c d=S →
        Nonempty (EdgeFamily G (markFourEdge a b c d) ((S+1)/4))) ∧
    EdgeAttains S := by
  refine ⟨?_,edge_attains_all S hS⟩
  intro n G M a b c d _ score
  have h := four_edge_separators M a b c d
  rwa [score] at h

end HakKozerenkoEdgeSeparator

#print axioms HakKozerenkoEdgeSeparator.edge_attains_all
#print axioms HakKozerenkoEdgeSeparator.sharp_four_edge_separator_bound
