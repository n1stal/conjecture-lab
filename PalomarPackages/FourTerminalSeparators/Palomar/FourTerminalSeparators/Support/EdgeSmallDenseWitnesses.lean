module

public import Palomar.FourTerminalSeparators.Support.EdgeSmallBounds

@[expose] public section

namespace HakKozerenkoEdgeSeparator
open TriameterQ3Graph HakKozerenkoSeparatorGraph

def edgeModel7 : SmallGraphData 5 where
  edge := boolEdge #v[30,13,27,23,13]
  dist := rowTable #v[#v[0,1,1,1,1],#v[1,0,1,1,2],#v[1,1,0,1,1],#v[1,1,1,0,1],#v[1,2,1,1,0]]
  next := fun a b => ⟨rowTable #v[#v[0,1,2,3,4],#v[0,1,2,3,0],#v[0,1,2,3,4],#v[0,1,2,3,4],#v[0,0,2,3,4]] a b, by
    have H : ∀ (a b : Fin 5), rowTable #v[#v[0,1,2,3,4],#v[0,1,2,3,0],#v[0,1,2,3,4],#v[0,1,2,3,4],#v[0,0,2,3,4]] a b < 5 := by decide +kernel
    exact H a b⟩
  symm := by decide +kernel
  noloop := by decide +kernel
  zero := by decide +kernel
  triangle := by decide +kernel
  edgeBound := by decide +kernel
  nextOK := by decide +kernel

theorem edge_attains_7 : EdgeAttains 7 := by
  refine ⟨5,edgeModel7.graph,edgeModel7.metric,0,1,4,3,?_,?_,?_⟩
  · constructor <;> decide
  · decide +kernel
  · apply edgeCap_of_subgraph ?_ base_two_triangles_cap
    have H : ∀ x y : Fin 5,
        ((x.val+1=y.val ∨ y.val+1=x.val) ∨
          ((x.val=0 ∧ y.val=2) ∨ (x.val=2 ∧ y.val=0)) ∨
          ((x.val=2 ∧ y.val=4) ∨ (x.val=4 ∧ y.val=2))) →
        edgeModel7.edge x y=true := by decide +kernel
    intro x y E
    rcases E with E|⟨_,E⟩|⟨_,E⟩
    · exact H x y (Or.inl E)
    · exact H x y (Or.inr (Or.inl E))
    · exact H x y (Or.inr (Or.inr E))


def edgeModel8 : SmallGraphData 5 where
  edge := boolEdge #v[30,5,27,21,13]
  dist := rowTable #v[#v[0,1,1,1,1],#v[1,0,1,2,2],#v[1,1,0,1,1],#v[1,2,1,0,1],#v[1,2,1,1,0]]
  next := fun a b => ⟨rowTable #v[#v[0,1,2,3,4],#v[0,1,2,0,0],#v[0,1,2,3,4],#v[0,0,2,3,4],#v[0,0,2,3,4]] a b, by
    have H : ∀ (a b : Fin 5), rowTable #v[#v[0,1,2,3,4],#v[0,1,2,0,0],#v[0,1,2,3,4],#v[0,0,2,3,4],#v[0,0,2,3,4]] a b < 5 := by decide +kernel
    exact H a b⟩
  symm := by decide +kernel
  noloop := by decide +kernel
  zero := by decide +kernel
  triangle := by decide +kernel
  edgeBound := by decide +kernel
  nextOK := by decide +kernel

theorem edge_attains_8 : EdgeAttains 8 := by
  refine ⟨5,edgeModel8.graph,edgeModel8.metric,0,1,4,3,?_,?_,?_⟩
  · constructor <;> decide
  · decide +kernel
  · apply edgeCap_of_subgraph ?_ base_two_triangles_cap
    have H : ∀ x y : Fin 5,
        ((x.val+1=y.val ∨ y.val+1=x.val) ∨
          ((x.val=0 ∧ y.val=2) ∨ (x.val=2 ∧ y.val=0)) ∨
          ((x.val=2 ∧ y.val=4) ∨ (x.val=4 ∧ y.val=2))) →
        edgeModel8.edge x y=true := by decide +kernel
    intro x y E
    rcases E with E|⟨_,E⟩|⟨_,E⟩
    · exact H x y (Or.inl E)
    · exact H x y (Or.inr (Or.inl E))
    · exact H x y (Or.inr (Or.inr E))


def edgeModel9 : SmallGraphData 5 where
  edge := boolEdge #v[14,5,27,21,12]
  dist := rowTable #v[#v[0,1,1,1,2],#v[1,0,1,2,2],#v[1,1,0,1,1],#v[1,2,1,0,1],#v[2,2,1,1,0]]
  next := fun a b => ⟨rowTable #v[#v[0,1,2,3,2],#v[0,1,2,0,2],#v[0,1,2,3,4],#v[0,0,2,3,4],#v[2,2,2,3,4]] a b, by
    have H : ∀ (a b : Fin 5), rowTable #v[#v[0,1,2,3,2],#v[0,1,2,0,2],#v[0,1,2,3,4],#v[0,0,2,3,4],#v[2,2,2,3,4]] a b < 5 := by decide +kernel
    exact H a b⟩
  symm := by decide +kernel
  noloop := by decide +kernel
  zero := by decide +kernel
  triangle := by decide +kernel
  edgeBound := by decide +kernel
  nextOK := by decide +kernel

theorem edge_attains_9 : EdgeAttains 9 := by
  refine ⟨5,edgeModel9.graph,edgeModel9.metric,0,1,4,3,?_,?_,?_⟩
  · constructor <;> decide
  · decide +kernel
  · apply edgeCap_of_subgraph ?_ base_two_triangles_cap
    have H : ∀ x y : Fin 5,
        ((x.val+1=y.val ∨ y.val+1=x.val) ∨
          ((x.val=0 ∧ y.val=2) ∨ (x.val=2 ∧ y.val=0)) ∨
          ((x.val=2 ∧ y.val=4) ∨ (x.val=4 ∧ y.val=2))) →
        edgeModel9.edge x y=true := by decide +kernel
    intro x y E
    rcases E with E|⟨_,E⟩|⟨_,E⟩
    · exact H x y (Or.inl E)
    · exact H x y (Or.inr (Or.inl E))
    · exact H x y (Or.inr (Or.inr E))

end HakKozerenkoEdgeSeparator
