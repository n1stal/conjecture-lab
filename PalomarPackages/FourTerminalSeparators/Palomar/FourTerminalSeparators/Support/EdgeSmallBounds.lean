module
public import Palomar.FourTerminalSeparators.Support.BarbellSharp
public import Palomar.FourTerminalSeparators.Support.SmallSharpWitnesses

@[expose] public section

namespace HakKozerenkoEdgeSeparator
open TriameterQ3Graph HakKozerenkoSeparatorGraph
universe u
variable {V : Type u} {G H : SimpleGraph V} {T : V→Prop}

theorem edgeCap_of_subgraph (incl : ∀ x y, G.adj x y→H.adj x y)
    {k : Nat} (cap : EdgeCap G T k) : EdgeCap H T k := by
  intro m F
  apply cap m
  refine {part := fun i x y => G.adj x y ∧ F.part i x y
          symm := fun i _ _ h => ⟨G.symm h.1,F.symm i _ _ h.2⟩
          valid := fun _ _ _ h => h.1
          disjoint := fun i j ne x y a b => F.disjoint i j ne x y a.2 b.2
          each := ?_}
  intro i
  obtain ⟨x,y,a,b,c⟩ := F.each i
  refine ⟨x,y,a,b,?_⟩
  intro n W
  let W' : Walk H x y n := ⟨W.point,W.first,W.last,fun j hj => incl _ _ (W.step j hj)⟩
  obtain ⟨j,hj,hit⟩ := c n W'
  exact ⟨j,hj,W.step j hj,hit⟩

theorem complete_edge_cap_one (complete : ∀ x y, x≠y→G.adj x y) : EdgeCap G T 1 := by
  classical
  intro m F
  apply Classical.byContradiction
  intro h
  let i : Fin m := ⟨0,by omega⟩
  let j : Fin m := ⟨1,by omega⟩
  have hne : i≠j := by intro e; have eq := congrArg Fin.val e; change 0=1 at eq; omega
  obtain ⟨s,t,_,_,st⟩ := F.each i
  obtain ⟨a,b,_,_,ab⟩ := F.each j
  let A := afterCut G (F.part i) (F.symm i)
  let B := afterCut G (F.part j) (F.symm j)
  let shore (x : V) := ∃ n, Nonempty (Walk A s x n)
  have hs : shore s := ⟨0,⟨Walk.trivial A s⟩⟩
  have ht : ¬shore t := by
    rintro ⟨n,⟨W⟩⟩
    obtain ⟨k,hk,hit⟩ := st n (forgetCut W)
    exact (W.step k hk).2 hit
  have toCross (x y : V) (hx : shore x) (hy : ¬shore y) : B.adj x y := by
    have nee : x≠y := fun e => hy (e ▸ hx)
    have E := complete x y nee
    have cut : F.part i x y := by
      apply Classical.byContradiction
      intro z
      obtain ⟨n,⟨W⟩⟩ := hx
      have step : A.adj x y := ⟨E,z⟩
      exact hy ⟨n+1,⟨W.concat (unitWalk step)⟩⟩
    exact ⟨E,fun no => F.disjoint i j hne x y cut no⟩
  have conn : ∃ n, Nonempty (Walk B a b n) := by
    by_cases ha : shore a <;> by_cases hb : shore b
    · exact ⟨2,⟨(unitWalk (toCross a t ha ht)).concat (unitWalk (B.symm (toCross b t hb ht)))⟩⟩
    · exact ⟨1,⟨unitWalk (toCross a b ha hb)⟩⟩
    · exact ⟨1,⟨unitWalk (B.symm (toCross b a hb ha))⟩⟩
    · exact ⟨2,⟨(unitWalk (B.symm (toCross s a hs ha))).concat (unitWalk (toCross s b hs hb))⟩⟩
  obtain ⟨n,⟨W⟩⟩ := conn
  obtain ⟨k,hk,hit⟩ := ab n (forgetCut W)
  exact (W.step k hk).2 hit

theorem edge_attains_six : EdgeAttains 6 := by
  refine ⟨4,model6.graph,model6.metric,0,1,2,3,?_,?_,?_⟩
  · constructor <;> decide
  · decide +kernel
  · apply complete_edge_cap_one
    have H : ∀ x y : Fin 4,x≠y→model6.edge x y=true := by decide +kernel
    exact H

theorem edge_attains_ten : EdgeAttains 10 := by
  have h := bar_attains .triangle .triangle 0 (by decide) (by decide)
  exact h

theorem base_two_triangles_cap : EdgeCap (barGraph 3 3 0)
    (markFourEdge (0 : Fin 5) (1 : Fin 5) (4 : Fin 5) (3 : Fin 5)) 2 := by
  have h := bar_edge_cap 3 3 0 (by decide) (by decide) (markFourEdge (0 : Fin 5) (1 : Fin 5) (4 : Fin 5) (3 : Fin 5)) (by
    intro x _
    have A : x.val≤(2 : Nat) ∨ 2≤x.val := by omega
    exact A)
  exact h

instance barGraphDecidable (p q L : Nat) (x y : Fin (barOrder p q L)) :
    Decidable ((barGraph p q L).adj x y) := by
  unfold barGraph stepBetween endpoints
  dsimp
  infer_instance

end HakKozerenkoEdgeSeparator

#print axioms HakKozerenkoEdgeSeparator.edge_attains_six
#print axioms HakKozerenkoEdgeSeparator.base_two_triangles_cap
