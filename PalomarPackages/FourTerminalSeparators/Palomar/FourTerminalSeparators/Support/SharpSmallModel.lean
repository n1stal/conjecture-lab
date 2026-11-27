module

public import Palomar.FourTerminalSeparators.Support.FourSharpPath

@[expose] public section

/-! Small actual shortest-path certificates. A successful finite check
does not merely assert a proposed terminal distance matrix: the
geodesic and minimality checks construct actual walks. -/
namespace HakKozerenkoSeparatorGraph
open TriameterQ3Graph

def rowTable {n : Nat} (T : Vector (Vector Nat n) n) (a b : Fin n) : Nat :=
  (T.get a).get b

def boolEdge {n : Nat} (rows : Vector Nat n) (a b : Fin n) : Bool :=
  (rows.get a).testBit b.val

structure SmallGraphData (n : Nat) where
  edge : Fin n → Fin n → Bool
  dist : Fin n → Fin n → Nat
  next : Fin n → Fin n → Fin n
  symm : ∀ a b, edge a b=edge b a
  noloop : ∀ a, edge a a=false
  zero : ∀ a b, dist a b=0 ↔ a=b
  triangle : ∀ a b c, dist a c≤dist a b+dist b c
  edgeBound : ∀ a b, edge a b=true → dist a b≤1
  nextOK : ∀ a b, a≠b → edge a (next a b)=true ∧ dist (next a b) b+1=dist a b

def SmallGraphData.graph {n : Nat} (P : SmallGraphData n) : SimpleGraph (Fin n) where
  adj a b := P.edge a b=true
  symm := by intro a b h; change P.edge a b=true at h; rwa [P.symm] at h
  loopless := by intro a h; change P.edge a a=true at h; simp [P.noloop] at h

theorem SmallGraphData.findWalk {n : Nat} (P : SmallGraphData n) (a b : Fin n) :
    Nonempty (Walk P.graph a b (P.dist a b)) := by
  have byD (l : Nat) : ∀ u v : Fin n, P.dist u v=l →
      Nonempty (Walk P.graph u v (P.dist u v)) := by
    induction l using Nat.strongRecOn with
    | ind l ih =>
      intro u v eq
      by_cases s : u=v
      · subst v
        have hz := (P.zero u u).mpr rfl
        rw [hz]
        exact ⟨Walk.trivial P.graph u⟩
      · obtain ⟨e,he⟩ := P.nextOK u v s
        have hlt : P.dist (P.next u v) v<l := by omega
        obtain ⟨W⟩ := ih _ hlt (P.next u v) v rfl
        have J := (unitWalk (G := P.graph) e).concat W
        have h : P.dist u v=1+P.dist (P.next u v) v := by omega
        rw [h]
        exact ⟨J⟩
  exact byD _ a b rfl

theorem SmallGraphData.boundWalk {n : Nat} (P : SmallGraphData n) (a b : Fin n)
    (k : Nat) (W : Walk P.graph a b k) : P.dist a b≤k := by
  have up (i : Nat) (hi : i≤k) : P.dist a (W.point i)≤i := by
    induction i with
    | zero =>
      rw [W.first,(P.zero a a).mpr rfl]
      exact Nat.le_refl _
    | succ i ih =>
      have h := ih (by omega)
      have e := W.step i (by omega)
      have h' := P.edgeBound _ _ e
      have t := P.triangle a (W.point i) (W.point (i+1))
      omega
  have h := up k (Nat.le_refl k)
  rwa [W.last] at h

noncomputable def SmallGraphData.metric {n : Nat} (P : SmallGraphData n) :
    ShortestDistances P.graph where
  dist := P.dist
  geodesic := fun a b => Classical.choice (P.findWalk a b)
  minimal := P.boundWalk

theorem SmallGraphData.attains {n S : Nat} (P : SmallGraphData n) (a b c d : Fin n)
    (neq : FourApart a b c d) (score : fourSum P.metric a b c d=S)
    (size : n-4=(S-7)/4) : VertexAttains S := by
  refine ⟨n,P.graph,P.metric,a,b,c,d,neq,score,?_⟩
  rw [←size]
  exact cap_of_order P.metric a b c d neq

end HakKozerenkoSeparatorGraph

#print axioms HakKozerenkoSeparatorGraph.SmallGraphData.findWalk
#print axioms HakKozerenkoSeparatorGraph.SmallGraphData.attains
