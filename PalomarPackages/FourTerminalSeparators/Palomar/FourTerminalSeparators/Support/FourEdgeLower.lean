module

public import Palomar.FourTerminalSeparators.Support.EdgeSeparatorGraph

@[expose] public section

/-! A direct actual graph proof of the edge version from Hak–Kozerenko
Remark 6.2, kept separate from the sharp vertex result. -/
namespace HakKozerenkoEdgeSeparator
open TriameterQ3Graph HakKozerenkoSeparatorGraph
universe u
variable {V : Type u} {G : SimpleGraph V} {T : V → Prop}

def edgeTake {r s : Nat} (F : EdgeFamily G T r) (h : s≤r) : EdgeFamily G T s where
  part := fun i => F.part (Fin.castLE h i)
  symm := fun i => F.symm (Fin.castLE h i)
  valid := fun i => F.valid (Fin.castLE h i)
  each := fun i => F.each (Fin.castLE h i)
  disjoint := fun i j ne x y hx hy =>
    F.disjoint (Fin.castLE h i) (Fin.castLE h j)
      (fun e => ne (Fin.ext (congrArg (fun z : Fin r => z.val) e))) x y hx hy

def edgeWiden {U : V→Prop} {r : Nat} (F : EdgeFamily G T r)
    (h : ∀ x,T x→U x) : EdgeFamily G U r where
  part := F.part
  symm := F.symm
  valid := F.valid
  each := by
    intro i
    obtain ⟨s,t,hs,ht,sep⟩ := F.each i
    exact ⟨s,t,h s hs,h t ht,sep⟩
  disjoint := F.disjoint

theorem three_edge_rings (M : ShortestDistances G) (a b c : V)
    (ha : T a) (hb : T b) (hc : T c)
    (r s t : Nat) (ab : r+s≤M.dist a b) (ac : r+t≤M.dist a c) (bc : s+t≤M.dist b c) :
    Nonempty (EdgeFamily G T (r+s+t)) := by
  have ba : s+r≤M.dist b a := by rw [M.dist_symm]; omega
  have ca : t+r≤M.dist c a := by rw [M.dist_symm]; omega
  let A := edgeRings M a b r ha hb (by omega)
  let B := edgeRings M b a s hb ha (by omega)
  let C := edgeRings M c a t hc ha (by omega)
  let AB := mergeEdges A B (edge_balls_disjoint M a b r s ab)
  let F := mergeEdges AB C (fun x y hf hg => by
    rcases hf with hf|hf
    · exact edge_balls_disjoint M a c r t ac x y hf hg
    · exact edge_balls_disjoint M b c s t bc x y hf hg)
  exact ⟨F.family⟩

/-- Remark 6.2 edge count realized by ordinary distance boundary cuts.
For odd perimeter one of the three radius bounds may be increased by one. -/
theorem triple_edge_separators (M : ShortestDistances G) (a b c : V)
    (ha : T a) (hb : T b) (hc : T c) :
    Nonempty (EdgeFamily G T ((M.dist a b+M.dist a c+M.dist b c)/2)) := by
  let x := M.dist a b
  let y := M.dist a c
  let z := M.dist b c
  have xt : x≤y+z := by
    have h := M.dist_triangle a c b
    rw [M.dist_symm c b] at h
    exact h
  have yt : y≤x+z := M.dist_triangle a b c
  have zt : z≤x+y := by
    have h := M.dist_triangle b a c
    rw [M.dist_symm b a] at h
    exact h
  let l := (x+y-z)/2
  let m := (x+z-y)/2
  let n := (y+z-x)/2
  change Nonempty (EdgeFamily G T ((x+y+z)/2))
  by_cases parity : (x+y+z)%2=0
  · have hx : x=l+m := by dsimp [l,m]; omega
    have hy : y=l+n := by dsimp [l,n]; omega
    have hz : z=m+n := by dsimp [m,n]; omega
    obtain ⟨F⟩ := three_edge_rings M a b c ha hb hc l m n
      (by change l+m≤x; omega) (by change l+n≤y; omega) (by change m+n≤z; omega)
    exact ⟨edgeTake F (by omega)⟩
  · have hx : x=l+m+1 := by dsimp [l,m]; omega
    have hy : y=l+n+1 := by dsimp [l,n]; omega
    have hz : z=m+n+1 := by dsimp [m,n]; omega
    obtain ⟨F⟩ := three_edge_rings M a b c ha hb hc (l+1) m n
      (by change l+1+m≤x; omega) (by change l+1+n≤y; omega) (by change m+n≤z; omega)
    exact ⟨edgeTake F (by omega)⟩

def fourSumEdge (M : ShortestDistances G) (a b c d : V) : Nat :=
  M.dist a b+M.dist c d+M.dist a c+M.dist b d+M.dist a d+M.dist b c

def markFourEdge (a b c d v : V) : Prop := v=a ∨ v=b ∨ v=c ∨ v=d

theorem four_edge_sum_cap (M : ShortestDistances G) (a b c d : V)
    (limit : Nat) (cap : EdgeCap G (markFourEdge a b c d) limit) :
    fourSumEdge M a b c d≤4*limit+2 := by
  have A : markFourEdge a b c d a := Or.inl rfl
  have B : markFourEdge a b c d b := Or.inr (Or.inl rfl)
  have C : markFourEdge a b c d c := Or.inr (Or.inr (Or.inl rfl))
  have D : markFourEdge a b c d d := Or.inr (Or.inr (Or.inr rfl))
  obtain ⟨F₀⟩ := triple_edge_separators M a b c A B C
  obtain ⟨F₁⟩ := triple_edge_separators M a b d A B D
  obtain ⟨F₂⟩ := triple_edge_separators M a c d A C D
  obtain ⟨F₃⟩ := triple_edge_separators M b c d B C D
  have h₀ := cap _ F₀
  have h₁ := cap _ F₁
  have h₂ := cap _ F₂
  have h₃ := cap _ F₃
  unfold fourSumEdge
  omega

/-- Actual universal four-terminal edge-separator lower bound. Distinct
terminals are not needed for this lower inequality on the supplied sum;
for the sharp problem the four terminals are distinct. -/
theorem four_edge_separators (M : ShortestDistances G) (a b c d : V) :
    Nonempty (EdgeFamily G (markFourEdge a b c d) ((fourSumEdge M a b c d+1)/4)) := by
  classical
  let n := (fourSumEdge M a b c d+1)/4
  change Nonempty (EdgeFamily G (markFourEdge a b c d) n)
  by_cases zero : n=0
  · rw [zero]
    exact ⟨⟨fun i => Fin.elim0 i,fun i => Fin.elim0 i,fun i => Fin.elim0 i,
      fun i => Fin.elim0 i,fun i => Fin.elim0 i⟩⟩
  · by_cases has : Nonempty (EdgeFamily G (markFourEdge a b c d) n)
    · exact has
    · exfalso
      have cap : EdgeCap G (markFourEdge a b c d) (n-1) := by
        intro q F
        by_cases enough : n≤q
        · exact (has ⟨edgeTake F enough⟩).elim
        · omega
      have h := four_edge_sum_cap M a b c d (n-1) cap
      dsimp [n] at h
      dsimp [n] at zero
      omega

end HakKozerenkoEdgeSeparator

#print axioms HakKozerenkoEdgeSeparator.triple_edge_separators
#print axioms HakKozerenkoEdgeSeparator.four_edge_separators
