module

public import Palomar.FourTerminalSeparators.Support.FourBallGroup

@[expose] public section

namespace HakKozerenkoEdgeSeparator
open TriameterQ3Graph HakKozerenkoSeparatorGraph
universe u
variable {V : Type u} {G : SimpleGraph V} {T : V → Prop}

def EdgeSeparates (G : SimpleGraph V) (A : V→V→Prop) (s t : V) : Prop :=
  ∀ (n : Nat) (W : Walk G s t n), ∃ j, j<n ∧ A (W.point j) (W.point (j+1))

structure EdgeFamily (G : SimpleGraph V) (T : V→Prop) (m : Nat) where
  part : Fin m → V → V → Prop
  symm : ∀ i x y, part i x y → part i y x
  valid : ∀ i x y, part i x y → G.adj x y
  each : ∀ i, ∃ s t, T s ∧ T t ∧ EdgeSeparates G (part i) s t
  disjoint : ∀ i j, i≠j → ∀ x y, part i x y → part j x y → False

def EdgeCap (G : SimpleGraph V) (T : V→Prop) (e : Nat) : Prop :=
  ∀ m, EdgeFamily G T m → m≤e

structure SupportedEdgeFamily (G : SimpleGraph V) (T : V→Prop)
    (m : Nat) (S : V→V→Prop) where
  family : EdgeFamily G T m
  support : ∀ i x y, family.part i x y → S x y

def mergeEdges {r s : Nat} {A B : V→V→Prop}
    (F : SupportedEdgeFamily G T r A) (H : SupportedEdgeFamily G T s B)
    (d : ∀ x y, A x y → B x y → False) :
    SupportedEdgeFamily G T (r+s) (fun x y => A x y ∨ B x y) := by
  let f : Fin (r+s)→V→V→Prop := Fin.addCases F.family.part H.family.part
  have l (i : Fin r) : f (Fin.castAdd s i)=F.family.part i := Fin.addCases_left i
  have r₁ (i : Fin s) : f (Fin.natAdd r i)=H.family.part i := Fin.addCases_right i
  refine ⟨⟨f,?_,?_,?_,?_⟩,?_⟩
  · intro i
    induction i using Fin.addCases with
    | left i => simpa only [l] using F.family.symm i
    | right i => simpa only [r₁] using H.family.symm i
  · intro i
    induction i using Fin.addCases with
    | left i => simpa only [l] using F.family.valid i
    | right i => simpa only [r₁] using H.family.valid i
  · intro i
    induction i using Fin.addCases with
    | left i => simpa only [l] using F.family.each i
    | right i => simpa only [r₁] using H.family.each i
  · intro i
    induction i using Fin.addCases with
    | left i =>
      intro j
      induction j using Fin.addCases with
      | left j =>
        intro ne x y hi hj
        rw [l] at hi hj
        exact F.family.disjoint i j (fun eq => ne (congrArg (Fin.castAdd s) eq)) x y hi hj
      | right j =>
        intro _ x y hi hj
        rw [l] at hi
        rw [r₁] at hj
        exact d x y (F.support i x y hi) (H.support j x y hj)
    | right i =>
      intro j
      induction j using Fin.addCases with
      | left j =>
        intro _ x y hi hj
        rw [r₁] at hi
        rw [l] at hj
        exact d x y (F.support j x y hj) (H.support i x y hi)
      | right j =>
        intro ne x y hi hj
        rw [r₁] at hi hj
        exact H.family.disjoint i j (fun eq => ne (congrArg (Fin.natAdd r) eq)) x y hi hj
  · intro i
    induction i using Fin.addCases with
    | left i =>
      intro x y h
      change f (Fin.castAdd s i) x y at h
      rw [l] at h
      exact Or.inl (F.support i x y h)
    | right i =>
      intro x y h
      change f (Fin.natAdd r i) x y at h
      rw [r₁] at h
      exact Or.inr (H.support i x y h)

theorem crossed_edge_layer (f : Nat→Nat) (n j : Nat)
    (first : f 0≤j) (last : j<f n)
    (lip : ∀ i, i<n → f (i+1)≤f i+1) :
    ∃ i, i<n ∧ f i=j ∧ f (i+1)=j+1 := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases earlier : j<f n
    · obtain ⟨i,hi,hj,hk⟩ := ih earlier (fun i hi => lip i (by omega))
      exact ⟨i,by omega,hj,hk⟩
    · have h := lip n (by omega)
      exact ⟨n,by omega,by omega,by omega⟩

def edgeBall (M : ShortestDistances G) (a : V) (r : Nat) (x y : V) : Prop :=
  M.dist a x≤r ∧ M.dist a y≤r ∧ (M.dist a x<r ∨ M.dist a y<r)

theorem edge_balls_disjoint (M : ShortestDistances G) (a b : V) (r s : Nat)
    (apart : r+s≤M.dist a b) :
    ∀ x y, edgeBall M a r x y → edgeBall M b s x y → False := by
  intro x y hx hy
  have H := M.dist_triangle a x b
  have J := M.dist_triangle a y b
  rw [M.dist_symm x b] at H
  rw [M.dist_symm y b] at J
  obtain ⟨_,_,h⟩ := hx
  obtain ⟨h₀,h₁,_⟩ := hy
  rcases h with h|h <;> omega

/-- Consecutive ordinary BFS boundaries are disjoint edge separators.
T-terminals may lie on either side, so no forbidden level is dropped. -/
def edgeRings (M : ShortestDistances G) (a b : V) (r : Nat)
    (ha : T a) (hb : T b) (fit : r≤M.dist a b) :
    SupportedEdgeFamily G T r (edgeBall M a r) := by
  let f : Fin r→V→V→Prop := fun i x y => G.adj x y ∧
    ((M.dist a x=i.val ∧ M.dist a y=i.val+1) ∨
      (M.dist a y=i.val ∧ M.dist a x=i.val+1))
  refine ⟨⟨f,?_,?_,?_,?_⟩,?_⟩
  · intro i x y h
    exact ⟨G.symm h.1,h.2.symm⟩
  · exact fun _ _ _ h => h.1
  · intro i
    have hi := i.isLt
    refine ⟨a,b,ha,hb,?_⟩
    intro n W
    let F := fun j => M.dist a (W.point j)
    have s : F 0≤i.val := by simp [F,W.first,M.dist_self]
    have t : i.val<F n := by dsimp [F]; rw [W.last]; omega
    obtain ⟨j,hj,he,hf⟩ := crossed_edge_layer F n i.val s t
      (fun j hj => distance_step M a (W.step j hj))
    exact ⟨j,hj,W.step j hj,Or.inl ⟨he,hf⟩⟩
  · intro i j ne x y hi hj
    apply ne
    apply Fin.ext
    rcases hi.2 with ⟨ha,hb⟩|⟨ha,hb⟩ <;>
      rcases hj.2 with ⟨hc,hd⟩|⟨hc,hd⟩ <;> omega
  · intro i x y h
    have H := i.isLt
    rcases h.2 with ⟨ha,hb⟩|⟨ha,hb⟩
    · exact ⟨by omega,by omega,Or.inl (by omega)⟩
    · exact ⟨by omega,by omega,Or.inr (by omega)⟩

end HakKozerenkoEdgeSeparator

#print axioms HakKozerenkoEdgeSeparator.edgeRings
#print axioms HakKozerenkoEdgeSeparator.edge_balls_disjoint
