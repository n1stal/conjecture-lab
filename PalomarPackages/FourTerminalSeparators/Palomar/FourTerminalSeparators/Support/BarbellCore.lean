module

public import Palomar.FourTerminalSeparators.Support.EdgeResources
public import Palomar.FourTerminalSeparators.Support.FourSharpPath

@[expose] public section

namespace HakKozerenkoEdgeSeparator
open TriameterQ3Graph HakKozerenkoSeparatorGraph

def barOrder (p q L : Nat) : Nat := p+q+L-1
def leftRoot (p : Nat) : Nat := p-1
def rightRoot (p L : Nat) : Nat := p-1+L

def stepBetween (x y : Nat) : Prop := x+1=y ∨ y+1=x
def endpoints (u v x y : Nat) : Prop := (x=u ∧ y=v) ∨ (x=v ∧ y=u)

def barGraph (p q L : Nat) : SimpleGraph (Fin (barOrder p q L)) where
  adj x y := stepBetween x.val y.val ∨
    (3≤p ∧ endpoints 0 (leftRoot p) x.val y.val) ∨
    (3≤q ∧ endpoints (rightRoot p L) (barOrder p q L-1) x.val y.val)
  symm := by
    intro x y h
    rcases h with h|⟨hp,h⟩|⟨hq,h⟩
    · exact Or.inl h.symm
    · exact Or.inr (Or.inl ⟨hp, h.elim
        (fun h => Or.inr ⟨h.2,h.1⟩) (fun h => Or.inl ⟨h.2,h.1⟩)⟩)
    · exact Or.inr (Or.inr ⟨hq, h.elim
        (fun h => Or.inr ⟨h.2,h.1⟩) (fun h => Or.inl ⟨h.2,h.1⟩)⟩)
  loopless := by
    intro x h
    rcases h with h|⟨hp,h⟩|⟨hq,h⟩
    · rcases h with h|h <;> omega
    · unfold endpoints leftRoot at h
      rcases h with h|h <;> omega
    · unfold endpoints rightRoot barOrder at h
      rcases h with h|h <;> omega

def ofPath {p q L : Nat} {x y : Fin (barOrder p q L)} {n : Nat}
    (W : Walk (pathGraph (barOrder p q L)) x y n) :
    Walk (barGraph p q L) x y n :=
  ⟨W.point,W.first,W.last,fun i hi => Or.inl (W.step i hi)⟩

def barForward {p q L : Nat} (x y : Fin (barOrder p q L)) (h : x.val≤y.val) :
    Walk (barGraph p q L) x y (y.val-x.val) :=
  ofPath (pathForward x y h)

theorem bar_forward_point {p q L : Nat} (x y : Fin (barOrder p q L)) (h : x.val≤y.val)
    (i : Nat) (hi : i≤y.val-x.val) :
    ((barForward x y h).point i).val = x.val+i := by
  change min (x.val+i) y.val=x.val+i
  exact Nat.min_eq_left (by omega)

theorem barConnected (p q L : Nat) : Connected (barGraph p q L) := by
  intro x y
  exact ⟨_,⟨ofPath ((pathDistance (barOrder p q L)).geodesic x y)⟩⟩

noncomputable def barMetric (p q L : Nat) : ShortestDistances (barGraph p q L) :=
  distancesOfConnected (barGraph p q L) (barConnected p q L)

def rootLeft (p q L : Nat) (hp : 2≤p) (hq : 2≤q) : Fin (barOrder p q L) :=
  ⟨leftRoot p,by unfold leftRoot barOrder; omega⟩

def rootRight (p q L : Nat) (hp : 2≤p) (hq : 2≤q) : Fin (barOrder p q L) :=
  ⟨rightRoot p L,by unfold rightRoot barOrder; omega⟩

def trunkCoord (p L : Nat) (x : Nat) : Nat :=
  min L (x-leftRoot p)

theorem trunc_coord_step {p q L : Nat} {x y : Fin (barOrder p q L)}
    (hp : 2≤p) (_hq : 2≤q) (E : (barGraph p q L).adj x y) :
    trunkCoord p L y.val ≤ trunkCoord p L x.val+1 := by
  rcases E with E|⟨_,h⟩|⟨_,h⟩
  · unfold stepBetween at E
    unfold trunkCoord
    rcases E with h|h <;> omega
  · unfold trunkCoord endpoints leftRoot at *
    rcases h with h|h <;> omega
  · unfold trunkCoord endpoints leftRoot rightRoot barOrder at *
    rcases h with h|h <;> omega

theorem bar_trunk_distance (p q L : Nat) (hp : 2≤p) (hq : 2≤q) :
    (barMetric p q L).dist (rootLeft p q L hp hq) (rootRight p q L hp hq) = L := by
  let s := rootLeft p q L hp hq
  let t := rootRight p q L hp hq
  have hst : s.val≤t.val := by dsimp [s,t,rootLeft,rootRight,leftRoot,rightRoot]; omega
  have len : t.val-s.val=L := by dsimp [s,t,rootLeft,rootRight,leftRoot,rightRoot]; omega
  have upper := (barMetric p q L).minimal s t _ (barForward s t hst)
  rw [len] at upper
  let W := (barMetric p q L).geodesic s t
  let D := (barMetric p q L).dist s t
  have at0 : trunkCoord p L s.val=0 := by
    dsimp [s,rootLeft,trunkCoord]
    omega
  have atL : trunkCoord p L t.val=L := by
    dsimp [t,rootRight,trunkCoord,rightRoot,leftRoot]
    omega
  have go (i : Nat) (hi : i≤D) : trunkCoord p L (W.point i).val≤i := by
    induction i with
    | zero => rw [W.first,at0]; exact Nat.le_refl 0
    | succ i ih =>
      have h := ih (by omega)
      have k := trunc_coord_step hp hq (W.step i (by omega))
      omega
  have lower := go D (Nat.le_refl D)
  rw [W.last,atL] at lower
  exact Nat.le_antisymm upper lower

theorem hit_bar_gate_aux (f : Nat→Nat) (n g : Nat) (start : f 0≤g) (last : g≤f n)
    (noleap : ∀ i, i<n → f i<g → f (i+1)≤g) :
    ∃ i, i≤n ∧ f i=g := by
  induction n with
  | zero => exact ⟨0,by omega,by omega⟩
  | succ n ih =>
    by_cases old : g≤f n
    · obtain ⟨i,hi,he⟩ := ih old (fun i hi => noleap i (by omega))
      exact ⟨i,by omega,he⟩
    · have H := noleap n (by omega) (by omega)
      exact ⟨n+1,by omega,by omega⟩

theorem bar_no_skip_left {p q L : Nat} {x y : Fin (barOrder p q L)}
    (hp : 2≤p) (_hq : 2≤q)
    (edge : (barGraph p q L).adj x y) (a : x.val<leftRoot p) :
    y.val≤leftRoot p := by
  rcases edge with e|⟨_,h⟩|⟨_,h⟩
  · unfold stepBetween at e; rcases e with e|e <;> omega
  · unfold endpoints at h
    rcases h with h|h <;> omega
  · unfold endpoints rightRoot barOrder leftRoot at *
    rcases h with h|h <;> omega

theorem bar_no_skip_right {p q L : Nat} {x y : Fin (barOrder p q L)}
    (_hp : 2≤p) (_hq : 2≤q)
    (edge : (barGraph p q L).adj x y) (a : x.val<rightRoot p L) :
    y.val≤rightRoot p L := by
  rcases edge with e|⟨_,h⟩|⟨_,h⟩
  · unfold stepBetween at e; rcases e with e|e <;> omega
  · unfold endpoints rightRoot leftRoot at *
    rcases h with h|h <;> omega
  · simp only [endpoints,rightRoot,barOrder] at h
    simp only [rightRoot] at a ⊢
    rcases h with h|h <;> omega

theorem bar_cross_distance {p q L : Nat} (hp : 2≤p) (hq : 2≤q)
    (x y : Fin (barOrder p q L)) (hx : x.val≤leftRoot p) (hy : rightRoot p L≤y.val) :
    (barMetric p q L).dist x y =
      (barMetric p q L).dist x (rootLeft p q L hp hq)+L+
      (barMetric p q L).dist (rootRight p q L hp hq) y := by
  let M := barMetric p q L
  let a := rootLeft p q L hp hq
  let b := rootRight p q L hp hq
  let k := M.dist x y
  let W := M.geodesic x y
  have hab : M.dist a b=L := bar_trunk_distance p q L hp hq
  have lr : leftRoot p≤rightRoot p L := Nat.le_add_right _ _
  obtain ⟨i,hi,hpi⟩ := hit_bar_gate_aux (fun j => (W.point j).val) k (leftRoot p)
    (by rw [W.first]; exact hx)
    (by rw [W.last]; exact Nat.le_trans lr hy)
    (fun j hj h => bar_no_skip_left hp hq (W.step j hj) h)
  have eqA : W.point i=a := Fin.ext hpi
  let tail := W.slice i k hi (by omega)
  obtain ⟨j,hj,hpj⟩ := hit_bar_gate_aux (fun z => (tail.point z).val) (k-i) (rightRoot p L)
    (by
      rw [tail.first]
      rw [eqA]
      exact lr)
    (by rw [tail.last,W.last]; exact hy)
    (fun z hz h => bar_no_skip_right hp hq (tail.step z hz) h)
  have eqB : W.point (i+j)=b := Fin.ext hpj
  have le : i+j≤k := by omega
  have p0 := W.slice 0 i (by omega) hi
  have p1 := W.slice i (i+j) (by omega) le
  have p2 := W.slice (i+j) k le (by omega)
  rw [W.first,eqA] at p0
  rw [eqA,eqB] at p1
  rw [eqB,W.last] at p2
  have h0 := M.minimal x a _ p0
  have h1 := M.minimal a b _ p1
  have h2 := M.minimal b y _ p2
  rw [hab] at h1
  have up0 := M.dist_triangle x a y
  have up1 := M.dist_triangle a b y
  rw [hab] at up1
  change k=M.dist x a+L+M.dist b y
  change k≤M.dist x a+M.dist a y at up0
  omega

end HakKozerenkoEdgeSeparator

#print axioms HakKozerenkoEdgeSeparator.bar_trunk_distance
#print axioms HakKozerenkoEdgeSeparator.bar_cross_distance
