module

public import Palomar.FourTerminalSeparators.Support.BarbellCapGeometry

@[expose] public section

namespace HakKozerenkoEdgeSeparator
open TriameterQ3Graph HakKozerenkoSeparatorGraph

theorem same_resource_implies_same_family {n q : Nat} {G : SimpleGraph (Fin n)} {T}
    (F : EdgeFamily G T q) (i j : Fin q) {x y : Nat}
    (hi : EdgeAt (F.part i) x y) (hj : EdgeAt (F.part j) x y) : i=j := by
  by_cases eq : i=j
  · exact eq
  · obtain ⟨hx,hy,h⟩ := hi
    obtain ⟨_,_,h'⟩ := hj
    exact (F.disjoint i j eq ⟨x,hx⟩ ⟨y,hy⟩ h h').elim

theorem same_cap_resource {n q : Nat} {G : SimpleGraph (Fin n)} {T}
    (F : EdgeFamily G T q) (base p : Nat) (i j : Fin q) (k : Fin (capSlots p))
    (hi : capHit (F.part i) base p k) (hj : capHit (F.part j) base p k) : i=j := by
  by_cases h : k.val<p-1 <;> simp only [capHit,h,ite_true,ite_false] at hi hj <;>
    exact same_resource_implies_same_family F i j hi hj

theorem cap_region_quota {n q : Nat} {G : SimpleGraph (Fin n)} {T}
    (F : EdgeFamily G T q) (base p : Nat) (L : List (Fin q)) (nd : L.Nodup)
    (has : ∀ i∈L, capConsumed (F.part i) base p) : L.length≤capBudget p := by
  classical
  by_cases small : p=2
  · have pick (i : Fin q) (hi : i∈L) : ∃ k : Fin (capSlots p), capHit (F.part i) base p k := by
      simpa only [capConsumed,small,ite_true] using has i hi
    let choose (i : Fin q) (hi : i∈L) := (pick i hi).choose
    have hit (i : Fin q) (hi : i∈L) : capHit (F.part i) base p (choose i hi) :=
      (pick i hi).choose_spec
    have H := counted_one_resource L nd choose (fun i j hi hj eq => by
      have hh := hit j hj
      rw [←eq] at hh
      exact same_cap_resource F base p i j _ (hit i hi) hh)
    simpa [capSlots,capBudget,small] using H
  · have pick (i : Fin q) (hi : i∈L) :
      ∃ f : Fin 2→Fin (capSlots p), Function.Injective f ∧ ∀ s, capHit (F.part i) base p (f s) := by
      have hh := has i hi
      simp only [capConsumed,small,ite_false] at hh
      obtain ⟨a,b,ne,ha,hb⟩ := hh
      let f (s : Fin 2) := if s.val=0 then a else b
      refine ⟨f,?_,?_⟩
      · intro s t eq
        apply Fin.ext
        have hS := s.isLt
        have hT := t.isLt
        change (if s.val=0 then a else b) = (if t.val=0 then a else b) at eq
        by_cases h₀ : s.val=0 <;> by_cases h₁ : t.val=0
        · omega
        · rw [ite_eq_left h₀,ite_eq_right h₁] at eq; exact (ne eq).elim
        · rw [ite_eq_right h₀,ite_eq_left h₁] at eq; exact (ne eq.symm).elim
        · omega
      · intro s
        change capHit (F.part i) base p (if s.val=0 then a else b)
        by_cases h : s.val=0
        · rwa [ite_eq_left h]
        · rwa [ite_eq_right h]
    let choose (i : Fin q) (hi : i∈L) := (pick i hi).choose
    have yes (i : Fin q) (hi : i∈L) := (pick i hi).choose_spec
    have H := counted_two_resources L nd choose (fun i hi => (yes i hi).1)
      (fun i j hi hj s t eq => by
        have hh := (yes j hj).2 t
        change capHit (F.part j) base p (choose j hj t) at hh
        rw [←eq] at hh
        exact same_cap_resource F base p i j _ ((yes i hi).2 s) hh)
    simpa [capSlots,capBudget,small] using H

theorem bar_resource_cover {p q L m : Nat}
    (hp : 2≤p) (hq : 2≤q) {T : Fin (barOrder p q L)→Prop}
    (sides : ∀ x,T x→x.val≤leftRoot p ∨ rightRoot p L≤x.val)
    (F : EdgeFamily (barGraph p q L) T m) (i : Fin m) :
    (∃ j : Fin L, EdgeAt (F.part i) (leftRoot p+j.val) (leftRoot p+j.val+1)) ∨
      capConsumed (F.part i) 0 p ∨ capConsumed (F.part i) (rightRoot p L) q := by
  classical
  by_cases h1 : ∃ j : Fin L, EdgeAt (F.part i) (leftRoot p+j.val) (leftRoot p+j.val+1)
  · exact Or.inl h1
  by_cases h2 : capConsumed (F.part i) 0 p
  · exact Or.inr (Or.inl h2)
  by_cases h3 : capConsumed (F.part i) (rightRoot p L) q
  · exact Or.inr (Or.inr h3)
  exfalso
  let g := afterCut (barGraph p q L) (F.part i) (F.symm i)
  let a := rootLeft p q L hp hq
  let b := rootRight p q L hp hq
  let z : Fin (barOrder p q L) := ⟨0,by unfold barOrder; omega⟩
  have clean (j : Nat) (l : a.val≤j) (r : j<b.val) :
      ¬ EdgeAt (F.part i) j (j+1) := by
    intro hit
    have lo : leftRoot p≤j := l
    have hi : j<leftRoot p+L := r
    let k : Fin L := ⟨j-leftRoot p,by omega⟩
    have eq : leftRoot p+k.val=j := by dsimp [k]; omega
    apply h1
    exact ⟨k,by rwa [eq]⟩
  have a_b : a.val≤b.val := Nat.le_add_right _ _
  obtain ⟨W⟩ := forward_without (p := p) (q := q) (L := L) (F.part i) (F.symm i) a b a_b clean
  have sizeL : 0+p≤barOrder p q L := by unfold barOrder; omega
  have sizeR : rightRoot p L+q≤barOrder p q L := by unfold rightRoot barOrder; omega
  have chL : 3≤p → ∀ x y : Fin (barOrder p q L),
      x.val=0 → y.val=0+p-1 → (barGraph p q L).adj x y := by
    intro h x y a b
    exact Or.inr (Or.inl ⟨h,Or.inl ⟨a,by simpa [leftRoot] using b⟩⟩)
  have chR : 3≤q → ∀ x y : Fin (barOrder p q L),
      x.val=rightRoot p L → y.val=rightRoot p L+q-1 → (barGraph p q L).adj x y := by
    intro h x y a b
    have E : rightRoot p L+q-1=barOrder p q L-1 := by
      unfold rightRoot barOrder
      omega
    exact Or.inr (Or.inr ⟨h,Or.inl ⟨a,b.trans E⟩⟩)
  have routeL (x : Fin (barOrder p q L)) (hx : x.val≤leftRoot p) :
      ∃ n, Nonempty (Walk g z x n) :=
    cap_avoids_from_start (F.part i) (F.symm i) 0 p hp sizeL chL h2 z x rfl (by omega)
      (by unfold leftRoot at hx; omega)
  have routeR (x : Fin (barOrder p q L)) (hx : rightRoot p L≤x.val) :
      ∃ n, Nonempty (Walk g b x n) :=
    cap_avoids_from_start (F.part i) (F.symm i) (rightRoot p L) q hq sizeR chR h3 b x rfl hx
      (by have ht := x.isLt
          unfold rightRoot leftRoot barOrder at *
          omega)
  obtain ⟨_,⟨A⟩⟩ := routeL a (Nat.le_refl _)
  have toRoot (x : Fin (barOrder p q L)) (hx : T x) :
      ∃ n, Nonempty (Walk g a x n) := by
    rcases sides x hx with h|h
    · obtain ⟨_,⟨U⟩⟩ := routeL x h
      exact ⟨_,⟨A.reverse.concat U⟩⟩
    · obtain ⟨_,⟨U⟩⟩ := routeR x h
      exact ⟨_,⟨W.concat U⟩⟩
  obtain ⟨x,y,tx,ty,sep⟩ := F.each i
  obtain ⟨_,⟨X⟩⟩ := toRoot x tx
  obtain ⟨_,⟨Y⟩⟩ := toRoot y ty
  let Z := X.reverse.concat Y
  obtain ⟨j,hj,hit⟩ := sep _ (forgetCut Z)
  exact (Z.step j hj).2 hit

theorem bar_edge_cap (p q L : Nat) (hp : 2≤p) (hq : 2≤q)
    (T : Fin (barOrder p q L)→Prop)
    (sides : ∀ x,T x→x.val≤leftRoot p ∨ rightRoot p L≤x.val) :
    EdgeCap (barGraph p q L) T (L+capBudget p+capBudget q) := by
  classical
  intro m F
  let A (i : Fin m) : Prop :=
    ∃ j : Fin L, EdgeAt (F.part i) (leftRoot p+j.val) (leftRoot p+j.val+1)
  let B (i : Fin m) : Prop := capConsumed (F.part i) 0 p
  let C (i : Fin m) : Prop := capConsumed (F.part i) (rightRoot p L) q
  apply distribute_resources A B C (bar_resource_cover hp hq sides F)
  · intro H nd all
    let x (i : Fin m) (hi : i∈H) := (all i hi).choose
    have h (i : Fin m) (hi : i∈H) :
      EdgeAt (F.part i) (leftRoot p+(x i hi).val) (leftRoot p+(x i hi).val+1) :=
      (all i hi).choose_spec
    exact counted_one_resource H nd x (fun i j hi hj eq => by
      have g := h j hj
      rw [←eq] at g
      exact same_resource_implies_same_family F i j (h i hi) g)
  · exact cap_region_quota F 0 p
  · exact cap_region_quota F (rightRoot p L) q

end HakKozerenkoEdgeSeparator

#print axioms HakKozerenkoEdgeSeparator.bar_edge_cap
