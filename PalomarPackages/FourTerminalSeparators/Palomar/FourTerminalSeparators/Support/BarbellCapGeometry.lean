module

public import Palomar.FourTerminalSeparators.Support.BarbellCore

@[expose] public section

namespace HakKozerenkoEdgeSeparator
open TriameterQ3Graph HakKozerenkoSeparatorGraph
universe u
variable {V : Type u} {G : SimpleGraph V}

def afterCut (G : SimpleGraph V) (A : V→V→Prop) (sym : ∀ x y, A x y→ A y x) :
    SimpleGraph V where
  adj x y := G.adj x y ∧ ¬A x y
  symm := fun {x y} h => ⟨G.symm h.1,fun H => h.2 (sym y x H)⟩
  loopless := fun x h => G.loopless x h.1

def forgetCut {A : V→V→Prop} {sym} {a b : V} {n : Nat}
    (W : Walk (afterCut G A sym) a b n) : Walk G a b n :=
  ⟨W.point,W.first,W.last,fun i hi => (W.step i hi).1⟩

def EdgeAt {n : Nat} (A : Fin n→Fin n→Prop) (x y : Nat) : Prop :=
  ∃ (hx : x<n) (hy : y<n), A ⟨x,hx⟩ ⟨y,hy⟩

def capSlots (p : Nat) : Nat := if p=2 then 1 else p
def capBudget (p : Nat) : Nat := if p=2 then 1 else p/2

def capHit {n : Nat} (A : Fin n→Fin n→Prop) (base p : Nat) (j : Fin (capSlots p)) : Prop :=
  if j.val<p-1 then EdgeAt A (base+j.val) (base+j.val+1)
  else EdgeAt A base (base+p-1)

def capConsumed {n : Nat} (A : Fin n→Fin n→Prop) (base p : Nat) : Prop :=
  if p=2 then ∃ i : Fin (capSlots p), capHit A base p i
  else ∃ i j : Fin (capSlots p), i≠j ∧ capHit A base p i ∧ capHit A base p j

theorem cap_path_label {n : Nat} {A : Fin n→Fin n→Prop} {base p j : Nat}
    (hp : 2≤p) (lo : base≤j) (hi : j<base+p-1)
    (hit : EdgeAt A j (j+1)) :
    ∃ i : Fin (capSlots p), i.val=j-base ∧ capHit A base p i := by
  have H : j-base<capSlots p := by
    unfold capSlots
    by_cases eq : p=2 <;> simp [eq] <;> omega
  let i : Fin (capSlots p) := ⟨j-base,H⟩
  have E : base+i.val=j := by dsimp [i]; omega
  have iok : i.val<p-1 := by dsimp [i]; omega
  refine ⟨i,rfl,?_⟩
  simp only [capHit,iok,ite_true,E,hit]

theorem cap_chord_label {n : Nat} {A : Fin n→Fin n→Prop} {base p : Nat}
    (pbig : 3≤p) (hit : EdgeAt A base (base+p-1)) :
    ∃ i : Fin (capSlots p), i.val=p-1 ∧ capHit A base p i := by
  have hs : p-1<capSlots p := by simp [capSlots, show p≠2 by omega]; omega
  let i : Fin (capSlots p) := ⟨p-1,hs⟩
  refine ⟨i,rfl,?_⟩
  have he : ¬i.val<p-1 := by dsimp [i]; omega
  simpa only [capHit,he,ite_false] using hit

theorem forward_without {p q L : Nat}
    (A : Fin (barOrder p q L)→Fin (barOrder p q L)→Prop)
    (sym : ∀ x y, A x y→A y x) (x y : Fin (barOrder p q L)) (order : x.val≤y.val)
    (clean : ∀ j, x.val≤j → j<y.val → ¬ EdgeAt A j (j+1)) :
    Nonempty (Walk (afterCut (barGraph p q L) A sym) x y (y.val-x.val)) := by
  let W := barForward x y order
  refine ⟨⟨W.point,W.first,W.last,?_⟩⟩
  intro i hi
  refine ⟨W.step i hi,?_⟩
  intro hit
  have h0 := bar_forward_point x y order i (Nat.le_of_lt hi)
  have h1 := bar_forward_point x y order (i+1) (by omega)
  have hlt := (W.point i).isLt
  have hlt1 := (W.point (i+1)).isLt
  change (W.point i).val=x.val+i at h0
  change (W.point (i+1)).val=x.val+(i+1) at h1
  -- An original hit at this walk edge is a numeric step hit.
  have H : EdgeAt A (W.point i).val (W.point (i+1)).val := by
    exact ⟨hlt,hlt1,hit⟩
  rw [h0,h1] at H
  have eq : x.val+(i+1)=x.val+i+1 := by omega
  rw [eq] at H
  exact clean (x.val+i) (by omega) (by omega) H

/-- A cycle interval with fewer than two charged edges remains rooted
connected, and a two-vertex edge interval with no charge does too. -/
theorem cap_avoids_from_start {p q L : Nat}
    (A : Fin (barOrder p q L)→Fin (barOrder p q L)→Prop)
    (sym : ∀ x y, A x y→A y x) (base len : Nat)
    (nlen : 2≤len) (bounded : base+len≤barOrder p q L)
    (chord : 3≤len → ∀ a b : Fin (barOrder p q L),
      a.val=base → b.val=base+len-1 → (barGraph p q L).adj a b)
    (spare : ¬capConsumed A base len)
    (start x : Fin (barOrder p q L)) (s : start.val=base)
    (xlo : base≤x.val) (xhi : x.val<base+len) :
    ∃ m, Nonempty (Walk (afterCut (barGraph p q L) A sym) start x m) := by
  by_cases hit : ∃ j, base≤j ∧ j<x.val ∧ EdgeAt A j (j+1)
  · obtain ⟨j,hj,hjx,hja⟩ := hit
    obtain ⟨i,ieq,ihit⟩ := cap_path_label nlen hj (by omega) hja
    have hn2 : len≠2 := by
      intro e
      apply spare
      simp only [capConsumed,e,ite_true]
      exact ⟨i,ihit⟩
    have large : 3≤len := by omega
    have absent (ith : Fin (capSlots len)) (ne : i≠ith) : ¬capHit A base len ith := by
      intro H
      apply spare
      simp only [capConsumed,hn2,ite_false]
      exact ⟨i,ith,ne,ihit,H⟩
    let stop : Fin (barOrder p q L) := ⟨base+len-1,by omega⟩
    have noChord : ¬ A start stop := by
      intro h
      have hE : EdgeAt A start.val stop.val := ⟨start.isLt,stop.isLt,h⟩
      rw [s] at hE
      change EdgeAt A base (base+len-1) at hE
      obtain ⟨z,zeq,hit⟩ := cap_chord_label large hE
      apply absent z _ hit
      intro eq
      have val := congrArg (fun z : Fin (capSlots len) => z.val) eq
      omega
    have W0 := unitWalk (G := afterCut (barGraph p q L) A sym)
      (x := start) (y := stop) ⟨chord large start stop s rfl,noChord⟩
    have noTail (k : Nat) (lh : x.val≤k) (rh : k<stop.val) : ¬ EdgeAt A k (k+1) := by
      intro h
      obtain ⟨z,zeq,hit⟩ := cap_path_label nlen (by omega : base≤k) rh h
      apply absent z _ hit
      intro eq
      have val := congrArg (fun z : Fin (capSlots len) => z.val) eq
      omega
    obtain ⟨W1⟩ := forward_without A sym x stop (by
      change x.val≤base+len-1
      omega) noTail
    exact ⟨_,⟨W0.concat W1.reverse⟩⟩
  · have clean (j : Nat) (h1 : start.val≤j) (h2 : j<x.val) : ¬EdgeAt A j (j+1) := by
      intro h
      exact hit ⟨j,by omega,h2,h⟩
    exact ⟨_,forward_without A sym start x (by omega) clean⟩

end HakKozerenkoEdgeSeparator

#print axioms HakKozerenkoEdgeSeparator.cap_avoids_from_start
