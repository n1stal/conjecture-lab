import DeltaNordhaus

namespace DeltaNordhaus
open Finset
open scoped BigOperators

/-- Allow external witnesses for vertices isolated within the class. -/
theorem ambient_class_cover {V : Type*} (A : V → V → Prop)
    (hs : IsSymmetric A) (hN : NoIsolates A) (C : Finset V) :
    ∃ D : Finset V, OpenCovers A C D ∧ D.card≤C.card := by
  classical
  let active (i : V) := ∃ j ∈ C, A i j
  let f (i : V) := if active i then i else Classical.choose (hN i)
  refine ⟨C.image f,?_,Finset.card_image_le⟩
  intro i hi
  by_cases h : active i
  · obtain ⟨j,hj,ha⟩ := h
    have ha' : active j := ⟨i,hi,hs ha⟩
    have hf : f j=j := ite_eq_left ha'
    exact ⟨j,hf ▸ Finset.mem_image_of_mem f hj,ha⟩
  · exact ⟨f i,Finset.mem_image_of_mem f hi,by simpa [f,h] using Classical.choose_spec (hN i)⟩

private theorem universal_pair {V : Type*} (A : V → V → Prop) (hS : IsSymmetric A)
    (C : Finset V) (hC : 1<C.card) (x : V) (_hx : x∈C)
    (hU : ∀ y∈C, y≠x → A x y) :
    ∃ D : Finset V, OpenCovers A C D ∧ D.card≤2 := by
  classical
  have hE : ∃ y∈C, y≠x := by
    by_contra! h
    have hc : C ⊆ {x} := by intro y hy; simpa using h y hy
    have hh := Finset.card_le_card hc
    simp at hh
    omega
  obtain ⟨y,hy,hyx⟩ := hE
  have hcard : ({x,y} : Finset V).card≤2 := by
    simpa using Finset.card_insert_le x ({y} : Finset V)
  refine ⟨{x,y},?_,hcard⟩
  intro w hw
  by_cases he : w=x
  · subst w
    exact ⟨y,by simp,hU y hy hyx⟩
  · exact ⟨x,by simp,hS (hU w hw he)⟩

/-- Cost of covering one class in two graphs that are complementary within the class.
Its witnesses are allowed to come from anywhere in either graph. -/
theorem pair_cover_class {V : Type*} (A B : V → V → Prop)
    (hAS : IsSymmetric A) (hAI : IsLoopless A) (hAN : NoIsolates A)
    (hBS : IsSymmetric B) (hBN : NoIsolates B)
    (C : Finset V) (hFlip : ∀ i∈C, ∀ j∈C, (B i j ↔ compAdj A i j)) :
    ∃ D E : Finset V, OpenCovers A C D ∧ OpenCovers B C E ∧ D.card+E.card≤C.card+2 := by
  classical
  by_cases hL : C.card≤1
  · obtain ⟨D,hd,hs⟩ := ambient_class_cover A hAS hAN C
    obtain ⟨E,he,ht⟩ := ambient_class_cover B hBS hBN C
    exact ⟨D,E,hd,he,by omega⟩
  let hC : 1<C.card := lt_of_not_ge hL
  let W := {i // i∈C}
  let K (i j : W) := A i.val j.val
  let L (i j : W) := B i.val j.val
  by_cases ha : NoIsolates K
  · by_cases hb : NoIsolates L
    · have hN : Nonempty W := by
        obtain ⟨i,hi⟩ := Finset.card_pos.mp (by omega : 0<C.card)
        exact ⟨⟨i,hi⟩⟩
      have hm : IsSymmetric K := fun _ _ h => hAS h
      have hi : IsLoopless K := fun i => hAI i.val
      have hc : NoIsolates (compAdj K) := by
        intro x
        obtain ⟨y,hy⟩ := hb x
        have he := (hFlip x.val x.property y.val y.property).mp hy
        exact ⟨y,fun e => he.1 (congrArg Subtype.val e),he.2⟩
      obtain ⟨D,E,hd,he,hcost⟩ := ordinary_bound K hm hi ha hc hN
      have hcard : Fintype.card W = C.card := Fintype.card_coe C
      refine ⟨D.image Subtype.val,E.image Subtype.val,?_,?_,?_⟩
      · intro x hx
        obtain ⟨y,hy,ha⟩ := hd ⟨x,hx⟩ (Finset.mem_univ _)
        exact ⟨y.val,Finset.mem_image_of_mem _ hy,ha⟩
      · intro x hx
        obtain ⟨y,hy,hB⟩ := he ⟨x,hx⟩ (Finset.mem_univ _)
        exact ⟨y.val,Finset.mem_image_of_mem _ hy,(hFlip x hx y.val y.property).mpr
          ⟨fun e => hB.1 (Subtype.ext e),hB.2⟩⟩
      · have h1 : (D.image Subtype.val).card≤D.card := Finset.card_image_le
        have h2 : (E.image Subtype.val).card≤E.card := Finset.card_image_le
        omega
    · obtain ⟨x,hx⟩ := not_forall.mp hb
      have hu (y : V) (hy : y∈C) (he : y≠x.val) : A x.val y := by
        by_contra! h
        exact hx ⟨⟨y,hy⟩,(hFlip x.val x.property y hy).mpr ⟨he.symm,h⟩⟩
      obtain ⟨D,hd,hs⟩ := universal_pair A hAS C hC x.val x.property hu
      obtain ⟨E,he,ht⟩ := ambient_class_cover B hBS hBN C
      exact ⟨D,E,hd,he,by omega⟩
  · obtain ⟨x,hx⟩ := not_forall.mp ha
    have hu (y : V) (hy : y∈C) (he : y≠x.val) : B x.val y :=
      (hFlip x.val x.property y hy).mpr ⟨he.symm,fun h => hx ⟨⟨y,hy⟩,h⟩⟩
    obtain ⟨D,hd,hs⟩ := ambient_class_cover A hAS hAN C
    obtain ⟨E,he,ht⟩ := universal_pair B hBS C hC x.val x.property hu
    exact ⟨D,E,hd,he,by omega⟩

/-- The inequality only requires complementing each class of an arbitrary partition;
the relations between distinct classes may differ or even be chosen independently. -/
theorem partition_total_domination {V K : Type*} [Fintype V] [DecidableEq K]
    (A B : V → V → Prop) (p : V → K)
    (hAS : IsSymmetric A) (hAI : IsLoopless A) (hAN : NoIsolates A)
    (hBS : IsSymmetric B) (hBN : NoIsolates B)
    (hFlip : ∀ i j, p i=p j → (B i j ↔ compAdj A i j)) :
    ∃ D E : Finset V, OpenCovers A Finset.univ D ∧ OpenCovers B Finset.univ E ∧
      D.card+E.card≤Fintype.card V+2*(Finset.univ.image p).card := by
  classical
  let I := Finset.univ.image p
  let C (k : K) := Finset.univ.filter (fun v => p v=k)
  have hc (k : K) : ∃ D E : Finset V,
      OpenCovers A (C k) D ∧ OpenCovers B (C k) E ∧ D.card+E.card≤(C k).card+2 := by
    apply pair_cover_class A B hAS hAI hAN hBS hBN (C k)
    intro i hi j hj
    have h1 := (Finset.mem_filter.mp hi).2
    have h2 := (Finset.mem_filter.mp hj).2
    exact hFlip i j (h1.trans h2.symm)
  choose P Q hP hQ hCost using hc
  let D := I.biUnion P
  let E := I.biUnion Q
  have inI (j : V) : p j∈I := Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have inC (j : V) : j∈C (p j) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩
  refine ⟨D,E, ?_,?_,?_⟩
  · intro i _
    obtain ⟨j,hj,ha⟩ := hP (p i) i (inC i)
    exact ⟨j,Finset.mem_biUnion.mpr ⟨p i,inI i,hj⟩,ha⟩
  · intro i _
    obtain ⟨j,hj,hb⟩ := hQ (p i) i (inC i)
    exact ⟨j,Finset.mem_biUnion.mpr ⟨p i,inI i,hj⟩,hb⟩
  · have hclass : (∑ i∈I,(C i).card)=Fintype.card V := by
      simpa only [I,C,Finset.card_univ] using
        (Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset V)) (t := I)
          (f := p) (fun x _ => inI x)).symm
    calc
      _ ≤ (∑ i∈I, (P i).card)+(∑ i∈I,(Q i).card) :=
        Nat.add_le_add Finset.card_biUnion_le Finset.card_biUnion_le
      _ = ∑ i∈I, ((P i).card+(Q i).card) := Finset.sum_add_distrib.symm
      _ ≤ ∑ i∈I, ((C i).card+2) := Finset.sum_le_sum (fun i _ => hCost i)
      _ = _ := by simp [Finset.sum_add_distrib,hclass,mul_comm,I]

#print axioms partition_total_domination
end DeltaNordhaus
