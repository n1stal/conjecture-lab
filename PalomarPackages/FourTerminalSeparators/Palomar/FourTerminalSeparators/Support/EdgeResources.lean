module

public import Palomar.FourTerminalSeparators.Support.FourEdgeLower

@[expose] public section

namespace HakKozerenkoEdgeSeparator

theorem fin_injection_width {n m : Nat} (f : Fin n→Fin m) (hf : Function.Injective f) : n≤m := by
  have hn : ((List.finRange n).map f).Nodup :=
    List.Pairwise.map f (fun a b ne e => ne (hf e)) (List.nodup_finRange n)
  have hs : (List.finRange n).map f ⊆ List.finRange m := fun {x} _ => List.mem_finRange x
  have H := hn.length_le_of_subset hs
  simpa only [List.length_map,List.length_finRange] using H

theorem index_list_injective {I : Type} (L : List I) (h : L.Nodup) :
    Function.Injective (fun i : Fin L.length => L.get i) := by
  intro i j eq
  apply Fin.ext
  have e : L[i.val]=L[j.val] := eq
  exact h.getElem_inj.mp e

theorem index_member {I : Type} (L : List I) (i : Fin L.length) : L.get i ∈ L :=
  List.mem_iff_get.mpr ⟨i,rfl⟩

/-- Counting indices having a unique resource in a fixed finite region. -/
theorem counted_one_resource {I : Type} {m : Nat} (L : List I) (h : L.Nodup)
    (choose : (i : I) → i∈L → Fin m)
    (unique : ∀ i j hi hj, choose i hi=choose j hj → i=j) :
    L.length≤m := by
  let f (i : Fin L.length) := choose (L.get i) (index_member L i)
  apply fin_injection_width f
  intro i j e
  exact index_list_injective L h (unique (L.get i) (L.get j) _ _ e)

/-- Counting indices having two different resources, with resources
assigned to distinct indices disjoint even if the slots differ. -/
theorem counted_two_resources {I : Type} {m : Nat} (L : List I) (h : L.Nodup)
    (choose : (i : I) → i∈L → Fin 2→Fin m)
    (within : ∀ i hi, Function.Injective (choose i hi))
    (unique : ∀ i j hi hj s t, choose i hi s=choose j hj t → i=j) :
    L.length≤m/2 := by
  let f₀ (i : Fin L.length) := choose (L.get i) (index_member L i) (0 : Fin 2)
  let f₁ (i : Fin L.length) := choose (L.get i) (index_member L i) (1 : Fin 2)
  let f : Fin (L.length+L.length)→Fin m := Fin.addCases f₀ f₁
  have hl (i : Fin L.length) : f (Fin.castAdd L.length i)=f₀ i := Fin.addCases_left i
  have hr (i : Fin L.length) : f (Fin.natAdd L.length i)=f₁ i := Fin.addCases_right i
  have inj : Function.Injective f := by
    intro i
    induction i using Fin.addCases with
    | left i =>
      intro j
      induction j using Fin.addCases with
      | left j =>
        intro eq
        rw [hl,hl] at eq
        exact congrArg (Fin.castAdd L.length) (index_list_injective L h
          (unique (L.get i) (L.get j) _ _ 0 0 eq))
      | right j =>
        intro eq
        rw [hl,hr] at eq
        have idx := index_list_injective L h (unique (L.get i) (L.get j) _ _ 0 1 eq)
        subst j
        have e : (0 : Fin 2)=1 := within (L.get i) (index_member L i) eq
        exact ((by decide : (0 : Fin 2)≠1) e).elim
    | right i =>
      intro j
      induction j using Fin.addCases with
      | left j =>
        intro eq
        rw [hr,hl] at eq
        have idx := index_list_injective L h (unique (L.get i) (L.get j) _ _ 1 0 eq)
        subst j
        have e : (1 : Fin 2)=0 := within (L.get i) (index_member L i) eq
        exact ((by decide : (1 : Fin 2)≠0) e).elim
      | right j =>
        intro eq
        rw [hr,hr] at eq
        exact congrArg (Fin.natAdd L.length) (index_list_injective L h
          (unique (L.get i) (L.get j) _ _ 1 1 eq))
  have B := fin_injection_width f inj
  omega

theorem two_filter_lengths {I : Type} (L : List I) (f : I→Bool) :
    (L.filter f).length+(L.filter (fun i => !(f i))).length=L.length := by
  induction L with
  | nil => rfl
  | cons a tail ih =>
    cases h : f a <;> simp [List.filter,h] <;> omega

/-- Resource partition into connector, left cap, and right cap. -/
theorem distribute_resources {n a b c : Nat} (A B C : Fin n→Prop)
    (cover : ∀ i, A i ∨ B i ∨ C i)
    (fA : ∀ L : List (Fin n), L.Nodup → (∀ i∈L,A i) → L.length≤a)
    (fB : ∀ L : List (Fin n), L.Nodup → (∀ i∈L,B i) → L.length≤b)
    (fC : ∀ L : List (Fin n), L.Nodup → (∀ i∈L,C i) → L.length≤c) :
    n≤a+b+c := by
  classical
  let all := List.finRange n
  let AS := all.filter (fun i => decide (A i))
  let rest := all.filter (fun i => !(decide (A i)))
  let BS := rest.filter (fun i => decide (B i))
  let CS := rest.filter (fun i => !(decide (B i)))
  have nd := List.nodup_finRange n
  have aN : AS.Nodup := nd.filter _
  have rN : rest.Nodup := nd.filter _
  have bN : BS.Nodup := rN.filter _
  have cN : CS.Nodup := rN.filter _
  have G₀ : AS.length+rest.length=n := by
    have h := two_filter_lengths all (fun i => decide (A i))
    simpa only [List.length_finRange,AS,rest,all] using h
  have G₁ : BS.length+CS.length=rest.length := by
    exact two_filter_lengths rest (fun i => decide (B i))
  have wa := fA AS aN (fun i h => of_decide_eq_true (List.mem_filter.mp h).2)
  have wb := fB BS bN (fun i h => of_decide_eq_true (List.mem_filter.mp h).2)
  have wc := fC CS cN (fun i h => by
    have ha := (List.mem_filter.mp (List.mem_filter.mp h).1).2
    have hb := (List.mem_filter.mp h).2
    rcases cover i with aa|bb|cc
    · simp [aa] at ha
    · simp [bb] at hb
    · exact cc)
  omega

end HakKozerenkoEdgeSeparator

#print axioms HakKozerenkoEdgeSeparator.counted_two_resources
#print axioms HakKozerenkoEdgeSeparator.distribute_resources
