module

public import Palomar.Erdos617PairStar.Support.CanonicalPair
public import Lean.Elab.Tactic.Omega

@[expose] public section

namespace ParallelMantel.Pentagon

open Erdos617Geometry

universe u
variable {V : Type u} {r : Nat} {col : V→V→Fin r} {t : Fin r}

/-- Unordered pair slots in a list of length n, i.e. n(n−1)/2. -/
def pairSlots : Nat → Nat
  | 0 => 0
  | n+1 => pairSlots n+n

private theorem edges_le_slots (g : V→V→Bool) (W : List V) :
    edges g W ≤ pairSlots W.length := by
  induction W with
  | nil => exact Nat.le_refl _
  | cons v W ih =>
    have d := List.length_filter_le (g v) W
    change degree g v W ≤ W.length at d
    change degree g v W + edges g W ≤ pairSlots W.length+W.length
    omega

/-- Counts actual non-target edges from v to a row, without baking in a
particular containing list. Distinctness is explicit. -/
noncomputable def rowHoles (col : V→V→Fin r) (t : Fin r) (x : V) (P : List V) : Nat :=
  open Classical in
  (P.filter (fun y=>decide (x≠y ∧ col x y≠t))).length

theorem rowHoles_eq_degree (col : V→V→Fin r) (t : Fin r) (W P : List V) (x : V)
    (xW : x∈W) (pW : P⊆W) :
    rowHoles col t x P=degree (missingColor col t W) x P := by
  classical
  unfold rowHoles degree
  congr 1
  apply List.filter_congr
  intro y ym
  simp [missingColor,xW,pW ym]

private theorem rowEdges_zero (W P : List V)
    (cl : P.Pairwise (fun x y=>col x y=t)) :
    edges (missingColor col t W) P=0 := by
  induction P with
  | nil => rfl
  | cons x R ih =>
    obtain ⟨f,rest⟩ := List.pairwise_cons.mp cl
    have d : degree (missingColor col t W) x R=0 := by
      unfold degree
      apply List.length_eq_zero_iff.mpr
      apply List.filter_eq_nil_iff.mpr
      intro y ym
      simp [missingColor,f y ym]
    rw [edges,d,ih rest]

/-- Sum of the holes beyond the first per arriving exception. -/
noncomputable def arrivalDebt (col : V→V→Fin r) (t : Fin r) (P Z : List V) : Nat :=
  (Z.map (fun x=>rowHoles col t x P-1)).sum

private theorem arrivalDebt_cons (col : V→V→Fin r) (t : Fin r) (P : List V)
    (x : V) (Z : List V) :
    arrivalDebt col t P (x::Z)=(rowHoles col t x P-1)+arrivalDebt col t P Z := rfl

theorem arrivalDebt_sublist (col : V→V→Fin r) (t : Fin r) (P : List V)
    {Z Z' : List V} (s : Z.Sublist Z') :
    arrivalDebt col t P Z≤arrivalDebt col t P Z' := by
  induction s with
  | slnil => exact Nat.le_refl _
  | cons a h ih => rw [arrivalDebt_cons]; omega
  | cons_cons a h ih => rw [arrivalDebt_cons,arrivalDebt_cons]; omega

theorem arrivalDebt_append (col : V→V→Fin r) (t : Fin r) (P Z Z' : List V) :
    arrivalDebt col t P (Z++Z')=arrivalDebt col t P Z+arrivalDebt col t P Z' := by
  simp [arrivalDebt,List.sum_append]

private theorem sum_eq_zero_of_zero (f : V→Nat) (Z : List V)
    (fl : ∀ x∈Z, f x=0) : (Z.map f).sum=0 := by
  induction Z with
  | nil => rfl
  | cons x Z ih =>
    simp only [List.map_cons,List.sum_cons,fl x (by simp),Nat.zero_add]
    exact ih (fun y ym=>fl y (List.mem_cons_of_mem _ ym))

private theorem debt_if_single (f : V→Nat) (E : Option V) (Z : List V) (K : Nat)
    (nd : Z.Nodup)
    (charge : ∀ x∈Z, f x=0 ∨ E=some x ∧ f x≤K) :
    (Z.map f).sum ≤ K := by
  classical
  induction Z with
  | nil => simp
  | cons x Z ih =>
    have nds := List.nodup_cons.mp nd
    have ch := charge x (by simp)
    have chT (y : V) (ym : y∈Z) := charge y (List.mem_cons_of_mem _ ym)
    simp only [List.map_cons,List.sum_cons]
    by_cases eqX : E=some x
    · have each (y : V) (ym : y∈Z) : f y=0 := (chT y ym).elim id (fun ⟨eqY,cap⟩=>by
        have e := Option.some.inj (eqX.symm.trans eqY)
        exact False.elim (nds.1 (e.symm ▸ ym)))
      rw [sum_eq_zero_of_zero f Z each,Nat.add_zero]
      exact ch.elim (fun h=>by rw [h];omega) And.right
    · have fzero : f x=0 := ch.elim id (fun contradiction=>False.elim (eqX contradiction.1))
      simpa only [fzero,Nat.zero_add] using ih nds.2 chT

theorem arrivalDebt_single_cap (col : V→V→Fin r) (t : Fin r)
    (P Z : List V) (E : Option V) (K : Nat) (nd : Z.Nodup)
    (holes : ∀ x∈Z, rowHoles col t x P≤1 ∨ E=some x ∧ rowHoles col t x P≤K+1) :
    arrivalDebt col t P Z≤K := by
  have cap := debt_if_single (fun x=>rowHoles col t x P-1) E Z K nd
    (fun x xm=>(holes x xm).elim (fun cheap=>Or.inl (by omega))
      (fun ⟨eq,cost⟩=>Or.inr ⟨eq,by omega⟩))
  exact cap

private theorem cut_hole_sum (P Z : List V) :
    cut (missingColor col t (Z++P)) Z P ≤ Z.length+arrivalDebt col t P Z := by
  have count : cut (missingColor col t (Z++P)) Z P=(Z.map (fun x=>rowHoles col t x P)).sum := by
    unfold cut
    congr 1
    apply List.map_congr_left
    intro x xm
    exact (rowHoles_eq_degree col t (Z++P) P x (List.mem_append_left _ xm)
      (fun _ ym=>List.mem_append_right _ ym)).symm
  rw [count]
  clear count
  induction Z with
  | nil => exact Nat.le_refl _
  | cons x Z ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons,arrivalDebt_cons]
    omega

/-- A completed actual r+1 row violates balance if the maximum number of
exception-pair slots plus its total hole budget is below r−1. -/
theorem palette_count_of_row (bal : Balanced col r) (P Z : List V)
    (distinct : (Z++P).Nodup)
    (clique : P.Pairwise (fun x y=>col x y=t))
    (size : Z.length+P.length=r+1) :
    r-1 ≤ pairSlots Z.length+Z.length+arrivalDebt col t P Z := by
  let W := Z++P
  let g := missingColor col t W
  have low := missingColor_floor col t bal W distinct
  have wlen : W.length-r=1 := by simp only [W,List.length_append];omega
  rw [wlen,Nat.mul_one] at low
  change r-1≤edges g (Z++P) at low
  rw [edges_append] at low
  have no := rowEdges_zero (col:=col) (t:=t) W P clique
  change edges g P=0 at no
  have ec := edges_le_slots g Z
  have cc := cut_hole_sum (col:=col) (t:=t) P Z
  change cut g Z P ≤ _ at cc
  omega

/-- Exact row capacity consequence: more than d arrivals of bounded total
excess holes are impossible at a clique whose length is r−d. -/
theorem routed_row_capacity (bal : Balanced col r) (P Z : List V) (d K : Nat)
    (distinct : (Z++P).Nodup) (clique : P.Pairwise (fun x y=>col x y=t))
    (len : P.length+d=r)
    (debt : arrivalDebt col t P Z≤K)
    (palette : pairSlots (d+1)+(d+1)+K<r-1) :
    Z.length≤d := by
  apply Classical.byContradiction
  intro big
  let Y := Z.take (d+1)
  have sub : Y.Sublist Z := List.take_sublist _ _
  have yd : (Y++P).Nodup := (sub.append (List.Sublist.refl P)).nodup distinct
  have ly : Y.length=d+1 := by
    simp only [Y,List.length_take]
    omega
  have tot : Y.length+P.length=r+1 := by omega
  have low := palette_count_of_row bal P Y yd clique tot
  have dg := arrivalDebt_sublist col t P sub
  rw [ly] at low
  omega

end ParallelMantel.Pentagon

#print axioms ParallelMantel.Pentagon.palette_count_of_row
#print axioms ParallelMantel.Pentagon.routed_row_capacity
