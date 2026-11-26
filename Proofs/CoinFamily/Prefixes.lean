module

public import Proofs.CoinFamily.CoinFamily

@[expose] public section

set_option autoImplicit false
namespace CoinOrder.Family

theorem prefix_cons (a : Nat) (D : List Nat) (i : Nat) (hi : i ≤ D.length) :
    coinPrefix (a::D).reverse i = coinPrefix D.reverse i := by
  unfold coinPrefix
  rw [List.reverse_cons,List.take_append_of_le_length (by simpa using hi)]

@[simp] theorem tail_length (k : Nat) : (tail k).length = k+12 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [tail,ih]

@[simp] theorem full_length (k : Nat) : (full k).length = k+13 := by
  simp [full]

theorem first (k i : Nat) (h1 : 1 ≤ i) (h3 : i ≤ 3) :
    Orderly (coinPrefix (full k).reverse i) := by
  unfold full
  rw [prefix_cons _ _ _ (by simp; omega)]
  induction k with
  | zero =>
    have hi : i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi with rfl | rfl | rfl
    · exact orderly_of_check 1 [] (by decide) (by decide) (by decide)
    · exact orderly_of_check 2 [1] (by decide) (by decide) (by decide)
    · exact orderly_of_check 4 [2,1] (by decide) (by decide) (by decide)
  | succ k ih =>
    change Orderly (coinPrefix (top (k+1) :: tail k).reverse i)
    rwa [prefix_cons _ _ _ (by simp; omega)]

private theorem nonorderly_better (D : List Nat) (v x y : Nat)
    (hx : x ∈ D) (hy : y ∈ D) (hv : x+y=v)
    (hcount : 2 < greedyCount D v) : ¬ Orderly D := by
  apply not_orderly_of_better D v [x,y]
  · simp [hx,hy]
  · simpa using hv
  · exact hcount

theorem tail_nonorderly (k : Nat) : ¬ Orderly (tail k) := by
  cases k with
  | zero => exact nonorderly_better _ 28 14 14 (by decide) (by decide) (by decide) (by decide)
  | succ k =>
    let A := top (k+1)
    have hA : 11 < A := by dsimp [A,top]; omega
    exact nonorderly_better _ (11+A) (top k) 14
      (by change top k ∈ A :: tail k
          refine List.mem_cons_of_mem _ ((mem_tail k _).2 (Or.inl ⟨?_,Nat.le_refl _⟩))
          unfold top; omega)
      (by apply (mem_tail _ _).2; exact Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      (by dsimp [A,top]; omega)
      (by
        change 2 < greedyCount (A :: tail k) (11+A)
        rw [greedyCount]
        have hd := Nat.add_mul_div_left 11 1 (show 0 < A by omega)
        rw [Nat.mul_one,Nat.div_eq_of_lt hA,Nat.zero_add] at hd
        rw [hd,Nat.add_mod_right,Nat.mod_eq_of_lt hA,small k _ (by decide)]
        decide)

theorem middle_tail (k i : Nat) (h4 : 4 ≤ i) (ht : i ≤ (tail k).length) :
    ¬ Orderly (coinPrefix (tail k).reverse i) := by
  by_cases he : i = (tail k).length
  · subst i
    unfold coinPrefix
    rw [List.take_of_length_le (by simp), List.reverse_reverse]
    exact tail_nonorderly k
  · induction k with
    | zero =>
      have hi : i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 := by
        simp only [tail_length] at *; omega
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact nonorderly_better _ 8 4 4 (by decide) (by decide) (by decide) (by decide)
      · exact nonorderly_better _ 10 5 5 (by decide) (by decide) (by decide) (by decide)
      · exact nonorderly_better _ 11 4 7 (by decide) (by decide) (by decide) (by decide)
      · exact nonorderly_better _ 13 5 8 (by decide) (by decide) (by decide) (by decide)
      · exact nonorderly_better _ 16 8 8 (by decide) (by decide) (by decide) (by decide)
      · exact nonorderly_better _ 17 4 13 (by decide) (by decide) (by decide) (by decide)
      · exact nonorderly_better _ 19 5 14 (by decide) (by decide) (by decide) (by decide)
      · exact nonorderly_better _ 22 8 14 (by decide) (by decide) (by decide) (by decide)
    | succ k ih =>
      change ¬ Orderly (coinPrefix (top (k+1) :: tail k).reverse i)
      have hs : i ≤ (tail k).length := by simp only [tail_length] at *; omega
      rw [prefix_cons _ _ _ hs]
      by_cases hj : i = (tail k).length
      · subst i
        unfold coinPrefix
        rw [List.take_of_length_le (by simp),List.reverse_reverse]
        exact tail_nonorderly k
      · exact ih hs hj

theorem middle (k i : Nat) (h4 : 4 ≤ i) (ht : i < (full k).length) :
    ¬ Orderly (coinPrefix (full k).reverse i) := by
  have hs : i ≤ (tail k).length := by simp only [full_length,tail_length] at *; omega
  unfold full
  rw [prefix_cons _ _ _ hs]
  exact middle_tail k i h4 hs

theorem tail_strict (k : Nat) : (tail k).Pairwise (fun x y => y < x) := by
  induction k with
  | zero => decide
  | succ k ih =>
    simp only [tail,List.pairwise_cons]
    refine ⟨fun x hx => ?_,ih⟩
    have hh := (mem_tail _ _).1 hx
    unfold coin top at *
    omega

theorem full_strict (k : Nat) : (full k).reverse.Pairwise (· < ·) := by
  rw [List.pairwise_reverse]
  simp only [full,List.pairwise_cons]
  refine ⟨fun x hx => ?_,tail_strict k⟩
  have hh := (mem_tail _ _).1 hx
  unfold coin top at *
  omega

theorem tail_unit (k : Nat) : (tail k).getLast? = some 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [tail,List.getLast?_cons,ih]

theorem full_unit (k : Nat) : (full k).reverse.head? = some 1 := by
  simp [full,List.head?_reverse,tail_unit]

/-- Exact Van Cott–Zhang prefix pattern at length n. -/
def HasPrefixPattern (n : Nat) : Prop :=
  ∃ C : List Nat, C.length = n ∧ C.head? = some 1 ∧ C.Pairwise (· < ·) ∧
    (∀ i, 1 ≤ i → i ≤ 3 → Orderly (coinPrefix C i)) ∧
    (∀ i, 4 ≤ i → i < C.length → ¬ Orderly (coinPrefix C i)) ∧
    Orderly C.reverse

theorem hasPrefixPattern_at (k : Nat) (hLast : Orderly (full k)) :
    HasPrefixPattern (k + 13) := by
  refine ⟨(full k).reverse,by simp,full_unit k,full_strict k,first k,?_,by simpa using hLast⟩
  intro i h4 hi
  exact middle k i h4 (by simpa using hi)

theorem hasPrefixPattern_at_length (n : Nat) (hn : 13 ≤ n)
    (hLast : Orderly (full (n-13))) : HasPrefixPattern n := by
  have h := hasPrefixPattern_at (n-13) hLast
  rwa [Nat.sub_add_cancel hn] at h

#print axioms first
#print axioms middle
#print axioms hasPrefixPattern_at_length

end CoinOrder.Family
