module

public import Std

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 4096
namespace CoinOrder

/-- Greedy processes the denominations in decreasing order. -/
def greedyCount : List Nat → Nat → Nat
  | [], _ => 0
  | d :: ds, v => v / d + greedyCount ds (v % d)

noncomputable def greedyCoins : List Nat → Nat → List Nat :=
  List.rec (fun _ => [])
    (fun d _ rec v => List.replicate (v / d) d ++ rec (v % d))

@[simp] private theorem greedyCoins_nil (v : Nat) : greedyCoins [] v = [] := rfl

@[simp] private theorem greedyCoins_cons (d : Nat) (ds : List Nat) (v : Nat) :
    greedyCoins (d::ds) v = List.replicate (v / d) d ++ greedyCoins ds (v % d) := rfl

def Represents (C : List Nat) (v : Nat) (R : List Nat) : Prop :=
  (∀ x ∈ R, x ∈ C) ∧ R.sum = v

/-- The greedy representation is valid and uses at most as many coins
    as every other representation, for every amount. -/
def Orderly (C : List Nat) : Prop :=
  ∀ v, Represents C v (greedyCoins C v) ∧
    ∀ R, Represents C v R → (greedyCoins C v).length ≤ R.length

theorem greedy_length (C : List Nat) (v : Nat) :
    (greedyCoins C v).length = greedyCount C v := by
  induction C generalizing v with
  | nil => rfl
  | cons d ds ih =>
    simp [greedyCount, ih]

private theorem greedy_zero (C : List Nat) : greedyCoins C 0 = [] := by
  induction C with
  | nil => rfl
  | cons d ds ih => simp [ih]

private theorem sum_replicate_nat (n x : Nat) :
    (List.replicate n x).sum = n*x := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih, Nat.succ_mul, Nat.add_comm]

private theorem greedy_members (C : List Nat) (v : Nat) :
    ∀ x ∈ greedyCoins C v, x ∈ C := by
  induction C generalizing v with
  | nil => simp
  | cons d ds ih =>
    intro x hx
    rw [greedyCoins_cons, List.mem_append] at hx
    rcases hx with h | h
    · have hxD : x=d := (List.mem_replicate.mp h).2
      subst x
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih _ x h)

private theorem greedy_sum (C : List Nat) (one : 1 ∈ C) (v : Nat) :
    (greedyCoins C v).sum = v := by
  induction C generalizing v with
  | nil => simp at one
  | cons d ds ih =>
    simp only [greedyCoins_cons,List.sum_append,sum_replicate_nat]
    have resid : (greedyCoins ds (v % d)).sum = v % d := by
      rcases List.mem_cons.mp one with hd | hs
      · rw [← hd,Nat.mod_one,greedy_zero]; rfl
      · exact ih hs _
    rw [resid, Nat.mul_comm (v / d) d, Nat.add_comm]
    exact Nat.mod_add_div v d

/-- Adding q copies of the first denomination adds q to the greedy count.
    We use it with the largest coin first. -/
theorem greedy_period (m : Nat) (D : List Nat) (hm : 0 < m) (r q : Nat) :
    greedyCount (m :: D) (r + m*q) = greedyCount (m :: D) r + q := by
  simp only [greedyCount, Nat.add_mul_div_left _ _ hm, Nat.add_mul_mod_self_left]
  omega

/-- Finite Bellman test, one check for each denomination and each
    residue modulo the largest denomination. Unlike a raw finite
    comparison, this lemma proves a criterion for every amount. -/
theorem orderly_of_residues (m : Nat) (D : List Nat) (hm : 0 < m)
    (hOne : 1 ∈ m :: D)
    (h : ∀ d ∈ m :: D, ∀ r < m,
      greedyCount (m :: D) (d+r) ≤ 1 + greedyCount (m :: D) r) :
    Orderly (m :: D) := by
  let C := m :: D
  have hstep (d : Nat) (hd : d ∈ C) (v : Nat) :
      greedyCount C (d+v) ≤ 1 + greedyCount C v := by
    have hh := h d hd (v % m) (Nat.mod_lt _ hm)
    change greedyCount C (d + v % m) ≤ 1 + greedyCount C (v % m) at hh
    have hdec := Nat.mod_add_div v m
    have hl := greedy_period m D hm (d + v % m) (v / m)
    have hr := greedy_period m D hm (v % m) (v / m)
    rw [Nat.add_assoc, hdec] at hl
    rw [hdec] at hr
    change greedyCount C (d+v) = greedyCount C (d + v % m) + v / m at hl
    change greedyCount C v = greedyCount C (v % m) + v / m at hr
    omega
  have hrep (R : List Nat) (hR : ∀ d ∈ R, d ∈ C) :
      greedyCount C R.sum ≤ R.length := by
    induction R with
    | nil => rw [← greedy_length, List.sum_nil, greedy_zero]; simp
    | cons d R ih =>
      have htail := ih fun x hx => hR x (List.mem_cons_of_mem _ hx)
      have hfront := hstep d (hR d List.mem_cons_self) R.sum
      simp only [List.sum_cons,List.length_cons]
      omega
  intro v
  refine ⟨⟨greedy_members C v,greedy_sum C hOne v⟩,?_⟩
  intro R hR
  rw [greedy_length, ← hR.2]
  exact hrep R hR.1

def residuesPass (m : Nat) (D : List Nat) : Bool :=
  (m :: D).all fun d => (List.range m).all fun r =>
    decide (greedyCount (m :: D) (d+r) ≤ 1 + greedyCount (m :: D) r)

theorem orderly_of_check (m : Nat) (D : List Nat) (hm : 0 < m)
    (hOne : 1 ∈ m :: D) (h : residuesPass m D = true) :
    Orderly (m :: D) := by
  apply orderly_of_residues m D hm hOne
  intro d hd r hr
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp h d hd) r (List.mem_range.mpr hr))

theorem not_orderly_of_better (C : List Nat) (v : Nat) (R : List Nat)
    (hmem : R.all (fun x => decide (x ∈ C)) = true) (hsum : R.sum = v)
    (hlt : R.length < greedyCount C v) : ¬ Orderly C := by
  intro h
  have he := (h v).2 R ⟨fun x hx => of_decide_eq_true (List.all_eq_true.mp hmem x hx), hsum⟩
  rw [greedy_length] at he
  exact (Nat.not_lt_of_le he) hlt

def C13 : List Nat := [1,2,4,5,7,8,10,12,15,18,23,26,34]
def coinPrefix (C : List Nat) (n : Nat) : List Nat := (C.take n).reverse

set_option maxHeartbeats 3000000 in
theorem final_orderly : Orderly C13.reverse := by
  apply orderly_of_check 34 [26,23,18,15,12,10,8,7,5,4,2,1] <;> decide

theorem first_three_orderly (i : Nat) (h1 : 1 ≤ i) (h3 : i ≤ 3) :
    Orderly (coinPrefix C13 i) := by
  have hi : i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hi with rfl | rfl | rfl
  · exact orderly_of_check 1 [] (by decide) (by decide) (by decide)
  · exact orderly_of_check 2 [1] (by decide) (by decide) (by decide)
  · exact orderly_of_check 4 [2,1] (by decide) (by decide) (by decide)

theorem all_middle_nonorderly (i : Nat) (h4 : 4 ≤ i) (h13 : i < C13.length) :
    ¬ Orderly (coinPrefix C13 i) := by
  have hi : i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨
      i = 10 ∨ i = 11 ∨ i = 12 := by
    change i < 13 at h13
    omega
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact not_orderly_of_better _ 8 [4,4] (by decide) (by decide) (by decide)
  · exact not_orderly_of_better _ 10 [5,5] (by decide) (by decide) (by decide)
  · exact not_orderly_of_better _ 11 [4,7] (by decide) (by decide) (by decide)
  · exact not_orderly_of_better _ 13 [5,8] (by decide) (by decide) (by decide)
  · exact not_orderly_of_better _ 15 [5,10] (by decide) (by decide) (by decide)
  · exact not_orderly_of_better _ 18 [8,10] (by decide) (by decide) (by decide)
  · exact not_orderly_of_better _ 24 [12,12] (by decide) (by decide) (by decide)
  · exact not_orderly_of_better _ 26 [8,18] (by decide) (by decide) (by decide)
  · exact not_orderly_of_better _ 35 [12,23] (by decide) (by decide) (by decide)

/-- Van Cott--Zhang, arXiv:2303.00078v2, Conjecture 5.2(1). There is
    allegedly no system of 3r+1 values with the +++-...-+ prefix pattern. -/
def VanCottZhangConjecture521 : Prop :=
  ¬ ∃ (r : Nat) (C : List Nat), 2 ≤ r ∧ C.length = 3*r+1 ∧
    C.head? = some 1 ∧ C.Pairwise (· < ·) ∧
    (∀ i : Nat, 1 ≤ i → i ≤ 3 → Orderly (coinPrefix C i)) ∧
    (∀ i : Nat, 4 ≤ i → i < C.length → ¬ Orderly (coinPrefix C i)) ∧
    Orderly C.reverse

theorem vanCottZhangConjecture521_false : ¬ VanCottZhangConjecture521 := by
  intro h
  exact h ⟨4,C13,by decide,by decide,by decide,by decide,
    first_three_orderly,all_middle_nonorderly,final_orderly⟩

#print axioms orderly_of_residues
#print axioms final_orderly
#print axioms all_middle_nonorderly
#print axioms vanCottZhangConjecture521_false

end CoinOrder
