module

public import Proofs.VanCottZhang

@[expose] public section

set_option autoImplicit false
namespace CoinOrder.Family

def top (k : Nat) := 22 + 3*k

def tail : Nat → List Nat
  | 0 => [22,19,16,14,13,10,8,7,5,4,2,1]
  | k+1 => top (k+1) :: tail k

def full (k : Nat) := (top k + 6) :: tail k

def coin (k x : Nat) : Prop :=
  (x % 3 = 1 ∧ x ≤ top k) ∨ x = 2 ∨ x = 5 ∨ x = 8 ∨ x = 14

instance (k x : Nat) : Decidable (coin k x) := by unfold coin; infer_instance

theorem mem_tail (k x : Nat) : x ∈ tail k ↔ coin k x := by
  induction k with
  | zero =>
    simp only [tail, List.mem_cons, List.not_mem_nil, or_false, coin, top]
    omega
  | succ k ih =>
    simp only [tail, List.mem_cons, ih, coin, top]
    omega

theorem small (k v : Nat) (h : v < 22) :
    greedyCount (tail k) v = greedyCount (tail 0) v := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have ht : v < top (k+1) := by unfold top; omega
    simp only [tail, greedyCount, Nat.div_eq_of_lt ht, Nat.mod_eq_of_lt ht,
      Nat.zero_add, ih]

def profile (k v : Nat) : Nat :=
  if v = 0 then 0 else if coin k v then 1 else if v = top k+3 then 3 else 2

theorem greedy_profile (k v : Nat) (h : v < top k + 6) :
    greedyCount (tail k) v = profile k v := by
  induction k with
  | zero =>
    have hv : v < 28 := by simpa [top] using h
    have cert : ∀ x : Fin 28,
      greedyCount (tail 0) x.val = profile 0 x.val := by decide
    exact cert ⟨v,hv⟩
  | succ k ih =>
    let a := top (k+1)
    have ha : a = top k + 3 := by dsimp [a,top]; omega
    change greedyCount (a :: tail k) v = profile (k+1) v
    by_cases hv : v < a
    · rw [greedyCount, Nat.div_eq_of_lt hv, Nat.mod_eq_of_lt hv, Nat.zero_add, ih (by omega)]
      have hc : coin k v ↔ coin (k+1) v := by unfold coin top at *; dsimp [a,top] at *; omega
      simp [profile,hc, show v ≠ top k + 3 by omega, show v ≠ top (k+1) + 3 by omega]
    · have hb : v = a + (v-a) := by omega
      have hr : v - a < 6 := by change v < a + 6 at h; omega
      have hap : 0 < a := by dsimp [a,top]; omega
      have hlt : v-a < a := by dsimp [a,top] at *; omega
      have ht : v % a = v-a := by
        conv => lhs; rw [hb]
        rw [Nat.add_mod_left, Nat.mod_eq_of_lt hlt]
      have hq : v / a = 1 := by
        have hh := Nat.mod_add_div v a
        rw [ht] at hh
        have hx : a * (v / a) = a := by omega
        exact Nat.eq_of_mul_eq_mul_left hap (hx.trans (Nat.mul_one a).symm)
      rw [greedyCount,hq,ht,small k _ (by omega)]
      have rr := v-a
      have aux (r : Nat) (hr : r < 6) :
          1 + greedyCount (tail 0) r = if r = 0 then 1 else if r = 3 then 3 else 2 := by
        have cert : ∀ x : Fin 6, 1 + greedyCount (tail 0) x.val =
          if x.val = 0 then 1 else if x.val = 3 then 3 else 2 := by decide
        exact cert ⟨r,hr⟩
      rw [aux _ hr]
      have hc : coin (k+1) v ↔ v-a = 0 := by
        change v < a + 6 at h
        unfold coin
        dsimp [a,top] at *
        omega
      simp [profile,hc, show v ≠ 0 by omega, show (v-a=3) ↔ v=top (k+1)+3 by omega]

end CoinOrder.Family
