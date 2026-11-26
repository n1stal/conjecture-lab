module

public import Proofs.CoinFamily.CoinFamily
public import Proofs.CoinFamily.FamilyResidues

@[expose] public section

set_option autoImplicit false
namespace CoinOrder.Family

private theorem coin_bridge (k v : Nat) :
    coin k v ↔ CoinFamilyResidue.LowerCoin (top k) v := by
  unfold coin CoinFamilyResidue.LowerCoin
  omega

private theorem profile_bridge (k v : Nat) :
    profile k v = CoinFamilyResidue.count (top k) v := by
  unfold profile CoinFamilyResidue.count
  by_cases h : coin k v
  · simp [h, (coin_bridge k v).mp h]
  · simp [h, mt (coin_bridge k v).mpr h]

theorem full_orderly (k : Nat) (hk : k ≠ 1) :
    Orderly (full k) := by
  let L := top k
  let M := L+6
  have hm : 0 < M := by dsimp [M,L,top]; omega
  have hL : L = 22 ∨ 28 ≤ L := by dsimp [L,top]; omega
  have hLmin : 22 ≤ L := by omega
  have hmod : L % 3 = 1 := by dsimp [L,top]; omega
  change Orderly (M :: tail k)
  apply orderly_of_residues M (tail k) hm
  · apply List.mem_cons_of_mem
    apply (mem_tail k 1).mpr
    unfold coin top
    omega
  intro d hd r hr
  have gsmall (v : Nat) (hv : v < M) : greedyCount (M :: tail k) v =
      CoinFamilyResidue.count L v := by
    simp only [greedyCount, Nat.div_eq_of_lt hv, Nat.mod_eq_of_lt hv, Nat.zero_add]
    rw [greedy_profile k v hv, profile_bridge]
  rcases List.mem_cons.mp hd with h | h
  · subst d
    have heq := greedy_period M (tail k) hm r 1
    rw [Nat.mul_one, Nat.add_comm r M] at heq
    omega
  · have hc := (coin_bridge k d).mp ((mem_tail k d).mp h)
    have hdc := CoinFamilyResidue.lower_range hLmin hc
    by_cases huv : d+r < M
    · rw [gsmall _ huv, gsmall _ hr]
      exact CoinFamilyResidue.unwrapped hL hmod hc
    · let s := d+r-M
      have hs : s < M := by dsimp [s,M] at *; omega
      have hs' : s + M = d+r := by dsimp [s]; omega
      have heq := greedy_period M (tail k) hm s 1
      rw [Nat.mul_one, hs', gsmall _ hs] at heq
      rw [heq, gsmall _ hr]
      have hh := CoinFamilyResidue.wrapped hLmin hmod hc hr (by omega)
      change CoinFamilyResidue.count L s ≤ CoinFamilyResidue.count L r at hh
      omega

#print axioms full_orderly
end CoinOrder.Family
