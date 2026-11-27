module

public import Proofs.VanCottZhang

@[expose] public section

set_option autoImplicit false
namespace CoinOrder

private theorem gc_skip (d x : Nat) (D : List Nat) (h : x < d) :
    greedyCount (d::D) x = greedyCount D x := by
  simp [greedyCount,Nat.div_eq_of_lt h,Nat.mod_eq_of_lt h]

private theorem gc_one (a : Nat) : greedyCount [1] a = a := by
  simp [greedyCount]

private theorem gc_once (d r : Nat) (D : List Nat) (h : r < d) :
    greedyCount (d::D) (d+r) = 1 + greedyCount D r := by
  have hh := greedy_period d D (by omega) r 1
  simpa [Nat.add_comm, gc_skip d r D h] using hh

private theorem gc_step_of_orderly (D : List Nat) (hO : Orderly D)
    (d : Nat) (hd : d ∈ D) (r : Nat) :
    greedyCount D (d+r) ≤ 1 + greedyCount D r := by
  obtain ⟨hm,hs⟩ := (hO r).1
  have hb := (hO (d+r)).2 (d::greedyCoins D r) (by
    constructor
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hh
      · exact hd
      · exact hm x hh
    · simp [hs])
  simpa [greedy_length,Nat.add_comm] using hb

private theorem three_remainder_bound (a b : Nat) (hab : a < b) (ha : 1 < a)
    (hO : Orderly [b,a,1]) (hr : 0 < b%a) : a ≤ b/a + b%a := by
  let q := b/a
  let t := b%a
  let v := b + (a-t)
  have hta : t < a := Nat.mod_lt _ (by omega)
  have hdecomp : t + a*q = b := Nat.mod_add_div _ _
  have hv : (q+1)*a = v := by
    dsimp [v]
    rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm q]
    omega
  let R := List.replicate (q+1) a
  have hR : Represents [b,a,1] v R := by
    refine ⟨?_,?_⟩
    · intro x hx
      have heq := (List.mem_replicate.mp hx).2
      simp [heq]
    · change (List.replicate (q+1) a).sum = v
      rw [List.sum_replicate_nat]
      exact hv
  have hh := (hO v).2 R hR
  rw [greedy_length] at hh
  have hcount : greedyCount [b,a,1] v = 1+(a-t) := by
    unfold v
    rw [gc_once _ _ _ (by omega),gc_skip _ _ _ (by change 0<t at hr; omega),gc_one]
  rw [hcount] at hh
  change 1+(a-t) ≤ (List.replicate (q+1) a).length at hh
  rw [List.length_replicate] at hh
  omega

private theorem small_tail_growth (a b s r : Nat) (ha : 1 < a) (hab : a < b)
    (hs : s = 0 ∨ s = 1 ∨ s = a)
    (hO : Orderly [b,a,1]) (hr : r < s) :
    greedyCount [b,a,1] r ≤ greedyCount [b,a,1] (b-s+r) := by
  rcases hs with hs | hs | hs
  · omega
  · subst s
    have hr0 : r=0 := by omega
    subst r
    simp [greedyCount]
  · subst s
    have hq : 1 ≤ b/a := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
    let q := b/a
    let t := b%a
    have hta : t < a := Nat.mod_lt _ (by omega)
    have hdecomp : t+a*q = b := Nat.mod_add_div _ _
    have hnorm : b-a+r = t+r + a*(q-1) := by
      have hu : q = (q-1)+1 := by change 1≤q at hq; omega
      have hmul : a*q = a*(q-1)+a := by
        conv => lhs; rw [hu]
        rw [Nat.mul_add,Nat.mul_one]
      omega
    have hbr : b-a+r < b := by omega
    rw [gc_skip _ _ _ (by omega : r < b),gc_skip _ _ _ hr,gc_one,gc_skip _ _ _ hbr,hnorm]
    rw [greedy_period _ _ (by omega),greedyCount]
    rw [gc_one]
    by_cases hc : t+r < a
    · rw [Nat.div_eq_of_lt hc,Nat.mod_eq_of_lt hc]
      omega
    · have hpos : 0 < b%a := by change 0<t; omega
      have hineq := three_remainder_bound a b hab ha hO hpos
      have hrest : t+r-a < a := by omega
      have hrewrite : (t+r) = (t+r-a)+a*1 := by omega
      have hdiv : (t+r)/a=1 := by
        conv => lhs; rw [hrewrite]
        rw [Nat.add_mul_div_left _ _ (by omega),Nat.div_eq_of_lt hrest,Nat.zero_add]
      have hmod : (t+r)%a=t+r-a := by
        conv => lhs; rw [hrewrite]
        rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hrest]
      rw [hdiv,hmod]
      change a ≤ q+t at hineq
      change 1 ≤ q at hq
      omega

/-- The four-denomination instance of the One Point Theorem with m=2,
    on the explicit greedy function; no external structural premise. -/
theorem four_orderly_of_residue (a b c : Nat) (ha : 1 < a) (hab : a < b) (hbc : b < c)
    (hc : c ≤ 2*b) (hO : Orderly [b,a,1])
    (hfit : 2*b=c ∨ 2*b=c+1 ∨ 2*b=c+a) :
    Orderly [c,b,a,1] := by
  let s := 2*b-c
  have hs : s=0 ∨ s=1 ∨ s=a := by
    dsimp [s]; omega
  have hss : s < b := by dsimp [s]; omega
  have he : c+s=2*b := by dsimp [s]; omega
  have compare (v : Nat) (hv : v < c+b) :
      greedyCount [c,b,a,1] v ≤ greedyCount [b,a,1] v := by
    by_cases hvc : v < c
    · rw [gc_skip _ _ _ hvc]; exact Nat.le_refl _
    · let r := v-c
      have hrv : v=c+r := by dsimp [r]; omega
      have hrb : r < b := by dsimp [r]; omega
      conv => lhs; rw [hrv]
      rw [gc_once _ _ _ (by omega : r<c)]
      by_cases hlarge : s ≤ r
      · have hv2 : v=(r-s)+b*2 := by omega
        conv => rhs; rw [hv2]
        rw [greedy_period _ _ (by omega)]
        have heq : greedyCount [b,a,1] r ≤ 1 + greedyCount [b,a,1] (r-s) := by
          by_cases h0 : s=0
          · simp [h0]
          · have hmem : s ∈ [b,a,1] := by
              rcases hs with h | h | h
              · omega
              · simp [h]
              · simp [h]
            have hstep := gc_step_of_orderly [b,a,1] hO s hmem (r-s)
            rwa [show s+(r-s)=r by omega] at hstep
        omega
      · have hsmall : r < s := by omega
        have hv1 : v=b+(b-s+r) := by omega
        have hres : b-s+r < b := by omega
        conv => rhs; rw [hv1]
        rw [gc_once _ _ _ hres,←gc_skip b _ _ hres]
        have hg := small_tail_growth a b s r ha hab hs hO hsmall
        omega
  apply orderly_of_residues c [b,a,1] (by omega) (by simp)
  intro d hd r hr
  rcases List.mem_cons.mp hd with hdc | hd
  · subst d
    rw [gc_once _ _ _ hr,gc_skip _ _ _ hr]; exact Nat.le_refl _
  · have hdb : d ≤ b := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hd
      omega
    rw [gc_skip _ _ _ hr]
    exact Nat.le_trans (compare _ (by omega)) (gc_step_of_orderly _ hO d hd r)

#print axioms four_orderly_of_residue
end CoinOrder
