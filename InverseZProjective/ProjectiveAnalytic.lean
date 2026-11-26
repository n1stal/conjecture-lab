module
public import InverseZProjective.ProjectiveFactor
public import Mathlib.Tactic.Linarith
@[expose] public section
set_option autoImplicit false
namespace InverseZProjective.GaussianIncidence
open Finset

theorem gaussianCount_pos (K : Type*) [Field K] [Finite K] (n i : ℕ) (hi : i ≤ n) :
    0 < gaussianCount K n i := by
  induction n generalizing i with
  | zero =>
    have he : i = 0 := by omega
    subst i
    rw [gaussianCount_zero]
    decide
  | succ n ih =>
    cases i with
    | zero => simp [gaussianCount_zero]
    | succ i =>
      rw [gaussian_pascal K n i (by omega)]
      exact Nat.add_pos_left (ih i (by omega)) _

theorem gaussianA_pos (K : Type*) [Field K] [Finite K] (n i : ℕ) (hi : i ≤ n) :
    0 < gaussianA K n i := by
  unfold gaussianA
  have hc : 0 < (gaussianCount K n i : ℤ) := by exact_mod_cast gaussianCount_pos K n i hi
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hq' : 1 < (Nat.card K : ℤ) := by exact_mod_cast hq
  exact mul_pos hc (pow_pos (by omega) _)

theorem gaussianA_ratio (K : Type*) [Field K] [Finite K] (n i : ℕ) (hi : i < n) :
    gaussianA K n (i+1) * (Nat.card K : ℤ)^(n-i) * ((Nat.card K : ℤ)^(i+1)-1) =
      gaussianA K n i * (Nat.card K : ℤ)^(i+1) * ((Nat.card K : ℤ)^(n-i)-1) := by
  let q : ℤ := Nat.card K
  let j := n-i-1
  have hj : j+1=n-i := by omega
  have hj' : n-(i+1)=j := by omega
  have h := congrArg (fun t : ℕ => (t:ℤ)) (gaussian_adjacent_ratio_canonical K n i hi)
  simp only [Nat.cast_mul, gaussianCount_one_canonical] at h
  change (gaussianCount K n (i+1) : ℤ)*(qInteger (Nat.card K) (i+1) : ℤ) =
    (gaussianCount K n i : ℤ)*(qInteger (Nat.card K) (n-i) : ℤ) at h
  have hc : (gaussianCount K n (i+1) : ℤ)*(q^(i+1)-1) =
      (gaussianCount K n i : ℤ)*(q^(n-i)-1) := by
    rw [← qInteger_mul_sub_one,← qInteger_mul_sub_one]
    calc
      _ = (q-1)*((gaussianCount K n (i+1) : ℤ)*(qInteger (Nat.card K) (i+1) : ℤ)) := by ring
      _ = (q-1)*((gaussianCount K n i : ℤ)*(qInteger (Nat.card K) (n-i) : ℤ)) := by rw [h]
      _ = _ := by ring
  unfold gaussianA
  change ((gaussianCount K n (i+1) : ℤ)*q^((i+1).choose 2+(n-(i+1)).choose 2))*q^(n-i)*(q^(i+1)-1) = _
  have hp : (i+1).choose 2+(n-(i+1)).choose 2+(n-i) =
      i.choose 2+(n-i).choose 2+(i+1) := by
    rw [hj',← hj, choose_two_step,choose_two_step]
    omega
  calc
    _ = ((gaussianCount K n (i+1) : ℤ)*(q^(i+1)-1))*
          q^((i+1).choose 2+(n-(i+1)).choose 2+(n-i)) := by rw [pow_add]; ring
    _ = ((gaussianCount K n i : ℤ)*(q^(n-i)-1))*q^(i.choose 2+(n-i).choose 2+(i+1)) := by rw [hc,hp]
    _ = _ := by rw [pow_add]; ring

private theorem cross_ratio_strict (q u v a b c : ℤ)
    (hq : 1 < q) (hu : 1 < u) (hv : 1 < v) (hb : 0 < b)
    (h₁ : b*(q*v)*(u-1) = a*u*(q*v-1))
    (h₂ : c*v*(q*u-1) = b*(q*u)*(v-1)) :
    a*c < b*b := by
  have hu' : q*(u-1) < q*u-1 := by rw [Int.mul_sub, Int.mul_one]; omega
  have hv' : q*(v-1) < q*v-1 := by rw [Int.mul_sub, Int.mul_one]; omega
  have hposU : 0 < q*(u-1) := Int.mul_pos (by omega) (by omega)
  have hposV : 0 < q*(v-1) := Int.mul_pos (by omega) (by omega)
  have hprod : (q*(u-1))*(q*(v-1)) < (q*u-1)*(q*v-1) :=
    Int.lt_trans (Int.mul_lt_mul_of_pos_right hu' hposV)
      (Int.mul_lt_mul_of_pos_left hv' (by omega))
  let E := (u*v)*((q*(u-1))*(q*(v-1)))
  let H := (u*v)*((q*u-1)*(q*v-1))
  have hEH : E < H := Int.mul_lt_mul_of_pos_left hprod (Int.mul_pos (by omega) (by omega))
  have hH : 0 ≤ H := by
    unfold H
    exact Int.mul_nonneg (Int.mul_nonneg (by omega) (by omega))
      (Int.mul_nonneg (by omega) (by omega))
  have heq : (a*c)*H = (b*b)*E := by
    calc
      (a*c)*H = (a*u*(q*v-1))*(c*v*(q*u-1)) := by unfold H; ac_rfl
      _ = (b*(q*v)*(u-1))*(b*(q*u)*(v-1)) := by rw [← h₁, h₂]
      _ = (b*b)*E := by unfold E; ac_rfl
  have himp : (a*c)*H < (b*b)*H := by
    rw [heq]
    exact Int.mul_lt_mul_of_pos_left hEH (Int.mul_pos hb hb)
  by_contra hn
  have h := Int.mul_le_mul_of_nonneg_right (show b*b ≤ a*c by omega) hH
  omega

theorem gaussianA_strict (K : Type*) [Field K] [Finite K] (n i : ℕ) (hi : i+2 ≤ n) :
    gaussianA K n i * gaussianA K n (i+2) < gaussianA K n (i+1)*gaussianA K n (i+1) := by
  let q : ℤ := Nat.card K
  have hq₀ : 1 < Nat.card K := Finite.one_lt_card
  have hq : 1 < q := by change 1 < (Nat.card K : ℤ); exact_mod_cast hq₀
  have h₁ := gaussianA_ratio K n i (by omega)
  have h₂ := gaussianA_ratio K n (i+1) (by omega)
  have hP : q^(n-i)=q*q^(n-(i+1)) := by
    rw [show n-i=n-(i+1)+1 by omega,pow_succ,mul_comm]
  have hI : q^(i+1+1)=q*q^(i+1) := by rw [pow_succ,mul_comm]
  change gaussianA K n (i+1)*q^(n-i)*(q^(i+1)-1) =
    gaussianA K n i*q^(i+1)*(q^(n-i)-1) at h₁
  change gaussianA K n (i+2)*q^(n-(i+1))*(q^(i+1+1)-1) =
    gaussianA K n (i+1)*q^(i+1+1)*(q^(n-(i+1))-1) at h₂
  rw [hP] at h₁
  rw [hI] at h₂
  exact cross_ratio_strict q (q^(i+1)) (q^(n-(i+1))) _ _ _
    hq (one_lt_pow₀ hq (by omega)) (one_lt_pow₀ hq (by omega))
    (gaussianA_pos K n _ (by omega)) h₁ h₂

theorem projectiveFactor_pos (K : Type*) [Field K] [Finite K] (n : ℕ) (D : ℤ) (i : ℕ)
    (hd : 0 ≤ D) (hk : 0 < profileEndpoint K n D) :
    0 < projectiveFactor K n D i := by
  have hq₀ : 1 < Nat.card K := Finite.one_lt_card
  have hq : 1 ≤ (Nat.card K : ℤ) := by exact_mod_cast hq₀.le
  have hh : 0 ≤ D*((Nat.card K : ℤ)^i-1)*((Nat.card K : ℤ)^(n-i)-1) :=
    mul_nonneg (mul_nonneg hd (sub_nonneg.mpr (one_le_pow₀ hq)))
      (sub_nonneg.mpr (one_le_pow₀ hq))
  unfold projectiveFactor
  omega

theorem projectiveFactor_concave (K : Type*) [Field K] [Finite K] (n : ℕ) (D : ℤ) (i : ℕ)
    (hi : i+2 ≤ n) (hd : 0 ≤ D) :
    projectiveFactor K n D i + projectiveFactor K n D (i+2) ≤
      projectiveFactor K n D (i+1) + projectiveFactor K n D (i+1) := by
  let q : ℤ := Nat.card K
  let E := profileEndpoint K n D
  have hq₀ : 1 < Nat.card K := Finite.one_lt_card
  have hq : 0 ≤ q := Int.natCast_nonneg _
  have hform (j : ℕ) (hj : j ≤ n) :
      projectiveFactor K n D j = E + D*(q^n+1-q^j-q^(n-j)) := by
    unfold projectiveFactor
    change E+D*(q^j-1)*(q^(n-j)-1) = _
    rw [← show j+(n-j)=n by omega, pow_add]
    have hg : j+(n-j)-j=n-j := by omega
    rw [hg]
    ring
  rw [hform i (by omega),hform (i+2) hi,hform (i+1) (by omega)]
  have hi₁ : n-(i+1) = n-(i+2)+1 := by omega
  have hi₀ : n-i = n-(i+2)+2 := by omega
  rw [hi₀,hi₁]
  simp only [pow_succ]
  have hh : 0 ≤ D*(q^i+q^(n-(i+2)))*(q-1)^2 :=
    mul_nonneg (mul_nonneg hd (add_nonneg (pow_nonneg hq _) (pow_nonneg hq _))) (sq_nonneg _)
  nlinarith only [hh]

theorem projectiveFactor_logConcave (K : Type*) [Field K] [Finite K] (n : ℕ) (D : ℤ) (i : ℕ)
    (hi : i+2 ≤ n) (hd : 0 ≤ D) (hk : 0 < profileEndpoint K n D) :
    projectiveFactor K n D i*projectiveFactor K n D (i+2) ≤
      projectiveFactor K n D (i+1)*projectiveFactor K n D (i+1) := by
  let a := projectiveFactor K n D i
  let b := projectiveFactor K n D (i+1)
  let c := projectiveFactor K n D (i+2)
  have ha : 0 < a := projectiveFactor_pos K n D _ hd hk
  have hb : 0 < b := projectiveFactor_pos K n D _ hd hk
  have hc : 0 < c := projectiveFactor_pos K n D _ hd hk
  have h : a+c ≤ b+b := projectiveFactor_concave K n D i hi hd
  have hm := mul_nonneg (show 0 ≤ b+b-a-c by omega) (show 0 ≤ b+b+a+c by omega)
  have he := sq_nonneg (a-c)
  change a*c ≤ b*b
  nlinarith only [hm,he]

#print axioms gaussianA_strict
#print axioms projectiveFactor_logConcave
end InverseZProjective.GaussianIncidence
