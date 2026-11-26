module
public import InverseZProjective.ProjectiveEndpoints
@[expose] public section
set_option autoImplicit false
namespace InverseZProjective.GaussianIncidence
open Module Finset InverseZ.Algebra InverseZProjective.ProjectiveTrace InverseZProjective.ProjectiveBridge

theorem choose_two_step (n : ℕ) : (n+1).choose 2 = n.choose 2+n := by
  have h := Nat.choose_succ_succ' n 1
  rw [Nat.choose_one_right] at h
  exact h.trans (Nat.add_comm _ _)

theorem qInteger_succ (q n : ℕ) : qInteger q (n+1) = qInteger q n + q^n := by
  unfold qInteger
  rw [sum_range_succ]

theorem qInteger_mul_sub_one (q n : ℕ) :
    ((q : ℤ)-1)*(qInteger q n : ℤ) = (q : ℤ)^n-1 := by
  induction n with
  | zero => simp [qInteger]
  | succ n ih =>
    rw [qInteger_succ,Nat.cast_add,Nat.cast_pow,mul_add,ih,pow_succ]
    ring

private theorem factored_scalar (q x y u v n G G₀ G₁ w D : ℤ)
    (hu : (q-1)*u=x-1) (hv : (q-1)*v=y-1) (hn : (q-1)*n=q^2*x*y-1)
    (h₀ : n*G₀=G*(v+y)) (h₁ : n*G₁=G*(u+x)) :
    (n*(q*x*y)*(q-1)^2)*(G*x*y*w-D*G₀*x*w+D*G₁*v*w) =
      (G*x*y*w)*(n*(q-1)^2*(q*x*y-D)+D*(q*x-1)*(q*y-1)) := by
  have hh : q*(q-1)^2*(u*v-x*y) = -n*(q-1)^2+(q*x-1)*(q*y-1) := by
    calc
      _ = q*(((q-1)*u)*((q-1)*v))-q*(q-1)^2*x*y := by ring
      _ = q*((x-1)*(y-1))-q*(q-1)^2*x*y := by rw [hu,hv]
      _ = -((q-1)*n)*(q-1)+(q*x-1)*(q*y-1) := by rw [hn]; ring
      _ = _ := by ring
  calc
    _ = q*(q-1)^2*(n*G*x*y*x*y*w-D*(n*G₀)*x*x*y*w+D*(n*G₁)*v*x*y*w) := by ring
    _ = q*(q-1)^2*(n*G*x*y*x*y*w-D*(G*(v+y))*x*x*y*w+D*(G*(u+x))*v*x*y*w) := by rw [h₀,h₁]
    _ = G*x*y*w*(n*(q*x*y)*(q-1)^2)+D*(G*x*y*w)*(q*(q-1)^2*(u*v-x*y)) := by ring
    _ = _ := by rw [hh]; ring

variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V] [Finite V] [LocallyFiniteOrder (Submodule K V)]
variable (S : Set V)
local notation "M" => representedMatroid (K:=K) S
local notation "r" => flatRank M
local notation "q" => (Nat.card K : ℤ)
local notation "Q" => Nat.card K
local notation "L" => matroidLayerCoefficient M (projA S) (projB S)

noncomputable def gaussianA (K : Type*) [Field K] (n i : ℕ) : ℤ :=
  gaussianCount K n i * (Nat.card K : ℤ)^(i.choose 2 + (n-i).choose 2)

noncomputable def profileScale (K : Type*) [Field K] (n : ℕ) : ℤ :=
  qInteger (Nat.card K) n * (Nat.card K : ℤ)^(n-1) * ((Nat.card K : ℤ)-1)^2

noncomputable def profileEndpoint (K : Type*) [Field K] (n : ℕ) (D : ℤ) : ℤ :=
  qInteger (Nat.card K) n * ((Nat.card K : ℤ)-1)^2 * ((Nat.card K : ℤ)^(n-1)-D)

noncomputable def projectiveFactor (K : Type*) [Field K] (n : ℕ) (D : ℤ) (i : ℕ) : ℤ :=
  profileEndpoint K n D + D*((Nat.card K : ℤ)^i-1)*((Nat.card K : ℤ)^(n-i)-1)

/-- The actual, unscaled flat-layer sum agrees with the projective factor after
    multiplying by the common denominator. -/
theorem projective_scaled_interior (hS : LinePreserving (K:=K) S) (b : Flats M)
    (i : ℕ) (h₀ : 0 < i) (hi : i < r b) :
    profileScale K (r b) * L b i =
      gaussianA K (r b) i * projectiveFactor K (r b) ((deletedInFlat S b).card : ℤ) i := by
  rw [projective_layer_interior S hS b i h₀ hi]
  let n := r b
  let j := n-i
  have hj : 0 < j := by omega
  have hjn : j < n := by omega
  have hip : i-1+1=i := by omega
  have hjp : j-1+1=j := by omega
  have hji : n-j=i := by omega
  have hn1 : n-1 = 1+(i-1)+(j-1) := by omega
  have hn2 : n = 2+(i-1)+(j-1) := by omega
  have hpI : q^i = q*q^(i-1) := by nth_rw 1 [← hip]; rw [pow_succ,mul_comm]
  have hpJ : q^j = q*q^(j-1) := by nth_rw 1 [← hjp]; rw [pow_succ,mul_comm]
  have hcI : q^(i.choose 2) = q^((i-1).choose 2)*q^(i-1) := by
    have hh := choose_two_step (i-1)
    rw [hip] at hh
    rw [hh,pow_add]
  have hcJ : q^(j.choose 2) = q^((j-1).choose 2)*q^(j-1) := by
    have hh := choose_two_step (j-1)
    rw [hjp] at hh
    rw [hh,pow_add]
  have hg : gaussianCount K n i = gaussianCount K n j := gaussianCount_symm_canonical K n i (by omega)
  have hPoint := congrArg (fun t : ℕ => (t : ℤ)) (gaussian_point_ratio_canonical K n (j-1))
  have hCodim := congrArg (fun t : ℕ => (t : ℤ)) (gaussian_codim_ratio_canonical K n j hjn)
  simp only [hjp,hji,Nat.cast_mul,gaussianCount_one_canonical] at hPoint hCodim
  have hQ₀ : (qInteger Q n : ℤ)*(gaussianCount K (n-1) (j-1) : ℤ) =
      (gaussianCount K n j : ℤ)*(qInteger Q (j-1) + q^(j-1)) := by
    rw [← Nat.cast_pow,← Nat.cast_add,← qInteger_succ,hjp]
    exact hPoint.symm
  have hQ₁ : (qInteger Q n : ℤ)*(gaussianCount K (n-1) j : ℤ) =
      (gaussianCount K n j : ℤ)*(qInteger Q (i-1)+q^(i-1)) := by
    rw [← Nat.cast_pow,← Nat.cast_add,← qInteger_succ,hip]
    exact hCodim.symm
  let D : ℤ := (deletedInFlat S b).card
  change profileScale K n *
      (q^(i.choose 2)*((gaussianCount K n j : ℤ)*q^(j.choose 2)- D * gaussianCount K (n-1) (j-1) * q^((j-1).choose 2)) +
       q^((i-1).choose 2)*(D * gaussianCount K (n-1) j * qInteger Q (j-1) * q^((j-1).choose 2))) = _
  rw [profileScale,gaussianA,projectiveFactor,profileEndpoint]
  change _ = ((gaussianCount K n i : ℤ)*q^(i.choose 2+j.choose 2)) *
    ((qInteger Q n : ℤ)*(q-1)^2*(q^(n-1)-((deletedInFlat S b).card : ℤ)) +
      ((deletedInFlat S b).card : ℤ)*(q^i-1)*(q^j-1))
  have hpn : q^(n-1) = q*q^(i-1)*q^(j-1) := by rw [hn1,pow_add,pow_add,pow_one]
  rw [hg,hcI,hcJ,pow_add q (i.choose 2) _,hcI,hcJ,hpI,hpJ,hpn]
  have hsz : (q-1)*(qInteger Q n : ℤ) = q^2*q^(i-1)*q^(j-1)-1 := by
    rw [qInteger_mul_sub_one,hn2,pow_add,pow_add]
  have hs := factored_scalar q (q^(i-1)) (q^(j-1)) (qInteger Q (i-1)) (qInteger Q (j-1))
    (qInteger Q n) (gaussianCount K n j) (gaussianCount K (n-1) (j-1)) (gaussianCount K (n-1) j)
    (q^((i-1).choose 2)*q^((j-1).choose 2)) ((deletedInFlat S b).card : ℤ)
    (qInteger_mul_sub_one Q (i-1)) (qInteger_mul_sub_one Q (j-1)) hsz hQ₀ hQ₁
  convert hs using 1 <;> ring


theorem gaussianA_symm (K : Type*) [Field K] (n i : ℕ) (hi : i ≤ n) :
    gaussianA K n (n-i) = gaussianA K n i := by
  unfold gaussianA
  rw [← gaussianCount_symm_canonical K n i hi,show n-(n-i)=i by omega,add_comm]

theorem projectiveFactor_symm (K : Type*) [Field K] (n : ℕ) (D : ℤ) (i : ℕ) (hi : i ≤ n) :
    projectiveFactor K n D (n-i) = projectiveFactor K n D i := by
  unfold projectiveFactor
  rw [show n-(n-i)=i by omega]
  ring

theorem profileScale_pos (K : Type*) [Field K] [Finite K] (n : ℕ) (hn : 0 < n) :
    0 < profileScale K n := by
  unfold profileScale
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hq' : 1 < (Nat.card K : ℤ) := by exact_mod_cast hq
  have hN : 0 < (qInteger (Nat.card K) n : ℤ) := by exact_mod_cast qInteger_pos (Nat.card K) n hn
  exact mul_pos (mul_pos hN (pow_pos (by omega) _)) (pow_pos (by omega) _)

theorem projective_scaled_zero (hS : LinePreserving (K:=K) S) (b : Flats M)
    (hb : 0 < r b) :
    profileScale K (r b) * L b 0 =
      gaussianA K (r b) 0 * projectiveFactor K (r b) ((deletedInFlat S b).card : ℤ) 0 := by
  rw [projective_layer_zero S b,projA]
  let n := r b-1
  have hbn : r b = n+1 := by omega
  rw [represented_signedMu_bottom S hS b n hbn]
  rw [hbn]
  simp only [profileScale,gaussianA,projectiveFactor,profileEndpoint,gaussianCount_zero,
    Nat.cast_one,one_mul,pow_zero,sub_self,mul_zero,zero_mul,add_zero,Nat.sub_zero,show Nat.choose 0 2 = 0 by decide,zero_add]
  rw [show n+1-1=n by omega,choose_two_step,pow_add]
  ring

theorem projective_scaled_layer (hS : LinePreserving (K:=K) S) (b : Flats M)
    (hb : 0 < r b) (i : ℕ) (hi : i ≤ r b) :
    profileScale K (r b) * L b i =
      gaussianA K (r b) i * projectiveFactor K (r b) ((deletedInFlat S b).card : ℤ) i := by
  by_cases h₀ : i = 0
  · subst i
    exact projective_scaled_zero S hS b hb
  by_cases ht : i = r b
  · subst i
    rw [projective_layer_top S b,← projective_layer_zero S b,projective_scaled_zero S hS b hb]
    have ha := gaussianA_symm K (r b) 0 (Nat.zero_le _)
    have hf := projectiveFactor_symm K (r b) ((deletedInFlat S b).card : ℤ) 0 (Nat.zero_le _)
    rw [Nat.sub_zero] at ha hf
    rw [ha,hf]
  · exact projective_scaled_interior S hS b i (by omega) (by omega)

theorem projective_source_coefficient (hS : LinePreserving (K:=K) S)
    (i : ℕ) (hi : i ≤ r (topFlat M)) (ht : 0 < r (topFlat M)) :
    profileScale K (r (topFlat M)) * (matroidInverseZ M).coeff i =
      gaussianA K (r (topFlat M)) i * projectiveFactor K (r (topFlat M))
        ((deletedInFlat S (topFlat M)).card : ℤ) i := by
  have hsym (b : Flats M) (j : ℕ) (hj : j ≤ r b) : L b (r b-j) = L b j := by
    by_cases hb : 0 < r b
    · apply mul_left_cancel₀ (ne_of_gt (profileScale_pos K (r b) hb))
      rw [projective_scaled_layer S hS b hb _ (by omega),
        projective_scaled_layer S hS b hb j hj, gaussianA_symm K _ _ hj,
        projectiveFactor_symm K _ _ _ hj]
    · have he : r b-j=j := by omega
      rw [he]
  rw [matroidInverseZ_coeff_of_layer_symmetry M (projA S) (projB S)
    (projA_bottom S) (projB_small S _ (by rw [flatRank_bottom]; decide)) (fun f _ => projB_small S f)
    hsym]
  exact projective_scaled_layer S hS (topFlat M) ht i hi

#print axioms projective_scaled_interior
#print axioms projective_source_coefficient
end InverseZProjective.GaussianIncidence
