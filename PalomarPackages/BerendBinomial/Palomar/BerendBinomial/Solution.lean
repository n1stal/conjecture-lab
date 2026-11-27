module

public import Mathlib

@[expose] public section

/-  Finite binomial reflection and endpoint deletion. -/
namespace BerendBinomial
open Polynomial Finset
open scoped BigOperators

abbrev Nodes (m : Nat) := Fin (m+1)
abbrev Poly := Polynomial ℝ

def x {m : Nat} (i : Nodes m) : ℝ := i.val

def bin (m : Nat) (p : ℝ) (i : Nodes m) : ℝ :=
  (m.choose i.val : ℝ) * p^i.val * (1-p)^(m-i.val)

def moment {m : Nat} (u : Nodes m → ℝ) (f : Poly) : ℝ :=
  ∑ i, u i * f.eval (x i)

def Quadrature {m : Nat} (d : Nat) (p : ℝ) (u : Nodes m → ℝ) : Prop :=
  ∀ f : Poly, f.natDegree ≤ d → moment u f = moment (bin m p) f

def rev (m : Nat) : Equiv.Perm (Nodes m) where
  toFun i := ⟨m-i.val, by omega⟩
  invFun i := ⟨m-i.val, by omega⟩
  left_inv i := Fin.ext (by simp; omega)
  right_inv i := Fin.ext (by simp; omega)

theorem rev_twice {m : Nat} (i : Nodes m) : rev m (rev m i) = i :=
  (rev m).left_inv i

theorem x_rev {m : Nat} (i : Nodes m) : x (rev m i) = (m:ℝ)-x i := by
  change (↑(m-i.val):ℝ) = (m:ℝ)-(i.val:ℝ)
  rw [Nat.cast_sub (by omega : i.val ≤ m)]

theorem bin_reflect {m : Nat} (p : ℝ) (i : Nodes m) :
    bin m (1-p) (rev m i) = bin m p i := by
  have h : i.val ≤ m := by omega
  have e : m-(m-i.val)=i.val := by omega
  simp only [bin,rev,Equiv.coe_fn_mk]
  rw [Nat.choose_symm h, e]
  ring

theorem natDegree_C_sub_X (a : ℝ) : (C a-X : Poly).natDegree = 1 := by
  have h : (C a-X : Poly) = -(X-C a) := by ring
  rw [h,natDegree_neg,natDegree_X_sub_C]

noncomputable def reflectPoly (m : Nat) (f : Poly) : Poly := f.comp (C (m:ℝ)-X)

theorem reflectPoly_degree (m : Nat) (f : Poly) :
    (reflectPoly m f).natDegree ≤ f.natDegree := by
  unfold reflectPoly
  calc
    _ ≤ f.natDegree * (C (m:ℝ)-X : Poly).natDegree := natDegree_comp_le
    _ ≤ f.natDegree * 1 := by
      apply Nat.mul_le_mul_left
      exact (natDegree_C_sub_X _).le
    _ = _ := Nat.mul_one _

theorem reflectPoly_eval {m : Nat} (f : Poly) (i : Nodes m) :
    (reflectPoly m f).eval (x i) = f.eval (x (rev m i)) := by
  simp [reflectPoly, x_rev]

theorem moment_reflect {m : Nat} (u : Nodes m → ℝ) (f : Poly) :
    moment (u ∘ rev m) f = moment u (reflectPoly m f) := by
  classical
  unfold moment
  have he := Equiv.sum_comp (rev m) (fun i : Nodes m => u (rev m i) * f.eval (x i))
  simpa only [Function.comp_apply, reflectPoly_eval, rev_twice] using he.symm

theorem quadrature_reflect {m d : Nat} {p : ℝ} {u : Nodes m → ℝ}
    (h : Quadrature d p u) : Quadrature d (1-p) (u ∘ rev m) := by
  intro f hf
  have hbin : bin m p ∘ rev m = bin m (1-p) := by
    funext i
    have hh := bin_reflect p (rev m i)
    simpa only [Function.comp_apply, rev_twice] using hh.symm
  calc
    _ = moment u (reflectPoly m f) := moment_reflect u f
    _ = moment (bin m p) (reflectPoly m f) := h _ ((reflectPoly_degree _ _).trans hf)
    _ = _ := by rw [← moment_reflect, hbin]

noncomputable def deleteEndpoint {m : Nat} (p : ℝ) (u : Nodes (m+1) → ℝ) (i : Nodes m) : ℝ :=
  ((((m+1:ℕ):ℝ)-x i) * u i.castSucc) / (((m+1:ℕ):ℝ)*(1-p))

theorem bin_remove {m : Nat} (p : ℝ) (i : Nodes m) :
    ((((m+1:ℕ):ℝ)-x i) * bin (m+1) p i.castSucc) =
      (((m+1:ℕ):ℝ)*(1-p)) * bin m p i := by
  have hi : i.val ≤ m := by omega
  have he : m+1-i.val=(m-i.val)+1 := by omega
  have hc := Nat.choose_mul_succ_eq m i.val
  have hcast : ((m+1-i.val:ℕ):ℝ) = (((m+1:ℕ):ℝ)-x i) := by
    exact Nat.cast_sub (by omega)
  unfold bin
  simp only [Fin.val_castSucc, he, pow_succ]
  rw [← hcast]
  have hc' := congrArg (fun z : Nat => (z:ℝ)) hc
  push_cast at hc'
  rw [hcast] at hc'
  calc
    _ = ((((m+1:ℕ):ℝ)-x i) * ((m+1).choose i.val:ℝ)) *
        (p^i.val * (1-p)^(m-i.val) * (1-p)) := by rw [hcast]; ring
    _ = _ := by rw [mul_comm ((((m+1:ℕ):ℝ)-x i)), ← hc']; push_cast; ring

noncomputable def endpointFactor (m : Nat) : Poly := C (((m+1:ℕ):ℝ))-X

theorem remove_moment {m : Nat} (p : ℝ) (hp : p ≠ 1)
    (u : Nodes (m+1) → ℝ) (f : Poly) :
    moment (deleteEndpoint p u) f =
      moment u (endpointFactor m * f) / (((m+1:ℕ):ℝ)*(1-p)) := by
  have hne : (((m+1:ℕ):ℝ)*(1-p)) ≠ 0 := by
    apply mul_ne_zero
    · positivity
    · exact sub_ne_zero.mpr (Ne.symm hp)
  unfold moment
  rw [Fin.sum_univ_castSucc (fun i : Nodes (m+1) => u i * (endpointFactor m * f).eval (x i))]
  simp only [endpointFactor, eval_mul, eval_sub, eval_C, eval_X, x, Fin.val_last]
  rw [sub_self, zero_mul, mul_zero, add_zero, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [deleteEndpoint, x, Fin.val_castSucc]
  field_simp

theorem quadrature_delete {m k : Nat} {p : ℝ} (hp : p ≠ 1) (hk : 0 < k)
    {u : Nodes (m+1) → ℝ} (h : Quadrature k p u) :
    Quadrature (k-1) p (deleteEndpoint p u) := by
  have hne : (((m+1:ℕ):ℝ)*(1-p)) ≠ 0 := by
    exact mul_ne_zero (by positivity) (sub_ne_zero.mpr (Ne.symm hp))
  have hbd : (endpointFactor m).natDegree ≤ 1 :=
    (natDegree_C_sub_X _).le
  have hprob : deleteEndpoint p (bin (m+1) p) = bin m p := by
    funext i
    unfold deleteEndpoint
    rw [bin_remove]
    field_simp
  intro f hf
  rw [remove_moment p hp]
  rw [h (endpointFactor m*f) (natDegree_mul_le.trans (by omega))]
  rw [← remove_moment p hp, hprob]

end BerendBinomial

/-  Constructive inverse to endpoint deletion and paired
   dual polynomial certificate; no LP black box used in reflection. -/
namespace BerendBinomial
open Polynomial Finset
open scoped BigOperators

noncomputable def liftEndpoint {m : Nat} (p : ℝ) (u : Nodes m → ℝ) (j : Nodes (m+1)) : ℝ :=
  Fin.lastCases
    (moment (bin (m+1) p) 1 -
      ∑ i : Nodes m, (((m+1:ℕ):ℝ)*(1-p))*u i / (((m+1:ℕ):ℝ)-x i))
    (fun i => (((m+1:ℕ):ℝ)*(1-p))*u i / (((m+1:ℕ):ℝ)-x i)) j

theorem endpoint_gap_pos {m : Nat} (i : Nodes m) :
    0 < (((m+1:ℕ):ℝ)-x i) := by
  unfold x
  have h : i.val < m+1 := i.isLt
  exact sub_pos.mpr (by exact_mod_cast h)

theorem lift_remove {m : Nat} {p : ℝ} (hp : p ≠ 1) (u : Nodes m → ℝ) :
    deleteEndpoint p (liftEndpoint p u) = u := by
  have he : (((m+1:ℕ):ℝ)*(1-p)) ≠ 0 :=
    mul_ne_zero (by positivity) (sub_ne_zero.mpr (Ne.symm hp))
  funext i
  simp [deleteEndpoint, liftEndpoint]
  have hgap : (↑m + (1:ℝ) - x i) ≠ 0 := by
    simpa only [Nat.cast_add, Nat.cast_one] using (endpoint_gap_pos i).ne'
  field_simp [hgap, he]

theorem lift_mass {m : Nat} (p : ℝ) (u : Nodes m → ℝ) :
    moment (liftEndpoint p u) 1 = moment (bin (m+1) p) 1 := by
  unfold moment
  rw [Fin.sum_univ_castSucc (fun i : Nodes (m+1) => liftEndpoint p u i * (1 : Poly).eval (x i))]
  simp [liftEndpoint, moment]

private theorem poly_split {k : Nat} (_hk : 0 < k) {f : Poly}
    (hf : f.natDegree ≤ k) (a : ℝ) :
    ∃ g : Poly, g.natDegree ≤ k-1 ∧ f = C (f.eval a) + (C a-X)*g := by
  let q := X - C a
  let g := -(f /ₘ q)
  have hm : q.Monic := monic_X_sub_C _
  have hd : q.natDegree = 1 := natDegree_X_sub_C _
  refine ⟨g,?_,?_⟩
  · have hh := natDegree_divByMonic f hm
    simp only [g,natDegree_neg,hd,hh]
    omega
  · have hh := modByMonic_add_div f q
    have hm' : f %ₘ q = C (f.eval a) := modByMonic_X_sub_C_eq_C_eval _ _
    rw [hm'] at hh
    calc
      f = C (f.eval a) + q * (f /ₘ q) := hh.symm
      _ = C (f.eval a) + (C a-X)*g := by dsimp [g,q]; ring

theorem quadrature_lift {m k : Nat} {p : ℝ} (hp : p ≠ 1) (hk : 0 < k)
    {u : Nodes m → ℝ} (h : Quadrature (k-1) p u) :
    Quadrature k p (liftEndpoint p u) := by
  intro f hf
  obtain ⟨g,hg,hf'⟩ := poly_split hk hf (((m+1:ℕ):ℝ))
  have hm : moment (liftEndpoint p u) (endpointFactor m*g) =
      moment (bin (m+1) p) (endpointFactor m*g) := by
    have h1 := remove_moment p hp (liftEndpoint p u) g
    rw [lift_remove hp] at h1
    have h2 := remove_moment p hp (bin (m+1) p) g
    have hd : deleteEndpoint p (bin (m+1) p) = bin m p := by
      funext i
      unfold deleteEndpoint
      rw [bin_remove]
      field_simp [sub_ne_zero.mpr (Ne.symm hp)]
    rw [hd] at h2
    have hne : (((m+1:ℕ):ℝ)*(1-p)) ≠ 0 :=
      mul_ne_zero (by positivity) (sub_ne_zero.mpr (Ne.symm hp))
    have he := h1.symm.trans ((h g hg).trans h2)
    exact (div_eq_div_iff hne hne).mp he |> fun eq => mul_right_cancel₀ hne eq
  rw [hf']
  change moment (liftEndpoint p u) (C (f.eval _) + endpointFactor m*g) =
      moment (bin (m+1) p) (C (f.eval _) + endpointFactor m*g)
  have decomp (v : Nodes (m+1) → ℝ) (c : ℝ) (P : Poly) :
      moment v (C c + P) = c * moment v 1 + moment v P := by
    simp only [moment,eval_add,eval_C,eval_one,mul_one,Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [decomp,decomp,lift_mass,hm]

/-- The lower support is a union of disjoint adjacent pairs. The explicit
pair separation is equivalent to the sorted condition in source Eq. (35). -/
def Paired (m k : Nat) (J : Finset (Nodes m)) : Prop :=
  J.card = k ∧ ∃ T : Finset Nat, 2*T.card=k ∧
    (∀ a ∈ T, a+1 ≤ m) ∧
    (∀ a ∈ T, ∀ b ∈ T, a < b → a+2 ≤ b) ∧
    ∀ i : Nodes m, i∈J ↔ ∃ a∈T, i.val=a ∨ i.val=a+1

noncomputable def pairPoly (T : Finset Nat) : Poly :=
  ∏ a ∈ T, (X-C (a:ℝ))*(X-C ((a+1:ℕ):ℝ))

theorem pairPoly_degree (T : Finset Nat) : (pairPoly T).natDegree ≤ 2*T.card := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [pairPoly]
  | @insert a T hT ih =>
    simp only [pairPoly,Finset.prod_insert hT,Finset.card_insert_of_notMem hT]
    have hf (b : ℝ) : (X-C b : Poly).natDegree ≤ 1 := by
      exact (natDegree_X_sub_C b).le
    have hfg : (((X-C (a:ℝ))*(X-C ((a+1:ℕ):ℝ))) : Poly).natDegree ≤ 2 :=
      natDegree_mul_le.trans (by have h₁ := hf (a:ℝ); have h₂ := hf ((a+1:ℕ):ℝ); omega)
    simp only [pairPoly] at ih
    exact natDegree_mul_le.trans (by omega)

theorem pairPoly_nonneg (T : Finset Nat) (j : Nat) :
    0 ≤ (pairPoly T).eval (j:ℝ) := by
  simp only [pairPoly,eval_prod,eval_mul,eval_sub,eval_X,eval_C]
  apply Finset.prod_nonneg
  intro a ha
  by_cases h : j ≤ a
  · apply mul_nonneg_of_nonpos_of_nonpos <;> apply sub_nonpos.mpr
    · exact_mod_cast h
    · exact_mod_cast h.trans (Nat.le_succ a)
  · apply mul_nonneg <;> apply sub_nonneg.mpr
    · exact_mod_cast (Nat.le_of_lt (lt_of_not_ge h))
    · exact_mod_cast (Nat.succ_le_of_lt (lt_of_not_ge h))

theorem pairPoly_pos_at_end {m : Nat} {T : Finset Nat} (h : ∀ a ∈ T, a + 1 ≤ m) :
    0 < (pairPoly T).eval ((m+1:ℕ):ℝ) := by
  simp only [pairPoly,eval_prod,eval_mul,eval_sub,eval_X,eval_C]
  apply Finset.prod_pos
  intro a ha
  have hh := h a ha
  apply mul_pos <;> apply sub_pos.mpr
  · exact_mod_cast (show a < m+1 by omega)
  · exact_mod_cast (show a+1 < m+1 by omega)

theorem pairPoly_zero {m : Nat} {J : Finset (Nodes m)}
    {T : Finset Nat} (h : ∀ i : Nodes m, i∈J ↔ ∃ a∈T, i.val=a ∨ i.val=a+1)
    {i : Nodes m} (hi : i ∈ J) : (pairPoly T).eval (x i) = 0 := by
  obtain ⟨a,ha,he⟩ := (h i).mp hi
  simp only [pairPoly,eval_prod,eval_mul,eval_sub,eval_X,eval_C]
  refine Finset.prod_eq_zero ha ?_
  rcases he with he|he <;> simp [x,he]

/-- The full law is feasible precisely when the reduced law is: converse
positivity at the endpoint is certified by the paired-root polynomial. -/
def Feasible (m k : Nat) (J : Finset (Nodes m)) (p : ℝ) : Prop :=
  Paired m k J ∧ ∃ v : Nodes (m+1) → ℝ,
    Quadrature k p v ∧ (∀ j, 0≤v j) ∧ ∀ i : Nodes m, i∉J → v i.castSucc=0

def ReducedFeasible (m k : Nat) (J : Finset (Nodes m)) (p : ℝ) : Prop :=
  Paired m k J ∧ ∃ u : Nodes m → ℝ,
    Quadrature (k-1) p u ∧ (∀ i, 0≤u i) ∧ ∀ i, i∉J → u i=0

theorem feasible_iff_reduced {m k : Nat} {J : Finset (Nodes m)} {p : ℝ}
    (hk : 0 < k) (hp0 : 0 < p) (hp1 : p < 1) :
    Feasible m k J p ↔ ReducedFeasible m k J p := by
  have hd : 0 < (((m+1:ℕ):ℝ)*(1-p)) := mul_pos (by positivity) (sub_pos.mpr hp1)
  constructor
  · rintro ⟨hJ,v,hv,hpos,hs⟩
    refine ⟨hJ,deleteEndpoint p v,quadrature_delete hp1.ne hk hv,?_,?_⟩
    · intro i
      exact div_nonneg (mul_nonneg (endpoint_gap_pos i).le (hpos _)) hd.le
    · intro i hi
      simp [deleteEndpoint,hs i hi]
  · rintro ⟨hJ,u,hu,hpos,hs⟩
    let v := liftEndpoint p u
    have hq := quadrature_lift hp1.ne hk hu
    have hsupport (i : Nodes m) (hi : i∉J) : v i.castSucc=0 := by
      simp [v,liftEndpoint,hs i hi]
    refine ⟨hJ,v,hq,?_,hsupport⟩
    intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · obtain ⟨_,T,hcard,hbound,_,hmem⟩ := hJ
      have ht := hq (pairPoly T) (by simpa only [hcard] using pairPoly_degree T)
      have hP := pairPoly_pos_at_end hbound
      have hL : moment v (pairPoly T) =
          v (Fin.last (m+1)) * (pairPoly T).eval ((m+1:ℕ):ℝ) := by
        unfold moment
        rw [Fin.sum_univ_castSucc]
        have hz : (∑ i : Nodes m, v i.castSucc * (pairPoly T).eval (x i.castSucc)) = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          by_cases hh : i∈J
          · have h0 := pairPoly_zero hmem hh
            simpa [x] using mul_eq_zero.mpr (Or.inr h0)
          · simp [hsupport i hh]
        rw [hz, zero_add]
        simp [x]
      have hR : 0 ≤ moment (bin (m+1) p) (pairPoly T) := by
        apply Finset.sum_nonneg
        intro i hi
        apply mul_nonneg _ (pairPoly_nonneg T i.val)
        unfold bin
        exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hp0.le _))
          (pow_nonneg (sub_nonneg.mpr hp1.le) _)
      have hprod : 0 ≤ v (Fin.last (m+1)) * (pairPoly T).eval ((m+1:ℕ):ℝ) := by
        rw [← hL,ht]
        exact hR
      exact nonneg_of_mul_nonneg_left hprod hP
    · simpa [v,liftEndpoint] using
        div_nonneg (mul_nonneg hd.le (hpos i)) (endpoint_gap_pos i).le

end BerendBinomial


namespace BerendBinomial
open Finset

def reflectSet (m : Nat) (J : Finset (Nodes m)) : Finset (Nodes m) :=
  J.map (rev m).toEmbedding

theorem mem_reflectSet {m : Nat} {J : Finset (Nodes m)} {i : Nodes m} :
    i ∈ reflectSet m J ↔ rev m i ∈ J := by
  constructor
  · intro h
    obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp h
    simpa only [Equiv.toEmbedding_apply,rev_twice] using hj
  · intro h
    exact Finset.mem_map.mpr ⟨rev m i,h,rev_twice i⟩

theorem paired_reflect {m k : Nat} {J : Finset (Nodes m)}
    (hJ : Paired m k J) : Paired m k (reflectSet m J) := by
  classical
  obtain ⟨hJcard,T,hcard,hbound,hsep,hmem⟩ := hJ
  let f : Nat → Nat := fun a => m-(a+1)
  let U := T.image f
  have hinj : Set.InjOn f (↑T : Set Nat) := by
    intro a ha b hb e
    have h₁ := hbound a ha
    have h₂ := hbound b hb
    dsimp [f] at e
    omega
  have hc : U.card=T.card := Finset.card_image_of_injOn hinj
  refine ⟨by simpa [reflectSet] using hJcard,U,by omega,?_,?_,?_⟩
  · intro a ha
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
    have hh := hbound i hi
    dsimp [f]
    omega
  · intro a ha b hb hab
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hb
    have h₁ := hbound i hi
    have h₂ := hbound j hj
    dsimp [f] at hab ⊢
    have hh := hsep j hj i hi (by omega)
    omega
  · intro i
    rw [mem_reflectSet,hmem]
    have hi : i.val ≤ m := by omega
    constructor
    · rintro ⟨a,ha,e⟩
      refine ⟨f a,Finset.mem_image.mpr ⟨a,ha,rfl⟩,?_⟩
      have h := hbound a ha
      change m-i.val=a ∨ m-i.val=a+1 at e
      dsimp [f]
      omega
    · rintro ⟨b,hb,e⟩
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
      refine ⟨a,ha,?_⟩
      have h := hbound a ha
      change m-i.val=a ∨ m-i.val=a+1
      dsimp [f] at e
      omega

theorem feasible_reflect {m k : Nat} {J : Finset (Nodes m)} {p : ℝ}
    (hk : 0<k) (hp0 : 0<p) (hp1 : p<1) (h : Feasible m k J p) :
    Feasible m k (reflectSet m J) (1-p) := by
  obtain ⟨hJ,u,hu,hpos,hs⟩ := (feasible_iff_reduced hk hp0 hp1).mp h
  apply (feasible_iff_reduced hk (by linarith) (by linarith)).mpr
  refine ⟨paired_reflect hJ,u ∘ rev m,quadrature_reflect hu,fun i => hpos _,?_⟩
  intro i hi
  exact hs _ (fun h => hi (mem_reflectSet.mpr h))

/-- A basis is valid just to the left/right, excluding isolated endpoint
degeneracy. Interior feasibility at the common parameter is kept explicit. -/
def LeftActive (m k : Nat) (J : Finset (Nodes m)) (p : ℝ) : Prop :=
  ∃ ε : ℝ, 0<ε ∧ ∀ q : ℝ, 0<q → q<1 → p-ε<q → q<p → Feasible m k J q

def RightActive (m k : Nat) (J : Finset (Nodes m)) (p : ℝ) : Prop :=
  ∃ ε : ℝ, 0<ε ∧ ∀ q : ℝ, 0<q → q<1 → p<q → q<p+ε → Feasible m k J q

/-- Source Sect. 5.2: an exceptional point is an internal transition
with at least two departing indices. n = m+1, the fixed endpoint n is
omitted from both lower support sets, and thus from their difference. -/
def Exceptional (m k : Nat) (p : ℝ) : Prop :=
  0<p ∧ p<1 ∧ ∃ J K : Finset (Nodes m),
    Feasible m k J p ∧ Feasible m k K p ∧
    LeftActive m k J p ∧ RightActive m k K p ∧ 2≤(J\K).card

theorem left_to_right {m k : Nat} {J : Finset (Nodes m)} {p : ℝ}
    (hk : 0<k) (h : LeftActive m k J p) :
    RightActive m k (reflectSet m J) (1-p) := by
  obtain ⟨e,he,hl⟩ := h
  refine ⟨e,he,fun q hq hq1 ha hb => ?_⟩
  have h := feasible_reflect hk (p := 1-q) (by linarith) (by linarith)
    (hl (1-q) (by linarith) (by linarith) (by linarith) (by linarith))
  convert h using 1; ring

theorem right_to_left {m k : Nat} {J : Finset (Nodes m)} {p : ℝ}
    (hk : 0<k) (h : RightActive m k J p) :
    LeftActive m k (reflectSet m J) (1-p) := by
  obtain ⟨e,he,hl⟩ := h
  refine ⟨e,he,fun q hq hq1 ha hb => ?_⟩
  have h := feasible_reflect hk (p := 1-q) (by linarith) (by linarith)
    (hl (1-q) (by linarith) (by linarith) (by linarith) (by linarith))
  convert h using 1; ring

theorem reflectSet_sdiff {m : Nat} (J K : Finset (Nodes m)) :
    reflectSet m (J\K) = reflectSet m J \ reflectSet m K := by
  ext i
  simp only [mem_reflectSet,Finset.mem_sdiff]

/-- Berend–Ernst–Kontorovich–Kumar, Conjecture 5.11, JTP 39 (2026).
Even k, 2 ≤ k ≤ n−1; indexing uses m = n−1. -/
theorem exceptional_reflect {m k : Nat} {p : ℝ}
    (hk : 2 ≤ k) (_hle : k ≤ m) (_he : Even k)
    (h : Exceptional m k p) : Exceptional m k (1-p) := by
  obtain ⟨hp,hp1,J,K,hJ,hK,hL,hR,hN⟩ := h
  have hk0 : 0<k := by omega
  refine ⟨by linarith,by linarith,reflectSet m K,reflectSet m J,
    feasible_reflect hk0 hp hp1 hK,feasible_reflect hk0 hp hp1 hJ,
    right_to_left hk0 hR,left_to_right hk0 hL,?_⟩
  rw [← reflectSet_sdiff]
  change 2 ≤ ((K\J).map (rev m).toEmbedding).card
  rw [Finset.card_map]
  have hJcard := hJ.1.1
  have hKcard := hK.1.1
  have h₁ := Finset.card_sdiff_add_card_inter J K
  have h₂ := Finset.card_sdiff_add_card_inter K J
  rw [Finset.inter_comm K J] at h₂
  omega

/-- Source-native notation: n is the total number of Bernoulli variables. -/
abbrev SourceExceptional (n k : Nat) (p : ℝ) : Prop := Exceptional (n-1) k p

theorem source_exceptional_reflect {n k : Nat} {p : ℝ}
    (hk : 2 ≤ k) (hle : k ≤ n - 1) (he : Even k)
    (h : SourceExceptional n k p) : SourceExceptional n k (1-p) :=
  exceptional_reflect hk hle he h

#print axioms exceptional_reflect
#print axioms source_exceptional_reflect
end BerendBinomial
