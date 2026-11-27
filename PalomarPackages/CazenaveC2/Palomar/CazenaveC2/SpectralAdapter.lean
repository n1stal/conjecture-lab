module

public import Palomar.CazenaveC2.DiamondGraph
public import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.LinearCombination
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-! Source-exact sorted spectral adapter for the single native witness.
The infinite family has the separate unbounded paper proof. No compiled receipt. -/
namespace CazenaveC2

open Matrix Module End WithLp
open scoped Matrix BigOperators

def oddP (t : ℝ) : ℝ := t^4-t^3-5*t^2+t+2
def evenP (t : ℝ) : ℝ := t^3-3*t^2-t+5

def oddVec (t : ℝ) : Fin 11 → ℝ :=
  let a := t*(t^2-t-2)
  let b := t^2
  let d := 2*t
  let e := t^2-t-2
  ![a,b,b,d,-a,-b,-b,-d,e,0,-e]

def evenVec (t : ℝ) : Fin 11 → ℝ :=
  let u := t^2-2
  let w := t^2-t-2
  let a := u*w
  let b := t*u
  let d := 2*u
  let e := t*w
  let f := 2*w
  ![a,b,b,d,a,b,b,d,e,f,e]

theorem odd_eigenvector {t : ℝ} (hp : oddP t = 0) :
    A *ᵥ oddVec t = t • oddVec t := by
  unfold oddP at hp
  funext i
  rw [adjAction_apply]
  fin_cases i <;> simp [adjAction, oddVec, Pi.smul_apply, smul_eq_mul] <;>
    first | (ring; done) | linear_combination hp | linear_combination -hp

theorem even_eigenvector {t : ℝ} (hp : evenP t = 0) :
    A *ᵥ evenVec t = t • evenVec t := by
  unfold evenP at hp
  funext i
  rw [adjAction_apply]
  fin_cases i <;> simp [adjAction, evenVec, Pi.smul_apply, smul_eq_mul] <;>
    first | (ring; done) | linear_combination (-t*(t+2))*hp

theorem odd_nonzero {t : ℝ} (ht : 0 < t) : oddVec t ≠ 0 := by
  intro h
  have hz : t^2 = 0 := by simpa [oddVec] using congrFun h (1 : Fin 11)
  exact (pow_ne_zero 2 (ne_of_gt ht)) hz

theorem even_nonzero {t : ℝ} (ht : 2 < t) : evenVec t ≠ 0 := by
  intro h
  have hz : t*(t^2-2) = 0 := by simpa [evenVec] using congrFun h (1 : Fin 11)
  have hp : 0 < (t-2)*(t+2) := mul_pos (by linarith) (by linarith)
  have hp' : 0 < t^2-2 := by nlinarith only [hp]
  exact (ne_of_gt (mul_pos (by linarith : 0 < t) hp')) hz

private theorem spectrum_of_mulVec {M : Matrix (Fin 11) (Fin 11) ℝ}
    {r : ℝ} {v : Fin 11 → ℝ} (hn : v ≠ 0) (hv : M *ᵥ v = r • v) :
    r ∈ spectrum ℝ M := by
  have he : HasEigenvector M.toLin' r v :=
    ⟨mem_eigenspace_iff.mpr (by simpa only [Matrix.toLin'_apply] using hv), hn⟩
  have hs := (hasEigenvalue_of_hasEigenvector he).mem_spectrum
  simpa only [Matrix.spectrum_toLin'] using hs

private theorem odd_root :
    ∃ t : ℝ, (21/8:ℝ) < t ∧ t < 8/3 ∧ oddP t = 0 := by
  have hc : Continuous oddP := by unfold oddP; fun_prop
  have hsgn : (0:ℝ) ∈ Set.Ioo (oddP (21/8)) (oddP (8/3)) := by
    constructor <;> norm_num [oddP]
  obtain ⟨t, h, he⟩ :=
    intermediate_value_Ioo (f := oddP) (by norm_num : (21/8:ℝ) ≤ 8/3)
      hc.continuousOn hsgn
  exact ⟨t,h.1,h.2,he⟩

private theorem even_root :
    ∃ t : ℝ, (8/3:ℝ) < t ∧ t < 11/4 ∧ evenP t = 0 := by
  have hc : Continuous evenP := by unfold evenP; fun_prop
  have hsgn : (0:ℝ) ∈ Set.Ioo (evenP (8/3)) (evenP (11/4)) := by
    constructor <;> norm_num [evenP]
  obtain ⟨t, h, he⟩ :=
    intermediate_value_Ioo (f := evenP) (by norm_num : (8/3:ℝ) ≤ 11/4)
      hc.continuousOn hsgn
  exact ⟨t,h.1,h.2,he⟩

abbrev EigenIndex := Fin (Fintype.card (Fin 11))
def firstIdx : EigenIndex := ⟨0,by simp⟩
def secondIdx : EigenIndex := ⟨1,by simp⟩

private theorem second_le_of_ne {i : EigenIndex} (h : i ≠ firstIdx) :
    secondIdx ≤ i := by
  change 1 ≤ i.val
  by_contra hn
  apply h
  apply Fin.ext
  change i.val = 0
  omega

private noncomputable def indexEquiv : EigenIndex ≃ Fin 11 :=
  Fintype.equivOfCardEq (Fintype.card_fin 11)

private theorem at_least_two_above {M : Matrix (Fin 11) (Fin 11) ℝ}
    (hM : M.IsHermitian) {b s t : ℝ} (hb : b < s) (hst : s < t)
    (hs : s ∈ spectrum ℝ M) (ht : t ∈ spectrum ℝ M) :
    b < hM.eigenvalues₀ secondIdx := by
  rw [hM.spectrum_real_eq_range_eigenvalues] at hs ht
  obtain ⟨i, hi⟩ := hs
  obtain ⟨j, hj⟩ := ht
  let a : EigenIndex := indexEquiv.symm i
  let c : EigenIndex := indexEquiv.symm j
  have ha : hM.eigenvalues₀ a = s := hi
  have hc : hM.eigenvalues₀ c = t := hj
  have hdif : a ≠ c := by
    intro e
    exact (ne_of_lt hst) (ha.symm.trans ((congrArg hM.eigenvalues₀ e).trans hc))
  by_cases hz : a = firstIdx
  · have hcz : c ≠ firstIdx := fun h => hdif (hz.trans h.symm)
    apply (hb.trans hst).trans_le
    rw [← hc]
    exact hM.eigenvalues₀_antitone (second_le_of_ne hcz)
  · apply hb.trans_le
    rw [← ha]
    exact hM.eigenvalues₀_antitone (second_le_of_ne hz)

theorem adjSecond_strict : (21/8:ℝ) < A_hermitian.eigenvalues₀ secondIdx := by
  obtain ⟨s, hs, hs', hp⟩ := odd_root
  obtain ⟨t, ht, _, hq⟩ := even_root
  exact at_least_two_above A_hermitian hs (hs'.trans ht)
    (spectrum_of_mulVec (odd_nonzero (by linarith)) (odd_eigenvector hp))
    (spectrum_of_mulVec (even_nonzero (by linarith)) (even_eigenvector hq))

theorem lapFirst_bound : L_hermitian.eigenvalues₀ firstIdx ≤ (37/8:ℝ) := by
  let i : Fin 11 := indexEquiv firstIdx
  let w : Fin 11 → ℝ := ⇑(L_hermitian.eigenvectorBasis i)
  have hne : w ≠ 0 :=
    (ofLp_eq_zero 2).ne.2 (L_hermitian.eigenvectorBasis.orthonormal.ne_zero i)
  have hw : 0 < dotProduct w w := by
    simpa only [star_trivial] using (dotProduct_self_star_pos_iff.mpr hne)
  have he : L *ᵥ w = L_hermitian.eigenvalues i • w :=
    L_hermitian.mulVec_eigenvectorBasis i
  have hn := lapShiftForm_nonnegative w
  rw [← lapShift_eval, he, dotProduct_smul, smul_eq_mul] at hn
  have hb := le_of_mul_le_mul_right (sub_nonneg.mp hn) hw
  have heq : L_hermitian.eigenvalues i = L_hermitian.eigenvalues₀ firstIdx := by
    unfold Matrix.IsHermitian.eigenvalues
    change L_hermitian.eigenvalues₀ (indexEquiv.symm (indexEquiv firstIdx)) = _
    rw [Equiv.symm_apply_apply]
  linarith only [hb, heq]

theorem exact_counterexample :
    L_hermitian.eigenvalues₀ firstIdx - 2 < A_hermitian.eigenvalues₀ secondIdx := by
  linarith only [adjSecond_strict, lapFirst_bound]

/-- The paper quantifies finite connected simple graphs. Fin n ranges over all
orders and standard finite labellings; the witness below is native itself. -/
def SourceC2 : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (H : SimpleGraph (Fin n)) (d : DecidableRel H.Adj),
    letI := d
    H.Connected →
    (H.isHermitian_adjMatrix ℝ).eigenvalues₀ ⟨1,by simpa only [Fintype.card_fin] using (show 1 < n by omega)⟩ ≤
      (H.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨0,by simpa only [Fintype.card_fin] using (show 0 < n by omega)⟩ - 2

theorem source_conjecture_false : ¬ SourceC2 := by
  intro h
  have hb := h 11 (by decide) G adjacency_decidable G_connected
  change A_hermitian.eigenvalues₀ secondIdx ≤ L_hermitian.eigenvalues₀ firstIdx-2 at hb
  exact (not_le_of_gt exact_counterexample) hb

end CazenaveC2

#print axioms CazenaveC2.source_conjecture_false
