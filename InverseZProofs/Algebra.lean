module

public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
public import Mathlib.Combinatorics.Matroid.Rank.ENat

@[expose] public section

set_option autoImplicit false
namespace InverseZ.Algebra
open Finset Polynomial
open scoped BigOperators

section Ranked
variable {L : Type*} [PartialOrder L] [LocallyFiniteOrder L] [DecidableEq L]
variable (rk : L → ℕ)

/-- The signed Möbius function of a ranked interval, with integer values. -/
noncomputable def signedMu (a b : L) : ℤ := by
  classical
  exact (-1) ^ (rk b - rk a) * IncidenceAlgebra.mu ℤ a b

@[simp] theorem signedMu_self (a : L) : signedMu rk a a = 1 := by
  classical
  simp [signedMu]

/-- Add only the low coefficients needed to reflect the high slice of a polynomial
    across formal degree d. -/
noncomputable def lowCorrection (d : ℕ) (p : ℤ[X]) : ℤ[X] :=
  ∑ i ∈ range ((d+1)/2), monomial i (p.coeff (d-i) - p.coeff i)

theorem coeff_lowCorrection (d i : ℕ) (p : ℤ[X]) :
    (lowCorrection d p).coeff i =
      if 2*i < d then p.coeff (d-i) - p.coeff i else 0 := by
  classical
  simp only [lowCorrection, finsetSum_coeff, coeff_monomial, sum_ite_eq',
    mem_range]
  split <;> split <;> first | rfl | omega

/-- Sum the terms strictly below b. Separating off the b-summand lets
    palindromicity determine the inverse KL polynomial recursively. -/
noncomputable def properSum (q : L → L → ℤ[X]) (a b : L) : ℤ[X] :=
  ∑ x ∈ Ico a b, C (signedMu rk x b) * (X ^ (rk b-rk x) * q a x)

/-- Recursive construction from the inverse-KL degree condition and symmetry
    of inverse Z (Braden–Ferroni–Matherne–Nepal, Thm. 2.2). -/
noncomputable def inverseKL (strict : StrictMono rk) (a b : L) : ℤ[X] :=
  if a = b then 1
  else lowCorrection (rk b-rk a)
    ((Ico a b).attach.sum fun x =>
      C (signedMu rk x.val b) * (X ^ (rk b-rk x.val) * inverseKL strict a x.val))
termination_by rk b
decreasing_by exact strict (mem_Ico.mp x.property).2

theorem inverseKL_eq (strict : StrictMono rk) (a b : L) :
    inverseKL rk strict a b = if a = b then 1
      else lowCorrection (rk b-rk a) (properSum rk (inverseKL rk strict) a b) := by
  rw [inverseKL]
  classical
  simp only [properSum]
  by_cases h : a = b
  · simp only [ite_eq_left h]
  · simp only [ite_eq_right h]
    congr 1
    exact sum_attach (Ico a b) (fun x => C (signedMu rk x b) *
      (X ^ (rk b-rk x) * inverseKL rk strict a x))

/-- The flat-lattice sum in Theorem 2.2. -/
noncomputable def inverseZ (q : L → L → ℤ[X]) (a b : L) : ℤ[X] :=
  ∑ x ∈ Icc a b, C (signedMu rk x b) * (X ^ (rk b-rk x) * q a x)

theorem coeff_inverseZ (q : L → L → ℤ[X]) (a b : L) (i : ℕ) :
    (inverseZ rk q a b).coeff i =
      ∑ x ∈ Icc a b, signedMu rk x b *
        if rk b-rk x ≤ i then (q a x).coeff (i-(rk b-rk x)) else 0 := by
  simp only [inverseZ, finsetSum_coeff, coeff_C_mul, coeff_X_pow_mul']

theorem inverseZ_eq_proper_add (q : L → L → ℤ[X]) {a b : L} (hab : a ≤ b) :
    inverseZ rk q a b = properSum rk q a b + q a b := by
  classical
  have hh : Icc a b = insert b (Ico a b) := by
    ext x
    simp only [mem_Icc, mem_insert, mem_Ico]
    constructor
    · intro hx
      exact (eq_or_lt_of_le hx.2).elim Or.inl (fun hr => Or.inr ⟨hx.1, hr⟩)
    · rintro (rfl | hx)
      · exact ⟨hab, le_rfl⟩
      · exact ⟨hx.1, hx.2.le⟩
  rw [inverseZ, properSum, hh, sum_insert (by simp : b ∉ Ico a b)]
  simp [add_comm]

theorem inverseKL_self (strict : StrictMono rk) (a : L) :
    inverseKL rk strict a a = 1 := by
  rw [inverseKL_eq]
  simp

theorem inverseKL_high_coeff (strict : StrictMono rk) {a b : L} (hab : a ≠ b)
    (i : ℕ) (hi : rk b-rk a ≤ 2*i) :
    (inverseKL rk strict a b).coeff i = 0 := by
  rw [inverseKL_eq, ite_eq_right hab, coeff_lowCorrection, ite_eq_right (not_lt.mpr hi)]

theorem inverseZ_self (q : L → L → ℤ[X]) (a : L) :
    inverseZ rk q a a = q a a := by
  rw [inverseZ_eq_proper_add rk q le_rfl]
  simp [properSum]

/-- Its coefficients are symmetric about the prescribed interval rank, not
    just about an unspecified polynomial degree. -/
theorem inverseZ_coeff_palindromic (strict : StrictMono rk) {a b : L} (hab : a ≤ b)
    (i : ℕ) (hi : i ≤ rk b-rk a) :
    (inverseZ rk (inverseKL rk strict) a b).coeff (rk b-rk a-i) =
    (inverseZ rk (inverseKL rk strict) a b).coeff i := by
  classical
  by_cases e : a = b
  · subst b
    simp only [Nat.sub_self, Nat.le_zero] at hi
    subst i
    simp
  rw [inverseZ_eq_proper_add rk _ hab]
  rw [inverseKL_eq rk strict a b, ite_eq_right e]
  simp only [coeff_add, coeff_lowCorrection]
  generalize heq : rk b-rk a = d at *
  have hd : d - (d - i) = i := by omega
  rw [hd]
  split <;> split <;> try omega
  rw [show d-i=i by omega]

/-- Uniqueness of the source characterization. No inverse-KL polynomial or
    palindromicity axiom is assumed in the construction above. -/
theorem inverseKL_unique (strict : StrictMono rk) (q : L → L → ℤ[X])
    (base : ∀ a, q a a = 1)
    (high : ∀ a b, a < b → ∀ i, rk b-rk a ≤ 2*i → (q a b).coeff i = 0)
    (pal : ∀ a b, a ≤ b → ∀ i, i ≤ rk b-rk a →
      (inverseZ rk q a b).coeff (rk b-rk a-i) = (inverseZ rk q a b).coeff i)
    {a b : L} (hab : a ≤ b) :
    q a b = inverseKL rk strict a b := by
  classical
  by_cases e : a = b
  · subst b
    rw [base, inverseKL_self]
  have hlt : a < b := lt_of_le_of_ne hab e
  have hp : properSum rk q a b = properSum rk (inverseKL rk strict) a b := by
    unfold properSum
    apply sum_congr rfl
    intro x hx
    rw [inverseKL_unique strict q base high pal (mem_Ico.mp hx).1]
  ext i
  by_cases hi : 2*i < rk b-rk a
  · have h := pal a b hab i (by omega)
    rw [inverseZ_eq_proper_add rk q hab, coeff_add, coeff_add,
      high a b hlt _ (by omega), add_zero, hp] at h
    rw [inverseKL_eq rk strict, ite_eq_right e, coeff_lowCorrection, ite_eq_left hi]
    omega
  · rw [high a b hlt i (by omega), inverseKL_high_coeff rk strict e i (by omega)]
termination_by rk b
decreasing_by all_goals exact strict (mem_Ico.mp hx).2

/-- No coefficient lies above the advertised interval rank. -/
theorem inverseZ_high_coeff (strict : StrictMono rk) {a b : L} {i : ℕ}
    (hi : rk b-rk a < i) :
    (inverseZ rk (inverseKL rk strict) a b).coeff i = 0 := by
  classical
  rw [coeff_inverseZ]
  apply sum_eq_zero
  intro x hx
  obtain ⟨hax, hxb⟩ := mem_Icc.mp hx
  have ra := strict.monotone hax
  have rb := strict.monotone hxb
  by_cases hr : rk b-rk x ≤ i
  · rw [ite_eq_left hr]
    by_cases e : a = x
    · subst x
      rw [inverseKL_self, coeff_one, ite_eq_right (by omega), mul_zero]
    · rw [inverseKL_high_coeff rk strict e _ (by omega), mul_zero]
  · simp only [ite_eq_right hr, mul_zero]

/-- The coefficient in interval rank is its signed Möbius invariant. -/
theorem inverseZ_top_coeff (strict : StrictMono rk) {a b : L} (hab : a ≤ b) :
    (inverseZ rk (inverseKL rk strict) a b).coeff (rk b-rk a) = signedMu rk a b := by
  classical
  rw [coeff_inverseZ, sum_eq_single a]
  · rw [ite_eq_left le_rfl, Nat.sub_self, inverseKL_self, coeff_one, ite_eq_left rfl, mul_one]
  · intro x hx e
    obtain ⟨hax, hxb⟩ := mem_Icc.mp hx
    have ra := strict.monotone hax
    have rb := strict.monotone hxb
    rw [ite_eq_left (by omega), inverseKL_high_coeff rk strict (Ne.symm e) _ (by omega), mul_zero]
  · exact fun hn => (hn (mem_Icc.mpr ⟨le_rfl,hab⟩)).elim

theorem inverseZ_constant_eq_inverseKL (strict : StrictMono rk) {a b : L} (hab : a ≤ b) :
    (inverseZ rk (inverseKL rk strict) a b).coeff 0 =
    (inverseKL rk strict a b).coeff 0 := by
  classical
  rw [coeff_inverseZ, sum_eq_single b]
  · simp
  · intro x hx e
    have ht := strict (lt_of_le_of_ne (mem_Icc.mp hx).2 e)
    rw [ite_eq_right (by omega), mul_zero]
  · exact fun hn => (hn (mem_Icc.mpr ⟨hab, le_rfl⟩)).elim

theorem inverseKL_constant (strict : StrictMono rk) {a b : L} (hab : a ≤ b) :
    (inverseKL rk strict a b).coeff 0 = signedMu rk a b := by
  rw [← inverseZ_constant_eq_inverseKL rk strict hab,
    ← inverseZ_coeff_palindromic rk strict hab 0 (Nat.zero_le _), Nat.sub_zero]
  exact inverseZ_top_coeff rk strict hab

/-- Concrete polynomial degree bound, expressed without dividing in the naturals. -/
theorem inverseKL_degree (strict : StrictMono rk) {a b : L} (hab : a < b) :
    (inverseKL rk strict a b).natDegree < (rk b-rk a+1)/2 := by
  have hp := strict hab
  have hh : 0 < (rk b-rk a+1)/2 := by omega
  have h := (natDegree_le_iff_coeff_eq_zero (p := inverseKL rk strict a b)
    (n := (rk b-rk a+1)/2-1)).mpr
    (fun i hi => inverseKL_high_coeff rk strict hab.ne i (by omega))
  omega

end Ranked

section Matroid

open Set Matroid
open scoped ENat
variable {α : Type*} [Finite α] (M : Matroid α)

/-- The type of Mathlib matroid flats, ordered by inclusion. -/
abbrev Flats := {F : Set α // M.IsFlat F}

noncomputable instance flatLocallyFinite : LocallyFiniteOrder (Flats M) :=
  LocallyFiniteOrder.ofFiniteIcc fun _ _ => Set.toFinite _

noncomputable def flatRank (F : Flats M) : ℕ := (M.eRk F.val).toNat

theorem flatRank_strict : StrictMono (flatRank M) := by
  classical
  intro F G hFG
  have hsub : F.val ⊆ G.val := le_of_lt hFG
  obtain ⟨u, huG, huF⟩ := Set.exists_of_ssubset hFG
  obtain ⟨I, J, hI, hJ, hIJ⟩ := M.exists_isBasis_subset_isBasis hsub G.property.subset_ground
  have hIJ' : I ⊂ J := by
    refine lt_of_le_of_ne hIJ ?_
    intro e
    have huCF : u ∈ M.closure F.val := by
      rw [← hI.closure_eq_closure, e, hJ.closure_eq_closure]
      exact M.mem_closure_of_mem huG G.property.subset_ground
    rw [F.property.closure] at huCF
    exact huF huCF
  rw [flatRank, flatRank, ← ENat.natCast_lt_natCast,
    ENat.natCast_toNat ((M.eRk_le_encard F.val).trans_lt (Set.toFinite F.val).encard_lt_top).ne,
    ENat.natCast_toNat ((M.eRk_le_encard G.val).trans_lt (Set.toFinite G.val).encard_lt_top).ne,
    ← hI.encard_eq_eRk, ← hJ.encard_eq_eRk]
  exact (Set.toFinite I).encard_lt_encard hIJ'

def bottomFlat : Flats M := ⟨M.closure ∅, M.isFlat_closure _⟩
def topFlat : Flats M := ⟨M.E, M.ground_isFlat⟩

omit [Finite α] in
theorem bottomFlat_le (F : Flats M) : bottomFlat M ≤ F := by
  change M.closure ∅ ⊆ F.val
  rw [← F.property.closure]
  exact M.closure_subset_closure (Set.empty_subset _)

omit [Finite α] in
theorem le_topFlat (F : Flats M) : F ≤ topFlat M := F.property.subset_ground

omit [Finite α] in
@[simp] theorem flatRank_bottom : flatRank M (bottomFlat M) = 0 := by
  simp [flatRank, bottomFlat]

omit [Finite α] in
@[simp] theorem flatRank_top : flatRank M (topFlat M) = M.eRank.toNat := by
  simp [flatRank, topFlat]

/-- The signed inverse KL polynomial of the interval [bottom,F]. This also
    covers parallel elements and loops since the inputs are actual flats. -/
noncomputable def matroidInverseKL (a b : Flats M) : ℤ[X] := by
  classical
  exact inverseKL (flatRank M) (flatRank_strict M) a b

/-- Inverse Z of a finite matroid, defined on its actual flat lattice. -/
noncomputable def matroidInverseZ : ℤ[X] := by
  classical
  exact inverseZ (flatRank M) (matroidInverseKL M) (bottomFlat M) (topFlat M)

noncomputable def matroidSignedMu (F G : Flats M) : ℤ := by
  classical
  exact signedMu (flatRank M) F G

/-- Exact inverse Z coefficient with the source summation, all ranks. -/
theorem matroidInverseZ_coeff (i : ℕ) :
    (matroidInverseZ M).coeff i =
      ∑ F ∈ Icc (bottomFlat M) (topFlat M), matroidSignedMu M F (topFlat M) *
        if M.eRank.toNat-flatRank M F ≤ i then
          (matroidInverseKL M (bottomFlat M) F).coeff (i-(M.eRank.toNat-flatRank M F))
        else 0 := by
  classical
  simpa only [matroidInverseZ, matroidSignedMu, flatRank_top] using
    coeff_inverseZ (flatRank M) (matroidInverseKL M) (bottomFlat M) (topFlat M) i

theorem matroidInverseZ_support (i : ℕ) (hi : M.eRank.toNat < i) :
    (matroidInverseZ M).coeff i = 0 := by
  classical
  exact inverseZ_high_coeff _ (flatRank_strict M) (by simpa using hi)

theorem matroidInverseZ_palindromic (i : ℕ) (hi : i ≤ M.eRank.toNat) :
    (matroidInverseZ M).coeff (M.eRank.toNat-i) = (matroidInverseZ M).coeff i := by
  classical
  delta matroidInverseZ matroidInverseKL
  simpa only [flatRank_top, flatRank_bottom, Nat.sub_zero]
    using inverseZ_coeff_palindromic (flatRank M) (flatRank_strict M) (bottomFlat_le M _)
      i (by simpa using hi : i ≤ flatRank M (topFlat M) - flatRank M (bottomFlat M))

theorem matroidInverseZ_top_coeff :
    (matroidInverseZ M).coeff M.eRank.toNat = matroidSignedMu M (bottomFlat M) (topFlat M) := by
  classical
  delta matroidInverseZ matroidInverseKL matroidSignedMu
  simpa only [flatRank_top, flatRank_bottom, Nat.sub_zero] using
    inverseZ_top_coeff (flatRank M) (flatRank_strict M) (bottomFlat_le M (topFlat M))

end Matroid

#print axioms matroidInverseZ_coeff
#print axioms matroidInverseZ_support
#print axioms matroidInverseZ_palindromic
#print axioms matroidInverseZ_top_coeff
#print axioms coeff_inverseZ
#print axioms inverseZ_coeff_palindromic
#print axioms inverseKL_unique
end InverseZ.Algebra
