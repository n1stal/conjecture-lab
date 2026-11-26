module

public import SpectralRank.Coverage
public import SpectralRank.IndexedMeaning
public import SpectralRank.PrincipalMinor
public import SpectralRank.OrderedComparator

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
open Matrix Finset
open scoped BigOperators
namespace SpectralRank

def boolAdj {m : Type*} (A : m → m → Bool) : Matrix m m ℝ := fun i j => if A i j then 1 else 0
theorem sqFrob_reindex {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m m ℝ) (p : n ≃ m) :
    sqFrob (A.submatrix p p) = sqFrob A := by
  change (∑ i, ∑ j, (A (p i) (p j))^2) = ∑ i, ∑ j, (A i j)^2
  calc
    (∑ i, ∑ j, (A (p i) (p j))^2) = ∑ i, ∑ j : m, (A (p i) j)^2 := by
      apply Finset.sum_congr rfl
      intro i _
      exact Equiv.sum_comp p (fun j => (A (p i) j)^2)
    _ = _ := Equiv.sum_comp p (fun i => ∑ j, (A i j)^2)
theorem near_rank_of_cover {k : ℕ} (R : Array Nat) (hR : SpectralRank.CoverageData.Covers k R)
    (hcert : ∀ r : Fin R.size, ∃ x, SpectralRank.Indexed.good k R[r] x = true)
    (A : Fin k → Fin k → Bool) (hdiag : ∀ i, A i i = false) (hsymm : ∀ i j, A i j = A j i)
    (hdet : (boolAdj A).det ≠ 0) :
    ∀ C : Matrix (Fin k) (Fin k) ℝ, C.rank ≤ 3 → (2/3 : ℝ) < sqFrob (boolAdj A-C) := by
  intro C hC
  obtain ⟨r,p,hp⟩ := hR A hdiag hsymm
  obtain ⟨x,hx⟩ := hcert r
  let M := (SpectralRank.Indexed.mat k R[r]).map (Int.castRingHom ℝ)
  have hA : boolAdj A = M.submatrix p p := by
    ext i j
    change (if A i j then (1 : ℝ) else 0) = _
    rw [hp]
    change (if SpectralRank.CoverageData.edge R[r] (p i) (p j) then (1 : ℝ) else 0) =
      (Int.castRingHom ℝ) (if SpectralRank.CoverageData.edge R[r] (p i) (p j) then 1 else 0)
    cases SpectralRank.CoverageData.edge R[r] (p i) (p j) <;> simp
  have hM : M.det ≠ 0 := by rwa [hA,det_submatrix_equiv_self] at hdet
  let C' := C.submatrix p.symm p.symm
  have hc' : C'.rank ≤ 3 := by
    change (C.submatrix p.symm p.symm).rank ≤ 3
    rwa [rank_submatrix]
  have hComp : (M-C').submatrix p p = boolAdj A-C := by
    ext i j
    simp [hA,C',Matrix.submatrix_apply]
  rw [← hComp,sqFrob_reindex]
  exact SpectralRank.Indexed.good_sound k R[r] x hx hM C' hc'

theorem universal_adjacency_rank_bound
    (h6 : ∀ (A : Fin 6 → Fin 6 → Bool), (∀ i, A i i = false) →
      (∀ i j, A i j = A j i) → (boolAdj A).det ≠ 0 →
      ∀ C : Matrix (Fin 6) (Fin 6) ℝ, C.rank ≤ 3 → (2/3 : ℝ) < sqFrob (boolAdj A-C))
    (h7 : ∀ (A : Fin 7 → Fin 7 → Bool), (∀ i, A i i = false) →
      (∀ i j, A i j = A j i) → (boolAdj A).det ≠ 0 →
      ∀ C : Matrix (Fin 7) (Fin 7) ℝ, C.rank ≤ 3 → (2/3 : ℝ) < sqFrob (boolAdj A-C))
    {m : Type*} [Fintype m] [DecidableEq m]
    (A : m → m → Bool) (hdiag : ∀ i, A i i = false) (hsymm : ∀ i j, A i j = A j i)
    (hHerm : (boolAdj A).IsHermitian)
    (v : Fin (Fintype.card m) → ℝ) (hv : Fintype.card {i // v i ≠ 0} ≤ 3)
    (hClose : ∑ i, (hHerm.eigenvalues₀ i-v i)^2 < (2/3 : ℝ)) :
    (boolAdj A).rank ≤ 5 := by
  by_contra! hLarge
  have hTranspose : (boolAdj A)ᵀ = boolAdj A := by
    ext i j
    change (if A j i then (1 : ℝ) else 0) = if A i j then 1 else 0
    rw [hsymm]
  have contrad {k : ℕ}
      (h : ∀ (M : Fin k → Fin k → Bool), (∀ i, M i i = false) →
        (∀ i j, M i j = M j i) → (boolAdj M).det ≠ 0 →
        ∀ C : Matrix (Fin k) (Fin k) ℝ, C.rank ≤ 3 → (2/3 : ℝ) < sqFrob (boolAdj M-C))
      (f : Fin k ↪ m) (hf : ((boolAdj A).submatrix f f).det ≠ 0) : False := by
    have hminor (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.rank ≤ 3) :
      (2/3 : ℝ) ≤ sqFrob (((boolAdj A).submatrix f f)-C) := by
      exact (h (fun i j => A (f i) (f j)) (fun i => hdiag (f i))
        (fun i j => hsymm (f i) (f j)) hf C hC).le
    exact (not_lt_of_ge (ordered_distance_ge_of_minor (boolAdj A) hHerm f (2/3) hminor v hv)) hClose
  rcases rank_six_principal (boolAdj A) hTranspose (by omega) with ⟨f,hf⟩|⟨f,hf⟩
  · exact contrad h6 f hf
  · exact contrad h7 f hf

noncomputable def tripartiteProfile (n : Nat) (i : Fin (Fintype.card (Fin (3*n)))) : ℝ :=
  if i.val = 0 then 2*(n : ℝ) else if 3*n ≤ i.val+2 then -(n : ℝ) else 0

theorem tripartite_profile_support (n : Nat) (_hn : 3 ≤ n) :
    Fintype.card {i // tripartiteProfile n i ≠ 0} ≤ 3 := by
  classical
  let e (i : {i // tripartiteProfile n i ≠ 0}) : Fin 3 :=
    if i.val.val = 0 then 0 else if i.val.val+2 = 3*n then 1 else 2
  have relevant (i : {i // tripartiteProfile n i ≠ 0}) :
      i.val.val=0 ∨ i.val.val+2=3*n ∨ i.val.val+1=3*n := by
    have hLt : i.val.val < 3*n := i.val.isLt.trans_eq (Fintype.card_fin _)
    have hne := i.property
    by_cases h0 : i.val.val=0
    · exact Or.inl h0
    · by_cases h2 : 3*n ≤ i.val.val+2
      · omega
      · simp [tripartiteProfile,h0,h2] at hne
  have inj : Function.Injective e := by
    intro i j h
    have hi := relevant i
    have hj := relevant j
    apply Subtype.ext
    apply Fin.ext
    by_cases h0i : i.val.val = 0 <;> by_cases h0j : j.val.val = 0 <;>
      by_cases h2i : i.val.val+2 = 3*n <;> by_cases h2j : j.val.val+2 = 3*n <;>
      simp [e,h0i,h0j,h2i,h2j] at h <;> omega
  simpa using Fintype.card_le_of_injective e inj

end SpectralRank
namespace SpectralRank.Indexed
theorem cert_of_corpus (n : Nat) (R : Array Nat) (l : List (Nat × Cert))
    (hc : l.all (fun x => good n x.1 x.2) = true)
    (hr : R.toList = l.map Prod.fst) :
    ∀ r : Fin R.size, ∃ x, good n R[r] x = true := by
  intro r
  have hm : R[r] ∈ R.toList := by
    have hi : r.val < R.toList.length := by simp
    have h := List.getElem_mem hi
    rwa [Array.getElem_toList] at h
  rw [hr] at hm
  obtain ⟨w,hw,he⟩ := List.mem_map.mp hm
  refine ⟨w.2,?_⟩
  rw [← he]
  exact List.all_eq_true.mp hc w hw
end SpectralRank.Indexed
namespace SpectralRank
theorem problem_21_of_checked_corpora
    (R6 R7 : Array Nat)
    (hCov6 : SpectralRank.CoverageData.Covers 6 R6) (hCov7 : SpectralRank.CoverageData.Covers 7 R7)
    (l6 l7 : List (Nat × SpectralRank.Indexed.Cert))
    (hc6 : l6.all (fun x => SpectralRank.Indexed.good 6 x.1 x.2) = true)
    (hc7 : l7.all (fun x => SpectralRank.Indexed.good 7 x.1 x.2) = true)
    (hr6 : R6.toList = l6.map Prod.fst) (hr7 : R7.toList = l7.map Prod.fst)
    (n : Nat) (hn : 3 ≤ n)
    (A : Fin (3*n) → Fin (3*n) → Bool)
    (hdiag : ∀ i, A i i = false) (hsymm : ∀ i j, A i j = A j i)
    (hHerm : (boolAdj A).IsHermitian)
    (hClose : ∑ i, (hHerm.eigenvalues₀ i-tripartiteProfile n i)^2 < (2/3 : ℝ)) :
    (boolAdj A).rank ≤ 5 := by
  have six := near_rank_of_cover R6 hCov6 (SpectralRank.Indexed.cert_of_corpus 6 R6 l6 hc6 hr6)
  have seven := near_rank_of_cover R7 hCov7 (SpectralRank.Indexed.cert_of_corpus 7 R7 l7 hc7 hr7)
  exact universal_adjacency_rank_bound six seven A hdiag hsymm hHerm
    (tripartiteProfile n) (tripartite_profile_support n hn) hClose

theorem boolAdj_isHermitian {m : Type*} (A : m → m → Bool)
    (hsymm : ∀ i j, A i j = A j i) : (boolAdj A).IsHermitian := by
  change (boolAdj A)ᴴ = boolAdj A
  ext i j
  simp [boolAdj, hsymm j i]

/-- An affirmative answer to Jovanović–Sedlar–Škrekovski Problem 21
(arXiv:2610.18636v2), with no connectedness requirement. -/
theorem problem_21
    (n : Nat) (hn : 3 ≤ n) (A : Fin (3*n) → Fin (3*n) → Bool)
    (hdiag : ∀ i, A i i = false) (hsymm : ∀ i j, A i j = A j i)
    (hClose : ∑ i, ((boolAdj_isHermitian A hsymm).eigenvalues₀ i-
      tripartiteProfile n i)^2 < (2/3 : ℝ)) :
    (boolAdj A).rank ≤ 5 := by
  exact problem_21_of_checked_corpora SpectralRank.CoverageData.R6 SpectralRank.CoverageData.R7
    SpectralRank.CoverageData.covers6 SpectralRank.CoverageData.covers7
    SpectralRank.Indexed.allCert6 SpectralRank.Indexed.allCert7
    SpectralRank.Indexed.allCert6_ok SpectralRank.Indexed.allCert7_ok rfl rfl
    n hn A hdiag hsymm (boolAdj_isHermitian A hsymm) hClose

#print axioms SpectralRank.problem_21
end SpectralRank
