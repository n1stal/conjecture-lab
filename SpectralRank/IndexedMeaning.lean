module

public import SpectralRank.SpectralFinite
public import SpectralRank.IntegerCut
public import SpectralRank.FrobeniusBridge

@[expose] public section

open Matrix Finset Module SpectralRank
open scoped BigOperators InnerProductSpace
namespace SpectralRank.Indexed

def mat (n mask : Nat) : Matrix (Fin n) (Fin n) ℤ := fun i j => adj mask i j
theorem dotF_eq (n : Nat) (x y : Fin n → ℤ) : dotF n x y = x ⬝ᵥ y := by
  simp [dotF,dotProduct,List.sum_ofFn]
theorem actF_eq (n m : Nat) (x : Fin n → ℤ) :
    actF n m x = mat n m *ᵥ x := by
  ext i
  simp [actF,dotF_eq,Matrix.mulVec,mat]
theorem every_true {n : Nat} {f : Fin n → Bool} (h : every n f = true) :
    ∀ i, f i = true := by
  intro i
  exact List.all_eq_true.mp h _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
theorem someB_true {n : Nat} {f : Fin n → Bool} (h : someB n f = true) :
    ∃ i, f i = true := by
  obtain ⟨x,hx,hval⟩ := List.any_eq_true.mp h
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
  exact ⟨i,hval⟩
theorem sing_sound (n m : Nat) (z : Vec) (h : sing n m z = true) :
    ((mat n m).map (Int.castRingHom ℝ)).det = 0 := by
  simp only [sing, Bool.and_eq_true] at h
  obtain ⟨i,hi⟩ := someB_true h.1
  let u : Fin n → ℤ := fun j => vec z j
  have hu : u ≠ 0 := by
    intro h
    have hz : vec z i = 0 := congrFun h i
    simp [hz] at hi
  have ha : mat n m *ᵥ u = 0 := by
    rw [← actF_eq]
    funext j
    exact beq_iff_eq.mp (every_true h.2 j)
  have hd := (Matrix.exists_mulVec_eq_zero_iff (M := mat n m)).mp ⟨u,hu,ha⟩
  change (((Int.castRingHom ℝ).mapMatrix (mat n m))).det = 0
  rw [← RingHom.map_det,hd,map_zero]
theorem gramF_eq (n m q d : Nat) (A : Array Vec) (i j : Fin d) :
    let P : Matrix (Fin n) (Fin d) ℤ := fun r s => col A s r
    let B := mat n m
    gramF n m q A i j = (Pᵀ * ((100 : ℤ) • (Bᵀ * B) -
      (Int.ofNat q)^2 • (1 : Matrix (Fin n) (Fin n) ℤ)) * P) i j := by
  let P : Matrix (Fin n) (Fin d) ℤ := fun r s => col A s r
  let K : Matrix (Fin n) (Fin n) ℤ := (100 : ℤ) • ((mat n m)ᵀ * mat n m) -
    (Int.ofNat q)^2 • (1 : Matrix (Fin n) (Fin n) ℤ)
  change _ = ((Pᵀ * K) * P) i j
  rw [Matrix.mul_assoc]
  change _ = (fun r : Fin n => col A i r) ⬝ᵥ
      (((100 : ℤ) • ((mat n m)ᵀ * mat n m) -
      (Int.ofNat q)^2 • (1 : Matrix (Fin n) (Fin n) ℤ)) *ᵥ
          (fun r : Fin n => col A j r))
  rw [sub_mulVec,smul_mulVec,smul_mulVec,one_mulVec,dotProduct_sub,dotProduct_smul,
      dotProduct_smul,← mulVec_mulVec,dotProduct_transpose_mulVec]
  simp only [gramF,dotF_eq,actF_eq,smul_eq_mul]
  rw [dotProduct_comm (mat n m *ᵥ fun r => col A i r)]
theorem positive_gram_of_check (n m q d : Nat) (A : Array Vec)
    (h : ∀ (r s : Fin d),
      (if r == s then decide (0 < gramF n m q A r s) else gramF n m q A r s == 0) = true) :
    ∃ V : Submodule ℝ (EuclideanSpace ℝ (Fin n)), Module.finrank ℝ V = d ∧
      ∀ x ∈ V, ((q : ℝ)/10)^2 * ‖x‖^2 ≤
        ‖((mat n m).map (Int.castRingHom ℝ)).toEuclideanLin x‖^2 := by
  let P : Matrix (Fin n) (Fin d) ℤ := fun r s => col A s r
  let diag (r : Fin d) := gramF n m q A r r
  have hd (r : Fin d) : 0 < diag r := by
    simpa [diag] using h r r
  have hg : Pᵀ * ((100 : ℤ) • ((mat n m)ᵀ * mat n m) -
      (Int.ofNat q)^2 • (1 : Matrix (Fin n) (Fin n) ℤ)) * P = diagonal diag := by
    ext r s
    rw [← gramF_eq n m q d A r s]
    by_cases hr : r = s
    · subst s
      simp [diag]
    · have hz : gramF n m q A r s = 0 := by simpa [hr] using h r s
      rw [hz,diagonal_apply_ne _ hr]
  simpa using SpectralRank.integer_square_cut_positive (mat n m) P diag
    (Int.ofNat q) hg hd
theorem nonSing_sound (n m : Nat) (a : Array Bound) (h : nonSing n m a = true) :
    ∀ C : Matrix (Fin n) (Fin n) ℝ, C.rank ≤ 3 →
      2/3 < SpectralRank.sqFrob (((mat n m).map (Int.castRingHom ℝ)) - C) := by
  intro C hC
  let get (i : Fin (n-3)) := a[i.val]?.getD (0,0,#[])
  let q (i : Fin (n-3)) : ℝ := ((get i).1 : ℝ)/10
  simp only [nonSing,Bool.and_eq_true,decide_eq_true_eq] at h
  have hvec (i : Fin (n-3)) :
      ∃ V : Submodule ℝ (EuclideanSpace ℝ (Fin n)),
        3+i.val+1 ≤ Module.finrank ℝ V ∧
        ∀ x ∈ V, (q i)^2 * ‖x‖^2 ≤
        ‖((mat n m).map (Int.castRingHom ℝ)).toEuclideanLin x‖^2 := by
    have hi := every_true h.2 i
    change (let (j,d,A) := get i
      if j == 0 then true else
        decide (i.val+4 ≤ d) && every d (fun r => every d (fun s =>
          let g := gramF n m j A r s
          if r == s then decide (0 < g) else g == 0))) = true at hi
    rcases hg : get i with ⟨j,d,A⟩
    rw [hg] at hi
    simp only [q,hg]
    by_cases hj : j=0
    · refine ⟨⊤,?_ ,?_⟩
      · simpa using show 3+i.val+1 ≤ n by have := i.isLt; omega
      · intro x hx
        simp [hj]
    · have hIf : (j == 0) ≠ true := fun ht => hj (beq_iff_eq.mp ht)
      simp only [hIf] at hi
      have hh := Bool.and_eq_true_iff.mp hi
      have hd : i.val+4 ≤ d := of_decide_eq_true hh.1
      obtain ⟨V,hV,hx⟩ := positive_gram_of_check n m j d A
        (fun r s => every_true (every_true hh.2 r) s)
      exact ⟨V,by rw [hV]; omega,hx⟩
  classical
  let V (i : Nat) := if hi : i < n-3 then Classical.choose (hvec ⟨i,hi⟩) else ⊥
  have selected (i : Fin (n-3)) :
      3+i.val+1 ≤ Module.finrank ℝ (V i) ∧
      ∀ x ∈ V i, (q i)^2 * ‖x‖^2 ≤
        ‖((mat n m).map (Int.castRingHom ℝ)).toEuclideanLin x‖^2 := by
    unfold V
    rw [dite_eq_left i.isLt]
    exact Classical.choose_spec (hvec i)
  refine LT.lt.trans_le ?_ (SpectralRank.frobenius_ge_thresholds
    ((mat n m).map (Int.castRingHom ℝ)) C 3 (n-3) hC q V
    (fun i => (selected i).1) (fun i => (selected i).2))
  have hn : 200 < 3 * ∑ i : Fin (n-3), (get i).1 * (get i).1 := by
    simpa [List.sum_ofFn,get] using h.1
  have hr : (200 : ℝ) < 3 * ∑ i : Fin (n-3), ((get i).1 : ℝ) * ((get i).1 : ℝ) := by
    exact_mod_cast hn
  have heq : (∑ i, q i ^ 2) = ∑ i : Fin (n-3),
        ((get i).1 : ℝ) * ((get i).1 : ℝ) / 100 := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp [q]
    ring
  rw [heq,← Finset.sum_div]
  linarith

theorem good_sound (n m : Nat) (x : Cert) (h : good n m x = true)
    (hd : ((mat n m).map (Int.castRingHom ℝ)).det ≠ 0) :
    ∀ C : Matrix (Fin n) (Fin n) ℝ, C.rank ≤ 3 →
      2/3 < SpectralRank.sqFrob (((mat n m).map (Int.castRingHom ℝ)) - C) := by
  rcases Bool.or_eq_true_iff.mp h with hs|hn
  · exact (hd (sing_sound n m x.1 hs)).elim
  · exact nonSing_sound n m x.2 hn

#print axioms SpectralRank.Indexed.good_sound
end SpectralRank.Indexed
