module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Basic.Real.Basic

@[expose] public section

open Matrix
namespace SpectralRank

theorem schur_nonzero {s t : Type*} [Fintype s] [Fintype t] [DecidableEq s]
    (A : Matrix s s ℝ) (B : Matrix s t ℝ) (C : Matrix t s ℝ) (D : Matrix t t ℝ)
    [Invertible A] (h : Fintype.card s < (fromBlocks A B C D).rank) :
    D - C * ⅟A * B ≠ 0 := by
  intro hz
  have hz' : D = C * ⅟A * B := sub_eq_zero.mp hz
  let U : Matrix (s ⊕ t) s ℝ := fun i j => i.elim (fun a => (1 : Matrix s s ℝ) a j)
    (fun a => (C * ⅟A) a j)
  let V : Matrix s (s ⊕ t) ℝ := fun i j => j.elim (A i) (B i)
  have hf : fromBlocks A B C D = U * V := by
    ext (i|i) (j|j)
    · change A i j = ((1 : Matrix s s ℝ) * A) i j
      rw [Matrix.one_mul]
    · change B i j = ((1 : Matrix s s ℝ) * B) i j
      rw [Matrix.one_mul]
    · change C i j = ((C * ⅟A) * A) i j
      rw [Matrix.mul_assoc, invOf_mul_self, Matrix.mul_one]
    · change D i j = ((C * ⅟A) * B) i j
      rw [hz']
  exact (not_le_of_gt h) (hf ▸ (rank_mul_le_left U V).trans U.rank_le_card_width)

theorem small_principal_pivot {t : Type*} [Fintype t] [DecidableEq t]
    (E : Matrix t t ℝ) (hE : Eᵀ = E) (h0 : E ≠ 0) :
    ∃ (k : ℕ) (e : Fin k ↪ t), (k=1 ∨ k=2) ∧ (E.submatrix e e).det ≠ 0 := by
  classical
  by_cases h : ∃ i, E i i ≠ 0
  · obtain ⟨i,hi⟩ := h
    let e : Fin 1 ↪ t := ⟨fun _ => i,fun _ _ _ => Subsingleton.elim _ _⟩
    exact ⟨1,e,Or.inl rfl,by rw [det_fin_one]; exact hi⟩
  · push Not at h
    obtain ⟨i,j,hij⟩ : ∃ i j, E i j ≠ 0 := by
      by_contra! he
      exact h0 (by ext i j; exact he i j)
    have hne : i ≠ j := fun eq => hij (eq ▸ h i)
    let f : Fin 2 → t := fun a => if a=0 then i else j
    have hf : Function.Injective f := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all [f, Ne.symm hne]
    let e : Fin 2 ↪ t := ⟨f,hf⟩
    refine ⟨2,e,Or.inr rfl,?_⟩
    have hs : E j i = E i j := congrFun (congrFun hE i) j
    simpa [det_fin_two,e,f,h,hs] using mul_ne_zero hij hij

theorem extend_block_pivot {m s t : Type*} [Fintype m] [Fintype s] [Fintype t]
    [DecidableEq s] [DecidableEq t]
    (H : Matrix m m ℝ) (hH : Hᵀ = H) (e : s ⊕ t ≃ m)
    (hn : (H.submatrix (e ∘ Sum.inl) (e ∘ Sum.inl)).det ≠ 0)
    (hr : Fintype.card s < H.rank) :
    ∃ (k : ℕ) (f : s ⊕ Fin k ↪ m), (k=1 ∨ k=2) ∧
      (H.submatrix f f).det ≠ 0 := by
  let A : Matrix s s ℝ := H.submatrix (e ∘ Sum.inl) (e ∘ Sum.inl)
  let B : Matrix s t ℝ := H.submatrix (e ∘ Sum.inl) (e ∘ Sum.inr)
  let C : Matrix t s ℝ := H.submatrix (e ∘ Sum.inr) (e ∘ Sum.inl)
  let D : Matrix t t ℝ := H.submatrix (e ∘ Sum.inr) (e ∘ Sum.inr)
  let : Invertible A := invertibleOfIsUnitDet A (isUnit_iff_ne_zero.mpr hn)
  let E := D - C * ⅟A * B
  have hA : Aᵀ = A := by
    ext i j
    exact congrFun (congrFun hH (e (Sum.inl i))) (e (Sum.inl j))
  have hBC : Bᵀ = C := by
    ext i j
    exact congrFun (congrFun hH (e (Sum.inr i))) (e (Sum.inl j))
  have hCB : Cᵀ = B := by rw [← hBC, transpose_transpose]
  have hD : Dᵀ = D := by
    ext i j
    exact congrFun (congrFun hH (e (Sum.inr i))) (e (Sum.inr j))
  have hAi : (⅟A)ᵀ = ⅟A := by
    rw [invOf_eq_nonsing_inv,transpose_nonsing_inv,hA]
  have hE : Eᵀ = E := by
    dsimp only [E]
    rw [transpose_sub,transpose_mul,transpose_mul,hAi,hBC,hCB,hD,Matrix.mul_assoc]
  have hb : fromBlocks A B C D = H.submatrix e e := by
    ext (i|i) (j|j) <;> rfl
  have hr' : Fintype.card s < (fromBlocks A B C D).rank := by
    rwa [hb,rank_submatrix]
  obtain ⟨k,g,hk,hg⟩ := small_principal_pivot E hE (schur_nonzero A B C D hr')
  let f : s ⊕ Fin k ↪ m :=
    (Function.Embedding.sumMap (Function.Embedding.refl s) g).trans e.toEmbedding
  let B' : Matrix s (Fin k) ℝ := B.submatrix id g
  let C' : Matrix (Fin k) s ℝ := C.submatrix g id
  let D' : Matrix (Fin k) (Fin k) ℝ := D.submatrix g g
  have hBlock : H.submatrix f f = fromBlocks A B' C' D' := by
    ext (i|i) (j|j) <;> rfl
  have hCut : D' - C' * ⅟A * B' = E.submatrix g g := by
    ext i j
    change D (g i) (g j) - ((C' * ⅟A) * B') i j =
      D (g i) (g j) - ((C * ⅟A) * B) (g i) (g j)
    congr 1
  refine ⟨k,f,hk,?_⟩
  rw [hBlock,det_fromBlocks₁₁,hCut]
  exact mul_ne_zero hn hg

theorem exists_nonsingular_principal_near_rank {m : Type*} [Fintype m]
    (H : Matrix m m ℝ) (hH : Hᵀ = H) (k : ℕ) (hr : k ≤ H.rank) :
    ∃ (l : ℕ) (f : Fin l ↪ m), (l=k ∨ l=k+1) ∧ (H.submatrix f f).det ≠ 0 := by
  classical
  have step (s : Finset m) (hs : (H.submatrix (Subtype.val : s → m) Subtype.val).det ≠ 0) :
      s.card ≤ k+1 →
      ∃ (l : ℕ) (f : Fin l ↪ m), (l=k ∨ l=k+1) ∧ (H.submatrix f f).det ≠ 0 := by
    induction hn : k-s.card using Nat.strong_induction_on generalizing s with
    | h n ih =>
      intro hUpper
      by_cases hLower : k ≤ s.card
      · let e : Fin s.card ≃ s := (Fintype.equivFinOfCardEq (Fintype.card_coe s)).symm
        let f : Fin s.card ↪ m := e.toEmbedding.trans (Function.Embedding.subtype (· ∈ s))
        refine ⟨s.card,f,by omega,?_⟩
        change ((H.submatrix (Subtype.val : s → m) Subtype.val).submatrix e e).det ≠ 0
        rwa [det_submatrix_equiv_self]
      · let e := Equiv.sumCompl (· ∈ s)
        obtain ⟨j,f,hj,hf⟩ := extend_block_pivot H hH e hs
          (by rw [Fintype.card_coe]; omega)
        let S : Finset m := Finset.univ.map f
        have hCard : S.card = s.card+j := by simp [S,Fintype.card_sum]
        have hLt : k-S.card < n := by omega
        let g : s ⊕ Fin j ≃ S := Equiv.ofBijective
          (fun i => ⟨f i, by simp [S]⟩)
          ⟨fun i i' eq => f.injective (congrArg Subtype.val eq),
            fun x => by
              obtain ⟨i,_,hi⟩ := Finset.mem_map.mp x.property
              exact ⟨i,Subtype.ext hi⟩⟩
        have hS : (H.submatrix (Subtype.val : S → m) Subtype.val).det ≠ 0 := by
          rw [← det_submatrix_equiv_self g]
          exact hf
        exact ih _ hLt S hS rfl (by omega)
  apply step (∅ : Finset m)
  · have : IsEmpty (↑(∅ : Finset m)) := ⟨fun a => Finset.notMem_empty a.val a.property⟩
    rw [det_isEmpty]
    exact one_ne_zero
  · simp

theorem rank_six_principal {m : Type*} [Fintype m]
    (H : Matrix m m ℝ) (hH : Hᵀ = H) (hr : 6 ≤ H.rank) :
    (∃ f : Fin 6 ↪ m, (H.submatrix f f).det ≠ 0) ∨
    (∃ f : Fin 7 ↪ m, (H.submatrix f f).det ≠ 0) := by
  obtain ⟨l,f,hl,hf⟩ := exists_nonsingular_principal_near_rank H hH 6 hr
  rcases hl with rfl | rfl
  · exact Or.inl ⟨f,hf⟩
  · exact Or.inr ⟨f,hf⟩

#print axioms SpectralRank.rank_six_principal
end SpectralRank
