module
public import InverseZProjective.ProjectiveUpperMobius
@[expose] public section
set_option autoImplicit false
namespace InverseZProjective.GaussianIncidence
open Module Submodule Finset InverseZ.Algebra InverseZProjective.ProjectiveTrace
variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V] [Finite V]
variable [LocallyFiniteOrder (Submodule K V)]
noncomputable def deletedInFlat (S : Set V) (b : Flats (representedMatroid (K:=K) S)) :
    Finset (Submodule K V) := by
  classical
  exact (Ioc ⊥ (flatSubspaceEmbedding S b)).filter
    (fun x => ¬ ∃ a, flatSubspaceEmbedding S a = x)
theorem Icc_eq_insert_Ioc {L : Type*} [PartialOrder L] [LocallyFiniteOrder L]
    [DecidableEq L] {a b : L} (hab : a ≤ b) :
    Icc a b = insert a (Ioc a b) := by
  ext x
  simp only [mem_Icc, mem_Ioc, mem_insert]
  constructor
  · intro h
    exact (eq_or_lt_of_le h.1).elim (fun he => Or.inl he.symm) (fun hl => Or.inr ⟨hl,h.2⟩)
  · rintro (rfl|h)
    · exact ⟨le_rfl,hab⟩
    · exact ⟨h.1.le,h.2⟩
theorem represented_signedMu_bottom (S : Set V) (hS : LinePreserving (K:=K) S)
    (b : Flats (representedMatroid (K:=K) S)) (n : ℕ)
    (hb : flatRank (representedMatroid (K:=K) S) b = n+1) :
    matroidSignedMu (representedMatroid (K:=K) S) (bottomFlat _) b =
      (Nat.card K : ℤ)^((n+1).choose 2) -
        ((deletedInFlat S b).card : ℤ)*(Nat.card K : ℤ)^(n.choose 2) := by
  classical
  let M := representedMatroid (K:=K) S
  let a := bottomFlat M
  let e := flatSubspaceEmbedding (K:=K) S
  let W := e b
  let D := deletedInFlat S b
  let R := (Ioc (⊥ : Submodule K V) W).filter (fun x => ∃ f, e f = x)
  let C : ℤ := Nat.card K
  have hrank (x : Flats M) : flatRank M x = finrank K (e x) := flatSubspaceEmbedding_rank S x
  have hbot : e a = ⊥ := Submodule.finrank_eq_zero.mp (by rw [← hrank]; exact flatRank_bottom M)
  have hWa : finrank K W = n+1 := (hrank b).symm.trans hb
  have hne : a ≠ b := by
    intro eq
    have hh : flatRank M a = 0 := flatRank_bottom M
    rw [eq, hb] at hh
    omega
  have hne' : (⊥ : Submodule K V) ≠ W := by
    intro eq
    have h := finrank_bot K V
    rw [eq,hWa] at h
    omega
  have hactual := IncidenceAlgebra.sum_Icc_mu_left (𝕜:=ℤ) a b
  rw [Icc_eq_insert_Ioc (bottomFlat_le M _), sum_insert (by simp : a ∉ Ioc a b),
    ite_eq_right hne] at hactual
  have hfull := IncidenceAlgebra.sum_Icc_mu_left (𝕜:=ℤ) (⊥ : Submodule K V) W
  rw [Icc_eq_insert_Ioc bot_le, sum_insert (by simp : (⊥ : Submodule K V) ∉ Ioc ⊥ W),
    ite_eq_right hne'] at hfull
  have hmatches :
      (∑ x ∈ Ioc a b, IncidenceAlgebra.mu ℤ x b) = ∑ y ∈ R, IncidenceAlgebra.mu ℤ y W := by
    refine sum_bij (fun x _ => e x) ?_ ?_ ?_ ?_
    · intro x hx
      obtain ⟨hax,hxb⟩ := mem_Ioc.mp hx
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hbot ▸ e.strictMono hax,e.monotone hxb⟩,⟨x,rfl⟩⟩
    · intro x _ y _ h
      exact e.injective h
    · intro y hy
      obtain ⟨hy₀,⟨x,rfl⟩⟩ := mem_filter.mp hy
      obtain ⟨hy₁,hy₂⟩ := mem_Ioc.mp hy₀
      exact ⟨x,mem_Ioc.mpr ⟨e.lt_iff_lt.mp (hbot.symm ▸ hy₁),e.le_iff_le.mp hy₂⟩,rfl⟩
    · intro x hx
      obtain ⟨hax,_⟩ := mem_Ioc.mp hx
      have hr : 0 < flatRank M x := by
        have hh := flatRank_strict M hax
        rw [flatRank_bottom] at hh
        exact hh
      symm
      exact mu_eq_of_interval_embedding e (flatRank M) (flatRank_strict M) x b
        (fun y hy _ => interval_survives S hS x hr y hy)
  have hsums :
      (∑ y ∈ R, IncidenceAlgebra.mu ℤ y W) + (∑ y ∈ D, IncidenceAlgebra.mu ℤ y W) =
        ∑ y ∈ Ioc (⊥ : Submodule K V) W, IncidenceAlgebra.mu ℤ y W := by
    change (∑ y ∈ (Ioc (⊥ : Submodule K V) W).filter (fun x => ∃ f, e f = x), _) +
      (∑ y ∈ (Ioc (⊥ : Submodule K V) W).filter (fun x => ¬ ∃ f, e f = x), _) = _
    exact sum_filter_add_sum_filter_not _ _ _
  have hD :
      (∑ y ∈ D, IncidenceAlgebra.mu ℤ y W) = (D.card : ℤ)*((-1 : ℤ)^n*C^(n.choose 2)) := by
    calc
      _ = ∑ _y ∈ D, (-1 : ℤ)^n*C^(n.choose 2) := by
        apply sum_congr rfl
        intro y hy
        obtain ⟨hy₀,hy₁⟩ := mem_filter.mp hy
        obtain ⟨hy₂,hy₃⟩ := mem_Ioc.mp hy₀
        have hypos : 0 < finrank K y := by
          have h := Submodule.finrank_lt_finrank_of_lt hy₂
          rwa [finrank_bot] at h
        have hylt : finrank K y < 2 := by
          by_contra hn
          let Y : Surviving (K:=K) S := ⟨y, span_trace_eq_of_linePreserving S hS y (by omega)⟩
          apply hy₁
          refine ⟨representedFlatIso S Y, ?_⟩
          change (((representedFlatIso (K:=K) S).symm) (representedFlatIso S Y)).val = y
          rw [OrderIso.symm_apply_apply]
        have hyone : finrank K y = 1 := by omega
        rw [subspace_mu_closed y W hy₃, hWa, hyone, show n+1-1=n by omega]
      _ = _ := by simp
  have hfull' :
      (-1 : ℤ)^(n+1)*C^((n+1).choose 2) +
        ((∑ y ∈ R, IncidenceAlgebra.mu ℤ y W) + (D.card : ℤ)*((-1 : ℤ)^n*C^(n.choose 2))) = 0 := by
    rw [← hD, hsums]
    rw [subspace_mu_closed _ _ bot_le, hWa, finrank_bot, Nat.sub_zero] at hfull
    exact hfull
  have hactual' : IncidenceAlgebra.mu ℤ a b + (∑ y ∈ R, IncidenceAlgebra.mu ℤ y W) = 0 := by
    rw [← hmatches]
    exact hactual
  have he :
      IncidenceAlgebra.mu ℤ a b = (-1 : ℤ)^(n+1)*C^((n+1).choose 2) +
        (D.card : ℤ)*((-1 : ℤ)^n*C^(n.choose 2)) := by omega
  change (-1 : ℤ)^(flatRank M b-flatRank M a)*IncidenceAlgebra.mu ℤ a b = _
  rw [flatRank_bottom, Nat.sub_zero, hb, he]
  change _ = C^((n+1).choose 2)-(D.card : ℤ)*C^(n.choose 2)
  have ho : (-1 : ℤ)^n*(-1)^n = 1 := by rw [← mul_pow]; norm_num
  rw [pow_succ (-1 : ℤ) n]
  calc
    _ = (((-1 : ℤ)^n)*(-1)^n) *
        (C^((n+1).choose 2)-(D.card : ℤ)*C^(n.choose 2)) := by ring
    _ = _ := by rw [ho,one_mul]
#print axioms represented_signedMu_bottom
end InverseZProjective.GaussianIncidence
