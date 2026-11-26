module

public import InverseZProofs.Bridge
public import InverseZProofs.MobiusPositive
public import InverseZProofs.RankFour

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace InverseZ.Algebra
open Finset Polynomial Matroid Set
open scoped BigOperators ENat

variable {α : Type*} [Finite α] (M : Matroid α)

noncomputable def coefficients (M : Matroid α) : List ℤ :=
  (List.range (M.eRank.toNat+1)).map (matroidInverseZ M).coeff

theorem rank_from_toNat {k : ℕ} (hr : M.eRank.toNat = k) :
    M.eRank = (k : ℕ∞) := by
  rw [← M.eRk_ground]
  change M.eRk (topFlat M).val = (k : ℕ∞)
  rw [← coe_flatRank M (topFlat M), flatRank_top, hr]

theorem W_two_positive (h : 2 ≤ M.eRank) :
    0 < W (flatRank M) (bottomFlat M) (topFlat M) 2 := by
  rw [W_eq_card]
  have hNonempty : Nonempty (FlatAt M 2) := by
    obtain ⟨B,hB⟩ := M.exists_isBase
    obtain ⟨L,hLB,hLcard⟩ := Set.exists_subset_encard_eq (hB.encard_eq_eRank.symm ▸ h)
    exact ⟨⟨M.closure L, M.isFlat_closure _, by
      rw [M.eRk_closure_eq,(hB.indep.subset hLB).eRk_eq_encard,hLcard]⟩⟩
  exact_mod_cast (Nat.card_pos : 0 < Nat.card (FlatAt M 2))

theorem top_coeff_positive :
    0 < (matroidInverseZ M).coeff M.eRank.toNat := by
  rw [matroidInverseZ_top_coeff]
  exact InverseZ.matroid_signed_mobius_positive M (topFlat M)

theorem rank_four_actual_arithmetic
    (pairs : ∀ p ∈ M.E, ∀ q ∈ M.E, p ≠ q → M.Indep ({p,q} : Set α))
    (hr : M.eRank.toNat = 4) :
    let f := (matroidInverseZ M).coeff
    LogConcave [f 4,f 3,f 2,f 3,f 4] ∧ Positive [f 4,f 3,f 2,f 3,f 4] := by
  dsimp only
  classical
  set a := bottomFlat M
  set b := topFlat M
  set r := flatRank M
  have hle : a ≤ b := bottomFlat_le M _
  have hdiff : r b-r a=4 := by simpa [r,a,b] using hr
  have hR : M.eRank = 4 := rank_from_toNat M hr
  have hpoint : 1 < M.E.encard := (by decide : (1:ℕ∞) < 4).trans_le
    (hR ▸ M.eRank_le_encard_ground)
  have hfA := inverseZ_rank_four_A r (flatRank_strict M) hle hdiff
  have hfB := inverseZ_rank_four_B r (flatRank_strict M) hle hdiff
  have hfC := inverseZ_rank_four_C r (flatRank_strict M) hle hdiff
  change (matroidInverseZ M).coeff 4 = _ at hfA
  change (matroidInverseZ M).coeff 3 = _ at hfB
  change (matroidInverseZ M).coeff 2 = _ at hfC
  have hA : 0 < (matroidInverseZ M).coeff 4 := by simpa [hr] using top_coeff_positive M
  have hCB : (matroidInverseZ M).coeff 2 - (matroidInverseZ M).coeff 3 =
      W r a b 2-W r a b 1 := by omega
  have hd : ((matroidInverseZ M).coeff 3 - (matroidInverseZ M).coeff 4) -
      ((matroidInverseZ M).coeff 2 - (matroidInverseZ M).coeff 3) =
      I r a b 2 3-2*W r a b 2-W r a b 3+W r a b 1+1 := by omega
  have hCB' : (matroidInverseZ M).coeff 2 - (matroidInverseZ M).coeff 3 =
      (Nat.card (FlatAt M 2) : ℤ) - Nat.card M.E := by
    simpa [r,a,b,W_eq_card,W_one_eq_ground_card M pairs hpoint] using hCB
  have hInc : Nat.card (IncidentAt M 2 3) = Nat.card (Incidence M) := rfl
  have hd' : ((matroidInverseZ M).coeff 3 - (matroidInverseZ M).coeff 4) -
      ((matroidInverseZ M).coeff 2 - (matroidInverseZ M).coeff 3) =
      geomCurvature M := by
    simpa [r,a,b,geomCurvature,I_eq_card,hInc,W_eq_card,W_one_eq_ground_card M pairs hpoint]
      using hd
  have hp : Nat.card M.E ≤ Nat.card (FlatAt M 2) :=
    InverseZ.matroid_point_line M pairs (by rw [hR]; decide)
  have hcard : (Nat.card M.E : ℕ∞) = M.E.encard := by
    rw [Nat.card_coe_set_eq,(Set.toFinite M.E).cast_ncard_eq]
  have hc : 4 ≤ Nat.card M.E := by
    have hl := M.eRank_le_encard_ground
    rw [hR,←hcard] at hl
    exact (Nat.cast_le (α := ℕ∞)).mp hl
  have hbound := InverseZ.geom_curvature_bound M hR
  exact InverseZ.rank_four_arithmetic _ _ _ hA (by omega) (by omega)

/-- Inverse Z of any finite pair-independent matroid of rank at most four is
    log-concave, with positive coefficients in the full rank range. -/
theorem rank_at_most_four_pairs_logconcave
    (pairs : ∀ p ∈ M.E, ∀ q ∈ M.E, p ≠ q → M.Indep ({p,q} : Set α))
    (hr : M.eRank ≤ 4) :
    InverseZ.LogConcave (coefficients M) ∧ InverseZ.Positive (coefficients M) := by
  classical
  let f := (matroidInverseZ M).coeff
  have hrn : M.eRank.toNat ≤ 4 := ENat.toNat_le_of_le_natCast hr
  have cases : M.eRank.toNat=0 ∨ M.eRank.toNat=1 ∨ M.eRank.toNat=2 ∨
      M.eRank.toNat=3 ∨ M.eRank.toNat=4 := by omega
  have hpos : 0 < f M.eRank.toNat := top_coeff_positive M
  have hpal : ∀ i ≤ M.eRank.toNat, f (M.eRank.toNat-i) = f i :=
    matroidInverseZ_palindromic M
  set a := bottomFlat M
  set b := topFlat M
  set r := flatRank M
  have hle : a ≤ b := bottomFlat_le M _
  have hdiff : r b-r a = M.eRank.toNat := by simp [r,b,a]
  have hh : matroidInverseZ M = inverseZ r (inverseKL r (flatRank_strict M)) a b := rfl
  have hcoeff : coefficients M = (List.range (M.eRank.toNat+1)).map f := rfl
  rcases cases with h0 | h1 | h2 | h3 | h4
  · have hY0 := inverseZ_rank_zero r (flatRank_strict M) hle (hdiff.trans h0)
    rw [← hh] at hY0
    rw [hcoeff, h0, show List.range (0+1) = [0] by decide, List.map_cons, List.map_nil]
    have hf : f 0=1 := by dsimp [f]; rw [hY0]; simp
    rw [hf]
    exact rank_zero_one_arithmetic.1
  · have hY1 := inverseZ_rank_one r (flatRank_strict M) hle (hdiff.trans h1)
    rw [← hh] at hY1
    rw [hcoeff,h1, show List.range (1+1) = [0,1] by decide]
    simp only [List.map_cons,List.map_nil]
    dsimp only [f]
    rw [hY1.1,hY1.2]
    exact rank_zero_one_arithmetic.2
  · have hY2 := inverseZ_rank_two r (flatRank_strict M) hle (hdiff.trans h2)
    rw [← hh] at hY2
    have hpal0 := hpal 0 (by omega)
    simp only [h2, Nat.sub_zero] at hpal0 hpos
    have hP : 2 ≤ W r a b 1 := by
      change 0 < (matroidInverseZ M).coeff 2 at hpos
      omega
    rw [hcoeff,h2, show List.range (2+1) = [0,1,2] by decide]
    simp only [List.map_cons,List.map_nil,← hpal0]
    dsimp only [f]
    rw [hY2.1,hY2.2]
    exact rank_two_arithmetic _ hP
  · have hY3 := inverseZ_rank_three r (flatRank_strict M) hle (hdiff.trans h3)
    rw [← hh] at hY3
    have hr3 : M.eRank=3 := rank_from_toNat M h3
    have hW := W_two_positive M (by rw [hr3]; decide)
    have hpal0 := hpal 0 (by omega)
    have hpal1 := hpal 1 (by omega)
    norm_num [h3] at hpal0 hpal1 hpos
    rw [hcoeff,h3, show List.range (3+1) = [0,1,2,3] by decide]
    simp only [List.map_cons,List.map_nil,← hpal0,← hpal1]
    change InverseZ.LogConcave [f 3,f 2,f 2,f 3] ∧ _
    apply rank_three_arithmetic _ _ hpos
    change (matroidInverseZ M).coeff 3 ≤ (matroidInverseZ M).coeff 2
    change 0 < W r a b 2 at hW
    omega
  · have hpal0 := hpal 0 (by omega)
    have hpal1 := hpal 1 (by omega)
    norm_num [h4] at hpal0 hpal1
    rw [hcoeff,h4, show List.range (4+1) = [0,1,2,3,4] by decide]
    simp only [List.map_cons,List.map_nil,← hpal0,← hpal1]
    exact rank_four_actual_arithmetic M pairs h4

#print axioms rank_four_actual_arithmetic
#print axioms rank_at_most_four_pairs_logconcave
end InverseZ.Algebra
