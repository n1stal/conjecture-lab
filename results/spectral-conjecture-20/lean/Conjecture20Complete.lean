import Conjecture20Nearest
import C20Limit

namespace Conjecture20
open Conjecture20Squared ManhattanLarge PawUnbounded SpectralConjecture20 Filter
open scoped BigOperators Topology

/-- A uniform explicit rate for the actual graph H_n in the Manhattan metric. -/
theorem actual_hub_l1_rate (n : Nat) (hn : 5≤n) :
    |(n:ℝ)*(l1 n _ (hub_herm n)-1)| ≤ 4 := by
  let q := singletonQEigen (n-1) n n
  have hA := benchmark_spectral_antitone n
  have hab : q 1≤q 0 := hA (by decide)
  have hbc : q 2≤q 1 := hA (by decide)
  have hcd : q 3≤q 2 := hA (by decide)
  have hnR : (5:ℝ)≤n := by exact_mod_cast hn
  obtain ⟨hd,hf⟩ := HubBenchmark.reduce_quartic n (q 0) (q 1) (q 2) (q 3)
    (by linarith) (hcd.trans (hbc.trans hab)) (hcd.trans hbc) hcd
    (benchmark_actual_quartic n (by omega))
  have hb := HubBenchmark.brackets_large n (q 0) (q 1) (q 2) hnR hab hbc hf
  obtain ⟨⟨hr₀,hr₁⟩,⟨ht₀,ht₂⟩,htrace⟩ := C20NumericalCore.small_root_errors hnR hb hf
  have hsz := hub_card n (by omega)
  have hN : 4≤Fintype.card (Vertices (singletonWeights (n-1) n n) ⊕ Fin 0) := by omega
  obtain ⟨hy0,hy1,hy2,hy3,_,_,_,_,_,_,hyR⟩ := profile n _ (by omega) hsz
  have hEq := singleton_ordered_quartet_score_eq n (n-1) n n 0 (by omega) (by omega) (by omega)
    (hub_herm n) hN (target n _) hy0 hy1 hy2 hy3 hyR abs abs_zero
  change l1 n _ (hub_herm n) = |q 0-2*n|+|q 1|+|q 2+n|+|q 3+n| at hEq
  have hObj : l1 n _ (hub_herm n) = 2*(q 1+(q 2+n)) := by
    rw [hEq,hd,neg_add_cancel,abs_zero,add_zero,abs_of_neg (by linarith [hb.1.2]),
      abs_of_pos hb.2.1.1,abs_of_pos (by linarith [hb.2.2.1])]
    linarith only [htrace]
  have hErr : (n:ℝ)*(l1 n _ (hub_herm n)-1) =
      -2*((n:ℝ)*(1/2-q 1))+2*((n:ℝ)*(q 2+n)) := by
    rw [hObj]
    ring
  rw [hErr,abs_le]
  constructor <;> linarith only [hr₀,hr₁,ht₀,ht₂]

/-- All realized Manhattan scores of eligible graphs, including any
non-isomorphic cospectral graph should one exist. -/
def manhattanCompetitors (n : Nat) : Set ℝ := {s | ∃ (A : Fin (3*n) → Fin (3*n) → Bool)
    (hs : ∀ i j, A i j=A j i), (∀ i, A i i=false) ∧
    (¬ RelabelAs (realAdj A) (balanced n)) ∧ l1 n _ (realAdjHerm A hs)=s}

noncomputable def manhattanCospectrality (n : Nat) : ℝ := sInf (manhattanCompetitors n)

theorem manhattan_cospectrality_eq (n : Nat) (hn : 3≤n) :
    manhattanCospectrality n=l1 n _ (hub_herm n) := by
  obtain ⟨A,hs,hd,hr⟩ := hub_has_bool_representative n (by omega)
  obtain ⟨hNot,hMin⟩ := ((nearest_both n hn A hs hd).1).mpr hr
  obtain ⟨e,he⟩ := hr
  have eq := l1_relabel n _ (realAdjHerm A hs) _ (hub_herm n) e he.symm
  apply IsLeast.csInf_eq
  constructor
  · exact ⟨A,hs,hd,hNot,eq.symm⟩
  · rintro s ⟨B,ht,hD,hnB,heq⟩
    exact eq.le.trans ((hMin B ht hD hnB).trans heq.le)

theorem conjecture_20_manhattan_limit :
    Tendsto manhattanCospectrality atTop (𝓝 (1:ℝ)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨K,hK⟩ := exists_nat_gt (4/ε)
  refine ⟨max K 5,?_⟩
  intro n hn
  have h5 : 5≤n := (le_max_right K 5).trans hn
  have hk : K≤n := (le_max_left K 5).trans hn
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have he : 4 < (n:ℝ)*ε := (div_lt_iff₀ hε).mp (hK.trans_le (by exact_mod_cast hk))
  rw [Real.dist_eq,manhattan_cospectrality_eq n (by omega)]
  have hb := actual_hub_l1_rate n h5
  rw [abs_mul,abs_of_pos hnR] at hb
  exact lt_of_mul_lt_mul_left (hb.trans_lt he) hnR.le

/-- The nearest graph and both asymptotic assertions of Conjecture 20. -/
theorem conjecture20 :
    (∀ (n : Nat) (_hn : 3≤n)
      (A : Fin (3*n) → Fin (3*n) → Bool) (hs : ∀ i j, A i j=A j i)
      (_hd : ∀ i, A i i=false),
      (IsNearest n (l1 n) A hs ↔ RelabelAs (realAdj A) (hub n)) ∧
      (IsNearest n (score n) A hs ↔ RelabelAs (realAdj A) (hub n))) ∧
    Tendsto manhattanCospectrality atTop (𝓝 (1:ℝ)) ∧
    Tendsto C20Rate.cospectralitySquared atTop (𝓝 (1/2:ℝ)) :=
  ⟨nearest_both,conjecture_20_manhattan_limit,C20Rate.conjecture_20_squared_limit⟩

#print axioms actual_hub_l1_rate
#print axioms conjecture20
end Conjecture20
