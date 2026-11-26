module

public import SpectralRank.CoverageFinite
public import SpectralRank.CoverageProfiles
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Tactic.ByContra

@[expose] public section

namespace SpectralRank.CoverageData

theorem edge_symm (mask i j : Nat) : edge mask i j = edge mask j i := by
  by_cases h : i=j
  · simp [h]
  · simp [edge,h,Ne.symm h,max_comm,min_comm]

theorem extension_symm (n mask b i j : Nat) :
    extension n mask b i j = extension n mask b j i := by
  by_cases h : i=j
  · simp [h]
  · simp [extension,h,Ne.symm h,Bool.and_comm,edge_symm,min_comm]

theorem checkWitness_sound (n mask b : Nat) (R : Array Nat) (v : Nat × Nat)
    (h : checkWitness n mask b R v = true) :
    ∃ (r : Fin R.size) (e : Equiv.Perm (Fin (n+1))), ∀ i j : Fin (n+1),
      extension n mask b i.val j.val = edge R[r] (e i).val (e j).val := by
  rcases v with ⟨r,p⟩
  simp only [checkWitness,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at h
  obtain ⟨⟨hr,hBound⟩,hp⟩ := h
  let f (i : Fin (n+1)) : Fin (n+1) := ⟨permutation p i,by
    have := hBound i (List.mem_range.mpr i.isLt)
    omega⟩
  have hPair (i j : Fin (n+1)) (hij : i.val < j.val) :
      permutation p i ≠ permutation p j ∧
        extension n mask b i j = edge R[r]! (permutation p i) (permutation p j) := by
    simpa using hp j (List.mem_range.mpr j.isLt) i (List.mem_range.mpr hij)
  have hInj : Function.Injective f := by
    intro i j h
    apply Fin.ext
    by_contra! hne
    have hhP : permutation p i = permutation p j := congrArg Fin.val h
    rcases lt_or_gt_of_ne hne with hh | hh
    · exact (hPair i j hh).1 hhP
    · exact (hPair j i hh).1 hhP.symm
  let e := Equiv.ofBijective f ⟨hInj,Finite.surjective_of_injective hInj⟩
  refine ⟨⟨r,hr⟩,e,fun i j => ?_⟩
  change extension n mask b i j =
    edge R[r] (permutation p i) (permutation p j)
  have hget : R[r]! = R[r] := getElem!_pos R r hr
  rcases lt_trichotomy i.val j.val with hij | hij | hij
  · rw [← hget]
    exact (hPair i j hij).2
  · obtain rfl : i=j := Fin.ext hij
    simp [extension,edge]
  · rw [extension_symm,edge_symm,← hget]
    exact (hPair j i hij).2

theorem checkRow_sound (n mask : Nat) (R : Array Nat) (row : Array (Nat × Nat))
    (h : checkRow n mask R row = true) :
    ∀ b < 2^n, ∃ (r : Fin R.size) (e : Equiv.Perm (Fin (n+1))),
      ∀ i j : Fin (n+1),
        extension n mask b i.val j.val = edge R[r] (e i).val (e j).val := by
  intro b hb
  simp only [checkRow,Bool.and_eq_true,List.all_eq_true] at h
  have hthere := h.2 b (List.mem_range.mpr hb)
  exact checkWitness_sound n mask b R row[b]! hthere

theorem bit_vector (n : Nat) (u : Fin n → Bool) :
    ∃ b < 2^n, ∀ i : Fin n, b.testBit i = u i := by
  induction n with
  | zero =>
    refine ⟨0,by decide,fun i => Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨b,hb,hu⟩ := ih (fun i => u i.castSucc)
    let a : Nat := if u (Fin.last n) then 1 else 0
    refine ⟨2^n*a+b,?_ ,?_⟩
    · rw [Nat.pow_succ]
      cases ha : u (Fin.last n) <;> simp [a,ha] <;> omega
    · intro i
      rw [Nat.testBit_two_pow_mul_add a hb]
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Fin.val_last,lt_self_iff_false,ite_false,Nat.sub_self]
        cases ha : u (Fin.last n) <;> simp [a,ha]
      · simpa [j.isLt] using hu j

theorem lift_permutation (n : Nat) (e : Equiv.Perm (Fin n)) :
    ∃ E : Equiv.Perm (Fin (n+1)), E (Fin.last n) = Fin.last n ∧
      ∀ i : Fin n, E i.castSucc = (e i).castSucc := by
  let f := finSuccEquiv' (Fin.last n)
  let E := f.trans (e.optionCongr.trans f.symm)
  have hlast : f (Fin.last n) = none := by simp [f]
  have hold (i : Fin n) : f i.castSucc = some i := by
    exact finSuccEquiv'_last_apply_castSucc i
  refine ⟨E,?_ ,?_⟩
  · apply f.injective
    simp [E,hlast]
  · intro i
    apply f.injective
    simp [E,hold]

def Covers (n : Nat) (R : Array Nat) : Prop :=
  ∀ (A : Fin n → Fin n → Bool), (∀ i, A i i = false) → (∀ i j, A i j = A j i) →
    ∃ (r : Fin R.size) (e : Equiv.Perm (Fin n)), ∀ i j, A i j = edge R[r] (e i) (e j)

theorem zero_covers (R : Array Nat) (h : 0 < R.size) : Covers 0 R := by
  intro A _ _
  exact ⟨⟨0,h⟩,Equiv.refl _,fun i => Fin.elim0 i⟩

theorem extend_covers (n : Nat) (R S : Array Nat) (hR : Covers n R)
    (hRows : ∀ r : Fin R.size, ∃ row, checkRow n R[r] S row = true) :
    Covers (n+1) S := by
  intro A hdiag hsymm
  obtain ⟨r,e,hr⟩ := hR (fun i j => A i.castSucc j.castSucc)
    (fun i => hdiag i.castSucc) (fun i j => hsymm _ _)
  obtain ⟨E,hElast,hEold⟩ := lift_permutation n e
  obtain ⟨b,hb,hbits⟩ := bit_vector n (fun i => A ((e.symm i).castSucc) (Fin.last n))
  obtain ⟨row,hrow⟩ := hRows r
  obtain ⟨s,p,hp⟩ := checkRow_sound n R[r] S row hrow b hb
  have Realize (i j : Fin (n+1)) : A i j = extension n R[r] b (E i) (E j) := by
    refine Fin.lastCases ?_ (fun x => ?_) i
    · refine Fin.lastCases ?_ (fun y => ?_) j
      · simp [hdiag,hElast,extension]
      · rw [hsymm, hElast, hEold]
        have he : (e y).val < n := (e y).isLt
        have hn : n ≠ (e y).val := by omega
        simp [extension, hn, hbits (e y)]
    · refine Fin.lastCases ?_ (fun y => ?_) j
      · rw [hElast,hEold]
        have he : (e x).val < n := (e x).isLt
        have hn : (e x).val ≠ n := by omega
        simp [extension, hn, hbits (e x)]
      · rw [hEold,hEold,hr]
        by_cases h : (e x).val = (e y).val
        · simp [extension,edge,h]
        · simp [extension,h,(e x).isLt,(e y).isLt]
  refine ⟨s,E.trans p,fun i j => ?_⟩
  rw [Realize, hp]
  rfl

theorem covers0 : Covers 0 R0 := zero_covers R0 (by decide)
theorem covers1 : Covers 1 R1 := extend_covers 0 R0 R1 covers0 rows0
theorem covers2 : Covers 2 R2 := extend_covers 1 R1 R2 covers1 rows1
theorem covers3 : Covers 3 R3 := extend_covers 2 R2 R3 covers2 rows2
theorem covers4 : Covers 4 R4 := extend_covers 3 R3 R4 covers3 rows3
theorem covers5 : Covers 5 R5 := extend_covers 4 R4 R5 covers4 rows4
theorem covers6 : Covers 6 R6 := extend_covers 5 R5 R6 covers5 rows5
theorem covers7 : Covers 7 R7 := extend_covers 6 R6 R7 covers6 rows6
#print axioms SpectralRank.CoverageData.covers6
#print axioms SpectralRank.CoverageData.covers7
end SpectralRank.CoverageData
