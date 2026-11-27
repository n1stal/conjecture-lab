module

public import Proofs.VanCottZhang

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 4096

namespace CoinOrder
namespace Bridge

def Bad (C : List Nat) (v : Nat) : Prop :=
  ∃ R, Represents C v R ∧ R.length < greedyCount C v

def LeastBad (C : List Nat) (v : Nat) : Prop :=
  Bad C v ∧ ∀ w < v, ¬ Bad C w

theorem least_exists {P : Nat → Prop} (h : ∃ n, P n) :
    ∃ n, P n ∧ ∀ m < n, ¬ P m := by
  obtain ⟨n, hn⟩ := h
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : ∃ m, m < n ∧ P m
    · obtain ⟨m, hm, hmp⟩ := h
      exact ih m hm hmp
    · exact ⟨n, hn, fun m hm hmp => h ⟨m, hm, hmp⟩⟩

theorem max_exists {P : Nat → Prop} (w : ∃ n, P n)
    (B : Nat) (hB : ∀ n, P n → n ≤ B) :
    ∃ n, P n ∧ ∀ m, P m → m ≤ n := by
  obtain ⟨k, hk, hmin⟩ :=
    least_exists (P := fun k => ∃ n, P n ∧ B - n = k)
      (by obtain ⟨n, hn⟩ := w; exact ⟨B-n, n, hn, rfl⟩)
  obtain ⟨n, hn, hkn⟩ := hk
  refine ⟨n, hn, ?_⟩
  intro m hm
  apply Nat.le_of_not_gt
  intro hnm
  have hnB := hB n hn
  have hmB := hB m hm
  exact hmin (B-m) (by omega) ⟨m, hm, rfl⟩

theorem all_mem_greedy (C : List Nat) (v : Nat) :
    ∀ z ∈ greedyCoins C v, z ∈ C := by
  induction C generalizing v with
  | nil => simp [greedyCoins]
  | cons d ds ih =>
    intro z hz
    rw [greedyCoins, List.mem_append] at hz
    rcases hz with hm | hm
    · have : z=d := (List.mem_replicate.mp hm).2
      subst z; simp
    · exact List.mem_cons_of_mem _ (ih _ z hm)

theorem greedy_nil_zero (C : List Nat) : greedyCoins C 0 = [] := by
  induction C with
  | nil => rfl
  | cons d ds ih => simp [greedyCoins, ih]

theorem rep_greedy (C : List Nat) (v : Nat) (h1 : 1 ∈ C) :
    Represents C v (greedyCoins C v) := by
  refine ⟨all_mem_greedy C v, ?_⟩
  induction C generalizing v with
  | nil => simp at h1
  | cons d ds ih =>
    have hrep (n : Nat) : (List.replicate n d).sum = n*d := by
      induction n with
      | zero => simp
      | succ n ih => simp [List.replicate_succ, ih, Nat.succ_mul, Nat.add_comm]
    simp only [greedyCoins, List.sum_append, hrep]
    have htail : (greedyCoins ds (v % d)).sum = v % d := by
      rcases List.mem_cons.mp h1 with hd | hs
      · rw [← hd, Nat.mod_one, greedy_nil_zero]; rfl
      · exact ih _ hs
    rw [htail, Nat.mul_comm (v / d) d, Nat.add_comm]
    exact Nat.mod_add_div v d

theorem rep_erase {C R : List Nat} {v z : Nat} (rep : Represents C v R)
    (hz : z ∈ R) : Represents C (v-z) (R.erase z) := by
  refine ⟨fun a ha => rep.1 a (List.mem_of_mem_erase ha), ?_⟩
  have erase_sum (L : List Nat) (h : z ∈ L) : (L.erase z).sum + z = L.sum := by
    induction L with
    | nil => simp at h
    | cons a L ih =>
      rcases List.mem_cons.mp h with he | hm
      · subst a; rw [List.erase_cons_head,List.sum_cons]; omega
      · by_cases ha : a = z
        · subst a; rw [List.erase_cons_head,List.sum_cons]; omega
        · rw [List.erase_cons_tail (by simpa using ha)]
          simp only [List.sum_cons]
          have h := ih hm
          omega
  have hh := erase_sum R hz
  have hrep := rep.2
  omega

theorem val_ge_mem {C R : List Nat} {v z : Nat} (rep : Represents C v R)
    (hz : z ∈ R) : z ≤ v := by
  have h := (List.mem_iff_append.mp hz)
  obtain ⟨xs, ys, hxy⟩ := h
  have hh := rep.2
  rw [hxy, List.sum_append, List.sum_cons] at hh
  omega

theorem rep_cons {C R : List Nat} {v z : Nat} (rep : Represents C v R)
    (hz : z ∈ C) : Represents C (z+v) (z::R) := by
  refine ⟨?_, by simp [List.sum_cons, rep.2]⟩
  intro a ha
  rcases List.mem_cons.mp ha with ha | ha
  · simpa [ha] using hz
  · exact rep.1 a ha

theorem count_remove_top {m v : Nat} {C : List Nat} (hm : 0 < m) (hv : m ≤ v) :
    greedyCount (m::C) v = greedyCount (m::C) (v-m) + 1 := by
  have h := greedy_period m C hm (v-m) 1
  rw [Nat.mul_one] at h
  have : v-m+m = v := by omega
  simpa only [this] using h

theorem bad_subset_drop_head {m v : Nat} {C : List Nat} (hlt : v < m) :
    Bad C v ↔ Bad (m::C) v := by
  have he : greedyCount (m::C) v = greedyCount C v := by
    simp [greedyCount, Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt]
  constructor
  · rintro ⟨R, hR, hs⟩
    refine ⟨R, ⟨fun z hz => List.mem_cons_of_mem _ (hR.1 z hz), hR.2⟩, ?_⟩
    omega
  · rintro ⟨R, hR, hs⟩
    refine ⟨R, ⟨?_, hR.2⟩, ?_⟩
    · intro z hz
      rcases List.mem_cons.mp (hR.1 z hz) with h | h
      · have := val_ge_mem hR hz
        omega
      · exact h
    · omega

theorem short_cannot_contain_top {m v : Nat} {C R : List Nat} (mpos : 0 < m)
    (least : LeastBad (m::C) v) (rep : Represents (m::C) v R)
    (short : R.length < greedyCount (m::C) v) : m ∉ R := by
  intro hm
  have hv := val_ge_mem rep hm
  have he := count_remove_top (C:=C) mpos hv
  have hr := rep_erase rep hm
  have hl := List.length_erase_of_mem hm
  have hpos : R.length > 0 := by
    cases R with
    | nil => simp at hm
    | cons _ _ => simp
  exact least.2 (v-m) (by omega) ⟨R.erase m, hr, by omega⟩

theorem orderly_of_not_bad {C : List Nat} (h1 : 1 ∈ C) (h : ∀ v, ¬ Bad C v) :
    Orderly C := by
  intro v
  refine ⟨rep_greedy C v h1, ?_⟩
  intro R hr
  rw [greedy_length]
  exact Nat.le_of_not_gt (fun hh => h v ⟨R, hr, hh⟩)

theorem not_bad_of_orderly {C : List Nat} (h : Orderly C) (v : Nat) :
    ¬ Bad C v := by
  rintro ⟨R, hr, hl⟩
  have hh := (h v).2 R hr
  rw [greedy_length] at hh
  omega

theorem largest_short_value {m v : Nat} {C : List Nat} (_mpos : 0 < m) (_hm : 1 ∈ m::C)
    (least : LeastBad (m::C) v) (hmax : ∀ z ∈ C, z < m)
    (_hpos : ∀ z ∈ C, 0 < z) :
    ∃ s R, s ∈ R ∧ Represents (m::C) v R ∧ R.length < greedyCount (m::C) v ∧
      ∀ L, Represents (m::C) v L → L.length < greedyCount (m::C) v → ∀ z ∈ L, z ≤ s := by
  let P := fun s : Nat => ∃ R, s ∈ R ∧ Represents (m::C) v R ∧ R.length < greedyCount (m::C) v
  have hP : ∃ s, P s := by
    obtain ⟨R, hR, hs⟩ := least.1
    cases R with
    | nil =>
      have hv : v=0 := by simpa using hR.2.symm
      have hz := greedy_nil_zero (m::C)
      rw [← greedy_length, hv, hz] at hs
      simp at hs
    | cons s R => exact ⟨s, s::R, by simp, hR, hs⟩
  have hB (s : Nat) (h : P s) : s ≤ m := by
    obtain ⟨R, hs, hR, ht⟩ := h
    rcases List.mem_cons.mp (hR.1 s hs) with he | he
    · omega
    · exact Nat.le_of_lt (hmax s he)
  obtain ⟨s, hs, hmax⟩ := max_exists hP m hB
  obtain ⟨R, hmR, hR, ht⟩ := hs
  exact ⟨s, R, hmR, hR, ht, fun L hL hl z hz => hmax z ⟨L, hz, hL, hl⟩⟩

theorem top_mem_greedy {m v : Nat} {D : List Nat} (mpos : 0 < m) (hv : m ≤ v) :
    m ∈ greedyCoins (m::D) v := by
  rw [greedyCoins, List.mem_append]
  exact Or.inl (List.mem_replicate.mpr ⟨Nat.ne_of_gt (Nat.div_pos hv mpos), rfl⟩)

theorem least_lt_max_sum {m p v : Nat} {D : List Nat}
    (mpos : 0 < m) (ones : 1 ∈ m::D)
    (least : LeastBad (m::D) v) (bound : ∀ z ∈ D, z ≤ p)
    (pos : ∀ z ∈ D, 0 < z) : v < m+p := by
  apply Nat.lt_of_not_ge
  intro hv
  obtain ⟨R, rep, small⟩ := least.1
  have hmR := short_cannot_contain_top mpos least rep small
  cases R with
  | nil =>
    have hsum := rep.2
    simp only [List.sum_nil] at hsum
    omega
  | cons z R =>
    have hz : z ∈ D := by
      rcases List.mem_cons.mp (rep.1 z (by simp)) with h | h
      · exact False.elim (hmR (by simp [h]))
      · exact h
    have hsum : R.sum = v-z := by
      have hh := rep.2
      simp only [List.sum_cons] at hh
      omega
    have repR : Represents (m::D) (v-z) R :=
      ⟨fun x hx => rep.1 x (by simp [hx]), hsum⟩
    have zPos := pos z hz
    have zBound := bound z hz
    have hcount : greedyCount (m::D) (v-z) ≤ R.length :=
      Nat.le_of_not_gt (fun h => least.2 (v-z) (by omega) ⟨R,repR,h⟩)
    have new := rep_cons (rep_greedy (m::D) (v-z) ones) (rep.1 z (by simp))
    have hvz : z+(v-z)=v := by omega
    rw [hvz] at new
    have hc : (z::greedyCoins (m::D) (v-z)).length < greedyCount (m::D) v := by
      rw [List.length_cons, greedy_length]
      simpa only [List.length_cons] using Nat.lt_of_le_of_lt (Nat.succ_le_succ hcount) small
    have hGr := top_mem_greedy (D:=D) mpos (v:=v-z) (by omega)
    exact short_cannot_contain_top mpos least new hc (List.mem_cons_of_mem _ hGr)

theorem greedy_count_first {m v : Nat} {D : List Nat} (hm : m ≤ v) (h2 : v < m+m) :
    greedyCount (m::D) v = 1 + greedyCount D (v-m) := by
  have hd : v/m=1 :=
    Nat.div_eq_of_lt_le (by simpa using hm) (by simpa [Nat.mul_succ, Nat.succ_mul] using h2)
  have hmod := Nat.mod_add_div v m
  rw [hd, Nat.mul_one] at hmod
  have hz : v%m=v-m := by omega
  simp [greedyCount, hd, hz]

theorem greedy_count_drop {m v : Nat} {D : List Nat} (h : v < m) :
    greedyCount (m::D) v = greedyCount D v := by
  simp [greedyCount, Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]

theorem greedy_count_zero (D : List Nat) : greedyCount D 0 = 0 := by
  rw [← greedy_length, greedy_nil_zero]
  rfl

theorem positive_count_rep {D : List Nat} {v : Nat} (one : 1 ∈ D) (hv : 0 < v) :
    0 < greedyCount D v := by
  have h := (rep_greedy D v one).2
  rw [← greedy_length]
  cases he : greedyCoins D v with
  | nil => rw [he, List.sum_nil] at h; omega
  | cons _ _ => simp

theorem count_le_one_iff {D : List Nat} {v : Nat} (one : 1 ∈ D) :
    greedyCount D v ≤ 1 → v = 0 ∨ v ∈ D := by
  intro h
  have rep := rep_greedy D v one
  rw [← greedy_length] at h
  cases he : greedyCoins D v with
  | nil =>
    have hh := rep.2
    rw [he] at hh
    simp only [List.sum_nil] at hh
    exact Or.inl hh.symm
  | cons z zs =>
    cases zs with
    | nil =>
      have hh := rep.2
      rw [he] at hh
      simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at hh
      refine Or.inr (?_)
      rw [← hh]
      exact rep.1 _ (by rw [he]; simp)
    | cons z' zs => simp [he] at h

theorem no_bad_at_top {m : Nat} {D : List Nat} (hp : 0 < m) :
    ¬ Bad (m::D) m := by
  rintro ⟨R, hR, short⟩
  have hh : greedyCount (m::D) m = 1 := by
    rw [greedy_count_first (D:=D) (Nat.le_refl m) (by omega), Nat.sub_self, greedy_count_zero]
  cases R with
  | nil =>
    have hsum := hR.2
    simp only [List.sum_nil] at hsum
    omega
  | cons _ _ => simp [hh] at short

theorem rep_lift_head {D R : List Nat} {v m : Nat} (rep : Represents D v R) :
    Represents (m::D) v R :=
  ⟨fun z hz => List.mem_cons_of_mem _ (rep.1 z hz), rep.2⟩

theorem greedy_contains_large {B : List Nat} {v t : Nat}
    (ord : B.Pairwise (fun u v => v < u)) (mem : t∈B) (hle : t≤v) (ht : 0<t) :
    ∃ w ∈ greedyCoins B v, t≤w := by
  induction B with
  | nil => simp at mem
  | cons m B ih =>
    have od := List.pairwise_cons.mp ord
    by_cases hm : m≤v
    · have htm : t≤m := by
        rcases List.mem_cons.mp mem with heq | htail
        · omega
        · exact Nat.le_of_lt (od.1 t htail)
      exact ⟨m, top_mem_greedy (by omega) hm, htm⟩
    · have hlt : v<m := by omega
      have hc : greedyCoins (m::B) v = greedyCoins B v := by
        simp [greedyCoins, Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt]
      rw [hc]
      have memB : t∈B := by
        rcases List.mem_cons.mp mem with heq | htail
        · omega
        · exact htail
      exact ih od.2 memB

theorem compact_cai
    {a b c d e : Nat} (ha : 1 < a) (hb : a < b) (hc : b < c) (hd : c < d) (he : d < e)
    (tight : ∀ v < e, ¬ Bad [e,d,c,b,a,1] v)
    (badD : ∃ v, Bad [d,c,b,a,1] v) (badE : ∃ v, Bad [e,d,c,b,a,1] v) :
    ∃ i ∈ [d,c,b,a,1], ∃ j ∈ [d,c,b,a,1], e < i+j ∧
      ¬ (i+j-e ∈ [d,c,b,a,1]) := by
  classical
  let D := [d,c,b,a,1]
  let E := e::D
  change ∃ i ∈ D, ∃ j ∈ D, e < i+j ∧ ¬ (i+j-e ∈ D)
  have hmD (z : Nat) (hz : z∈D) : z≤d := by
    simp [D] at hz; rcases hz with h|h|h|h|h <;> omega
  have hpD (z : Nat) (hz : z∈D) : 0<z := by
    simp [D] at hz; rcases hz with h|h|h|h|h <;> omega
  have oneD : 1∈D := by simp [D]
  have oneE : 1∈E := by simp [E,D]
  have dD : d∈D := by simp [D]
  have eE : e∈E := by simp [E]
  have eLt : e < d+d := by
    obtain ⟨y, hy⟩ := least_exists badD
    have hy := show LeastBad [d,c,b,a,1] y from hy
    have hh := least_lt_max_sum (m:=d) (p:=c) (by omega)
      (by simp) hy
      (by intro z hz; simp at hz; rcases hz with h|h|h|h <;> omega)
      (by intro z hz; simp at hz; rcases hz with h|h|h|h <;> omega)
    have hye : e ≤ y := by
      apply Nat.le_of_not_gt
      intro h
      exact tight y h ((bad_subset_drop_head (C:=D) h).mp hy.1)
    omega
  by_cases found : ∃ i ∈ D, ∃ j ∈ D, e < i+j ∧ ¬ (i+j-e ∈ D)
  · exact found
  exfalso
  have fit (i j : Nat) (hi : i∈D) (hj : j∈D) (hh : e < i+j) :
      i+j-e ∈ D := by
    by_cases h : i+j-e ∈ D
    · exact h
    · exact False.elim (found ⟨i,hi,j,hj,hh,h⟩)
  obtain ⟨x, least⟩ := least_exists badE
  have least := show LeastBad E x from least
  have hx : e < x := by
    apply Nat.lt_of_not_ge
    intro hh
    rcases Nat.lt_or_eq_of_le hh with hh | hh
    · exact tight x hh least.1
    · exact no_bad_at_top (D:=D) (by omega) (hh ▸ least.1)
  obtain ⟨s,R,hsR,rep,short,hbig⟩ :=
    largest_short_value (C:=D) (m:=e) (by omega) oneE least
      (fun z hz => by have := hmD z hz; omega) hpD
  have avoids (L : List Nat) (rep : Represents E x L) (short : L.length < greedyCount E x) :
      e ∉ L := short_cannot_contain_top (by omega) least rep short
  have Rbound (z : Nat) (hz : z ∈ R) : z∈D := by
    rcases List.mem_cons.mp (rep.1 z hz) with heq | hm
    · exact False.elim (avoids R rep short (heq ▸ hz))
    · exact hm
  have hsD := Rbound s hsR
  have hs := hmD s hsD
  have hxs : ∀ z ∈ R, ∀ t ∈ E, s < t → x-z < t := by
    intro z hz t ht hst
    apply Nat.lt_of_not_ge
    intro htz
    have good : greedyCount E (x-z) ≤ (R.erase z).length := by
      apply Nat.le_of_not_gt
      intro hh
      have zp := hpD z (Rbound z hz)
      have hb := val_ge_mem rep hz
      exact least.2 (x-z) (by omega) ⟨R.erase z,rep_erase rep hz,hh⟩
    have newRep := rep_cons (rep_greedy E (x-z) oneE) (rep.1 z hz)
    have hh := val_ge_mem rep hz
    have hxz : z+(x-z)=x := by omega
    rw [hxz] at newRep
    have newShort : (z::greedyCoins E (x-z)).length < greedyCount E x := by
      change R.length < greedyCount E x at short
      rw [List.length_cons, greedy_length]
      rw [List.length_erase_of_mem hz] at good
      have hn : 0 < R.length := by
        cases R with
        | nil => simp at hz
        | cons _ _ => simp
      omega
    have hdesc : E.Pairwise (fun u v => v < u) := by
      simp [E,D,List.pairwise_cons]
      omega
    have large_mem := greedy_contains_large hdesc ht htz (by omega : 0<t)
    obtain ⟨w,hw,hwge⟩ := large_mem
    have hws := hbig _ newRep newShort w (List.mem_cons_of_mem _ hw)
    omega
  let RS := R.erase s
  have repS : Represents E (x-s) RS := rep_erase rep hsR
  have hlenS : RS.length = R.length - 1 := List.length_erase_of_mem hsR
  have sx := val_ge_mem rep hsR
  have lenR : 2 ≤ R.length := by
    apply Nat.le_of_not_gt
    intro hh
    cases R with
    | nil => simp at hsR
    | cons u us =>
      cases us with
      | cons v vs => simp at hh; omega
      | nil =>
        have uD := Rbound u (by simp)
        have bu := hmD u uD
        have xx := rep.2
        simp only [List.sum_cons,List.sum_nil,Nat.add_zero] at xx
        omega
  have memRS : ∃ z, z ∈ RS := by
    apply List.exists_mem_of_ne_nil
    intro hh
    rw [hh,List.length_nil] at hlenS
    omega
  obtain ⟨z,hz⟩ := memRS
  have hzR : z∈R := List.mem_of_mem_erase hz
  have hzD := Rbound z hzR
  have zb := hmD z hzD
  let RZ := RS.erase z
  have lenZ : RZ.length+2 = R.length := by
    have hh := List.length_erase_of_mem hz
    change RZ.length = RS.length-1 at hh
    omega
  have repZ : Represents E (x-s-z) RZ := rep_erase repS hz
  have szx := val_ge_mem repS hz
  have gap_le (u v : Nat) (hv : v∈D) (hgap : ∀ w ∈ D, w≤u ∨ v≤w) :
      v-u ≤ e-d := by
    apply Nat.le_of_not_gt
    intro h
    have hlt : e < d+v := by omega
    have hin := fit d v dD hv hlt
    rcases hgap (d+v-e) hin with hlo | hhi <;> omega
  have pair_lt (hh : e ≤ s+z) : False := by
    by_cases hEq : s+z=e
    · have hnew := rep_cons repZ eE
      have hx' : e+(x-s-z)=x := by omega
      rw [hx'] at hnew
      have hsmall : (e::RZ).length < greedyCount E x := by
        change R.length < greedyCount E x at short
        rw [List.length_cons]
        omega
      exact avoids _ hnew hsmall (by simp)
    · have hlt : e < s+z := by omega
      have hw := fit s z hsD hzD hlt
      have hnew := rep_cons (rep_cons repZ (List.mem_cons_of_mem e hw)) eE
      have hx' : e+(s+z-e+(x-s-z))=x := by omega
      rw [hx'] at hnew
      have hsmall : (e::(s+z-e)::RZ).length < greedyCount E x := by
        change R.length < greedyCount E x at short
        simp only [List.length_cons]
        omega
      exact avoids _ hnew hsmall (by simp)
  have szlt : s+z<e := Nat.lt_of_not_ge pair_lt
  have lenR3 : 3 ≤ R.length := by
    apply Nat.le_of_not_gt
    intro h
    have hZ0 : RZ.length=0 := by omega
    have hZ : RZ=[] := List.eq_nil_of_length_eq_zero hZ0
    have hsum := repZ.2
    rw [hZ,List.sum_nil] at hsum
    omega
  have hsd : s=d := by
    by_cases hsd : s=d
    · exact hsd
    exfalso
    have hnext : ∃ t ∈ D, s < t ∧ t-s ≤ e-d := by
      have hh (u v : Nat) (hsu : s=u) (hv : v∈D) (huv : u<v)
          (hgap : ∀ w ∈ D, w≤u ∨ v≤w) :
          ∃ t ∈ D, s < t ∧ t-s ≤ e-d := by
        subst s
        exact ⟨v,hv,huv,gap_le u v hv hgap⟩
      simp only [D,List.mem_cons,List.not_mem_nil,or_false] at hsD
      rcases hsD with h|h|h|h|h
      · exact False.elim (hsd h)
      · apply hh c d h (by simp [D]) hd
        intro w hw; simp [D] at hw; rcases hw with h|h|h|h|h <;> omega
      · apply hh b c h (by simp [D]) hc
        intro w hw; simp [D] at hw; rcases hw with h|h|h|h|h <;> omega
      · apply hh a b h (by simp [D]) hb
        intro w hw; simp [D] at hw; rcases hw with h|h|h|h|h <;> omega
      · apply hh 1 a h (by simp [D]) ha
        intro w hw; simp [D] at hw; rcases hw with h|h|h|h|h <;> omega
    obtain ⟨t, ht, hst, hgap⟩ := hnext
    have htE : t∈E := List.mem_cons_of_mem e ht
    have zth := hxs z hzR t htE hst
    have tb := hmD t ht
    have zLarge : t < s+z := by omega
    obtain ⟨w,hw⟩ : ∃ w, w∈RZ := by
      apply List.exists_mem_of_ne_nil
      intro hnil
      rw [hnil,List.length_nil] at lenZ
      omega
    have wR : w ∈ R := List.mem_of_mem_erase (List.mem_of_mem_erase hw)
    have wle := val_ge_mem repZ hw
    have hwsmall := hxs w wR t htE hst
    omega
  let δ := x-e
  have hδz : δ < z := by
    have hh := hxs z hzR e eE (by omega)
    dsimp [δ]
    omega
  have hede : d+δ<e := by omega
  have hδe : δ<e := by omega
  have hδd : δ<d := by omega
  have hδ : e+δ=x := by dsimp [δ]; omega
  have hxd : x<e+e := by omega
  have hDd : d+δ<d+d := by omega
  have good : greedyCount E (x-d) ≤ RS.length := by
    apply Nat.le_of_not_gt
    intro hh
    have repD : Represents E (x-d) RS := by simpa only [hsd] using repS
    exact least.2 (x-d) (by omega) ⟨RS,repD,hh⟩
  have wMem : d+d-e ∈ D := fit d d dD dD (by omega)
  have hnew := rep_cons (rep_greedy E (x-d) oneE)
    (List.mem_cons_of_mem e wMem)
  have hh : d+d-e+(x-d)=d+δ := by omega
  rw [hh] at hnew
  have countDel : greedyCount D (d+δ)=1+greedyCount [c,b,a,1] δ := by
    change greedyCount (d::[c,b,a,1]) (d+δ)=1+greedyCount [c,b,a,1] δ
    rw [greedy_count_first (by omega : d≤d+δ) hDd]
    have hh : d+δ-d=δ := by omega
    rw [hh]
  have counts : greedyCount E (d+δ) = greedyCount E x := by
    change greedyCount (e::D) (d+δ) = greedyCount (e::D) x
    rw [greedy_count_drop hede,countDel,greedy_count_first (by omega : e≤x) hxd]
    change 1+greedyCount [c,b,a,1] δ = 1+greedyCount (d::[c,b,a,1]) (x-e)
    rw [greedy_count_drop hδd]
  have hnewShort : ((d+d-e)::greedyCoins E (x-d)).length < greedyCount E (d+δ) := by
    change R.length < greedyCount E x at short
    rw [counts,List.length_cons,greedy_length]
    omega
  exact tight (d+δ) hede ⟨_,hnew,hnewShort⟩

#print axioms compact_cai
end Bridge
end CoinOrder
