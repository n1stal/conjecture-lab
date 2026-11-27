module

public import Proofs.VanCottZhang
public import Proofs.CoinSeven.Bridge
public import Proofs.CoinSeven.OnePoint
public import Proofs.CoinSeven.Obstruction

@[expose] public section

set_option maxHeartbeats 4000000
set_option autoImplicit false

namespace CoinOrder

open Bridge

theorem fits_orderly_pair {D : List Nat} {m x y : Nat} (h1 : 1 ∈ D)
    (hx : x ∈ m::D) (hy : y ∈ m::D) (hm : m ≤ x+y) (h2 : x+y < m+m)
    (good : ¬ Bad (m::D) (x+y)) :
    x+y-m = 0 ∨ x+y-m ∈ D := by
  have hR : Represents (m::D) (x+y) [x,y] :=
    ⟨by intro z hz; simp at hz; rcases hz with h | h <;> simp [h, hx,hy], by simp⟩
  have hh := Nat.le_of_not_gt (fun hlt => good ⟨[x,y],hR,hlt⟩)
  change greedyCount (m::D) (x+y) ≤ 2 at hh
  rw [greedy_count_first hm h2] at hh
  exact count_le_one_iff h1 (by omega)

theorem three_gap {a b : Nat} (ha : 1 < a) (hb : a < b)
    (h3 : Orderly [b,a,1]) : 2*a-1 ≤ b := by
  apply Nat.le_of_not_gt
  intro h
  have hm : b≤a+a := by omega
  have h2 : a+a < b+b := by omega
  have hr : a+a-b < a := by omega
  have hR : Represents [b,a,1] (a+a) [a,a] :=
    ⟨by intro z hz; simp at hz; simp [hz], by simp⟩
  have hh := (h3 (a+a)).2 [a,a] hR
  rw [greedy_length, greedy_count_first hm h2, greedy_count_drop hr] at hh
  simp only [greedyCount, Nat.div_one, Nat.add_zero,List.length_cons,List.length_nil] at hh
  omega

theorem no_sorted_seven
    {a b c d e f : Nat} (ha : 1 < a) (hb : a < b) (hc : b < c)
    (hd : c < d) (he : d < e) (hf : e < f)
    (good3 : Orderly [b,a,1])
    (bad4 : ¬ Orderly [c,b,a,1])
    (bad5 : ¬ Orderly [d,c,b,a,1])
    (bad6 : ¬ Orderly [e,d,c,b,a,1])
    (good7 : Orderly [f,e,d,c,b,a,1]) : False := by
  classical
  have hbD {C : List Nat} (h1 : 1∈C) (bad : ¬ Orderly C) : ∃ v, Bad C v := by
    by_cases h : ∃ v, Bad C v
    · exact h
    · exact False.elim (bad (orderly_of_not_bad h1 (fun v hv => h ⟨v,hv⟩)))
  have tight : ∀ v < e, ¬ Bad [e,d,c,b,a,1] v := by
    intro v hv hn
    have hw := (bad_subset_drop_head (m:=f) (by omega : v<f)).mp hn
    exact not_bad_of_orderly good7 v hw
  obtain ⟨u,hu,v,hv,huv,hn⟩ := compact_cai ha hb hc hd he tight
    (hbD (by simp) bad5) (hbD (by simp) bad6)
  have ub : u≤d := by simp at hu; rcases hu with h|h|h|h|h <;> omega
  have vb : v≤d := by simp at hv; rcases hv with h|h|h|h|h <;> omega
  have hu' : u ∈ [a,b,c,d] := by
    simp at hu ⊢
    rcases hu with h|h|h|h|h
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · omega
  have hv' : v ∈ [a,b,c,d] := by
    simp at hv ⊢
    rcases hv with h|h|h|h|h
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · omega
  let A : Int := a
  let B : Int := b
  let C : Int := c
  let D : Int := d
  let E : Int := e
  let F : Int := f
  have small : C ≤ 2*B → ¬ Coin7Arithmetic.fitsFour A B C (2*B) := by
    intro hi hx
    have hi' : c≤2*b := by dsimp [B,C] at hi; omega
    simp only [Coin7Arithmetic.fitsFour] at hx
    dsimp [A,B,C] at hx
    have hrs : 2*b=c ∨ 2*b=c+1 ∨ 2*b=c+a := by
      rcases hx with h | h | h | h | h
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr (by omega))
      · omega
      · omega
    exact bad4 (four_orderly_of_residue a b c ha hb hc hi' good3 hrs)
  have gap : B-A ≥ A-1 := by
    dsimp [A,B]
    have hh := three_gap ha hb good3
    omega
  have six : ∀ X ∈ [A,B,C,D], ∀ Y ∈ [A,B,C,D], E≤X+Y → X+Y<F →
      Coin7Arithmetic.fitsSix A B C D E (X+Y) := by
    have nat6 (x y : Nat) (hx : x∈[a,b,c,d]) (hy : y∈[a,b,c,d])
        (hlo : e≤x+y) (hhi : x+y<f) :
        Coin7Arithmetic.fitsSix A B C D E ((x:Int)+(y:Int)) := by
      have hx' : x ∈ [e,d,c,b,a,1] := by
        simp at hx ⊢; rcases hx with h|h|h|h <;> simp [h]
      have hy' : y ∈ [e,d,c,b,a,1] := by
        simp at hy ⊢; rcases hy with h|h|h|h <;> simp [h]
      have h2 : x+y<e+e := by
        have hi : x≤d := by simp at hx; rcases hx with h|h|h|h <;> omega
        have hj : y≤d := by simp at hy; rcases hy with h|h|h|h <;> omega
        omega
      have hh : ¬ Bad [e,d,c,b,a,1] (x+y) := by
        intro hb
        exact not_bad_of_orderly good7 (x+y) ((bad_subset_drop_head hhi).mp hb)
      have hz := fits_orderly_pair (by simp : 1 ∈ [d,c,b,a,1]) hx' hy' hlo h2 hh
      simp only [Coin7Arithmetic.fitsSix]
      dsimp [A,B,C,D,E]
      have hm : e+(x+y-e)=x+y := by omega
      rcases hz with h | h
      · exact Or.inl (by omega)
      · simp at h
        rcases h with h | h | h | h | h
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
        · exact Or.inr (Or.inr (Or.inl (by omega)))
        · exact Or.inr (Or.inl (by omega))
    intro X hX Y hY hlow hhigh
    simp at hX hY
    rcases hX with hh|hh|hh|hh <;> subst X <;>
      rcases hY with hh|hh|hh|hh <;> subst Y
    all_goals
      apply nat6 _ _ (by simp) (by simp)
      all_goals dsimp [A,B,C,D,E,F] at *; omega
  have seven : ∀ X ∈ [A,B,C,D,E], ∀ Y ∈ [A,B,C,D,E], F≤X+Y →
      Coin7Arithmetic.fitsSeven A B C D E F (X+Y) := by
    have nat7 (x y : Nat) (hx : x∈[a,b,c,d,e]) (hy : y∈[a,b,c,d,e])
        (hlo : f≤x+y) :
        Coin7Arithmetic.fitsSeven A B C D E F ((x:Int)+(y:Int)) := by
      have hx' : x ∈ [f,e,d,c,b,a,1] := by
        simp at hx ⊢; rcases hx with h|h|h|h|h <;> simp [h]
      have hy' : y ∈ [f,e,d,c,b,a,1] := by
        simp at hy ⊢; rcases hy with h|h|h|h|h <;> simp [h]
      have h2 : x+y<f+f := by
        have hi : x≤e := by simp at hx; rcases hx with h|h|h|h|h <;> omega
        have hj : y≤e := by simp at hy; rcases hy with h|h|h|h|h <;> omega
        omega
      have hh := not_bad_of_orderly good7 (x+y)
      have hz := fits_orderly_pair (by simp : 1 ∈ [e,d,c,b,a,1]) hx' hy' hlo h2 hh
      simp only [Coin7Arithmetic.fitsSeven]
      dsimp [A,B,C,D,E,F]
      have hm : f+(x+y-f)=x+y := by omega
      rcases hz with h | h
      · exact Or.inl (by omega)
      · simp at h
        rcases h with h | h | h | h | h | h
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
        · exact Or.inr (Or.inr (Or.inl (by omega)))
        · exact Or.inr (Or.inl (by omega))
    intro X hX Y hY hlow
    simp at hX hY
    rcases hX with hh|hh|hh|hh|hh <;> subst X <;>
      rcases hY with hh|hh|hh|hh|hh <;> subst Y
    all_goals
      apply nat7 _ _ (by simp) (by simp)
      dsimp [A,B,C,D,E,F] at *
      omega
  have uIn : (u:Int) ∈ [A,B,C,D] := by
    simp at hu' ⊢
    dsimp [A,B,C,D]
    rcases hu' with h|h|h|h <;> simp [h]
  have vIn : (v:Int) ∈ [A,B,C,D] := by
    simp at hv' ⊢
    dsimp [A,B,C,D]
    rcases hv' with h|h|h|h <;> simp [h]
  have hn' : ¬ Coin7Arithmetic.fitsSix A B C D E ((u:Int)+(v:Int)) := by
    intro hh
    have huD : u≤d := by simp at hu'; rcases hu' with h|h|h|h <;> omega
    have hvD : v≤d := by simp at hv'; rcases hv' with h|h|h|h <;> omega
    simp only [Coin7Arithmetic.fitsSix] at hh
    dsimp [A,B,C,D,E] at hh
    apply hn
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    rcases hh with h|h|h|h|h|h|h
    · omega
    · exact Or.inr (Or.inr (Or.inr (Or.inr (by omega))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
    · exact Or.inr (Or.inr (Or.inl (by omega)))
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inl (by omega)
    · omega
  have wit : ∃ X ∈ [A,B,C,D], ∃ Y ∈ [A,B,C,D], X≤Y ∧ E<X+Y ∧
      ¬ Coin7Arithmetic.fitsSix A B C D E (X+Y) := by
    by_cases h : u≤v
    · exact ⟨(u:Int),uIn,(v:Int),vIn,by omega,by dsimp [E]; omega,hn'⟩
    · exact ⟨(v:Int),vIn,(u:Int),uIn,by omega,by dsimp [E]; omega,by simpa only [Int.add_comm] using hn'⟩
  exact Coin7Arithmetic.obstruction A B C D E F
    (by dsimp [A]; omega) (by dsimp [A,B]; omega) (by dsimp [B,C]; omega)
    (by dsimp [C,D]; omega) (by dsimp [D,E]; omega) (by dsimp [E,F]; omega)
    small gap six seven wit

#print axioms no_sorted_seven


/-- The separate seven-denomination assertion in Van Cott--Zhang
    Conjecture 5.2(1), in the paper's increasing list order. -/
theorem vanCottZhang_no_seven
    {C : List Nat} (len : C.length = 7) (first : C.head? = some 1)
    (strict : C.Pairwise (· < ·))
    (initial : ∀ i, 1 ≤ i → i ≤ 3 → Orderly (coinPrefix C i))
    (middle : ∀ i, 4 ≤ i → i < C.length → ¬ Orderly (coinPrefix C i))
    (full : Orderly C.reverse) : False := by
  cases C with
  | nil => simp at len
  | cons o t1 =>
    cases t1 with
    | nil => simp at len
    | cons a t2 =>
      cases t2 with
      | nil => simp at len
      | cons b t3 =>
        cases t3 with
        | nil => simp at len
        | cons c t4 =>
          cases t4 with
          | nil => simp at len
          | cons d t5 =>
            cases t5 with
            | nil => simp at len
            | cons e t6 =>
              cases t6 with
              | nil => simp at len
              | cons f t7 =>
                cases t7 with
                | cons g t => simp at len
                | nil =>
                  have ho : o=1 := by simpa only [List.head?_cons,Option.some.injEq] using first
                  subst o
                  have ord : 1<a ∧ a<b ∧ b<c ∧ c<d ∧ d<e ∧ e<f := by
                    simp only [List.pairwise_cons,List.mem_cons,List.not_mem_nil,or_false] at strict
                    obtain ⟨h1,h2,h3,h4,h5,h6⟩ := strict
                    exact ⟨h1 _ (Or.inl rfl),h2 _ (Or.inl rfl),h3 _ (Or.inl rfl),h4 _ (Or.inl rfl),h5 _ (Or.inl rfl),h6.1 _ rfl⟩
                  obtain ⟨ha,hb,hc,hd,he,hf⟩ := ord
                  exact no_sorted_seven ha hb hc hd he hf
                    (initial 3 (by decide) (by decide))
                    (middle 4 (by decide) (by simp))
                    (middle 5 (by decide) (by simp))
                    (middle 6 (by decide) (by simp)) full

#print axioms vanCottZhang_no_seven
end CoinOrder
