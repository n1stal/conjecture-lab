module

public import Palomar.FourTerminalSeparators.Support.FourSeparatorGraph
public import Palomar.FourTerminalSeparators.Support.FourCeilingArithmetic

@[expose] public section

namespace HakKozerenkoSeparatorGraph
open TriameterQ3Graph HakKozerenkoFourSeparator
universe u
variable {V : Type u} {G : SimpleGraph V} {T : V → Prop}

theorem terminalRoute_endpoint (M : ShortestDistances G) {s t : V} {n : Nat}
    (R : TerminalRoute M T s t n) : T t := by
  cases R with
  | start h => exact h
  | add _ h => exact h

/-- At four terminals a cheap complete-terminal walk always implies at
least one of the five canonical distinct-terminal routes is cheap.
The proof uses a small potential on the three vertices other than t;
it does not assume a graph path is already simple. -/
theorem fixed_pair_short_route_four (M : ShortestDistances G) (s t u v : V)
    (hs : T s) (ht : T t)
    (only : ∀ x, T x → x=s ∨ x=t ∨ x=u ∨ x=v)
    (st : s≠t) (su : s≠u) (sv : s≠v) (tu : t≠u) (tv : t≠v) (uv : u≠v)
    (c : Nat) (cap : PackingCap G T c) :
    ShortRoute c (M.dist s t) (M.dist u v)
      (M.dist s u) (M.dist v t) (M.dist s v) (M.dist u t) := by
  classical
  by_cases want : ShortRoute c (M.dist s t) (M.dist u v)
      (M.dist s u) (M.dist v t) (M.dist s v) (M.dist u t)
  · exact want
  · exfalso
    let w (x y : V) := M.dist x y-1
    have dpos {x y : V} (h : x≠y) : 0<M.dist x y := by
      apply Nat.pos_of_ne_zero
      exact fun hz => h ((M.dist_eq_zero_iff x y).mp hz)
    have S1 : c+1≤w s t := by
      have H : ¬ M.dist s t≤c+1 := fun h => want (Or.inl h)
      dsimp [w]
      omega
    have S2 : c+1≤w s u+w u t := by
      have H : ¬ M.dist s u+M.dist u t≤c+2 := fun h => want (Or.inr (Or.inl h))
      dsimp [w]
      have p := dpos su
      have q := dpos tu.symm
      omega
    have S3 : c+1≤w s v+w v t := by
      have H : ¬ M.dist s v+M.dist v t≤c+2 := fun h => want (Or.inr (Or.inr (Or.inl h)))
      dsimp [w]
      have p := dpos sv
      have q := dpos tv.symm
      omega
    have S4 : c+1≤w s u+w u v+w v t := by
      have H : ¬ M.dist s u+M.dist u v+M.dist v t≤c+3 :=
        fun h => want (Or.inr (Or.inr (Or.inr (Or.inl h))))
      dsimp [w]
      have p := dpos su
      have q := dpos uv
      have r := dpos tv.symm
      omega
    have S5 : c+1≤w s v+w v u+w u t := by
      have H : ¬ M.dist s v+M.dist u v+M.dist u t≤c+3 :=
        fun h => want (Or.inr (Or.inr (Or.inr (Or.inr h))))
      dsimp [w]
      rw [M.dist_symm v u]
      have p := dpos sv
      have q := dpos uv
      have r := dpos tu.symm
      omega
    let A := min (w s u) (w s v+w v u)
    let B := min (w s v) (w s u+w u v)
    have A₀ : A≤w s u := Nat.min_le_left _ _
    have B₀ : B≤w s v := Nat.min_le_left _ _
    have AB : B≤A+w u v := by
      dsimp only [A]
      by_cases h : w s u≤w s v+w v u
      · rw [Nat.min_eq_left h]
        exact Nat.min_le_right _ _
      · rw [Nat.min_eq_right (by omega : w s v+w v u≤w s u)]
        omega
    have BA : A≤B+w v u := by
      dsimp only [B]
      by_cases h : w s v≤w s u+w u v
      · rw [Nat.min_eq_left h]
        exact Nat.min_le_right _ _
      · rw [Nat.min_eq_right (by omega : w s u+w u v≤w s v)]
        omega
    have AT : c+1≤A+w u t := by
      dsimp only [A]
      by_cases h : w s u≤w s v+w v u
      · rwa [Nat.min_eq_left h]
      · rwa [Nat.min_eq_right (by omega : w s v+w v u≤w s u)]
    have BT : c+1≤B+w v t := by
      dsimp only [B]
      by_cases h : w s v≤w s u+w u v
      · rwa [Nat.min_eq_left h]
      · rwa [Nat.min_eq_right (by omega : w s u+w u v≤w s v)]
    let f (x : V) := if x=s then 0 else if x=u then A else if x=v then B else c+1
    have f_s : f s=0 := by simp [f]
    have f_t : f t=c+1 := by simp [f,st.symm,tu,tv]
    have f_u : f u=A := by simp [f,su.symm]
    have f_v : f v=B := by simp [f,sv.symm,uv.symm]
    have one (x y : V) (hx : T x) (hy : T y) (hxt : x≠t) :
        f y ≤ f x+w x y := by
      rcases only x hx with h₁|h₁|h₁|h₁
      · subst x
        rcases only y hy with h₂|h₂|h₂|h₂ <;> subst y
        · rw [f_s]; omega
        · rw [f_t,f_s]; omega
        · rw [f_u,f_s]; omega
        · rw [f_v,f_s]; omega
      · exact (hxt h₁).elim
      · subst x
        rcases only y hy with h₂|h₂|h₂|h₂ <;> subst y
        · rw [f_s,f_u]; omega
        · rw [f_t,f_u]; exact AT
        · rw [f_u]; omega
        · rw [f_v,f_u]; exact AB
      · subst x
        rcases only y hy with h₂|h₂|h₂|h₂ <;> subst y
        · rw [f_s,f_v]; omega
        · rw [f_t,f_v]; exact BT
        · rw [f_u,f_v]; exact BA
        · rw [f_v]; omega
    have track (x : V) (q : Nat) (P : TerminalRoute M T s x q) :
        c+1≤q ∨ f x≤q := by
      induction P with
      | start _ => exact Or.inr (by rw [f_s]; omega)
      | @add x y q path hy ih =>
        change c+1≤q+w x y ∨ f y≤q+w x y
        rcases ih with h|h
        · exact Or.inl (by omega)
        · by_cases e : x=t
          · rw [e,f_t] at h
            exact Or.inl (by omega)
          · exact Or.inr (Nat.le_trans (one x y (terminalRoute_endpoint M path) hy e)
              (Nat.add_le_add_right h _))
    obtain ⟨q,P,hq⟩ := terminal_route_of_cap M T s t hs ht c cap
    rcases track t q P with h|h
    · omega
    · rw [f_t] at h
      omega

end HakKozerenkoSeparatorGraph

#print axioms HakKozerenkoSeparatorGraph.fixed_pair_short_route_four
