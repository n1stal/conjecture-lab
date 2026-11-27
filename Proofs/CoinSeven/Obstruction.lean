module

public import Proofs.CoinSeven.Arithmetic

@[expose] public section

set_option maxHeartbeats 2000000
set_option autoImplicit false
namespace Coin7Arithmetic

def fitsFour (a b c s : Int) : Prop :=
  (s = (c + 0)) ∨ (s = (c + 1)) ∨ (s = (c + a)) ∨ (s = (c + b)) ∨ (s = (c + c))

def fitsSix (a b c d e s : Int) : Prop :=
  (s = (e + 0)) ∨ (s = (e + 1)) ∨ (s = (e + a)) ∨ (s = (e + b)) ∨ (s = (e + c)) ∨ (s = (e + d)) ∨ (s = (e + e))

def fitsSeven (a b c d e f s : Int) : Prop :=
  (s = (f + 0)) ∨ (s = (f + 1)) ∨ (s = (f + a)) ∨ (s = (f + b)) ∨ (s = (f + c)) ∨ (s = (f + d)) ∨ (s = (f + e)) ∨ (s = (f + f))

theorem obstruction (a b c d e f : Int)
    (o0 : 1 < a) (o1 : a < b) (o2 : b < c) (o3 : c < d) (o4 : d < e) (o5 : e < f)
    (smallBad : c ≤ 2*b → ¬ fitsFour a b c (2*b))
    (gap : b-a ≥ a-1)
    (fitsWhenSix : ∀ x ∈ [a,b,c,d], ∀ y ∈ [a,b,c,d], e ≤ x+y → x+y < f → fitsSix a b c d e (x+y))
    (fitsWhenSeven : ∀ x ∈ [a,b,c,d,e], ∀ y ∈ [a,b,c,d,e], f ≤ x+y → fitsSeven a b c d e f (x+y))
    (witness : ∃ x ∈ [a,b,c,d], ∃ y ∈ [a,b,c,d], x ≤ y ∧ e < x+y ∧ ¬ fitsSix a b c d e (x+y)) : False := by
  obtain ⟨x,hx,y,hy,hxy,hex,hn⟩ := witness
  have hf : f ≤ x+y := by
    by_cases h : f ≤ x+y
    · exact h
    exact False.elim (hn (fitsWhenSix x hx y hy (by omega) (by omega)))
  have hSix (x y : Int) (hx : x ∈ [a,b,c,d]) (hy : y ∈ [a,b,c,d]) :
      x+y < e ∨ f ≤ x+y ∨ fitsSix a b c d e (x+y) := by
    by_cases h : x+y < e
    · exact Or.inl h
    by_cases h2 : f ≤ x+y
    · exact Or.inr (Or.inl h2)
    exact Or.inr (Or.inr (fitsWhenSix x hx y hy (by omega) (by omega)))
  have hSeven (x y : Int) (hx : x ∈ [a,b,c,d,e]) (hy : y ∈ [a,b,c,d,e]) :
      x+y < f ∨ fitsSeven a b c d e f (x+y) := by
    by_cases h : x+y < f
    · exact Or.inl h
    exact Or.inr (fitsWhenSeven x hx y hy (by omega))
  have h0 := hSix b b (by simp) (by simp)
  have h1 := hSeven b b (by simp) (by simp)
  have h2 := hSix b c (by simp) (by simp)
  have h3 := hSeven b c (by simp) (by simp)
  have h4 := hSix b d (by simp) (by simp)
  have h5 := hSeven b d (by simp) (by simp)
  have h6 := hSeven b e (by simp) (by simp)
  have h7 := hSix c c (by simp) (by simp)
  have h8 := hSeven c c (by simp) (by simp)
  have h9 := hSix c d (by simp) (by simp)
  have h10 := hSeven c d (by simp) (by simp)
  have h11 := hSeven c e (by simp) (by simp)
  have h12 := hSix d d (by simp) (by simp)
  have h13 := hSeven d d (by simp) (by simp)
  have h14 := hSeven d e (by simp) (by simp)
  have h15 := hSeven e e (by simp) (by simp)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx hy
  rcases hx with hx | hx | hx | hx <;> subst x <;> rcases hy with hy | hy | hy | hy <;> subst y
  · by_cases hp : c ≤ 2*b
    · exact small0 a b c d e f o0 o1 o2 o3 o4 o5 hp (smallBad hp) gap hf hn 
    · exact large0 a b c d e f o0 o1 o2 o3 o4 o5 (by omega) hf hn 
  · by_cases hp : c ≤ 2*b
    · exact small1 a b c d e f o0 o1 o2 o3 o4 o5 hp (smallBad hp) gap hf hn h10 h13 h14
    · exact large1 a b c d e f o0 o1 o2 o3 o4 o5 (by omega) hf hn 
  · by_cases hp : c ≤ 2*b
    · exact small2 a b c d e f o0 o1 o2 o3 o4 o5 hp (smallBad hp) gap hf hn h10 h13 h14
    · exact large2 a b c d e f o0 o1 o2 o3 o4 o5 (by omega) hf hn h13 h14
  · by_cases hp : c ≤ 2*b
    · exact small3 a b c d e f o0 o1 o2 o3 o4 o5 hp (smallBad hp) gap hf hn h10 h13 h14 h15
    · exact large3 a b c d e f o0 o1 o2 o3 o4 o5 (by omega) hf hn h13 h14
  · omega
  · by_cases hp : c ≤ 2*b
    · exact small4 a b c d e f o0 o1 o2 o3 o4 o5 hp (smallBad hp) gap hf hn h10 h13 h14
    · exact large4 a b c d e f o0 o1 o2 o3 o4 o5 (by omega) hf hn 
  · by_cases hp : c ≤ 2*b
    · exact small5 a b c d e f o0 o1 o2 o3 o4 o5 hp (smallBad hp) gap hf hn h10 h13 h14 h15
    · exact large5 a b c d e f o0 o1 o2 o3 o4 o5 (by omega) hf hn h13 h14
  · by_cases hp : c ≤ 2*b
    · exact small6 a b c d e f o0 o1 o2 o3 o4 o5 hp (smallBad hp) gap hf hn h10 h13 h14 h15
    · exact large6 a b c d e f o0 o1 o2 o3 o4 o5 (by omega) hf hn h13 h14
  · omega
  · omega
  · by_cases hp : c ≤ 2*b
    · exact small7 a b c d e f o0 o1 o2 o3 o4 o5 hp (smallBad hp) gap hf hn h10 h11 h14
    · exact large7 a b c d e f o0 o1 o2 o3 o4 o5 (by omega) hf hn h13 h14 h15
  · by_cases hp : c ≤ 2*b
    · exact small8 a b c d e f o0 o1 o2 o3 o4 o5 hp (smallBad hp) gap hf hn h11 h14 h15
    · exact large8 a b c d e f o0 o1 o2 o3 o4 o5 (by omega) hf hn h7 h13 h14 h15
  · omega
  · omega
  · omega
  · by_cases hp : c ≤ 2*b
    · exact small9 a b c d e f o0 o1 o2 o3 o4 o5 hp (smallBad hp) gap hf hn h4 h9 h11 h13 h14 h15
    · exact large9 a b c d e f o0 o1 o2 o3 o4 o5 (by omega) hf hn h9 h11 h13 h14 h15

#print axioms obstruction

end Coin7Arithmetic
