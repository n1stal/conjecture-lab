module

public import Std
public import Lean.Elab.Tactic.Omega
public import Lean.Elab.Tactic.RCases

@[expose] public section

/-! Exact edge-table statement of the 11-vertex counterexample. -/
namespace StrongArboricityCore

abbrev V := Fin 11
abbrev E := Fin 19
abbrev Color := Fin 3

def edgeArray : Array (V × V) :=
  #[(0,1),(0,2),(1,2),(0,3),(1,3),(0,4),(1,4),
    (2,5),(3,5),(2,6),(3,6),(2,7),(4,7),(2,8),(4,8),(3,9),(4,9),(3,10),(4,10)]

theorem edgeArray_size : edgeArray.size = 19 := by decide

def ends (e : E) : V × V := edgeArray[e.val]'e.isLt

def On (e : E) (u v : V) : Prop := ends e = (u,v) ∨ ends e = (v,u)

instance (e : E) (u v : V) : Decidable (On e u v) := by
  unfold On
  infer_instance

theorem On.flip {e : E} {u v : V} (h : On e u v) : On e v u := by
  cases h with
  | inl h => exact Or.inr h
  | inr h => exact Or.inl h

/-- A path with ordered vertex and edge witnesses. No graph library needed. -/
inductive EdgePath : List V → List E → Prop
  | one (u : V) : EdgePath [u] []
  | step {u v : V} {vs : List V} {e : E} {es : List E} :
      On e u v → EdgePath (v::vs) es → EdgePath (u::v::vs) (e::es)

/-- A simple path of length at least two, with a closing edge, is exactly a
broken simple cycle. Palette function has one value for each actual edge. -/
def Strong (f : E → Color) : Prop :=
  ∀ (vs : List V) (es : List E), EdgePath vs es → vs.Nodup →
    2 ≤ es.length → (∃ (u v : V) (e : E),
      vs.head? = some u ∧ vs.getLast? = some v ∧ On e u v) →
    ∀ c : Color, (∀ e ∈ es, f e = c) → False

/-- For this increasing simple edge table, one earlier neighbor is counted
once per pair whose second endpoint is this vertex. -/
def backDegree (v : V) : Nat :=
  (edgeArray.toList.filter fun e => decide (e.2=v)).length

/-- Printed conjecture 3 fails: displayed order bounds the coloring
number by 3, yet no strongly woody coloring with 3 colors exists. -/
def Counterexample : Prop :=
  (edgeArray.toList.map fun p => (p.1.val,p.2.val)).Nodup ∧
  (edgeArray.toList.all fun p => decide (p.1.val<p.2.val)) = true ∧
  (∀ v : V, backDegree v ≤ 2) ∧
  ¬ ∃ f : E → Color, Strong f

private theorem no2 {f : E → Color} (h : Strong f)
    {e₁ e₂ e₃ : E} {a b c : V} (h₁ : On e₁ a b) (h₂ : On e₂ b c)
    (h₃ : On e₃ a c) (hn : ([a,b,c] : List V).Nodup)
    (he : f e₁ = f e₂) : False := by
  apply h [a,b,c] [e₁,e₂] (.step h₁ (.step h₂ (.one c))) hn (by change 2 ≤ 2; omega)
    ⟨a,c,e₃,rfl,rfl,h₃⟩ (f e₂)
  intro v hv
  simp at hv
  rcases hv with hv | hv
  · rw [hv]; exact he
  · rw [hv]

private theorem no3 {f : E → Color} (h : Strong f)
    {e₁ e₂ e₃ e₄ : E} {a b c d : V} (h₁ : On e₁ a b) (h₂ : On e₂ b c)
    (h₃ : On e₃ c d) (h₄ : On e₄ a d) (hn : ([a,b,c,d] : List V).Nodup)
    {k : Color} (c₁ : f e₁=k) (c₂ : f e₂=k) (c₃ : f e₃=k) : False := by
  apply h [a,b,c,d] [e₁,e₂,e₃] (.step h₁ (.step h₂ (.step h₃ (.one d)))) hn (by change 2 ≤ 3; omega)
    ⟨a,d,e₄,rfl,rfl,h₄⟩ k
  intro v hv
  simp at hv
  rcases hv with hv | hv | hv
  · rw [hv]; exact c₁
  · rw [hv]; exact c₂
  · rw [hv]; exact c₃

private theorem finval_ne {n : Nat} {a b : Fin n} (h : a ≠ b) : a.val ≠ b.val :=
  fun e => h (Fin.ext e)

private theorem unique_third (a b c d : Color)
    (hab : a≠b) (hca : c≠a) (hcb : c≠b) (hda : d≠a) (hdb : d≠b) : d=c := by
  apply Fin.ext
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  have hd := d.isLt
  have e₁ := finval_ne hab
  have e₂ := finval_ne hca
  have e₃ := finval_ne hcb
  have e₄ := finval_ne hda
  have e₅ := finval_ne hdb
  omega

private theorem repeat_three (c a₁ a₂ a₃ : Color)
    (h₁ : a₁≠c) (h₂ : a₂≠c) (h₃ : a₃≠c) :
    a₁=a₂ ∨ a₁=a₃ ∨ a₂=a₃ := by
  by_cases e₁ : a₁=a₂
  · exact Or.inl e₁
  · by_cases e₂ : a₁=a₃
    · exact Or.inr (Or.inl e₂)
    · apply Or.inr
      apply Or.inr
      apply Fin.ext
      have v₁ := a₁.isLt
      have v₂ := a₂.isLt
      have v₃ := a₃.isLt
      have vc := c.isLt
      have n₁ := finval_ne h₁
      have n₂ := finval_ne h₂
      have n₃ := finval_ne h₃
      have n₄ := finval_ne e₁
      have n₅ := finval_ne e₂
      omega

private theorem rainbow {f : E → Color} (h : Strong f) {u : V} {a b : E}
    (ha : On a 0 u) (hb : On b 1 u)
    (hn₁ : ([u,0,1] : List V).Nodup) (hn₂ : ([u,1,0] : List V).Nodup)
    (hn₃ : ([0,u,1] : List V).Nodup) :
    f a≠f 0 ∧ f b≠f 0 ∧ f a≠f b := by
  have h0 : On 0 0 1 := by decide
  exact ⟨no2 h ha.flip h0 hb.flip hn₁,
    no2 h hb.flip h0.flip ha.flip hn₂, no2 h ha hb.flip h0 hn₃⟩

private theorem twins {f : E → Color} (h : Strong f)
    {a b c d zu zv wu wv : E} {u v z w : V}
    (ua : On a 0 u) (ub : On b 1 u) (vc : On c 0 v) (vd : On d 1 v)
    (ezu : On zu z u) (ezv : On zv z v) (ewu : On wu w u) (ewv : On wv w v)
    (n1 : ([w,u,0,v] : List V).Nodup) (n2 : ([w,u,1,v] : List V).Nodup)
    (n3 : ([z,u,0,v] : List V).Nodup) (n4 : ([z,u,1,v] : List V).Nodup)
    (n5 : ([z,v,0,u] : List V).Nodup) (n6 : ([z,v,1,u] : List V).Nodup)
    (n7 : ([w,u,z,v] : List V).Nodup)
    (pa : f a=f c) (pb : f b=f d) (pab : f a≠f b) : False := by
  have wA : f wu≠f a := fun e => no3 h ewu ua.flip vc ewv n1 e rfl pa.symm
  have wB : f wu≠f b := fun e => no3 h ewu ub.flip vd ewv n2 e rfl pb.symm
  have zuA : f zu≠f a := fun e => no3 h ezu ua.flip vc ezv n3 e rfl pa.symm
  have zuB : f zu≠f b := fun e => no3 h ezu ub.flip vd ezv n4 e rfl pb.symm
  have zvA : f zv≠f a := fun e => no3 h ezv vc.flip ua ezu n5 e pa.symm rfl
  have zvB : f zv≠f b := fun e => no3 h ezv vd.flip ub ezu n6 e pb.symm rfl
  exact no3 h ewu ezu.flip ezv ewv n7 rfl
    (unique_third _ _ _ _ pab wA wB zuA zuB) (unique_third _ _ _ _ pab wA wB zvA zvB)

theorem no_three (f : E → Color) (h : Strong f) : False := by
  have p2 := rainbow h (u:=2) (a:=1) (b:=2) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have p3 := rainbow h (u:=3) (a:=3) (b:=4) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have p4 := rainbow h (u:=4) (a:=5) (b:=6) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  rcases repeat_three (f 0) (f 1) (f 3) (f 5) p2.1 p3.1 p4.1 with h1 | h2 | h3
  · have hb : f 2=f 4 := by
      apply unique_third (f 0) (f 1) (f 4) (f 2) p2.1.symm p3.2.1
        _ p2.2.1 p2.2.2.symm
      rw [h1]; exact p3.2.2.symm
    exact twins h (a:=1) (b:=2) (c:=3) (d:=4) (zu:=7) (zv:=8) (wu:=9) (wv:=10)
      (u:=2) (v:=3) (z:=5) (w:=6)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) h1 hb p2.2.2
  · have hb : f 2=f 6 := by
      apply unique_third (f 0) (f 1) (f 6) (f 2) p2.1.symm p4.2.1
        _ p2.2.1 p2.2.2.symm
      rw [h2]; exact p4.2.2.symm
    exact twins h (a:=1) (b:=2) (c:=5) (d:=6) (zu:=11) (zv:=12) (wu:=13) (wv:=14)
      (u:=2) (v:=4) (z:=7) (w:=8)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) h2 hb p2.2.2
  · have hb : f 4=f 6 := by
      apply unique_third (f 0) (f 3) (f 6) (f 4) p3.1.symm p4.2.1
        _ p3.2.1 p3.2.2.symm
      rw [h3]; exact p4.2.2.symm
    exact twins h (a:=3) (b:=4) (c:=5) (d:=6) (zu:=15) (zv:=16) (wu:=17) (wv:=18)
      (u:=3) (v:=4) (z:=9) (w:=10)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) h3 hb p3.2.2

theorem forward_unique_loopless :
    (edgeArray.toList.map fun p => (p.1.val,p.2.val)).Nodup ∧
      (edgeArray.toList.all fun p => decide (p.1.val<p.2.val)) = true := by decide

theorem rejection : ¬ ∃ f : E → Color, Strong f := by
  intro h
  obtain ⟨f,hf⟩ := h
  exact no_three f hf

theorem every_back_degree : ∀ v : V, backDegree v ≤ 2 := by
  intro v
  have hv := v.isLt
  have h : v=0 ∨ v=1 ∨ v=2 ∨ v=3 ∨ v=4 ∨ v=5 ∨ v=6 ∨ v=7 ∨ v=8 ∨ v=9 ∨ v=10 := by
    have he : v.val=0 ∨ v.val=1 ∨ v.val=2 ∨ v.val=3 ∨ v.val=4 ∨ v.val=5 ∨
        v.val=6 ∨ v.val=7 ∨ v.val=8 ∨ v.val=9 ∨ v.val=10 := by omega
    rcases he with he|he|he|he|he|he|he|he|he|he|he
    · exact Or.inl (Fin.ext he)
    · exact Or.inr (Or.inl (Fin.ext he))
    · exact Or.inr (Or.inr (Or.inl (Fin.ext he)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext he))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext he)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext he))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext he)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext he))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext he)))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext he))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext he))))))))))
  rcases h with h|h|h|h|h|h|h|h|h|h|h <;> (rw [h]; decide)

theorem strong_arboricity_coloring_number_counterexample : Counterexample := by
  exact ⟨forward_unique_loopless.1, forward_unique_loopless.2, every_back_degree, rejection⟩

#print axioms strong_arboricity_coloring_number_counterexample

end StrongArboricityCore
