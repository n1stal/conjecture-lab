module

public import Palomar.FourTerminalSeparators.Support.FourBallGroup

@[expose] public section

/-! Here Lemma 6.1 of Hak–Kozerenko is proved directly from disjoint balls
rather than relying on an imported projection or an unverified assumption. -/
namespace HakKozerenkoSeparatorGraph
open TriameterQ3Graph
universe u
variable {V : Type u} {G : SimpleGraph V} {T : V → Prop}

def markThree (a b c v : V) : Prop := v=a ∨ v=b ∨ v=c
def markFour (a b c d v : V) : Prop := v=a ∨ v=b ∨ v=c ∨ v=d

def singletonSupported {S : V → Prop} (sep : TSeparator G T S) :
    SupportedFamily G T 1 S where
  family := ⟨fun _ => S,fun _ => sep,fun i j ne _ _ _ => ne (Fin.ext (by
    have a := i.isLt
    have b := j.isLt
    omega))⟩
  in_support := fun _ _ h => h

def takeFamily {m n : Nat} (F : VertexFamily G T m) (hle : n≤m) : VertexFamily G T n where
  part := fun i => F.part (Fin.castLE hle i)
  each := fun i => F.each (Fin.castLE hle i)
  disjoint := fun i j ne v hi hj =>
    F.disjoint (Fin.castLE hle i) (Fin.castLE hle j) (fun h => ne (Fin.ext (congrArg (fun z : Fin m => z.val) h))) v hi hj

def three_ball_rings (M : ShortestDistances G) (a b c : V) (r s t : Nat)
    (ab : r+s<M.dist a b) (ac : r+t<M.dist a c) (bc : s+t<M.dist b c) :
    SupportedFamily G (markThree a b c) (r+s+t)
      (fun v => (M.dist a v≤r ∨ M.dist b v≤s) ∨ M.dist c v≤t) := by
  have ba : s+r<M.dist b a := by rw [M.dist_symm]; omega
  have ca : t+r<M.dist c a := by rw [M.dist_symm]; omega
  have cb : t+s<M.dist c b := by rw [M.dist_symm]; omega
  have A : markThree a b c a := Or.inl rfl
  have B : markThree a b c b := Or.inr (Or.inl rfl)
  have C : markThree a b c c := Or.inr (Or.inr rfl)
  have offA (v : V) (hv : markThree a b c v) : v=a ∨ r<M.dist a v := by
    rcases hv with h|h|h <;> subst v
    · exact Or.inl rfl
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have offB (v : V) (hv : markThree a b c v) : v=b ∨ s<M.dist b v := by
    rcases hv with h|h|h <;> subst v
    · exact Or.inr (by omega)
    · exact Or.inl rfl
    · exact Or.inr (by omega)
  have offC (v : V) (hv : markThree a b c v) : v=c ∨ t<M.dist c v := by
    rcases hv with h|h|h <;> subst v
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inl rfl
  let FA := distanceRings M a b r A B (by omega) offA
  let FB := distanceRings M b a s B A (by omega) offB
  let FC := distanceRings M c a t C A (by omega) offC
  let FAB := joinFamily FA FB (ball_disjoint M a b r s ab)
  exact joinFamily FAB FC (fun z h hz => by
    rcases h with h|h
    · exact ball_disjoint M a c r t ac z h hz
    · exact ball_disjoint M b c s t bc z h hz)

theorem separated_balls_have_no_edge (M : ShortestDistances G) (a b : V) (r s : Nat)
    (far : r+s+1<M.dist a b) {x y : V}
    (hx : M.dist a x≤r) (hy : M.dist b y≤s) (E : G.adj x y) : False := by
  have h1 := M.dist_triangle a x b
  have h2 := M.dist_triangle x y b
  have h3 := unit_dist M E
  rw [M.dist_symm y b] at h2
  omega

/-- The even-perimeter central separator: there is no edge between any
two of the three smaller terminal balls. -/
theorem three_ball_center (M : ShortestDistances G) (a b c : V) (r s t : Nat)
    (ab : r+s+1<M.dist a b) (ac : r+t+1<M.dist a c) (_bc : s+t+1<M.dist b c) :
    TSeparator G (markThree a b c)
      (fun v => ¬ ((M.dist a v≤r ∨ M.dist b v≤s) ∨ M.dist c v≤t)) := by
  classical
  refine ⟨?_, a,b,Or.inl rfl,Or.inr (Or.inl rfl),?_⟩
  · intro v hz hT
    apply hz
    rcases hT with h|h|h <;> subst v
    · exact Or.inl (Or.inl (by simp [M.dist_self]))
    · exact Or.inl (Or.inr (by simp [M.dist_self]))
    · exact Or.inr (by simp [M.dist_self])
  · intro n W
    by_cases hit : ∃ i, i≤n ∧ ¬ ((M.dist a (W.point i)≤r ∨ M.dist b (W.point i)≤s) ∨
          M.dist c (W.point i)≤t)
    · exact hit
    · exfalso
      have all (i : Nat) (hi : i≤n) : M.dist a (W.point i)≤r := by
        induction i with
        | zero => rw [W.first,M.dist_self]; exact Nat.zero_le _
        | succ i ih =>
          have here := ih (by omega)
          have edge := W.step i (by omega)
          have there : (M.dist a (W.point (i+1))≤r ∨ M.dist b (W.point (i+1))≤s) ∨
              M.dist c (W.point (i+1))≤t := by
            by_cases h : (M.dist a (W.point (i+1))≤r ∨ M.dist b (W.point (i+1))≤s) ∨
                M.dist c (W.point (i+1))≤t
            · exact h
            · exact (hit ⟨i+1,hi,h⟩).elim
          rcases there with (h|h)|h
          · exact h
          · exact (separated_balls_have_no_edge M a b r s ab here h edge).elim
          · exact (separated_balls_have_no_edge M a c r t ac here h edge).elim
      have endB := all n (Nat.le_refl n)
      rw [W.last] at endB
      omega

/-- Exact number of disjoint separators supplied by Hak–Kozerenko's
Lemma 6.1, by an independent ball proof. -/
theorem triple_separator_family (M : ShortestDistances G) (a b c : V)
    (ha : a≠b) (hb : a≠c) (hc : b≠c) :
    Nonempty (VertexFamily G (markThree a b c)
      ((M.dist a b+M.dist a c+M.dist b c-3)/2)) := by
  let x := M.dist a b
  let y := M.dist a c
  let z := M.dist b c
  have xp : 0<x := Nat.pos_of_ne_zero (fun h => ha ((M.dist_eq_zero_iff a b).mp h))
  have yp : 0<y := Nat.pos_of_ne_zero (fun h => hb ((M.dist_eq_zero_iff a c).mp h))
  have zp : 0<z := Nat.pos_of_ne_zero (fun h => hc ((M.dist_eq_zero_iff b c).mp h))
  have xt : x≤y+z := by
    have h := M.dist_triangle a c b
    rw [M.dist_symm c b] at h
    exact h
  have yt : y≤x+z := M.dist_triangle a b c
  have zt : z≤x+y := by
    have h := M.dist_triangle b a c
    rw [M.dist_symm b a] at h
    exact h
  let l := (x+y-z)/2
  let m := (x+z-y)/2
  let n := (y+z-x)/2
  change Nonempty (VertexFamily G (markThree a b c) ((x+y+z-3)/2))
  by_cases parity : (x+y+z)%2=0
  · have hx : x=l+m := by dsimp [l,m]; omega
    have hy : y=l+n := by dsimp [l,n]; omega
    have hz : z=m+n := by dsimp [m,n]; omega
    let r := l-1
    let s := m-1
    let t := n-1
    have ab : r+s<M.dist a b := by change r+s<x; dsimp [r,s]; omega
    have ac : r+t<M.dist a c := by change r+t<y; dsimp [r,t]; omega
    have bc : s+t<M.dist b c := by change s+t<z; dsimp [s,t]; omega
    let F := three_ball_rings M a b c r s t ab ac bc
    by_cases hp : 0<l ∧ 0<m ∧ 0<n
    · have ab' : r+s+1<M.dist a b := by
        change r+s+1<x
        dsimp [r,s]
        omega
      have ac' : r+t+1<M.dist a c := by
        change r+t+1<y
        dsimp [r,t]
        omega
      have bc' : s+t+1<M.dist b c := by
        change s+t+1<z
        dsimp [s,t]
        omega
      let Z := singletonSupported (three_ball_center M a b c r s t ab' ac' bc')
      let FW := joinFamily F Z (fun _ h nc => nc h)
      have enough : (x+y+z-3)/2 ≤ r+s+t+1 := by dsimp [r,s,t]; omega
      exact ⟨takeFamily FW.family enough⟩
    · have enough : (x+y+z-3)/2 ≤ r+s+t := by dsimp [r,s,t]; omega
      exact ⟨takeFamily F.family enough⟩
  · have hx : x=l+m+1 := by dsimp [l,m]; omega
    have hy : y=l+n+1 := by dsimp [l,n]; omega
    have hz : z=m+n+1 := by dsimp [m,n]; omega
    let F := three_ball_rings M a b c l m n
      (by change l+m<x; omega) (by change l+n<y; omega) (by change m+n<z; omega)
    have enough : (x+y+z-3)/2 ≤ l+m+n := by omega
    exact ⟨takeFamily F.family enough⟩

/-- Remove the single index bad, leaving a canonically indexed subfamily. -/
def skipIndex {q : Nat} (bad : Fin q) (i : Fin (q-1)) : Fin q :=
  if i.val<bad.val then ⟨i.val,by have h:=i.isLt; omega⟩
  else ⟨i.val+1,by have h:=i.isLt; omega⟩

theorem skipIndex_ne {q : Nat} (bad : Fin q) (i : Fin (q-1)) :
    skipIndex bad i≠bad := by
  intro e
  have ev := congrArg (fun z : Fin q => z.val) e
  by_cases h : i.val<bad.val <;> simp [skipIndex,h] at ev <;> omega

theorem skipIndex_injective {q : Nat} (bad : Fin q) :
    Function.Injective (skipIndex bad) := by
  intro i j e
  have ev := congrArg (fun z : Fin q => z.val) e
  apply Fin.ext
  by_cases h : i.val<bad.val <;> by_cases h' : j.val<bad.val <;>
    simp [skipIndex,h,h'] at ev <;> omega

def pullFamily {q n : Nat} (F : VertexFamily G T q) (f : Fin n→Fin q)
    (hf : Function.Injective f) : VertexFamily G T n where
  part := fun i => F.part (f i)
  each := fun i => F.each (f i)
  disjoint := fun _ _ ne v hv hw =>
    F.disjoint _ _ (fun h => ne (hf h)) v hv hw

def widenByTerminal {q : Nat} (F : VertexFamily G T q) (w : V)
    (away : ∀ i, ¬F.part i w) : VertexFamily G (fun v => T v ∨ v=w) q where
  part := F.part
  each := by
    intro i
    obtain ⟨avoid,a,b,ha,hb,meet⟩ := F.each i
    refine ⟨?_,a,b,Or.inl ha,Or.inl hb,meet⟩
    intro v hv hu
    rcases hu with hu|eq
    · exact avoid v hv hu
    · subst v
      exact away i hv
  disjoint := F.disjoint

/-- Disjointness lets one discard the only separator that might contain
one new terminal. -/
theorem widening_loses_at_most_one {q : Nat} (F : VertexFamily G T q) (w : V)
    (c : Nat) (cap : PackingCap G (fun v => T v ∨ v=w) c) : q≤c+1 := by
  classical
  by_cases has : ∃ i, F.part i w
  · obtain ⟨bad,marks⟩ := has
    let R := pullFamily F (skipIndex bad) (skipIndex_injective bad)
    have miss : ∀ i, ¬R.part i w := by
      intro i hi
      exact F.disjoint _ bad (skipIndex_ne bad i) w hi marks
    have h := cap _ (widenByTerminal R w miss)
    omega
  · have h := cap _ (widenByTerminal F w (fun i hi => has ⟨i,hi⟩))
    omega

theorem triple_perimeter_cap (M : ShortestDistances G) (a b c d : V)
    (ab : a≠b) (ac : a≠c) (bc : b≠c) (limit : Nat)
    (cap : PackingCap G (markFour a b c d) limit) :
    M.dist a b+M.dist a c+M.dist b c≤2*limit+6 := by
  obtain ⟨F⟩ := triple_separator_family M a b c ab ac bc
  have cap' : PackingCap G (fun v => markThree a b c v ∨ v=d) limit := by
    have eq : (fun v => markThree a b c v ∨ v=d) = markFour a b c d := by
      funext v
      apply propext
      simp [markThree,markFour,or_assoc]
    rwa [eq]
  have h := widening_loses_at_most_one F d limit cap'
  omega

end HakKozerenkoSeparatorGraph

#print axioms HakKozerenkoSeparatorGraph.three_ball_center
#print axioms HakKozerenkoSeparatorGraph.triple_separator_family
#print axioms HakKozerenkoSeparatorGraph.triple_perimeter_cap
