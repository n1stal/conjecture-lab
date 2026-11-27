module

public import Palomar.FourTerminalSeparators.Support.FourSeparatorGraph

@[expose] public section

namespace HakKozerenkoSeparatorGraph
open TriameterQ3Graph
universe u
variable {V : Type u} {G : SimpleGraph V} {T : V → Prop}

structure SupportedFamily (G : SimpleGraph V) (T : V → Prop) (n : Nat) (P : V → Prop) where
  family : VertexFamily G T n
  in_support : ∀ i v, family.part i v → P v

/-- Concatenation of supported families requires these two supports to
avoid each other, not their component separators individually. -/
def joinFamily {n m : Nat} {P Q : V → Prop}
    (F : SupportedFamily G T n P) (H : SupportedFamily G T m Q)
    (disj : ∀ v, P v → Q v → False) :
    SupportedFamily G T (n+m) (fun v => P v ∨ Q v) := by
  let f : Fin (n+m) → V → Prop := Fin.addCases F.family.part H.family.part
  have fl (i : Fin n) : f (Fin.castAdd m i) = F.family.part i := Fin.addCases_left i
  have fr (i : Fin m) : f (Fin.natAdd n i) = H.family.part i := Fin.addCases_right i
  refine ⟨⟨f,?_,?_⟩,?_⟩
  · intro i
    induction i using Fin.addCases with
    | left i => simpa only [fl] using F.family.each i
    | right i => simpa only [fr] using H.family.each i
  · intro i
    induction i using Fin.addCases with
    | left i =>
      intro j
      induction j using Fin.addCases with
      | left j =>
        intro ne v hi hj
        rw [fl] at hi hj
        exact F.family.disjoint i j (fun h => ne (congrArg (Fin.castAdd m) h)) v hi hj
      | right j =>
        intro _ v hi hj
        rw [fl] at hi
        rw [fr] at hj
        exact disj v (F.in_support i v hi) (H.in_support j v hj)
    | right i =>
      intro j
      induction j using Fin.addCases with
      | left j =>
        intro _ v hi hj
        rw [fr] at hi
        rw [fl] at hj
        exact disj v (F.in_support j v hj) (H.in_support i v hi)
      | right j =>
        intro ne v hi hj
        rw [fr] at hi hj
        exact H.family.disjoint i j (fun h => ne (congrArg (Fin.natAdd n) h)) v hi hj
  · intro i
    induction i using Fin.addCases with
    | left i =>
      intro v hv
      change f (Fin.castAdd m i) v at hv
      rw [fl] at hv
      exact Or.inl (F.in_support i v hv)
    | right i =>
      intro v hv
      change f (Fin.natAdd n i) v at hv
      rw [fr] at hv
      exact Or.inr (H.in_support i v hv)

theorem unit_dist (M : ShortestDistances G) {x y : V} (edge : G.adj x y) :
    M.dist x y ≤ 1 := M.minimal x y 1 (unitWalk edge)

theorem distance_step (M : ShortestDistances G) (a : V) {x y : V} (edge : G.adj x y) :
    M.dist a y ≤ M.dist a x+1 := by
  have h₀ := M.dist_triangle a x y
  have h₁ := unit_dist M edge
  omega

theorem separates_of_lip_level (f : V → Nat)
    (growth : ∀ x y, G.adj x y → f y ≤ f x+1) (a b : V)
    (j : Nat) (before : f a < j) (beyond : j≤f b) :
    Separates G (fun v => f v=j) a b := by
  intro n W
  let F := fun i => f (W.point i)
  have H0 : F 0<j := by simpa only [F,W.first] using before
  have HN : j≤F n := by simpa only [F,W.last] using beyond
  obtain ⟨i,hi,hev,_⟩ := hit_weighted_layer F (fun _ => 1) n j H0 HN
    (fun i hi => growth _ _ (W.step i hi)) (fun _ => Nat.le_refl 1)
  exact ⟨i+1,by omega,hev⟩

def distanceRings (M : ShortestDistances G) (a b : V) (r : Nat)
    (ha : T a) (hb : T b) (far : r < M.dist a b)
    (nont : ∀ v, T v → v=a ∨ r<M.dist a v) :
    SupportedFamily G T r (fun v => M.dist a v ≤ r) := by
  let f : Fin r → V → Prop := fun i v => M.dist a v=(i.val+1)
  refine ⟨⟨f,?_,?_⟩,?_⟩
  · intro i
    have hi := i.isLt
    refine ⟨?_,a,b,ha,hb,?_⟩
    · intro v h hv
      change M.dist a v=i.val+1 at h
      rcases nont v hv with he|hf
      · subst v
        rw [M.dist_self] at h
        omega
      · omega
    · exact separates_of_lip_level (M.dist a) (fun _ _ h => distance_step M a h)
        a b _ (by rw [M.dist_self]; omega) (by omega)
  · intro i j ne v hi hj
    apply ne
    apply Fin.ext
    change M.dist a v=i.val+1 at hi
    change M.dist a v=j.val+1 at hj
    omega
  · intro i v hi
    change M.dist a v=i.val+1 at hi
    have bnd := i.isLt
    omega

theorem ball_disjoint (M : ShortestDistances G) (x y : V) (r s : Nat)
    (far : r+s<M.dist x y) (v : V) (hx : M.dist x v≤r) (hy : M.dist y v≤s) : False := by
  have H := M.dist_triangle x v y
  rw [M.dist_symm v y] at H
  omega

def pairDistance (M : ShortestDistances G) (a b v : V) : Nat :=
  min (M.dist a v) (M.dist b v)

theorem pair_distance_step (M : ShortestDistances G) (a b : V)
    {x y : V} (edge : G.adj x y) :
    pairDistance M a b y ≤ pairDistance M a b x+1 := by
  unfold pairDistance
  have ha := distance_step M a edge
  have hb := distance_step M b edge
  by_cases H : M.dist a x≤M.dist b x
  · rw [Nat.min_eq_left H]
    exact Nat.le_trans (Nat.min_le_left _ _) ha
  · have H' : M.dist b x≤M.dist a x := by omega
    rw [Nat.min_eq_right H']
    exact Nat.le_trans (Nat.min_le_right _ _) hb

/-- The group layers from one terminal pair toward the other.  Their
support is strictly beyond the first two balls and strictly before the
second two balls. -/
def groupRings (M : ShortestDistances G) (a b c d : V) (r bound q : Nat)
    (ha : T a) (hc : T c)
    (only : ∀ v, T v → v=a ∨ v=b ∨ v=c ∨ v=d)
    (cross : bound≤M.dist a c ∧ bound≤M.dist b c ∧ bound≤M.dist a d ∧ bound≤M.dist b d)
    (fits : 2*r+q<bound) :
    SupportedFamily G T q
      (fun v => r<pairDistance M a b v ∧ pairDistance M a b v+r<bound) := by
  let f : Fin q → V → Prop := fun i v => pairDistance M a b v=(r+1+i.val)
  have h_a : pairDistance M a b a = 0 := by simp [pairDistance,M.dist_self]
  have h_b : pairDistance M a b b = 0 := by simp [pairDistance,M.dist_self]
  have h_c : bound≤pairDistance M a b c := Nat.le_min.mpr ⟨cross.1,cross.2.1⟩
  have h_d : bound≤pairDistance M a b d := Nat.le_min.mpr ⟨cross.2.2.1,cross.2.2.2⟩
  refine ⟨⟨f,?_,?_⟩,?_⟩
  · intro i
    have hi := i.isLt
    refine ⟨?_,a,c,ha,hc,?_⟩
    · intro v hh ht
      change pairDistance M a b v=r+1+i.val at hh
      rcases only v ht with e|e|e|e <;> subst v <;> omega
    · exact separates_of_lip_level (pairDistance M a b)
        (fun _ _ h => pair_distance_step M a b h) a c _
        (by rw [h_a]; omega) (by omega)
  · intro i j ne v hi hj
    apply ne
    apply Fin.ext
    change pairDistance M a b v=r+1+i.val at hi
    change pairDistance M a b v=r+1+j.val at hj
    omega
  · intro i v hi
    change pairDistance M a b v=r+1+i.val at hi
    have H := i.isLt
    exact ⟨by omega,by omega⟩

theorem group_disjoint_second_ball (M : ShortestDistances G) (a b c : V) (r bound : Nat)
    (h₁ : bound≤M.dist a c) (h₂ : bound≤M.dist b c)
    (v : V) (hc : M.dist c v≤r) (hg : pairDistance M a b v+r<bound) : False := by
  have hA := M.dist_triangle a v c
  have hB := M.dist_triangle b v c
  rw [M.dist_symm v c] at hA hB
  unfold pairDistance at hg
  by_cases h : M.dist a v≤M.dist b v
  · rw [Nat.min_eq_left h] at hg
    omega
  · have h' : M.dist b v≤M.dist a v := by omega
    rw [Nat.min_eq_right h'] at hg
    omega

/-- Actual graph proof of the four ball plus group layer count.
The six lower bounds on distance ensure the four balls are disjoint;
the group bound only involves the four cross pairs. -/
theorem four_ball_group_packing (M : ShortestDistances G) (a b c d : V)
    (ha : T a) (hb : T b) (hc : T c) (hd : T d)
    (only : ∀ v, T v → v=a ∨ v=b ∨ v=c ∨ v=d)
    (r bound q : Nat)
    (ab : 2*r<M.dist a b) (cd : 2*r<M.dist c d)
    (cross : bound≤M.dist a c ∧ bound≤M.dist b c ∧ bound≤M.dist a d ∧ bound≤M.dist b d)
    (fits : 2*r+q<bound) :
    Nonempty (VertexFamily G T (r+r+(r+r)+q)) := by
  have ac : 2*r<M.dist a c := by have h := cross.1; omega
  have bc : 2*r<M.dist b c := by have h := cross.2.1; omega
  have ad : 2*r<M.dist a d := by have h := cross.2.2.1; omega
  have bd : 2*r<M.dist b d := by have h := cross.2.2.2; omega
  have ab' : 2*r<M.dist b a := by rw [M.dist_symm]; exact ab
  have ac' : 2*r<M.dist c a := by rw [M.dist_symm]; exact ac
  have ad' : 2*r<M.dist d a := by rw [M.dist_symm]; exact ad
  have bc' : 2*r<M.dist c b := by rw [M.dist_symm]; exact bc
  have bd' : 2*r<M.dist d b := by rw [M.dist_symm]; exact bd
  have cd' : 2*r<M.dist d c := by rw [M.dist_symm]; exact cd
  have othA (v : V) (hv : T v) : v=a ∨ r<M.dist a v := by
    rcases only v hv with e|e|e|e <;> subst v
    · exact Or.inl rfl
    all_goals exact Or.inr (by omega)
  have othB (v : V) (hv : T v) : v=b ∨ r<M.dist b v := by
    rcases only v hv with e|e|e|e <;> subst v
    · exact Or.inr (by omega)
    · exact Or.inl rfl
    all_goals exact Or.inr (by omega)
  have othC (v : V) (hv : T v) : v=c ∨ r<M.dist c v := by
    rcases only v hv with e|e|e|e <;> subst v
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inl rfl
    · exact Or.inr (by omega)
  have othD (v : V) (hv : T v) : v=d ∨ r<M.dist d v := by
    rcases only v hv with e|e|e|e <;> subst v
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inl rfl
  let fa := distanceRings M a b r ha hb (by omega) othA
  let fb := distanceRings M b a r hb ha (by omega) othB
  let fc := distanceRings M c d r hc hd (by omega) othC
  let fd := distanceRings M d c r hd hc (by omega) othD
  let A := joinFamily fa fb (ball_disjoint M a b r r (by omega))
  let B := joinFamily fc fd (ball_disjoint M c d r r (by omega))
  let F := joinFamily A B (fun v hl hr => by
    rcases hl with hL|hL <;> rcases hr with hR|hR
    · exact ball_disjoint M a c r r (by omega) v hL hR
    · exact ball_disjoint M a d r r (by omega) v hL hR
    · exact ball_disjoint M b c r r (by omega) v hL hR
    · exact ball_disjoint M b d r r (by omega) v hL hR)
  let Q := groupRings M a b c d r bound q ha hc only cross fits
  let Z := joinFamily F Q (fun v hx hy => by
    rcases hx with (hA|hB)|(hC|hD)
    · have g := Nat.min_le_left (M.dist a v) (M.dist b v)
      change min (M.dist a v) (M.dist b v) ≤ M.dist a v at g
      have gy := hy.1
      unfold pairDistance at gy
      omega
    · have g := Nat.min_le_right (M.dist a v) (M.dist b v)
      have gy := hy.1
      unfold pairDistance at gy
      omega
    · exact group_disjoint_second_ball M a b c r bound cross.1 cross.2.1 v hC hy.2
    · exact group_disjoint_second_ball M a b d r bound cross.2.2.1 cross.2.2.2 v hD hy.2)
  exact ⟨Z.family⟩

theorem four_ball_group_cap (M : ShortestDistances G) (a b c d : V)
    (ha : T a) (hb : T b) (hc : T c) (hd : T d)
    (only : ∀ v, T v → v=a ∨ v=b ∨ v=c ∨ v=d)
    (amin bound cmax : Nat) (pos : 0<amin) (ord : amin≤bound)
    (ab : amin≤M.dist a b) (cd : amin≤M.dist c d)
    (cross : bound≤M.dist a c ∧ bound≤M.dist b c ∧ bound≤M.dist a d ∧ bound≤M.dist b d)
    (cap : PackingCap G T cmax) :
    amin+bound≤cmax+3 := by
  let r := (amin-1)/2
  let q := bound-2*r-1
  have ha' : 2*r<amin := by dsimp [r]; omega
  have hr : amin≤2*r+2 := by dsimp [r]; omega
  have hf : 2*r+q<bound := by dsimp [q]; omega
  obtain ⟨F⟩ := four_ball_group_packing M a b c d ha hb hc hd only r bound q (by omega) (by omega) cross hf
  have H := cap _ F
  dsimp [q] at H
  omega

end HakKozerenkoSeparatorGraph

#print axioms HakKozerenkoSeparatorGraph.four_ball_group_packing
#print axioms HakKozerenkoSeparatorGraph.four_ball_group_cap
