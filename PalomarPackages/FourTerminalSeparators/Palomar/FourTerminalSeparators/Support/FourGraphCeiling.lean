module

public import Palomar.FourTerminalSeparators.Support.ShortTerminalRoutes
public import Palomar.FourTerminalSeparators.Support.TripleSeparator

@[expose] public section

namespace HakKozerenkoSeparatorGraph
open TriameterQ3Graph HakKozerenkoFourSeparator
universe u
variable {V : Type u} {G : SimpleGraph V}

structure FourApart (a b c d : V) : Prop where
  ab : a≠b
  ac : a≠c
  ad : a≠d
  bc : b≠c
  bd : b≠d
  cd : c≠d

def fourSum (M : ShortestDistances G) (a b c d : V) : Nat :=
  M.dist a b+M.dist c d+M.dist a c+M.dist b d+M.dist a d+M.dist b c

def oppositeMin (M : ShortestDistances G) (a b c d : V) : Nat :=
  min (M.dist a b) (M.dist c d)

theorem dist_positive (M : ShortestDistances G) {a b : V} (h : a≠b) : 0<M.dist a b :=
  Nat.pos_of_ne_zero (fun hz => h ((M.dist_eq_zero_iff a b).mp hz))

theorem triangle_last (M : ShortestDistances G) (a b c : V) :
    M.dist a b≤M.dist a c+M.dist b c := by
  rw [M.dist_symm b c]
  exact M.dist_triangle a c b

theorem triangle_first (M : ShortestDistances G) (a b c : V) :
    M.dist a b≤M.dist c a+M.dist c b := by
  rw [M.dist_symm c a]
  exact M.dist_triangle a c b

/-- Actual four-terminal graph upper bound with the opposite matchings
labelled in increasing order of their distance minima. -/
theorem four_vertex_ceiling_ordered (M : ShortestDistances G) (a b c d : V)
    (neq : FourApart a b c d) (limit : Nat)
    (cap : PackingCap G (markFour a b c d) limit)
    (order : oppositeMin M a b c d≤oppositeMin M a c b d ∧
      oppositeMin M a c b d≤oppositeMin M a d b c) :
    fourSum M a b c d≤4*limit+10 := by
  have hcap (s t u v : V) (eq : markFour s t u v = markFour a b c d) :
      PackingCap G (markFour s t u v) limit := by rw [eq]; exact cap
  have route (s t u v : V) (eq : markFour s t u v = markFour a b c d)
      (ne : FourApart s t u v) :
      ShortRoute limit (M.dist s t) (M.dist u v)
        (M.dist s u) (M.dist v t) (M.dist s v) (M.dist u t) :=
    fixed_pair_short_route_four (T := markFour s t u v) M s t u v (Or.inl rfl)
      (Or.inr (Or.inl rfl)) (fun _ h => h) ne.ab ne.ac ne.ad ne.bc ne.bd ne.cd limit (hcap _ _ _ _ eq)
  have trib : TripleCaps limit (M.dist a b) (M.dist c d) (M.dist a c) (M.dist b d)
      (M.dist a d) (M.dist b c) := by
    refine ⟨triple_perimeter_cap M a b c d neq.ab neq.ac neq.bc limit cap,?_,?_,?_⟩
    · exact triple_perimeter_cap M a b d c neq.ab neq.ad neq.bd limit (hcap _ _ _ _ (by
        funext v; apply propext; simp [markFour,or_comm]))
    · exact triple_perimeter_cap M a c d b neq.ac neq.ad neq.cd limit (hcap _ _ _ _ (by
        funext v; apply propext; simp [markFour,or_comm,or_left_comm]))
    · exact triple_perimeter_cap M b c d a neq.bc neq.bd neq.cd limit (hcap _ _ _ _ (by
        funext v; apply propext; simp [markFour,or_comm,or_left_comm]))
  have triv : Triangles (M.dist a b) (M.dist c d) (M.dist a c) (M.dist b d)
      (M.dist a d) (M.dist b c) :=
    ⟨triangle_last M a b c, triangle_last M a b d,
      triangle_first M c d a, triangle_first M c d b,
      M.dist_triangle a b c,triangle_last M a c d,
      triangle_first M b d a,M.dist_triangle b c d,
      M.dist_triangle a b d,M.dist_triangle a c d,triangle_first M b c a,triangle_last M b c d⟩
  have rs : AllShortRoutes limit (M.dist a b) (M.dist c d) (M.dist a c) (M.dist b d)
      (M.dist a d) (M.dist b c) := by
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · simpa only [M.dist_symm d b,M.dist_symm c b] using route a b c d rfl neq
    · have h := route c d a b (by funext v; apply propext; simp [markFour,or_comm,or_left_comm])
        ⟨neq.cd,neq.ac.symm,neq.bc.symm,neq.ad.symm,neq.bd.symm,neq.ab⟩
      simpa only [M.dist_symm c a,M.dist_symm c b] using h
    · have h := route a c b d (by funext v; apply propext; simp [markFour,or_left_comm])
        ⟨neq.ac,neq.ab,neq.ad,neq.bc.symm,neq.cd,neq.bd⟩
      simpa only [M.dist_symm d c] using h
    · have h := route b d a c (by funext v; apply propext; simp [markFour,or_comm,or_left_comm])
        ⟨neq.bd,neq.ab.symm,neq.bc,neq.ad.symm,neq.cd.symm,neq.ac⟩
      simpa only [M.dist_symm b a] using h
    · exact route a d b c (by funext v; apply propext; simp [markFour,or_comm,or_left_comm])
        ⟨neq.ad,neq.ab,neq.ac,neq.bd.symm,neq.cd.symm,neq.bc⟩
    · have h := route b c a d (by funext v; apply propext; simp [markFour,or_left_comm])
        ⟨neq.bc,neq.ab.symm,neq.bd,neq.ac.symm,neq.cd,neq.ad⟩
      simpa only [M.dist_symm b a,M.dist_symm d c] using h
  let x := oppositeMin M a b c d
  let y := oppositeMin M a c b d
  let z := oppositeMin M a d b c
  have xs : 0<x := Nat.le_min.mpr ⟨dist_positive M neq.ab,dist_positive M neq.cd⟩
  have xx1 : x≤M.dist a b := Nat.min_le_left _ _
  have xx2 : x≤M.dist c d := Nat.min_le_right _ _
  have yy1 : y≤M.dist a c := Nat.min_le_left _ _
  have yy2 : y≤M.dist b d := Nat.min_le_right _ _
  have yz : y≤z := order.2
  have zz1 : z≤M.dist a d := Nat.min_le_left _ _
  have zz2 : z≤M.dist b c := Nat.min_le_right _ _
  have H : x+y≤limit+3 :=
    four_ball_group_cap M a b c d (Or.inl rfl) (Or.inr (Or.inl rfl))
      (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inr (Or.inr rfl)))
      (fun _ h => h) x y limit xs order.1 xx1 xx2
      ⟨yy1,Nat.le_trans yz zz2,Nat.le_trans yz zz1,yy2⟩ cap
  exact vertex_ceiling_arithmetic limit _ _ _ _ _ _
    ⟨dist_positive M neq.ab, dist_positive M neq.cd, dist_positive M neq.ac,
      dist_positive M neq.bd, dist_positive M neq.ad,dist_positive M neq.bc⟩
    trib triv rs order H

theorem packing_cap_permute {p q : V→Prop} (h : ∀ v, p v↔q v) {c : Nat}
    (cap : PackingCap G q c) : PackingCap G p c := by
  have eq : p=q := funext (fun v => propext (h v))
  rwa [eq]

set_option linter.unusedSimpArgs false in
/-- Sorting the three opposite matchings only permutes the last three
terminal labels. There is no order hypothesis in the graph theorem. -/
theorem four_vertex_ceiling (M : ShortestDistances G) (a b c d : V)
    (neq : FourApart a b c d) (limit : Nat)
    (cap : PackingCap G (markFour a b c d) limit) :
    fourSum M a b c d≤4*limit+10 := by
  let x := oppositeMin M a b c d
  let y := oppositeMin M a c b d
  let z := oppositeMin M a d b c
  by_cases xy : x≤y
  · by_cases yz : y≤z
    · exact four_vertex_ceiling_ordered M a b c d neq limit cap ⟨xy,yz⟩
    · by_cases xz : x≤z
      · have A := four_vertex_ceiling_ordered M a b d c
          ⟨neq.ab,neq.ad,neq.ac,neq.bd,neq.bc,neq.cd.symm⟩ limit
          (packing_cap_permute (fun v => by simp [markFour,or_comm,or_left_comm]) cap)
          (by
            simp [oppositeMin,M.dist_symm d c]
            have hyz : z≤y := by omega
            exact ⟨xz,hyz⟩)
        simp [fourSum,M.dist_symm d c] at A
        unfold fourSum
        omega
      · have A := four_vertex_ceiling_ordered M a d b c
          ⟨neq.ad,neq.ab,neq.ac,neq.bd.symm,neq.cd.symm,neq.bc⟩ limit
          (packing_cap_permute (fun v => by simp [markFour,or_comm,or_left_comm]) cap)
          (by
            simp [oppositeMin,M.dist_symm d c,M.dist_symm d b]
            have h : z≤x := by omega
            exact ⟨h,xy⟩)
        simp [fourSum,M.dist_symm d c,M.dist_symm d b] at A
        unfold fourSum
        omega
  · by_cases xz : x≤z
    · have A := four_vertex_ceiling_ordered M a c b d
        ⟨neq.ac,neq.ab,neq.ad,neq.bc.symm,neq.cd,neq.bd⟩ limit
        (packing_cap_permute (fun v => by simp [markFour,or_comm,or_left_comm]) cap)
        (by
          simp [oppositeMin,M.dist_symm c b]
          have h : y≤x := by omega
          exact ⟨h,xz⟩)
      simp [fourSum,M.dist_symm c b] at A
      unfold fourSum
      omega
    · by_cases yz : y≤z
      · have A := four_vertex_ceiling_ordered M a c d b
          ⟨neq.ac,neq.ad,neq.ab,neq.cd,neq.bc.symm,neq.bd.symm⟩ limit
          (packing_cap_permute (fun v => by simp [markFour,or_comm,or_left_comm]) cap)
          (by
            simp [oppositeMin,M.dist_symm d b,M.dist_symm c b]
            have h : z≤x := by omega
            exact ⟨yz,h⟩)
        simp [fourSum,M.dist_symm d b,M.dist_symm c b] at A
        unfold fourSum
        omega
      · have A := four_vertex_ceiling_ordered M a d c b
          ⟨neq.ad,neq.ac,neq.ab,neq.cd.symm,neq.bd.symm,neq.bc.symm⟩ limit
          (packing_cap_permute (fun v => by simp [markFour,or_comm,or_left_comm]) cap)
          (by
            simp [oppositeMin,M.dist_symm c b,M.dist_symm d b,M.dist_symm d c]
            have h1 : z≤y := by omega
            have h2 : y≤x := by omega
            exact ⟨h1,h2⟩)
        simp [fourSum,M.dist_symm c b,M.dist_symm d b,M.dist_symm d c] at A
        unfold fourSum
        omega

/-- Sharp universal four-terminal vertex-separator lower bound on actual
graphs. The existing paper constructions attain this integer count. -/
theorem four_vertex_separators (M : ShortestDistances G) (a b c d : V)
    (neq : FourApart a b c d) :
    Nonempty (VertexFamily G (markFour a b c d) ((fourSum M a b c d-7)/4)) := by
  classical
  let n := (fourSum M a b c d-7)/4
  change Nonempty (VertexFamily G (markFour a b c d) n)
  by_cases zero : n=0
  · rw [zero]
    exact ⟨⟨fun i => Fin.elim0 i,fun i => Fin.elim0 i,fun i => Fin.elim0 i⟩⟩
  · by_cases has : Nonempty (VertexFamily G (markFour a b c d) n)
    · exact has
    · exfalso
      have cap : PackingCap G (markFour a b c d) (n-1) := by
        intro q F
        by_cases enough : n≤q
        · exact (has ⟨takeFamily F enough⟩).elim
        · omega
      have h := four_vertex_ceiling M a b c d neq (n-1) cap
      have k := (vertex_ceiling_as_minimum (fourSum M a b c d) (n-1)).mpr h
      change n≤n-1 at k
      omega

end HakKozerenkoSeparatorGraph

#print axioms HakKozerenkoSeparatorGraph.four_vertex_ceiling_ordered
#print axioms HakKozerenkoSeparatorGraph.four_vertex_ceiling
#print axioms HakKozerenkoSeparatorGraph.four_vertex_separators
