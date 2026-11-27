module

public import Std
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-! Native proof of the sharp four-terminal distance packing bounds. -/

/-! Integer K₄ cut decomposition: a constructive proof for the scaled
four-terminal packing polytope, independent of Mathlib or an LP oracle. -/
namespace TriameterQ3Four

structure Edges where
  ab : Int
  ac : Int
  ad : Int
  bc : Int
  bd : Int
  cd : Int

def Nonneg (x : Edges) : Prop :=
  0 ≤ x.ab ∧
  0 ≤ x.ac ∧
  0 ≤ x.ad ∧
  0 ≤ x.bc ∧
  0 ≤ x.bd ∧
  0 ≤ x.cd

def Below (x y : Edges) : Prop :=
  x.ab ≤ y.ab ∧
  x.ac ≤ y.ac ∧
  x.ad ≤ y.ad ∧
  x.bc ≤ y.bc ∧
  x.bd ≤ y.bd ∧
  x.cd ≤ y.cd

def Feasible (R : Int) (x : Edges) : Prop :=
  0 ≤ x.ab ∧
  0 ≤ x.ac ∧
  0 ≤ x.ad ∧
  0 ≤ x.bc ∧
  0 ≤ x.bd ∧
  0 ≤ x.cd ∧
  x.ab ≤ R ∧
  x.ac ≤ R ∧
  x.ad ≤ R ∧
  x.bc ≤ R ∧
  x.bd ≤ R ∧
  x.cd ≤ R ∧
  x.ab + x.ac + x.bc ≤ 2*R ∧
  x.ab + x.ad + x.bd ≤ 2*R ∧
  x.ac + x.ad + x.cd ≤ 2*R ∧
  x.bc + x.bd + x.cd ≤ 2*R

def BlockAB (R : Int) (x : Edges) : Prop :=
  x.ab = R ∨ x.ab + x.ac + x.bc = 2*R ∨ x.ab + x.ad + x.bd = 2*R

def raiseAB (R : Int) (x : Edges) : Edges :=
  {x with ab := min R (min (2*R - x.ac - x.bc) (2*R - x.ad - x.bd))}

def BlockAC (R : Int) (x : Edges) : Prop :=
  x.ac = R ∨ x.ab + x.ac + x.bc = 2*R ∨ x.ac + x.ad + x.cd = 2*R

def raiseAC (R : Int) (x : Edges) : Edges :=
  {x with ac := min R (min (2*R - x.ab - x.bc) (2*R - x.ad - x.cd))}

def BlockAD (R : Int) (x : Edges) : Prop :=
  x.ad = R ∨ x.ab + x.ad + x.bd = 2*R ∨ x.ac + x.ad + x.cd = 2*R

def raiseAD (R : Int) (x : Edges) : Edges :=
  {x with ad := min R (min (2*R - x.ab - x.bd) (2*R - x.ac - x.cd))}

def BlockBC (R : Int) (x : Edges) : Prop :=
  x.bc = R ∨ x.ab + x.ac + x.bc = 2*R ∨ x.bc + x.bd + x.cd = 2*R

def raiseBC (R : Int) (x : Edges) : Edges :=
  {x with bc := min R (min (2*R - x.ab - x.ac) (2*R - x.bd - x.cd))}

def BlockBD (R : Int) (x : Edges) : Prop :=
  x.bd = R ∨ x.ab + x.ad + x.bd = 2*R ∨ x.bc + x.bd + x.cd = 2*R

def raiseBD (R : Int) (x : Edges) : Edges :=
  {x with bd := min R (min (2*R - x.ab - x.ad) (2*R - x.bc - x.cd))}

def BlockCD (R : Int) (x : Edges) : Prop :=
  x.cd = R ∨ x.ac + x.ad + x.cd = 2*R ∨ x.bc + x.bd + x.cd = 2*R

def raiseCD (R : Int) (x : Edges) : Edges :=
  {x with cd := min R (min (2*R - x.ac - x.ad) (2*R - x.bc - x.bd))}

def Saturated (R : Int) (x : Edges) : Prop :=
  BlockAB R x ∧
  BlockAC R x ∧
  BlockAD R x ∧
  BlockBC R x ∧
  BlockBD R x ∧
  BlockCD R x

def LowerTriangles (x : Edges) : Prop :=
  x.ab ≤ x.ac + x.bc ∧
  x.ac ≤ x.ab + x.bc ∧
  x.bc ≤ x.ab + x.ac ∧
  x.ab ≤ x.ad + x.bd ∧
  x.ad ≤ x.ab + x.bd ∧
  x.bd ≤ x.ab + x.ad ∧
  x.ac ≤ x.ad + x.cd ∧
  x.ad ≤ x.ac + x.cd ∧
  x.cd ≤ x.ac + x.ad ∧
  x.bc ≤ x.bd + x.cd ∧
  x.bd ≤ x.bc + x.cd ∧
  x.cd ≤ x.bc + x.bd

theorem below_trans (x y z : Edges) (hxy : Below x y) (hyz : Below y z) :
    Below x z := by
  rcases hxy with ⟨a0, a1, a2, a3, a4, a5⟩
  rcases hyz with ⟨b0, b1, b2, b3, b4, b5⟩
  exact ⟨Int.le_trans a0 b0, Int.le_trans a1 b1, Int.le_trans a2 b2, Int.le_trans a3 b3, Int.le_trans a4 b4, Int.le_trans a5 b5⟩

theorem raiseAB_good (R : Int) (x : Edges) (hx : Feasible R x) :
    Feasible R (raiseAB R x) := by
  rcases hx with ⟨n0, n1, n2, n3, n4, n5, u0, u1, u2, u3, u4, u5, t0, t1, t2, t3⟩
  unfold Feasible
  dsimp [raiseAB]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem raiseAB_above (R : Int) (x : Edges) (hx : Feasible R x) :
    Below x (raiseAB R x) := by
  rcases hx with ⟨n0, n1, n2, n3, n4, n5, u0, u1, u2, u3, u4, u5, t0, t1, t2, t3⟩
  unfold Below
  dsimp [raiseAB]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem raiseAB_block (R : Int) (x : Edges) :
    BlockAB R (raiseAB R x) := by
  unfold BlockAB
  dsimp [raiseAB]
  omega

theorem blockAB_up (R : Int) (x y : Edges)
    (hxy : Below x y) (hy : Feasible R y) (hx : BlockAB R x) : BlockAB R y := by
  rcases hxy with ⟨l0, l1, l2, l3, l4, l5⟩
  rcases hy with ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15⟩
  unfold BlockAB at hx ⊢
  rcases hx with h | h | h <;> omega

theorem raiseAC_good (R : Int) (x : Edges) (hx : Feasible R x) :
    Feasible R (raiseAC R x) := by
  rcases hx with ⟨n0, n1, n2, n3, n4, n5, u0, u1, u2, u3, u4, u5, t0, t1, t2, t3⟩
  unfold Feasible
  dsimp [raiseAC]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem raiseAC_above (R : Int) (x : Edges) (hx : Feasible R x) :
    Below x (raiseAC R x) := by
  rcases hx with ⟨n0, n1, n2, n3, n4, n5, u0, u1, u2, u3, u4, u5, t0, t1, t2, t3⟩
  unfold Below
  dsimp [raiseAC]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem raiseAC_block (R : Int) (x : Edges) :
    BlockAC R (raiseAC R x) := by
  unfold BlockAC
  dsimp [raiseAC]
  omega

theorem blockAC_up (R : Int) (x y : Edges)
    (hxy : Below x y) (hy : Feasible R y) (hx : BlockAC R x) : BlockAC R y := by
  rcases hxy with ⟨l0, l1, l2, l3, l4, l5⟩
  rcases hy with ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15⟩
  unfold BlockAC at hx ⊢
  rcases hx with h | h | h <;> omega

theorem raiseAD_good (R : Int) (x : Edges) (hx : Feasible R x) :
    Feasible R (raiseAD R x) := by
  rcases hx with ⟨n0, n1, n2, n3, n4, n5, u0, u1, u2, u3, u4, u5, t0, t1, t2, t3⟩
  unfold Feasible
  dsimp [raiseAD]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem raiseAD_above (R : Int) (x : Edges) (hx : Feasible R x) :
    Below x (raiseAD R x) := by
  rcases hx with ⟨n0, n1, n2, n3, n4, n5, u0, u1, u2, u3, u4, u5, t0, t1, t2, t3⟩
  unfold Below
  dsimp [raiseAD]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem raiseAD_block (R : Int) (x : Edges) :
    BlockAD R (raiseAD R x) := by
  unfold BlockAD
  dsimp [raiseAD]
  omega

theorem blockAD_up (R : Int) (x y : Edges)
    (hxy : Below x y) (hy : Feasible R y) (hx : BlockAD R x) : BlockAD R y := by
  rcases hxy with ⟨l0, l1, l2, l3, l4, l5⟩
  rcases hy with ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15⟩
  unfold BlockAD at hx ⊢
  rcases hx with h | h | h <;> omega

theorem raiseBC_good (R : Int) (x : Edges) (hx : Feasible R x) :
    Feasible R (raiseBC R x) := by
  rcases hx with ⟨n0, n1, n2, n3, n4, n5, u0, u1, u2, u3, u4, u5, t0, t1, t2, t3⟩
  unfold Feasible
  dsimp [raiseBC]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem raiseBC_above (R : Int) (x : Edges) (hx : Feasible R x) :
    Below x (raiseBC R x) := by
  rcases hx with ⟨n0, n1, n2, n3, n4, n5, u0, u1, u2, u3, u4, u5, t0, t1, t2, t3⟩
  unfold Below
  dsimp [raiseBC]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem raiseBC_block (R : Int) (x : Edges) :
    BlockBC R (raiseBC R x) := by
  unfold BlockBC
  dsimp [raiseBC]
  omega

theorem blockBC_up (R : Int) (x y : Edges)
    (hxy : Below x y) (hy : Feasible R y) (hx : BlockBC R x) : BlockBC R y := by
  rcases hxy with ⟨l0, l1, l2, l3, l4, l5⟩
  rcases hy with ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15⟩
  unfold BlockBC at hx ⊢
  rcases hx with h | h | h <;> omega

theorem raiseBD_good (R : Int) (x : Edges) (hx : Feasible R x) :
    Feasible R (raiseBD R x) := by
  rcases hx with ⟨n0, n1, n2, n3, n4, n5, u0, u1, u2, u3, u4, u5, t0, t1, t2, t3⟩
  unfold Feasible
  dsimp [raiseBD]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem raiseBD_above (R : Int) (x : Edges) (hx : Feasible R x) :
    Below x (raiseBD R x) := by
  rcases hx with ⟨n0, n1, n2, n3, n4, n5, u0, u1, u2, u3, u4, u5, t0, t1, t2, t3⟩
  unfold Below
  dsimp [raiseBD]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem raiseBD_block (R : Int) (x : Edges) :
    BlockBD R (raiseBD R x) := by
  unfold BlockBD
  dsimp [raiseBD]
  omega

theorem blockBD_up (R : Int) (x y : Edges)
    (hxy : Below x y) (hy : Feasible R y) (hx : BlockBD R x) : BlockBD R y := by
  rcases hxy with ⟨l0, l1, l2, l3, l4, l5⟩
  rcases hy with ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15⟩
  unfold BlockBD at hx ⊢
  rcases hx with h | h | h <;> omega

theorem raiseCD_good (R : Int) (x : Edges) (hx : Feasible R x) :
    Feasible R (raiseCD R x) := by
  rcases hx with ⟨n0, n1, n2, n3, n4, n5, u0, u1, u2, u3, u4, u5, t0, t1, t2, t3⟩
  unfold Feasible
  dsimp [raiseCD]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem raiseCD_above (R : Int) (x : Edges) (hx : Feasible R x) :
    Below x (raiseCD R x) := by
  rcases hx with ⟨n0, n1, n2, n3, n4, n5, u0, u1, u2, u3, u4, u5, t0, t1, t2, t3⟩
  unfold Below
  dsimp [raiseCD]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem raiseCD_block (R : Int) (x : Edges) :
    BlockCD R (raiseCD R x) := by
  unfold BlockCD
  dsimp [raiseCD]
  omega

theorem blockCD_up (R : Int) (x y : Edges)
    (hxy : Below x y) (hy : Feasible R y) (hx : BlockCD R x) : BlockCD R y := by
  rcases hxy with ⟨l0, l1, l2, l3, l4, l5⟩
  rcases hy with ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15⟩
  unfold BlockCD at hx ⊢
  rcases hx with h | h | h <;> omega

/-- Raise every coordinate once; later raises never unblock an earlier one. -/
theorem saturated_extension (R : Int) (x : Edges) (h : Feasible R x) :
    ∃ y : Edges, Feasible R y ∧ Below x y ∧ Saturated R y := by

  let x1 := raiseAB R x
  have g1 : Feasible R x1 := raiseAB_good R x h
  have a1 : Below x x1 := raiseAB_above R x h
  have b1 : BlockAB R x1 := raiseAB_block R x
  let x2 := raiseAC R x1
  have g2 : Feasible R x2 := raiseAC_good R x1 g1
  have a2 : Below x1 x2 := raiseAC_above R x1 g1
  have b2 : BlockAC R x2 := raiseAC_block R x1
  have bchain2 := below_trans _ _ _ a1 a2
  let x3 := raiseAD R x2
  have g3 : Feasible R x3 := raiseAD_good R x2 g2
  have a3 : Below x2 x3 := raiseAD_above R x2 g2
  have b3 : BlockAD R x3 := raiseAD_block R x2
  have bchain3 := below_trans _ _ _ bchain2 a3
  let x4 := raiseBC R x3
  have g4 : Feasible R x4 := raiseBC_good R x3 g3
  have a4 : Below x3 x4 := raiseBC_above R x3 g3
  have b4 : BlockBC R x4 := raiseBC_block R x3
  have bchain4 := below_trans _ _ _ bchain3 a4
  let x5 := raiseBD R x4
  have g5 : Feasible R x5 := raiseBD_good R x4 g4
  have a5 : Below x4 x5 := raiseBD_above R x4 g4
  have b5 : BlockBD R x5 := raiseBD_block R x4
  have bchain5 := below_trans _ _ _ bchain4 a5
  let x6 := raiseCD R x5
  have g6 : Feasible R x6 := raiseCD_good R x5 g5
  have a6 : Below x5 x6 := raiseCD_above R x5 g5
  have b6 : BlockCD R x6 := raiseCD_block R x5
  have bchain6 := below_trans _ _ _ bchain5 a6
  refine ⟨x6, g6, bchain6, ?_⟩
  unfold Saturated
  exact ⟨blockAB_up R x1 x6 (below_trans _ _ _ (below_trans _ _ _ (below_trans _ _ _ (below_trans _ _ _ a2 a3) a4) a5) a6) g6 b1, blockAC_up R x2 x6 (below_trans _ _ _ (below_trans _ _ _ (below_trans _ _ _ a3 a4) a5) a6) g6 b2, blockAD_up R x3 x6 (below_trans _ _ _ (below_trans _ _ _ a4 a5) a6) g6 b3, blockBC_up R x4 x6 (below_trans _ _ _ a5 a6) g6 b4, blockBD_up R x5 x6 a6 g6 b5, b6⟩

theorem saturated_lower (R : Int) (x : Edges) (hx : Feasible R x)
    (hs : Saturated R x) : LowerTriangles x := by
  rcases hx with ⟨n0, n1, n2, n3, n4, n5, u0, u1, u2, u3, u4, u5, t0, t1, t2, t3⟩
  rcases hs with ⟨b0, b1, b2, b3, b4, b5⟩
  unfold LowerTriangles
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩

  · unfold BlockAC at b1
    unfold BlockBC at b3
    rcases b1 with h | h | h <;> rcases b3 with j | j | j <;> omega
  · unfold BlockAB at b0
    unfold BlockBC at b3
    rcases b0 with h | h | h <;> rcases b3 with j | j | j <;> omega
  · unfold BlockAB at b0
    unfold BlockAC at b1
    rcases b0 with h | h | h <;> rcases b1 with j | j | j <;> omega
  · unfold BlockAD at b2
    unfold BlockBD at b4
    rcases b2 with h | h | h <;> rcases b4 with j | j | j <;> omega
  · unfold BlockAB at b0
    unfold BlockBD at b4
    rcases b0 with h | h | h <;> rcases b4 with j | j | j <;> omega
  · unfold BlockAB at b0
    unfold BlockAD at b2
    rcases b0 with h | h | h <;> rcases b2 with j | j | j <;> omega
  · unfold BlockAD at b2
    unfold BlockCD at b5
    rcases b2 with h | h | h <;> rcases b5 with j | j | j <;> omega
  · unfold BlockAC at b1
    unfold BlockCD at b5
    rcases b1 with h | h | h <;> rcases b5 with j | j | j <;> omega
  · unfold BlockAC at b1
    unfold BlockAD at b2
    rcases b1 with h | h | h <;> rcases b2 with j | j | j <;> omega
  · unfold BlockBD at b4
    unfold BlockCD at b5
    rcases b4 with h | h | h <;> rcases b5 with j | j | j <;> omega
  · unfold BlockBC at b3
    unfold BlockCD at b5
    rcases b3 with h | h | h <;> rcases b5 with j | j | j <;> omega
  · unfold BlockBC at b3
    unfold BlockBD at b4
    rcases b3 with h | h | h <;> rcases b4 with j | j | j <;> omega

structure Atoms where
  p000 : Int
  p001 : Int
  p010 : Int
  p011 : Int
  p100 : Int
  p101 : Int
  p110 : Int
  p111 : Int

def AtomNonneg (p : Atoms) : Prop :=
  0 ≤ p.p000 ∧
  0 ≤ p.p001 ∧
  0 ≤ p.p010 ∧
  0 ≤ p.p011 ∧
  0 ≤ p.p100 ∧
  0 ≤ p.p101 ∧
  0 ≤ p.p110 ∧
  0 ≤ p.p111

def mass (p : Atoms) : Int :=
  p.p000 + p.p001 + p.p010 + p.p011 + p.p100 + p.p101 + p.p110 + p.p111

def marginals (p : Atoms) : Edges :=
  ⟨p.p100 + p.p101 + p.p110 + p.p111,
   p.p010 + p.p011 + p.p110 + p.p111,
   p.p001 + p.p011 + p.p101 + p.p111,
   p.p010 + p.p011 + p.p100 + p.p101,
   p.p001 + p.p011 + p.p100 + p.p110,
   p.p001 + p.p010 + p.p101 + p.p110⟩

def Double (x : Edges) : Edges :=
  ⟨2*x.ab, 2*x.ac, 2*x.ad, 2*x.bc, 2*x.bd, 2*x.cd⟩

theorem saturated_decomposition (R : Int) (x : Edges) (hx : Feasible R x)
    (hl : LowerTriangles x) :
    ∃ p : Atoms, AtomNonneg p ∧ mass p = 2*R ∧ marginals p = Double x := by
  rcases hx with ⟨n0, n1, n2, n3, n4, n5, u0, u1, u2, u3, u4, u5, t0, t1, t2, t3⟩
  rcases hl with ⟨l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11⟩
  let b := 2*x.ab
  let c := 2*x.ac
  let d := 2*x.ad
  let bc := x.ab+x.ac-x.bc
  let bd := x.ab+x.ad-x.bd
  let cd := x.ac+x.ad-x.cd
  let t := max 0 (max (bc+bd-b) (max (bc+cd-c) (bd+cd-d)))
  let p : Atoms := ⟨2*R-b-c-d+bc+bd+cd-t, d-bd-cd+t, c-bc-cd+t, cd-t,
    b-bc-bd+t, bd-t, bc-t, t⟩
  refine ⟨p, ?_, ?_, ?_⟩
  · unfold AtomNonneg
    dsimp [p, t, b, c, d, bc, bd, cd]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
  · dsimp [mass, p]
    omega
  · have h_ab : (marginals p).ab = (Double x).ab := by dsimp [marginals, p, Double, b]; omega
    have h_ac : (marginals p).ac = (Double x).ac := by dsimp [marginals, p, Double, c]; omega
    have h_ad : (marginals p).ad = (Double x).ad := by dsimp [marginals, p, Double, d]; omega
    have h_bc : (marginals p).bc = (Double x).bc := by dsimp [marginals, p, Double, b, c, bc]; omega
    have h_bd : (marginals p).bd = (Double x).bd := by dsimp [marginals, p, Double, b, d, bd]; omega
    have h_cd : (marginals p).cd = (Double x).cd := by dsimp [marginals, p, Double, c, d, cd]; omega
    rcases hp : marginals p with ⟨za, zb, zc, zd, ze, zf⟩
    rw [hp] at h_ab h_ac h_ad h_bc h_bd h_cd
    dsimp [Double] at *
    rw [h_ab, h_ac, h_ad, h_bc, h_bd, h_cd]

/-- A dominated integer distance vector is a marginal of an explicitly
constructed scaled integral cut distribution. Its total mass is 2R. -/
theorem domination_by_cut_distribution (R : Int) (x : Edges) (h : Feasible R x) :
    ∃ p : Atoms, AtomNonneg p ∧ mass p = 2*R ∧ Below (Double x) (marginals p) := by
  obtain ⟨y,hy,hle,hb⟩ := saturated_extension R x h
  obtain ⟨p,hn,hm,hpg⟩ := saturated_decomposition R y hy (saturated_lower R y hy hb)
  refine ⟨p,hn,hm,?_⟩
  rw [hpg]
  rcases hle with ⟨a0, a1, a2, a3, a4, a5⟩
  unfold Below
  dsimp [Double]
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

def dot (x c : Edges) : Int :=
  x.ab*c.ab + x.ac*c.ac + x.ad*c.ad + x.bc*c.bc + x.bd*c.bd + x.cd*c.cd

def coefficientSum (c : Edges) : Int :=
  c.ab + c.ac + c.ad + c.bc + c.bd + c.cd

def cutCosts (c : Edges) : Atoms :=
  ⟨0,
   c.ad + c.bd + c.cd,
   c.ac + c.bc + c.cd,
   c.ac + c.ad + c.bc + c.bd,
   c.ab + c.bc + c.bd,
   c.ab + c.ad + c.bc + c.cd,
   c.ab + c.ac + c.bd + c.cd,
   c.ab + c.ac + c.ad⟩

def atomDot (p c : Atoms) : Int :=
  p.p000*c.p000 + p.p001*c.p001 + p.p010*c.p010 + p.p011*c.p011 + p.p100*c.p100 + p.p101*c.p101 + p.p110*c.p110 + p.p111*c.p111

def maxCut (c : Edges) : Int :=
  max (cutCosts c).p111 (max (cutCosts c).p110 (max (cutCosts c).p101 (max (cutCosts c).p100 (max (cutCosts c).p011 (max (cutCosts c).p010 (max (cutCosts c).p001 (0)))))))

def CutBound (c : Edges) (Q : Int) : Prop :=
  (cutCosts c).p000 ≤ Q ∧
  (cutCosts c).p001 ≤ Q ∧
  (cutCosts c).p010 ≤ Q ∧
  (cutCosts c).p011 ≤ Q ∧
  (cutCosts c).p100 ≤ Q ∧
  (cutCosts c).p101 ≤ Q ∧
  (cutCosts c).p110 ≤ Q ∧
  (cutCosts c).p111 ≤ Q

theorem maxCut_is_bound (c : Edges) : CutBound c (maxCut c) := by
  unfold CutBound maxCut
  dsimp [cutCosts]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem dot_mono (x y c : Edges) (hx : Below x y) (hc : Nonneg c) :
    dot x c ≤ dot y c := by

  rcases hx with ⟨b0, b1, b2, b3, b4, b5⟩
  rcases hc with ⟨a0, a1, a2, a3, a4, a5⟩
  have h0 : x.ab*c.ab ≤ y.ab*c.ab := Int.mul_le_mul_of_nonneg_right b0 a0
  have h1 : x.ac*c.ac ≤ y.ac*c.ac := Int.mul_le_mul_of_nonneg_right b1 a1
  have h2 : x.ad*c.ad ≤ y.ad*c.ad := Int.mul_le_mul_of_nonneg_right b2 a2
  have h3 : x.bc*c.bc ≤ y.bc*c.bc := Int.mul_le_mul_of_nonneg_right b3 a3
  have h4 : x.bd*c.bd ≤ y.bd*c.bd := Int.mul_le_mul_of_nonneg_right b4 a4
  have h5 : x.cd*c.cd ≤ y.cd*c.cd := Int.mul_le_mul_of_nonneg_right b5 a5
  unfold dot
  omega

theorem marginals_dot (p : Atoms) (c : Edges) :
    dot (marginals p) c = atomDot p (cutCosts c) := by
  simp only [dot, marginals, atomDot, cutCosts, Int.add_mul, Int.mul_add, Int.mul_zero,
    Int.zero_add]
  ac_rfl

theorem double_dot (p c : Edges) : dot (Double p) c = 2*dot p c := by
  simp only [dot, Double, Int.mul_assoc, Int.mul_add]

theorem convex_cut_bound (p : Atoms) (c : Edges) (Q : Int)
    (hp : AtomNonneg p) (hq : CutBound c Q) :
    atomDot p (cutCosts c) ≤ mass p * Q := by

  rcases hp with ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩
  rcases hq with ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩
  have h0 : p.p000*(cutCosts c).p000 ≤ p.p000*Q := Int.mul_le_mul_of_nonneg_left b0 a0
  have h1 : p.p001*(cutCosts c).p001 ≤ p.p001*Q := Int.mul_le_mul_of_nonneg_left b1 a1
  have h2 : p.p010*(cutCosts c).p010 ≤ p.p010*Q := Int.mul_le_mul_of_nonneg_left b2 a2
  have h3 : p.p011*(cutCosts c).p011 ≤ p.p011*Q := Int.mul_le_mul_of_nonneg_left b3 a3
  have h4 : p.p100*(cutCosts c).p100 ≤ p.p100*Q := Int.mul_le_mul_of_nonneg_left b4 a4
  have h5 : p.p101*(cutCosts c).p101 ≤ p.p101*Q := Int.mul_le_mul_of_nonneg_left b5 a5
  have h6 : p.p110*(cutCosts c).p110 ≤ p.p110*Q := Int.mul_le_mul_of_nonneg_left b6 a6
  have h7 : p.p111*(cutCosts c).p111 ≤ p.p111*Q := Int.mul_le_mul_of_nonneg_left b7 a7
  unfold atomDot mass
  simp only [Int.add_mul]
  omega

/-- Sharp upper cut functional bound for arbitrary nonnegative integer
edge coefficients; it is not restricted to products of terminal weights. -/
theorem scaled_cut_bound (R : Int) (x c : Edges) (Q : Int)
    (hx : Feasible R x) (hc : Nonneg c) (hQ : CutBound c Q) :
    dot x c ≤ R*Q := by
  obtain ⟨p,hp,hm,habove⟩ := domination_by_cut_distribution R x hx
  have he := dot_mono _ _ c habove hc
  rw [double_dot, marginals_dot] at he
  have hf := convex_cut_bound p c Q hp hQ
  rw [hm, Int.mul_assoc] at hf
  omega

def DistanceCaps (k R : Int) (d : Edges) : Prop :=
  d.ab ≤ k+R ∧
  d.ac ≤ k+R ∧
  d.ad ≤ k+R ∧
  d.bc ≤ k+R ∧
  d.bd ≤ k+R ∧
  d.cd ≤ k+R ∧
  d.ab + d.ac + d.bc ≤ 3*k+2*R ∧
  d.ab + d.ad + d.bd ≤ 3*k+2*R ∧
  d.ac + d.ad + d.cd ≤ 3*k+2*R ∧
  d.bc + d.bd + d.cd ≤ 3*k+2*R

def clipped (k : Int) (d : Edges) : Edges :=
  ⟨max 0 (d.ab-k), max 0 (d.ac-k), max 0 (d.ad-k), max 0 (d.bc-k), max 0 (d.bd-k), max 0 (d.cd-k)⟩

theorem clipped_feasible (k R : Int) (d : Edges)
    (hR : 0 ≤ R) (h : DistanceCaps k R d) : Feasible R (clipped k d) := by
  rcases h with ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9⟩
  unfold Feasible
  dsimp [clipped]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem clip_dot_bound (k : Int) (d c : Edges) (hc : Nonneg c) :
    dot d c ≤ k*coefficientSum c + dot (clipped k d) c := by

  rcases hc with ⟨a0, a1, a2, a3, a4, a5⟩
  have h0 : d.ab ≤ k+(clipped k d).ab := by dsimp [clipped]; omega
  have p0 := Int.mul_le_mul_of_nonneg_right h0 a0
  rw [Int.add_mul] at p0
  have h1 : d.ac ≤ k+(clipped k d).ac := by dsimp [clipped]; omega
  have p1 := Int.mul_le_mul_of_nonneg_right h1 a1
  rw [Int.add_mul] at p1
  have h2 : d.ad ≤ k+(clipped k d).ad := by dsimp [clipped]; omega
  have p2 := Int.mul_le_mul_of_nonneg_right h2 a2
  rw [Int.add_mul] at p2
  have h3 : d.bc ≤ k+(clipped k d).bc := by dsimp [clipped]; omega
  have p3 := Int.mul_le_mul_of_nonneg_right h3 a3
  rw [Int.add_mul] at p3
  have h4 : d.bd ≤ k+(clipped k d).bd := by dsimp [clipped]; omega
  have p4 := Int.mul_le_mul_of_nonneg_right h4 a4
  rw [Int.add_mul] at p4
  have h5 : d.cd ≤ k+(clipped k d).cd := by dsimp [clipped]; omega
  have p5 := Int.mul_le_mul_of_nonneg_right h5 a5
  rw [Int.add_mul] at p5
  unfold dot coefficientSum
  simp only [Int.mul_add]
  omega

/-- Four-terminal upper bound from the six individual and four triple
distance caps, with no LP oracle and no assumptions on how d was obtained. -/
theorem four_terminal_cut_bound (k R : Int) (d c : Edges)
    (hR : 0 ≤ R) (hd : DistanceCaps k R d) (hc : Nonneg c) :
    dot d c ≤ k*coefficientSum c + R*maxCut c := by
  have a := clip_dot_bound k d c hc
  have b := scaled_cut_bound R (clipped k d) c (maxCut c)
    (clipped_feasible k R d hR hd) hc (maxCut_is_bound c)
  omega

def terminalCoefficients (a b c d : Int) : Edges :=
  ⟨a*b,a*c,a*d,b*c,b*d,c*d⟩

/-- Product weights are the special case that yields the weighted graph
formula. Here R is D-k, i.e. (k+1)(p-1) in the packing application. -/
theorem four_terminal_product_bound (k R : Int) (x : Edges)
    (a b c d : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hR : 0 ≤ R) (hx : DistanceCaps k R x) :
    dot x (terminalCoefficients a b c d) ≤
      k*coefficientSum (terminalCoefficients a b c d) +
        R*maxCut (terminalCoefficients a b c d) := by
  apply four_terminal_cut_bound k R x _ hR hx
  exact ⟨Int.mul_nonneg ha hb, Int.mul_nonneg ha hc, Int.mul_nonneg ha hd,
    Int.mul_nonneg hb hc, Int.mul_nonneg hb hd, Int.mul_nonneg hc hd⟩

inductive Cut where
  | c000
  | c001
  | c010
  | c011
  | c100
  | c101
  | c110
  | c111

def cutCost (c : Edges) : Cut → Int
  | .c000 => (cutCosts c).p000
  | .c001 => (cutCosts c).p001
  | .c010 => (cutCosts c).p010
  | .c011 => (cutCosts c).p011
  | .c100 => (cutCosts c).p100
  | .c101 => (cutCosts c).p101
  | .c110 => (cutCosts c).p110
  | .c111 => (cutCosts c).p111

def scaledCut (R : Int) : Cut → Edges
  | .c000 => ⟨0, 0, 0, 0, 0, 0⟩
  | .c001 => ⟨0, 0, R, 0, R, R⟩
  | .c010 => ⟨0, R, 0, R, 0, R⟩
  | .c011 => ⟨0, R, R, R, R, 0⟩
  | .c100 => ⟨R, 0, 0, R, R, 0⟩
  | .c101 => ⟨R, 0, R, R, 0, R⟩
  | .c110 => ⟨R, R, 0, 0, R, R⟩
  | .c111 => ⟨R, R, R, 0, 0, 0⟩

theorem maxCut_cases (c : Edges) :
    maxCut c = (cutCosts c).p000 ∨
      maxCut c = (cutCosts c).p001 ∨
      maxCut c = (cutCosts c).p010 ∨
      maxCut c = (cutCosts c).p011 ∨
      maxCut c = (cutCosts c).p100 ∨
      maxCut c = (cutCosts c).p101 ∨
      maxCut c = (cutCosts c).p110 ∨
      maxCut c = (cutCosts c).p111 := by
  unfold maxCut
  dsimp [cutCosts]
  omega

theorem maxCut_realized (c : Edges) : ∃ b : Cut, maxCut c = cutCost c b := by
  rcases maxCut_cases c with h | h | h | h | h | h | h | h

  · exact ⟨.c000, h⟩
  · exact ⟨.c001, h⟩
  · exact ⟨.c010, h⟩
  · exact ⟨.c011, h⟩
  · exact ⟨.c100, h⟩
  · exact ⟨.c101, h⟩
  · exact ⟨.c110, h⟩
  · exact ⟨.c111, h⟩

theorem scaledCut_feasible (R : Int) (hR : 0 ≤ R) (b : Cut) :
    Feasible R (scaledCut R b) := by
  cases b <;> unfold Feasible <;> dsimp [scaledCut] <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem scaledCut_dot (R : Int) (c : Edges) (b : Cut) :
    dot (scaledCut R b) c = R * cutCost c b := by
  cases b <;>
    simp [dot, scaledCut, cutCost, cutCosts, Int.mul_add]

/-- The maximum of the four-terminal scaled feasible polytope is attained
by a single actual cut, not merely approached by a weighted solution. -/
theorem scaled_polytope_maximum (R : Int) (hR : 0 ≤ R) (c : Edges) (hc : Nonneg c) :
    (∀ x, Feasible R x → dot x c ≤ R*maxCut c) ∧
    ∃ x, Feasible R x ∧ dot x c = R*maxCut c := by
  refine ⟨fun x hx => scaled_cut_bound R x c _ hx hc (maxCut_is_bound c), ?_⟩
  obtain ⟨b,hb⟩ := maxCut_realized c
  exact ⟨scaledCut R b, scaledCut_feasible R hR b, (scaledCut_dot R c b).trans (congrArg (R*·) hb.symm)⟩

end TriameterQ3Four

/-! Source reading of unweighted finite simple graph shortest paths, in
Lean core/Std, independent of Mathlib and the four-terminal algebra. -/
namespace TriameterQ3Graph

universe u
structure SimpleGraph (V : Type u) where
  adj : V → V → Prop
  symm : ∀ {a b}, adj a b → adj b a
  loopless : ∀ a, ¬ adj a a

/-- A native walk of length n, with values outside [0,n] ignored. -/
structure Walk {V : Type u} (G : SimpleGraph V) (a b : V) (n : Nat) where
  point : Nat → V
  first : point 0 = a
  last : point n = b
  step : ∀ i, i < n → G.adj (point i) (point (i+1))

namespace Walk
variable {V : Type u} {G : SimpleGraph V} {a b c : V} {m n : Nat}

def trivial (G : SimpleGraph V) (a : V) : Walk G a a 0 :=
  ⟨fun _ => a, rfl, rfl, fun _ h => (Nat.not_lt_zero _ h).elim⟩

def concat (p : Walk G a b m) (q : Walk G b c n) : Walk G a c (m+n) := by
  refine ⟨fun i => if i ≤ m then p.point i else q.point (i-m), ?_, ?_, ?_⟩
  · simpa only [ite_eq_left (Nat.zero_le m)] using p.first
  · by_cases h : n = 0
    · subst n
      have hbc := q.first.symm.trans q.last
      simpa only [Nat.add_zero, ite_eq_left (Nat.le_refl m)] using p.last.trans hbc
    · have hn : ¬ m+n ≤ m := by omega
      simpa only [ite_eq_right hn, Nat.add_sub_cancel_left] using q.last
  · intro i hi
    by_cases h : i < m
    · have hu : i ≤ m := by omega
      have hv : i+1 ≤ m := by omega
      simpa only [ite_eq_left hu, ite_eq_left hv] using p.step i h
    · have hn : ¬ i+1 ≤ m := by omega
      by_cases he : i = m
      · subst i
        have ht : 0 < n := by omega
        have h1 : m+1-m = 1 := by omega
        have heq := q.first.trans p.last.symm
        simpa only [ite_eq_left (Nat.le_refl m), ite_eq_right hn, h1, heq, Nat.zero_add] using q.step 0 ht
      · have hu : ¬ i ≤ m := by omega
        have hs : i-m < n := by omega
        have hj : i+1-m = (i-m)+1 := by omega
        simpa only [ite_eq_right hu, ite_eq_right hn, hj] using q.step (i-m) hs

def slice (p : Walk G a b n) (i j : Nat) (hij : i ≤ j) (hj : j ≤ n) :
    Walk G (p.point i) (p.point j) (j-i) := by
  refine ⟨fun t => p.point (i+t), by simp, ?_, ?_⟩
  · have h : i+(j-i) = j := by omega
    rw [h]
  · intro t ht
    have h : i+t < n := by omega
    simpa only [Nat.add_assoc] using p.step (i+t) h

theorem zero_endpoints (p : Walk G a b 0) : a = b :=
  p.first.symm.trans p.last

def reverse (p : Walk G a b n) : Walk G b a n := by
  refine ⟨fun i => p.point (n-i), ?_, ?_, ?_⟩
  · simpa only [Nat.sub_zero] using p.last
  · simpa only [Nat.sub_self] using p.first
  · intro i hi
    have hh : n-(i+1) < n := by omega
    have he : n-(i+1)+1 = n-i := by omega
    simpa only [he] using G.symm (p.step (n-(i+1)) hh)
end Walk

variable {V : Type u}

/-- Connectivity expressed using actual unweighted-edge walks. -/
def Connected (G : SimpleGraph V) : Prop :=
  ∀ a b : V, ∃ n : Nat, Nonempty (Walk G a b n)

/-- Shortest-walk distances plus an exact finite-length witness for every pair. -/
structure ShortestDistances (G : SimpleGraph V) where
  dist : V → V → Nat
  geodesic : ∀ a b, Walk G a b (dist a b)
  minimal : ∀ a b n, Walk G a b n → dist a b ≤ n

theorem smallest_witness (P : Nat → Prop) (n : Nat) (hn : P n) :
    ∃ m, P m ∧ ∀ j, P j → m ≤ j := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : ∃ m, m < n ∧ P m
    · obtain ⟨m,hm,hp⟩ := h
      exact ih m hm hp
    · exact ⟨n,hn,fun j hj => Nat.le_of_not_gt (fun h' => h ⟨j,h',hj⟩)⟩

theorem shortest_witness {G : SimpleGraph V} (hc : Connected G)
    (a b : V) : ∃ n, Nonempty (Walk G a b n) ∧
      ∀ m, Nonempty (Walk G a b m) → n ≤ m := by
  obtain ⟨n,hn⟩ := hc a b
  exact smallest_witness _ n hn

/-- Connected undirected graphs provide the shortest-distance data without
assuming any metric identities. -/
noncomputable def distancesOfConnected (G : SimpleGraph V)
    (hc : Connected G) : ShortestDistances G where
  dist := fun a b => (shortest_witness hc a b).choose
  geodesic := fun a b => Classical.choice (shortest_witness hc a b).choose_spec.1
  minimal := fun a b n p => (shortest_witness hc a b).choose_spec.2 n ⟨p⟩

namespace ShortestDistances
variable {G : SimpleGraph V} (M : ShortestDistances G)

theorem dist_self (a : V) : M.dist a a = 0 := by
  exact Nat.le_antisymm (M.minimal a a 0 (Walk.trivial G a)) (Nat.zero_le _)

theorem dist_eq_zero_iff (a b : V) : M.dist a b = 0 ↔ a = b := by
  constructor
  · intro h
    have p := M.geodesic a b
    rw [h] at p
    exact p.zero_endpoints
  · rintro rfl
    exact dist_self M a

theorem dist_symm (a b : V) : M.dist a b = M.dist b a :=
  Nat.le_antisymm
    (M.minimal a b _ (M.geodesic b a).reverse)
    (M.minimal b a _ (M.geodesic a b).reverse)

theorem dist_triangle (a b c : V) : M.dist a c ≤ M.dist a b+M.dist b c :=
  M.minimal a c _ ((M.geodesic a b).concat (M.geodesic b c))

theorem unique (N : ShortestDistances G) (a b : V) : M.dist a b = N.dist a b :=
  Nat.le_antisymm (M.minimal a b _ (N.geodesic a b)) (N.minimal a b _ (M.geodesic a b))

theorem geodesic_slice_eq (a b : V) (i j : Nat)
    (hij : i ≤ j) (hj : j ≤ M.dist a b) :
    let w := M.geodesic a b
    M.dist (w.point i) (w.point j) = j-i := by
  let w := M.geodesic a b
  change M.dist (w.point i) (w.point j) = j-i
  have hii : i ≤ M.dist a b := Nat.le_trans hij hj
  have uw := M.minimal _ _ _ (w.slice i j hij hj)
  have right := w.slice j (M.dist a b) hj (Nat.le_refl _)
  have left := w.slice 0 i (Nat.zero_le i) hii
  have middle := M.geodesic (w.point i) (w.point j)
  have c := (left.concat middle).concat right
  have cz := M.minimal _ _ _ c
  rw [w.first, w.last] at cz
  omega
end ShortestDistances

/-- An actual k-packing, with one index per selected vertex. -/
def IsPacking {G : SimpleGraph V} (M : ShortestDistances G)
    (k : Nat) {p : Nat} (f : Fin p → V) : Prop :=
  ∀ i j, i ≠ j → k < M.dist (f i) (f j)

theorem packing_injective {G : SimpleGraph V} (M : ShortestDistances G)
    {k p : Nat} {f : Fin p → V} (hf : IsPacking M k f) : Function.Injective f := by
  intro i j h
  by_cases he : i = j
  · exact he
  · have hh := hf i j he
    rw [h, M.dist_self] at hh
    exact (Nat.not_lt_zero _ hh).elim

/-- Exact packing number: a certified attaining packing and a universal cap. -/
structure ExactPacking {G : SimpleGraph V} (M : ShortestDistances G)
    (k p : Nat) : Prop where
  attained : ∃ f : Fin p → V, IsPacking M k f
  upper : ∀ n (f : Fin n → V), IsPacking M k f → n ≤ p

theorem exactPacking_pos {G : SimpleGraph V} (M : ShortestDistances G)
    {k p : Nat} (P : ExactPacking M k p) (v : V) : 1 ≤ p :=
  P.upper 1 (fun _ => v) (fun i j hij => (hij (Subsingleton.elim i j)).elim)

/-- The geodesic diameter bound with the exact step convention d>k. -/
theorem diameter_le_of_packing {G : SimpleGraph V} (M : ShortestDistances G)
    {k p : Nat} (P : ExactPacking M k p) (a b : V) :
    M.dist a b ≤ (k+1)*p-1 := by
  have hp := exactPacking_pos M P a
  have hpos : 0 < (k+1)*p := Nat.mul_pos (Nat.succ_pos k) (by omega)
  by_cases hw : (k+1)*p ≤ M.dist a b
  · let w := M.geodesic a b
    let f : Fin (p+1) → V := fun i => w.point ((k+1)*i.val)
    have step (i j : Fin (p+1)) (hij : i.val < j.val) :
        k < M.dist (f i) (f j) := by
      have hle : i.val ≤ j.val := by omega
      have hbound := Nat.mul_le_mul_left (k+1) hle
      have hjp : j.val ≤ p := by have hh := j.isLt; omega
      have hlast := Nat.le_trans (Nat.mul_le_mul_left (k+1) hjp) hw
      have hh := M.geodesic_slice_eq a b _ _ hbound hlast
      have hinc : i.val+1 ≤ j.val := by omega
      have hs := Nat.mul_le_mul_left (k+1) hinc
      rw [Nat.mul_add, Nat.mul_one] at hs
      change M.dist (f i) (f j) = (k+1)*j.val-(k+1)*i.val at hh
      omega
    have hpack : IsPacking M k f := by
      intro i j h
      have hne : i.val ≠ j.val := fun he => h (Fin.ext he)
      rcases Nat.lt_or_gt_of_ne hne with hij | hji
      · exact step _ _ hij
      · rw [M.dist_symm]
        exact step _ _ hji
    have hbad := P.upper (p+1) f hpack
    omega
  · omega

theorem finite_packing_bound {n p k : Nat} {G : SimpleGraph (Fin n)}
    (M : ShortestDistances G) (f : Fin p → Fin n) (h : IsPacking M k f) :
    p ≤ n := by
  have hf := packing_injective M h
  have hn : ((List.finRange p).map f).Nodup :=
    List.Pairwise.map f (fun a b ne e => ne (hf e)) (List.nodup_finRange p)
  have hs : (List.finRange p).map f ⊆ List.finRange n := fun {x} _ => List.mem_finRange x
  have hlen := hn.length_le_of_subset hs
  simpa only [List.length_map, List.length_finRange] using hlen

theorem largest_bounded_witness (P : Nat → Prop) (n : Nat)
    (h0 : P 0) : ∃ p, p ≤ n ∧ P p ∧ ∀ q, q ≤ n → P q → q ≤ p := by
  induction n with
  | zero => exact ⟨0,Nat.le_refl _,h0,fun q hq _ => hq⟩
  | succ n ih =>
    by_cases hn : P (n+1)
    · exact ⟨n+1,Nat.le_refl _,hn,fun q hq _ => hq⟩
    · obtain ⟨p,hp,hit,hu⟩ := ih
      refine ⟨p,Nat.le_trans hp (Nat.le_succ n),hit,?_⟩
      intro q hq hP
      have he : q ≠ n+1 := by intro e; exact hn (e ▸ hP)
      exact hu q (Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hq he)) hP

theorem finite_exact_packing_exists {n : Nat} {G : SimpleGraph (Fin n)}
    (M : ShortestDistances G) (k : Nat) : ∃ p, ExactPacking M k p := by
  let P (p : Nat) := ∃ f : Fin p → Fin n, IsPacking M k f
  have P0 : P 0 := ⟨Fin.elim0, fun i => Fin.elim0 i⟩
  obtain ⟨p,_,ha,hu⟩ := largest_bounded_witness P n P0
  refine ⟨p,⟨ha,?_⟩⟩
  exact fun q f hf => hu q (finite_packing_bound M f hf) ⟨f,hf⟩

theorem exact_packing_unique {G : SimpleGraph V} (M : ShortestDistances G)
    {k p q : Nat} (hp : ExactPacking M k p) (hq : ExactPacking M k q) :
    p = q := by
  obtain ⟨f,hf⟩ := hp.attained
  obtain ⟨g,hg⟩ := hq.attained
  exact Nat.le_antisymm (hq.upper p f hf) (hp.upper q g hg)

/-- Actual distance-packing number of a connected finite graph. -/
noncomputable def packingNumber {n : Nat} {G : SimpleGraph (Fin n)}
    (M : ShortestDistances G) (k : Nat) : Nat :=
  (finite_exact_packing_exists M k).choose

theorem packingNumber_is_exact {n : Nat} {G : SimpleGraph (Fin n)}
    (M : ShortestDistances G) (k : Nat) : ExactPacking M k (packingNumber M k) :=
  (finite_exact_packing_exists M k).choose_spec


end TriameterQ3Graph

/-! Exact four-terminal graph adapter using the published three-terminal
packing bound as an explicit dependency, not as a new Lean axiom. -/
namespace TriameterQ3Graph

open TriameterQ3Four
universe u
variable {V : Type u} {G : SimpleGraph V}

structure Terminals (V : Type u) where
  a : V
  b : V
  c : V
  d : V

def Terminals.Distinct (T : Terminals V) : Prop :=
  T.a ≠ T.b ∧ T.a ≠ T.c ∧ T.a ≠ T.d ∧
  T.b ≠ T.c ∧ T.b ≠ T.d ∧ T.c ≠ T.d

def distanceVector (M : ShortestDistances G) (T : Terminals V) : Edges :=
  ⟨M.dist T.a T.b, M.dist T.a T.c, M.dist T.a T.d,
   M.dist T.b T.c, M.dist T.b T.d, M.dist T.c T.d⟩

/-- Each of the four three-terminal inputs is exactly the scalar inequality
from Theorem 1.1 of Hak–Kozerenko, not a four-terminal conclusion. -/
def HKTheorem1Inputs (M : ShortestDistances G) (k p : Nat) : Prop :=
  ∀ a b c : V, M.dist a b+M.dist a c+M.dist b c ≤ 2*(k+1)*p+k-2

def excess (k p : Nat) : Nat := (k+1)*(p-1)

theorem radius_rewrite (k p : Nat) (hp : 1 ≤ p) :
    (k+1)*p-1 = k + excess k p ∧
    2*(k+1)*p+k-2 = 3*k + 2*excess k p := by
  have hq : (p-1)+1 = p := by omega
  have hb : (k+1)*p = excess k p + (k+1) := calc
    (k+1)*p = (k+1)*((p-1)+1) := congrArg ((k+1)*·) hq.symm
    _ = _ := by simp only [excess, Nat.mul_add, Nat.mul_one]
  rw [Nat.mul_assoc, hb]
  omega

theorem packing_distance_caps (M : ShortestDistances G) (T : Terminals V)
    {k p : Nat} (P : ExactPacking M k p) (src : HKTheorem1Inputs M k p) :
    DistanceCaps (k : Int) (excess k p : Int) (distanceVector M T) := by
  have hp := exactPacking_pos M P T.a
  obtain ⟨hD,hTriangle⟩ := radius_rewrite k p hp
  have bound (x y : V) : M.dist x y ≤ k + excess k p := by
    rw [← hD]
    exact diameter_le_of_packing M P x y
  have triangle (x y z : V) :
      M.dist x y + M.dist x z + M.dist y z ≤ 3*k + 2*excess k p := by
    rw [← hTriangle]
    exact src x y z
  have hab := bound T.a T.b
  have hac := bound T.a T.c
  have had := bound T.a T.d
  have hbc := bound T.b T.c
  have hbd := bound T.b T.d
  have hcd := bound T.c T.d
  have habc := triangle T.a T.b T.c
  have habd := triangle T.a T.b T.d
  have hacd := triangle T.a T.c T.d
  have hbcd := triangle T.b T.c T.d
  unfold DistanceCaps
  dsimp [distanceVector]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

structure Weights where
  a : Int
  b : Int
  c : Int
  d : Int

def Weights.Nonnegative (w : Weights) : Prop :=
  0 ≤ w.a ∧ 0 ≤ w.b ∧ 0 ≤ w.c ∧ 0 ≤ w.d

def weightedTerminalSum (M : ShortestDistances G) (T : Terminals V) (w : Weights) : Int :=
  dot (distanceVector M T) (terminalCoefficients w.a w.b w.c w.d)

def pairMass (w : Weights) : Int :=
  coefficientSum (terminalCoefficients w.a w.b w.c w.d)

def cutMass (w : Weights) : Int :=
  maxCut (terminalCoefficients w.a w.b w.c w.d)

/-- The a-terminal is always in the zero side; three bits classify the
remaining terminals. Every unordered bipartition occurs once. -/
def leftWeight (w : Weights) : Cut → Int
  | .c000 => w.a+w.b+w.c+w.d
  | .c001 => w.a+w.b+w.c
  | .c010 => w.a+w.b+w.d
  | .c011 => w.a+w.b
  | .c100 => w.a+w.c+w.d
  | .c101 => w.a+w.c
  | .c110 => w.a+w.d
  | .c111 => w.a

def rightWeight (w : Weights) : Cut → Int
  | .c000 => 0
  | .c001 => w.d
  | .c010 => w.c
  | .c011 => w.c+w.d
  | .c100 => w.b
  | .c101 => w.b+w.d
  | .c110 => w.b+w.c
  | .c111 => w.b+w.c+w.d

theorem cutCost_eq_mass_product (w : Weights) (b : Cut) :
    cutCost (terminalCoefficients w.a w.b w.c w.d) b = leftWeight w b * rightWeight w b := by
  cases b <;> simp only [cutCost, cutCosts, terminalCoefficients, leftWeight,
    rightWeight, Int.add_mul, Int.mul_add, Int.mul_zero] <;> ac_rfl

theorem cutMass_is_maximum (w : Weights) :
    (∀ b : Cut, leftWeight w b*rightWeight w b ≤ cutMass w) ∧
    ∃ b : Cut, leftWeight w b*rightWeight w b = cutMass w := by
  constructor
  · intro b
    rw [← cutCost_eq_mass_product]
    obtain ⟨a,b',c,d,e,f,g,h⟩ := maxCut_is_bound (terminalCoefficients w.a w.b w.c w.d)
    cases b <;> assumption
  · obtain ⟨b,h⟩ := maxCut_realized (terminalCoefficients w.a w.b w.c w.d)
    exact ⟨b, (cutCost_eq_mass_product w b).symm.trans h.symm⟩

/-- Upper result for native graph distances. The only imported mathematical
dependency is the exact three-terminal cap, exposed in the hypotheses. -/
theorem weighted_four_terminal_graph_upper (M : ShortestDistances G)
    (T : Terminals V) (w : Weights) (hw : w.Nonnegative)
    {k p : Nat} (P : ExactPacking M k p) (src : HKTheorem1Inputs M k p) :
    weightedTerminalSum M T w ≤ (k : Int)*pairMass w + (excess k p : Int)*cutMass w := by
  obtain ⟨ha,hb,hc,hd⟩ := hw
  exact four_terminal_product_bound (k : Int) (excess k p : Int) (distanceVector M T)
    w.a w.b w.c w.d ha hb hc hd (by omega) (packing_distance_caps M T P src)

/-- Literal supplied theorem on finite connected graphs of suitable order.
Its proof is the cited source/Theorem 1.1, not a declaration in this module. -/
def SourceHKTheorem1 : Prop :=
  ∀ (n : Nat) (G : SimpleGraph (Fin n)) (hc : Connected G) (k p : Nat),
    3 ≤ n → 0 < k → ExactPacking (distancesOfConnected G hc) k p →
      HKTheorem1Inputs (distancesOfConnected G hc) k p

/-- This shape is exactly the finite graph weighting with r=4. No distance
oracle, mysterious locality assumption or surrogate d is used. -/
theorem four_terminal_upper_from_source (source : SourceHKTheorem1)
    (n : Nat) (G : SimpleGraph (Fin n)) (hC : Connected G) (T : Terminals (Fin n))
    (_different : T.Distinct) (hn : 4 ≤ n) (k p : Nat) (hk : 0 < k)
    (P : ExactPacking (distancesOfConnected G hC) k p) (w : Weights) (hw : w.Nonnegative) :
    weightedTerminalSum (distancesOfConnected G hC) T w ≤
      (k : Int)*pairMass w + (excess k p : Int)*cutMass w :=
  weighted_four_terminal_graph_upper (distancesOfConnected G hC) T w hw P
    (source n G hC k p (by omega) hk P)

theorem Terminals.order_at_least_four {n : Nat} (T : Terminals (Fin n))
    (ht : T.Distinct) : 4 ≤ n := by
  rcases ht with ⟨hab,hac,had,hbc,hbd,hcd⟩
  have hl : [T.a,T.b,T.c,T.d].Nodup := by simp [hab,hac,had,hbc,hbd,hcd]
  have hs : [T.a,T.b,T.c,T.d] ⊆ List.finRange n := fun {x} _ => List.mem_finRange x
  have hh := hl.length_le_of_subset hs
  simpa only [List.length_cons, List.length_nil, List.length_finRange] using hh

/-- Source-shaped four-terminal inequality using the actual graph's
packing number, not a caller-chosen upper parameter. -/
theorem four_terminal_upper_native (source : SourceHKTheorem1)
    (n : Nat) (G : SimpleGraph (Fin n)) (hC : Connected G) (T : Terminals (Fin n))
    (different : T.Distinct) (k : Nat) (hk : 0 < k) (w : Weights) (hw : w.Nonnegative) :
    let M := distancesOfConnected G hC
    let p := packingNumber M k
    weightedTerminalSum M T w ≤ (k : Int)*pairMass w + (excess k p : Int)*cutMass w :=
  four_terminal_upper_from_source source n G hC T different
    (T.order_at_least_four different) k _ hk
    (packingNumber_is_exact (distancesOfConnected G hC) k) w hw

/-- The diameter bound alone gives the special packing-one regime. -/
theorem theorem1_for_packing_one (M : ShortestDistances G) (k : Nat)
    (P : ExactPacking M k 1) : HKTheorem1Inputs M k 1 := by
  intro a b c
  have hab := diameter_le_of_packing M P a b
  have hac := diameter_le_of_packing M P a c
  have hbc := diameter_le_of_packing M P b c
  simp only [Nat.mul_one] at *
  omega

/-- No source hypothesis is needed when the packing number is one. -/
theorem weighted_upper_packing_one (M : ShortestDistances G)
    (T : Terminals V) (w : Weights) (k : Nat) (P : ExactPacking M k 1)
    (hw : w.Nonnegative) :
    weightedTerminalSum M T w ≤ (k : Int)*pairMass w := by
  have h := weighted_four_terminal_graph_upper M T w hw P (theorem1_for_packing_one M k P)
  simpa [excess] using h

/-- An attaining graph need only certify the six distances: k on same-side
pairs and k+R on crossing pairs. This is the exact weighted score, not merely
a lower estimate. -/
theorem exact_score_of_cut_metric (M : ShortestDistances G) (T : Terminals V) (w : Weights)
    (k R : Int) (b : Cut)
    (h : distanceVector M T =
      let x := scaledCut R b
      ⟨k+x.ab,k+x.ac,k+x.ad,k+x.bc,k+x.bd,k+x.cd⟩) :
    weightedTerminalSum M T w =
      k*pairMass w + R*(leftWeight w b*rightWeight w b) := by
  have hc := scaledCut_dot R (terminalCoefficients w.a w.b w.c w.d) b
  rw [cutCost_eq_mass_product] at hc
  unfold weightedTerminalSum pairMass
  rw [h]
  dsimp
  unfold dot coefficientSum
  simp only [Int.add_mul, Int.mul_add]
  unfold dot at hc
  omega

end TriameterQ3Graph

/-! Direct proof of the numeric Hak–Kozerenko Theorem 1.1 inequality.
The source's parity/outer-and-residue argument is credited, while this
module uses only chosen terminal geodesics, not a surjective graph quotient. -/
namespace TriameterQ3Graph

universe u
variable {V : Type u} {G : SimpleGraph V}
variable (M : ShortestDistances G)

/-- A length-L geodesic section pointing inward from terminal a. -/
structure Arm (M : ShortestDistances G) (a : V) (L : Nat) where
  point : Nat → V
  near : ∀ x ≤ L, M.dist a (point x) = L-x
  along : ∀ x y, x ≤ y → y ≤ L → M.dist (point x) (point y) = y-x

def armOfGeodesic (a b : V) (L : Nat) (h : L ≤ M.dist a b) : Arm M a L := by
  let w := M.geodesic a b
  refine ⟨fun x => w.point (L-x), ?_, ?_⟩
  · intro x hx
    have he := M.geodesic_slice_eq a b 0 (L-x) (Nat.zero_le _) (by omega)
    change M.dist (w.point 0) (w.point (L-x)) = (L-x)-0 at he
    simpa only [w.first, Nat.sub_zero] using he
  · intro x y hxy hy
    have he := M.geodesic_slice_eq a b (L-y) (L-x) (by omega) (by omega)
    change M.dist (w.point (L-y)) (w.point (L-x)) = (L-x)-(L-y) at he
    rw [M.dist_symm]
    omega

theorem different_arms_lower {a b : V} {L U e : Nat} (A : Arm M a L) (B : Arm M b U)
    (hd : M.dist a b = L+U+e) (x y : Nat) (hx : x ≤ L) (hy : y ≤ U) :
    x+y+e ≤ M.dist (A.point x) (B.point y) := by
  have t0 := M.dist_triangle a (A.point x) b
  have t1 := M.dist_triangle (A.point x) (B.point y) b
  have hx' := A.near x hx
  have hy' := B.near y hy
  rw [M.dist_symm] at hy'
  omega

def positions (k L mark : Nat) := L/(k+1)+mark
def indexStep (mark : Nat) (i : Nat) := i+1-mark
def depth (k L mark i : Nat) := L%(k+1)+(k+1)*indexStep mark i

theorem depth_fits {k L mark : Nat} (i : Fin (positions k L mark)) :
    depth k L mark i.val ≤ L := by
  have hi := i.isLt
  unfold positions at hi
  have hq0 : (0 : Int) ≤ (L/(k+1) : Nat) := Int.natCast_nonneg _
  have hi' : indexStep mark i.val ≤ L/(k+1) := by unfold indexStep; omega
  have hm := Nat.mul_le_mul_left (k+1) hi'
  have hdiv := Nat.mod_add_div L (k+1)
  unfold depth
  omega

theorem depth_gap {k L mark : Nat} (hmark : mark ≤ 1)
    {i j : Nat} (hij : i < j) :
    depth k L mark i + (k+1) ≤ depth k L mark j := by
  have hi : indexStep mark i+1 ≤ indexStep mark j := by unfold indexStep; omega
  have hm := Nat.mul_le_mul_left (k+1) hi
  rw [Nat.mul_add, Nat.mul_one] at hm
  unfold depth
  omega

theorem depth_ge_mod (k L mark i : Nat) :
    L%(k+1) ≤ depth k L mark i := by unfold depth; omega

theorem depth_big_or_mark (k L mark i : Nat) (hm : mark ≤ 1) :
    k+1 ≤ depth k L mark i ∨ mark = 1 := by
  by_cases h : mark=1
  · exact Or.inr h
  · have hi : 1 ≤ indexStep mark i := by unfold indexStep; omega
    have he := Nat.mul_le_mul_left (k+1) hi
    rw [Nat.mul_one] at he
    unfold depth
    exact Or.inl (by omega)

def armSelect {a : V} {L : Nat} (A : Arm M a L) (k mark : Nat) :
    Fin (positions k L mark) → V :=
  fun i => A.point (depth k L mark i.val)

theorem arm_packs {a : V} {L k mark : Nat} (hm : mark ≤ 1)
    (A : Arm M a L) : IsPacking M k (armSelect M A k mark) := by
  intro i j hn
  have hne : i.val ≠ j.val := fun h => hn (Fin.ext h)
  have step (i j : Fin (positions k L mark)) (hij : i.val < j.val) :
      k < M.dist (armSelect M A k mark i) (armSelect M A k mark j) := by
    have hgap := depth_gap (k := k) (L := L) hm hij
    have hd := A.along (depth k L mark i.val) (depth k L mark j.val) (by omega) (depth_fits j)
    unfold armSelect
    omega
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact step _ _ h
  · rw [M.dist_symm]
    exact step _ _ h

theorem arm_cross {a b : V} {L U e k m n : Nat} (A : Arm M a L) (B : Arm M b U)
    (hL : M.dist a b = L+U+e) (hm : m ≤ 1) (hn : n ≤ 1)
    (hinner : m=1 → n=1 → k < L%(k+1)+U%(k+1)+e)
    (i : Fin (positions k L m)) (j : Fin (positions k U n)) :
    k < M.dist (armSelect M A k m i) (armSelect M B k n j) := by
  have hdist := different_arms_lower M A B hL _ _ (depth_fits i) (depth_fits j)
  have hx := depth_ge_mod k L m i.val
  have hy := depth_ge_mod k U n j.val
  unfold armSelect
  rcases depth_big_or_mark k L m i.val hm with h | he
  · omega
  · rcases depth_big_or_mark k U n j.val hn with h | hf
    · omega
    · have hh := hinner he hf
      omega

def appendIndex {p q : Nat} (f : Fin p → V) (g : Fin q → V)
    (i : Fin (p+q)) : V :=
  if h : i.val < p then f ⟨i.val,h⟩ else g ⟨i.val-p,by have ht := i.isLt; omega⟩

theorem appendPacking {k p q : Nat} (f : Fin p → V) (g : Fin q → V)
    (hf : IsPacking M k f) (hg : IsPacking M k g)
    (hcross : ∀ i j, k < M.dist (f i) (g j)) : IsPacking M k (appendIndex f g) := by
  intro i j h
  have hval : i.val ≠ j.val := fun he => h (Fin.ext he)
  unfold appendIndex
  split <;> split
  · rename_i hi hj
    exact hf _ _ (fun he => hval (congrArg (fun v : Fin p => v.val) he))
  · exact hcross _ _
  · rw [M.dist_symm]
    exact hcross _ _
  · rename_i hi hj
    apply hg
    intro he
    have hs := congrArg Fin.val he
    change i.val-p = j.val-p at hs
    omega

theorem threeArmPacking {a b c : V} {L U J e k p : Nat}
    (A : Arm M a L) (B : Arm M b U) (C : Arm M c J)
    (hab : M.dist a b = L+U+e) (hac : M.dist a c = L+J+e) (hbc : M.dist b c = U+J+e)
    (P : ExactPacking M k p) {m n o : Nat} (hm : m ≤ 1) (hn : n ≤ 1) (ho : o ≤ 1)
    (hi01 : m=1 → n=1 → k < L%(k+1)+U%(k+1)+e)
    (hi02 : m=1 → o=1 → k < L%(k+1)+J%(k+1)+e)
    (hi12 : n=1 → o=1 → k < U%(k+1)+J%(k+1)+e) :
    L/(k+1)+U/(k+1)+J/(k+1)+m+n+o ≤ p := by
  let f := armSelect M A k m
  let g := armSelect M B k n
  let h := armSelect M C k o
  have hAB := appendPacking M f g (arm_packs M hm A) (arm_packs M hn B)
    (arm_cross M A B hab hm hn hi01)
  have hC (i : Fin (positions k L m+positions k U n)) (j : Fin (positions k J o)) :
      k < M.dist (appendIndex f g i) (h j) := by
    unfold appendIndex
    split
    · exact arm_cross M A C hac hm ho hi02 _ _
    · exact arm_cross M B C hbc hn ho hi12 _ _
  have hp := P.upper _ (appendIndex (appendIndex f g) h)
    (appendPacking M _ h hAB (arm_packs M ho C) hC)
  unfold positions at hp
  omega

/-- Complete parity-adjusted arm lengths calculated directly from any
three distances satisfying the triangle inequalities. -/
theorem parity_arm_lengths (x y z : Nat) (h₀ : x ≤ y+z) (h₁ : y ≤ x+z) (h₂ : z ≤ x+y) :
    let e := (x+y+z)%2
    let L := (x+y-z)/2
    let U := (x+z-y)/2
    let J := (y+z-x)/2
    e ≤ 1 ∧ x=L+U+e ∧ y=L+J+e ∧ z=U+J+e := by
  exact ⟨by omega,by omega,by omega,by omega⟩

/-- The numeric part of Hak–Kozerenko Theorem 1.1. No classification of
equality triples, global projection, or graph-realization conclusion. -/
theorem triple_perimeter_packing_bound {k p : Nat} (P : ExactPacking M k p)
    (a b c : V) :
    M.dist a b + M.dist a c + M.dist b c + 2 ≤ 2*(k+1)*p+k := by
  let x := M.dist a b
  let y := M.dist a c
  let z := M.dist b c
  let e := (x+y+z)%2
  let L := (x+y-z)/2
  let U := (x+z-y)/2
  let J := (y+z-x)/2
  have h₀ : x ≤ y+z := by
    have ht := M.dist_triangle a c b
    rw [M.dist_symm c b] at ht
    exact ht
  have h₁ : y ≤ x+z := M.dist_triangle a b c
  have h₂ : z ≤ x+y := by
    have ht := M.dist_triangle b a c
    rw [M.dist_symm b a] at ht
    exact ht
  have heq : e ≤ 1 ∧ x=L+U+e ∧ y=L+J+e ∧ z=U+J+e := parity_arm_lengths x y z h₀ h₁ h₂
  obtain ⟨he,hx,hy,hz⟩ := heq
  have ha : L ≤ M.dist a b := by change L ≤ x; omega
  have hb : U ≤ M.dist b a := by rw [M.dist_symm]; change U ≤ x; omega
  have hc : J ≤ M.dist c a := by rw [M.dist_symm]; change J ≤ y; omega
  let A := armOfGeodesic M a b L ha
  let B := armOfGeodesic M b a U hb
  let C := armOfGeodesic M c a J hc
  let r := L%(k+1)
  let s := U%(k+1)
  let t := J%(k+1)
  let Q := L/(k+1)+U/(k+1)+J/(k+1)
  have hr : r ≤ k := Nat.le_of_lt_succ (Nat.mod_lt L (Nat.succ_pos k))
  have hs : s ≤ k := Nat.le_of_lt_succ (Nat.mod_lt U (Nat.succ_pos k))
  have ht : t ≤ k := Nat.le_of_lt_succ (Nat.mod_lt J (Nat.succ_pos k))
  have hSum : L+U+J = r+s+t+(k+1)*Q := by
    have dL := Nat.mod_add_div L (k+1)
    have dU := Nat.mod_add_div U (k+1)
    have dJ := Nat.mod_add_div J (k+1)
    dsimp [r,s,t,Q]
    simp only [Nat.mul_add]
    omega
  have hPer : x+y+z = 2*((k+1)*Q) + 2*(r+s+t)+3*e := by omega
  have pack {m n o : Nat} (hm : m ≤ 1) (hn : n ≤ 1) (ho : o ≤ 1)
      (h01 : m=1 → n=1 → k < r+s+e)
      (h02 : m=1 → o=1 → k < r+t+e)
      (h12 : n=1 → o=1 → k < s+t+e) : Q+m+n+o ≤ p :=
    threeArmPacking M A B C hx hy hz P hm hn ho h01 h02 h12
  have finish (b : Nat) (hb : Q+b ≤ p)
      (hsmall : 2*(r+s+t)+3*e+2 ≤ (2*(k+1))*b+k) :
      x+y+z+2 ≤ 2*(k+1)*p+k := by
    have hm := Nat.mul_le_mul_left (2*(k+1)) hb
    rw [Nat.mul_add, Nat.mul_assoc 2 (k+1) Q] at hm
    omega
  change x+y+z+2 ≤ 2*(k+1)*p+k
  by_cases h01 : k < r+s+e
  · by_cases h02 : k < r+t+e
    · by_cases h12 : k < s+t+e
      · apply finish 3
        · exact pack (m:=1) (n:=1) (o:=1) (by decide) (by decide) (by decide)
            (fun _ _ => h01) (fun _ _ => h02) (fun _ _ => h12)
        · omega
      · apply finish 2
        · exact pack (m:=1) (n:=1) (o:=0) (by decide) (by decide) (by decide)
            (fun _ _ => h01) (by omega) (by omega)
        · omega
    · apply finish 2
      · exact pack (m:=1) (n:=1) (o:=0) (by decide) (by decide) (by decide)
          (fun _ _ => h01) (by omega) (by omega)
      · omega
  · by_cases h02 : k < r+t+e
    · apply finish 2
      · exact pack (m:=1) (n:=0) (o:=1) (by decide) (by decide) (by decide)
          (by omega) (fun _ _ => h02) (by omega)
      · omega
    · by_cases h12 : k < s+t+e
      · apply finish 2
        · exact pack (m:=0) (n:=1) (o:=1) (by decide) (by decide) (by decide)
            (by omega) (by omega) (fun _ _ => h12)
        · omega
      · apply finish 1
        · exact pack (m:=1) (n:=0) (o:=0) (by decide) (by decide) (by decide)
            (by omega) (by omega) (by omega)
        · omega

end TriameterQ3Graph

/-! Verified graph-metric four-terminal upper bound with no extra source
premise: the credited numerical three-terminal inequality is proved in
TripleArmPacking directly from chosen geodesics. -/
namespace TriameterQ3Graph

open TriameterQ3Four
universe u

theorem hk_theorem1_numeric : SourceHKTheorem1 := by
  intro n G hC k p _ _ hP a b c
  have h := triple_perimeter_packing_bound (distancesOfConnected G hC) hP a b c
  omega

theorem weighted_four_terminal_upper {V : Type u} {G : SimpleGraph V}
    (M : ShortestDistances G) (T : Terminals V) (w : Weights) (hw : w.Nonnegative)
    {k p : Nat} (P : ExactPacking M k p) :
    weightedTerminalSum M T w ≤ (k : Int)*pairMass w + (excess k p : Int)*cutMass w := by
  apply weighted_four_terminal_graph_upper M T w hw P
  intro a b c
  have h := triple_perimeter_packing_bound M P a b c
  omega

/-- Exact graph distance, finite simple connected graph, four distinct
terminals, and its actual distance-k packing number, with no auxiliary cap
or imported mathematical hypothesis. The coefficients are integer weights. -/
theorem weighted_four_terminal_finite_graph_bound
    (n : Nat) (G : SimpleGraph (Fin n)) (hC : Connected G) (T : Terminals (Fin n))
    (different : T.Distinct) (k : Nat) (hk : 0 < k) (w : Weights) (hw : w.Nonnegative) :
    let M := distancesOfConnected G hC
    let p := packingNumber M k
    weightedTerminalSum M T w ≤ (k : Int)*pairMass w + (excess k p : Int)*cutMass w :=
  four_terminal_upper_native hk_theorem1_numeric n G hC T different k hk w hw

/-- A coefficient-free integral certificate for the critical graph-derived
excesses: across all eight cuts, the actual six edge excesses are bounded
by the nonnegative integer cut mass marginals, after doubling. -/
theorem graph_cut_certificate {V : Type u} {G : SimpleGraph V}
    (M : ShortestDistances G) (T : Terminals V) {k p : Nat} (P : ExactPacking M k p) :
    ∃ a : Atoms, AtomNonneg a ∧ mass a = 2*(excess k p : Int) ∧
      Below (Double (clipped (k : Int) (distanceVector M T))) (marginals a) := by
  have hc : HKTheorem1Inputs M k p := by
    intro a b c
    have h := triple_perimeter_packing_bound M P a b c
    omega
  have hs := packing_distance_caps M T P hc
  have hR : 0 ≤ (excess k p : Int) := Int.natCast_nonneg _
  rcases hs with ⟨ab, ac, ad, bc, bd, cd, abc, abd, acd, bcd⟩
  have feasible : Feasible (excess k p : Int) (clipped (k : Int) (distanceVector M T)) := by
    unfold Feasible
    dsimp [clipped]
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega
  exact domination_by_cut_distribution (excess k p : Int) _ feasible

end TriameterQ3Graph

/-! Finite trunk with four terminal arms and odd-parity first-layer cliques. -/
namespace TriameterQ3Attainment
open TriameterQ3Graph TriameterQ3Four

abbrev Vertex (L H : Nat) := Fin (L+1) ⊕ (Fin 4 × Fin H)

def delta (a b : Nat) : Nat := a-b+(b-a)

theorem delta_symm (a b : Nat) : delta a b = delta b a := by
  unfold delta
  omega

theorem delta_triangle (a b c : Nat) : delta a c ≤ delta a b+delta b c := by
  unfold delta
  omega

theorem delta_step (a b : Nat) : delta a (b+1) ≤ delta a b+1 := by
  unfold delta
  omega

def treeDist {L H : Nat} (anchor : Fin 4 → Fin (L+1)) (e : Nat) :
    Vertex L H → Vertex L H → Nat
  | .inl x, .inl y => delta x.val y.val
  | .inl x, .inr (a,d) => delta x.val (anchor a).val + (d.val+1)
  | .inr (a,d), .inl y => delta (anchor a).val y.val + (d.val+1)
  | .inr (a,d), .inr (b,f) =>
      if a = b then delta d.val f.val
      else delta (anchor a).val (anchor b).val + (d.val+1) + (f.val+1) -
        (if anchor a = anchor b then e else 0)

theorem treeDist_symm {L H : Nat} (anchor : Fin 4 → Fin (L+1)) (e : Nat)
    (x y : Vertex L H) : treeDist anchor e x y = treeDist anchor e y x := by
  rcases x with x | ⟨a,d⟩ <;> rcases y with y | ⟨b,f⟩
  · exact delta_symm _ _
  · simp only [treeDist, delta_symm x.val (anchor b).val]
  · simp only [treeDist, delta_symm (anchor a).val y.val]
  · simp only [treeDist, eq_comm (a := b), eq_comm (a := anchor b), delta_symm f.val d.val,
      delta_symm (anchor b).val (anchor a).val]
    split <;> omega

theorem treeDist_self {L H : Nat} (anchor : Fin 4 → Fin (L+1)) (e : Nat)
    (x : Vertex L H) : treeDist anchor e x x = 0 := by
  rcases x with x | ⟨a,d⟩ <;> simp [treeDist, delta]

theorem correction_symm {L : Nat} (anchor : Fin 4 → Fin (L+1)) (e : Nat)
    (a b : Fin 4) : (if anchor a = anchor b then e else 0) =
      (if anchor b = anchor a then e else 0) := by
  by_cases h : anchor a = anchor b
  · exact congrArg (fun n : Nat => n) ((ite_eq_left h).trans (ite_eq_left h.symm).symm)
  · exact (ite_eq_right h).trans (ite_eq_right (Ne.symm h)).symm

theorem treeDist_triangle {L H : Nat} (anchor : Fin 4 → Fin (L+1))
    (e : Nat) (he : e ≤ 1) (x y z : Vertex L H) :
    treeDist anchor e x z ≤ treeDist anchor e x y+treeDist anchor e y z := by
  rcases x with x | ⟨a,d⟩ <;> rcases y with y | ⟨b,f⟩ <;> rcases z with z | ⟨c,g⟩
  · exact delta_triangle _ _ _
  · have ha := delta_triangle x.val y.val (anchor c).val
    simp only [treeDist]
    omega
  · have ha := delta_triangle x.val (anchor b).val z.val
    simp only [treeDist]
    omega
  · by_cases hbc : b = c
    · subst c
      simp [treeDist, delta]
      omega
    · have ha := delta_triangle x.val (anchor b).val (anchor c).val
      simp only [treeDist, ite_eq_right hbc]
      split <;> omega
  · have ha := delta_triangle (anchor a).val y.val z.val
    simp only [treeDist]
    omega
  · by_cases hac : a = c
    · subst c
      simp [treeDist, delta]
      omega
    · have ha := delta_triangle (anchor a).val y.val (anchor c).val
      simp only [treeDist, ite_eq_right hac]
      omega
  · by_cases hab : a = b
    · subst b
      simp [treeDist, delta]
      omega
    · have ha := delta_triangle (anchor a).val (anchor b).val z.val
      simp only [treeDist, ite_eq_right hab]
      split <;> omega
  · by_cases hab : a = b
    · subst b
      by_cases hac : a = c
      · subst c
        simpa [treeDist] using delta_triangle d.val f.val g.val
      · simp only [treeDist, ite_eq_right hac, ↓reduceIte]
        unfold delta
        omega
    · by_cases hbc : b = c
      · subst c
        simp only [treeDist, ite_eq_right hab, ↓reduceIte]
        unfold delta
        omega
      · by_cases hac : a = c
        · subst c
          have hba : b ≠ a := Ne.symm hab
          simp only [treeDist, ite_eq_right hab, ite_eq_right hba, ↓reduceIte]
          rw [← correction_symm anchor e a b]
          by_cases hh : anchor a = anchor b <;> simp [hh, delta] <;> omega
        · have ha := delta_triangle (anchor a).val (anchor b).val (anchor c).val
          simp only [treeDist, ite_eq_right hab, ite_eq_right hbc, ite_eq_right hac]
          repeat' first | split
          all_goals omega

def graph {L H : Nat} (anchor : Fin 4 → Fin (L+1)) (e : Nat) :
    SimpleGraph (Vertex L H) where
  adj x y := treeDist anchor e x y = 1
  symm := fun {x y} h => (treeDist_symm anchor e y x).trans h
  loopless := fun x h => by rw [treeDist_self] at h; contradiction

theorem lower_of_walk {L H : Nat} (anchor : Fin 4 → Fin (L+1)) (e : Nat)
    (he : e ≤ 1) {x y : Vertex L H} {n : Nat} (w : Walk (graph anchor e) x y n) :
    treeDist anchor e x y ≤ n := by
  have step (i : Nat) (hi : i ≤ n) : treeDist anchor e (w.point 0) (w.point i) ≤ i := by
    induction i with
    | zero => simp [treeDist_self]
    | succ i ih =>
      have hi' : i < n := by omega
      have ht := treeDist_triangle anchor e he (w.point 0) (w.point i) (w.point (i+1))
      have hs := w.step i hi'
      change treeDist anchor e (w.point i) (w.point (i+1)) = 1 at hs
      have hp := ih (by omega)
      omega
  simpa only [w.first,w.last] using step n (Nat.le_refl n)

end TriameterQ3Attainment

namespace TriameterQ3Attainment
open TriameterQ3Graph TriameterQ3Four

def unit {V : Type} {G : SimpleGraph V} {a b : V} (h : G.adj a b) :
    Walk G a b 1 := by
  refine ⟨fun i => if i = 0 then a else b,by simp,by simp,?_⟩
  intro i hi
  have e : i = 0 := by omega
  subst i
  simpa using h

def segmentUp {V : Type} {G : SimpleGraph V} {N : Nat}
    (line : Fin (N+1) → V)
    (edge : ∀ i : Nat, ∀ h : i < N,
      G.adj (line ⟨i,by omega⟩) (line ⟨i+1,by omega⟩))
    (a b : Fin (N+1)) (hab : a.val ≤ b.val) :
    Walk G (line a) (line b) (b.val-a.val) := by
  refine ⟨fun j => if h : a.val+j ≤ N then line ⟨a.val+j,by omega⟩ else line b, ?_, ?_, ?_⟩
  · have ha : a.val ≤ N := by omega
    simp [ha]
  · have hh : a.val+(b.val-a.val) = b.val := by omega
    have hb : b.val ≤ N := by omega
    simp [hh,hb]
  · intro i hi
    have hl : a.val+i < N := by omega
    have hr : a.val+(i+1) ≤ N := by omega
    have hs : a.val+i ≤ N := by omega
    simpa only [dite_eq_left hs,dite_eq_left hr,Nat.add_assoc] using edge _ hl

def segment {V : Type} {G : SimpleGraph V} {N : Nat}
    (line : Fin (N+1) → V)
    (edge : ∀ i : Nat, ∀ h : i < N,
      G.adj (line ⟨i,by omega⟩) (line ⟨i+1,by omega⟩)) (a b : Fin (N+1)) :
    Walk G (line a) (line b) (delta a.val b.val) := by
  by_cases h : a.val ≤ b.val
  · have hn : delta a.val b.val = b.val-a.val := by unfold delta; omega
    rw [hn]
    exact segmentUp line edge a b h
  · have hn : delta a.val b.val = a.val-b.val := by unfold delta; omega
    rw [hn]
    exact (segmentUp line edge b a (by omega)).reverse

def branch {L H : Nat} (anchor : Fin 4 → Fin (L+1)) (a : Fin 4)
    (j : Fin (H+1)) : Vertex L H :=
  if h : j.val = 0 then .inl (anchor a) else .inr (a,⟨j.val-1,by omega⟩)

def branchZero (H : Nat) : Fin (H+1) := ⟨0,by omega⟩
def branchDepth {H : Nat} (d : Fin H) : Fin (H+1) := ⟨d.val+1,by omega⟩

@[simp] theorem branch_zero {L H : Nat} (anchor : Fin 4 → Fin (L+1)) (a : Fin 4) :
    branch anchor a (branchZero H) = .inl (anchor a) := by
  rfl

@[simp] theorem branch_depth {L H : Nat} (anchor : Fin 4 → Fin (L+1)) (a : Fin 4) (d : Fin H) :
    branch anchor a (branchDepth d) = .inr (a,d) := by
  simp [branch,branchDepth]

def trunkWalk {L H : Nat} (anchor : Fin 4 → Fin (L+1)) (e : Nat)
    (a b : Fin (L+1)) :
    Walk (graph (H:=H) anchor e) (.inl a) (.inl b) (delta a.val b.val) := by
  apply segment Sum.inl _ a b
  intro i hi
  change delta i (i+1) = 1
  unfold delta
  omega

def branchWalk {L H : Nat} (anchor : Fin 4 → Fin (L+1)) (e : Nat) (a : Fin 4)
    (i j : Fin (H+1)) :
    Walk (graph anchor e) (branch anchor a i) (branch anchor a j) (delta i.val j.val) := by
  apply segment (branch anchor a) _ i j
  intro t ht
  by_cases h : t = 0
  · subst t
    change treeDist anchor e (branch anchor a ⟨0,_⟩) (branch anchor a ⟨1,_⟩) = 1
    simp [branch,treeDist,delta]
  · change treeDist anchor e (branch anchor a ⟨t,_⟩) (branch anchor a ⟨t+1,_⟩) = 1
    simp [branch,h,treeDist,delta]
    omega

def rootToArm {L H : Nat} (anchor : Fin 4 → Fin (L+1)) (e : Nat)
    (a : Fin 4) (d : Fin H) :
    Walk (graph anchor e) (.inl (anchor a)) (.inr (a,d)) (d.val+1) := by
  have h0 : delta (branchZero H).val (branchDepth d).val = d.val+1 := by
    simp [branchZero,branchDepth,delta]
  simpa only [branch_zero,branch_depth,h0] using
    branchWalk anchor e a (branchZero H) (branchDepth d)

def sameArm {L H : Nat} (anchor : Fin 4 → Fin (L+1)) (e : Nat)
    (a : Fin 4) (d f : Fin H) :
    Walk (graph anchor e) (.inr (a,d)) (.inr (a,f)) (delta d.val f.val) := by
  have hd : delta (branchDepth d).val (branchDepth f).val = delta d.val f.val := by
    change delta (d.val+1) (f.val+1) = delta d.val f.val
    unfold delta
    omega
  simpa only [branch_depth,hd] using
    branchWalk anchor e a (branchDepth d) (branchDepth f)

def generalThroughRoots {L H : Nat} (anchor : Fin 4 → Fin (L+1)) (e : Nat)
    (a b : Fin 4) (d f : Fin H) :
    Walk (graph anchor e) (.inr (a,d)) (.inr (b,f))
      (delta (anchor a).val (anchor b).val+(d.val+1)+(f.val+1)) := by
  have hw := (((rootToArm anchor e a d).reverse).concat
      (trunkWalk (H:=H) anchor e (anchor a) (anchor b))).concat (rootToArm anchor e b f)
  have hh : (d.val+1)+delta (anchor a).val (anchor b).val+(f.val+1) =
      delta (anchor a).val (anchor b).val+(d.val+1)+(f.val+1) := by omega
  rw [←hh]
  exact hw

def oddShortcut {L H : Nat} (anchor : Fin 4 → Fin (L+1))
    (a b : Fin 4) (d f : Fin H) (hab : a ≠ b) (he : anchor a = anchor b) :
    Walk (graph anchor 1) (.inr (a,d)) (.inr (b,f)) ((d.val+1)+(f.val+1)-1) := by
  have hh : 0 < H := by have h := d.isLt; omega
  let zero : Fin H := ⟨0,hh⟩
  have hedge : (graph anchor 1).adj (.inr (a,zero)) (.inr (b,zero)) := by
    change treeDist anchor 1 (.inr (a,zero)) (.inr (b,zero)) = 1
    simp [treeDist,hab,he,zero,delta]
  have hp := ((sameArm anchor 1 a d zero).concat (unit hedge)).concat
      (sameArm anchor 1 b zero f)
  have hlen : delta d.val zero.val + 1 + delta zero.val f.val =
      (d.val+1)+(f.val+1)-1 := by
    simp [zero,delta]
  rw [←hlen]
  exact hp

def realizeWalk {L H : Nat} (anchor : Fin 4 → Fin (L+1)) (e : Nat) (he : e ≤ 1)
    (x y : Vertex L H) : Walk (graph anchor e) x y (treeDist anchor e x y) := by
  rcases x with x | ⟨a,d⟩ <;> rcases y with y | ⟨b,f⟩
  · exact trunkWalk anchor e x y
  · exact (trunkWalk anchor e x (anchor b)).concat (rootToArm anchor e b f)
  · rw [treeDist_symm]
    exact ((trunkWalk anchor e y (anchor a)).concat (rootToArm anchor e a d)).reverse
  · by_cases hab : a = b
    · subst b
      simpa [treeDist] using sameArm anchor e a d f
    · by_cases ha : anchor a = anchor b
      · by_cases hz : e = 0
        · subst e
          simpa [treeDist,hab] using generalThroughRoots anchor 0 a b d f
        · have h1 : e = 1 := by omega
          subst e
          simpa [treeDist,hab,ha,delta] using oddShortcut anchor a b d f hab ha
      · simpa [treeDist,hab,ha] using generalThroughRoots anchor e a b d f

/-- The displayed coordinate formula is the actual shortest-walk metric,
not merely a metric lower bound on the resulting unweighted graph. -/
def exactDistances {L H : Nat} (anchor : Fin 4 → Fin (L+1)) (e : Nat) (he : e ≤ 1) :
    ShortestDistances (graph (H:=H) anchor e) where
  dist := treeDist anchor e
  geodesic := realizeWalk anchor e he
  minimal := fun _ _ _ => lower_of_walk anchor e he

theorem graph_connected {L H : Nat} (anchor : Fin 4 → Fin (L+1)) (e : Nat) (he : e ≤ 1) :
    Connected (graph (H:=H) anchor e) :=
  fun x y => ⟨_,⟨realizeWalk anchor e he x y⟩⟩

end TriameterQ3Attainment

namespace TriameterQ3Attainment
open TriameterQ3Graph TriameterQ3Four

def cap {L H : Nat} (anchor : Fin 4 → Fin (L+1)) (h : Nat) (c : Fin (L+1)) :
    Vertex L H → Prop
  | .inl t => delta t.val c.val ≤ h
  | .inr (a,_) => anchor a = c

theorem cap_diameter {L H : Nat} (anchor : Fin 4 → Fin (L+1)) (h e k : Nat)
    (hk : 2*h+e = k) (hH : H ≤ h+e) (c : Fin (L+1)) (x y : Vertex L H)
    (hx : cap anchor h c x) (hy : cap anchor h c y) :
    treeDist anchor e x y ≤ k := by
  rcases x with x | ⟨a,d⟩ <;> rcases y with y | ⟨b,f⟩
  · have hu := delta_triangle x.val c.val y.val
    have hb := delta_symm c.val y.val
    change delta x.val c.val ≤ h at hx
    change delta y.val c.val ≤ h at hy
    change delta x.val y.val ≤ k
    omega
  · change delta x.val c.val ≤ h at hx
    change anchor b = c at hy
    rw [treeDist, hy]
    omega
  · change anchor a = c at hx
    change delta y.val c.val ≤ h at hy
    rw [treeDist, hx, delta_symm]
    omega
  · change anchor a = c at hx
    change anchor b = c at hy
    by_cases hab : a = b
    · subst b
      simp [treeDist,delta]
      omega
    · simp [treeDist,hab,hx,hy,delta]
      omega

def leftEnd (L : Nat) : Fin (L+1) := ⟨0,by omega⟩
def rightEnd (L : Nat) : Fin (L+1) := ⟨L,by omega⟩

def color {L H : Nat} (anchor : Fin 4 → Fin (L+1)) (h k q : Nat) :
    Vertex L H → Nat
  | .inl t =>
    if t.val ≤ h then 0
    else if L-t.val ≤ h then q+1
    else 1+(t.val-h-1)/(k+1)
  | .inr (a,_) => if anchor a = leftEnd L then 0 else q+1

theorem interior_quotient {L h k q t : Nat} (hL : L = 2*h+1+(k+1)*q)
    (hleft : ¬ t ≤ h) (hright : ¬ L-t ≤ h) :
    (t-h-1)/(k+1) < q := by
  apply (Nat.div_lt_iff_lt_mul (by omega : 0 < k+1)).2
  rw [Nat.mul_comm]
  omega

theorem color_bounded {L H : Nat} (anchor : Fin 4 → Fin (L+1)) (h k q : Nat)
    (hL : L = 2*h+1+(k+1)*q) (x : Vertex L H) : color anchor h k q x < q+2 := by
  rcases x with t | ⟨a,d⟩
  · simp only [color]
    split
    · omega
    · rename_i hleft
      split
      · omega
      · rename_i hright
        have hh := interior_quotient hL hleft hright
        omega
  · simp only [color]
    split <;> omega

theorem color_zero_cap {L H : Nat} (anchor : Fin 4 → Fin (L+1))
    (h k q : Nat) (x : Vertex L H) (hx : color anchor h k q x = 0) :
    cap anchor h (leftEnd L) x := by
  rcases x with t | ⟨a,d⟩
  · simp only [color] at hx
    simp only [cap,leftEnd,delta, Nat.sub_zero, Nat.zero_sub,Nat.add_zero]
    split at hx
    · assumption
    · split at hx
      · omega
      · have hh : 0 < 1+(t.val-h-1)/(k+1) := by
          rw [Nat.add_comm]
          exact Nat.zero_lt_succ _
        omega
  · simp only [color] at hx
    split at hx
    · exact ‹anchor a = leftEnd L›
    · omega

theorem color_last_cap {L H : Nat} (anchor : Fin 4 → Fin (L+1))
    (ends : ∀ a, anchor a = leftEnd L ∨ anchor a = rightEnd L) (h k q : Nat)
    (hL : L = 2*h+1+(k+1)*q) (x : Vertex L H) (hx : color anchor h k q x = q+1) :
    cap anchor h (rightEnd L) x := by
  rcases x with t | ⟨a,d⟩
  · simp only [color] at hx
    simp only [cap,rightEnd,delta]
    split at hx
    · omega
    · rename_i hleft
      split at hx
      · omega
      · rename_i hright
        have hh := interior_quotient hL hleft hright
        omega
  · simp only [color] at hx
    split at hx
    · omega
    · rename_i hnot
      exact (ends a).resolve_left hnot

theorem color_interior {L H : Nat} (anchor : Fin 4 → Fin (L+1))
    (h k q : Nat) (x : Vertex L H)
    (hz : color anchor h k q x ≠ 0) (hl : color anchor h k q x ≠ q+1) :
    ∃ t : Fin (L+1), x = .inl t ∧ h < t.val ∧
      color anchor h k q x = 1+(t.val-h-1)/(k+1) := by
  rcases x with t | ⟨a,d⟩
  · refine ⟨t,rfl,?_,?_⟩
    · by_cases hle : t.val ≤ h
      · simp [color,hle] at hz
      · omega
    · change (if t.val ≤ h then 0 else if L-t.val ≤ h then q+1 else
          1+(t.val-h-1)/(k+1)) = _
      split
      · rename_i ht
        exact (hz (by simp [color,ht])).elim
      · rename_i ht
        split
        · rename_i hr
          exact (hl (by simp [color,ht,hr])).elim
        · rfl
  · simp only [color] at hz hl
    split at hz
    · exact (hz rfl).elim
    · rename_i he
      simp [he] at hl

theorem within_bucket {k u v : Nat} (hu : u/(k+1) = v/(k+1)) :
    delta u v ≤ k := by
  have hfu := Nat.mod_add_div u (k+1)
  have hfv := Nat.mod_add_div v (k+1)
  have hum := Nat.mod_lt u (by omega : 0 < k+1)
  have hvm := Nat.mod_lt v (by omega : 0 < k+1)
  rw [hu] at hfu
  unfold delta
  omega

theorem color_diameter {L H : Nat} (anchor : Fin 4 → Fin (L+1))
    (ends : ∀ a, anchor a = leftEnd L ∨ anchor a = rightEnd L) (h e k q : Nat)
    (hL : L = 2*h+1+(k+1)*q) (hk : 2*h+e = k) (hH : H ≤ h+e)
    (x y : Vertex L H) (hxy : color anchor h k q x = color anchor h k q y) :
    treeDist anchor e x y ≤ k := by
  by_cases hz : color anchor h k q x = 0
  · exact cap_diameter anchor h e k hk hH _ _ _
      (color_zero_cap anchor h k q x hz)
      (color_zero_cap anchor h k q y (hxy.symm.trans hz))
  · by_cases hl : color anchor h k q x = q+1
    · exact cap_diameter anchor h e k hk hH _ _ _
        (color_last_cap anchor ends h k q hL x hl)
        (color_last_cap anchor ends h k q hL y (hxy.symm.trans hl))
    · obtain ⟨x,rfl,hx,ex⟩ := color_interior anchor h k q x hz hl
      obtain ⟨y,rfl,hy,ey⟩ := color_interior anchor h k q y
        (fun t => hz (hxy.trans t)) (fun t => hl (hxy.trans t))
      have hEq : (x.val-h-1)/(k+1) = (y.val-h-1)/(k+1) := by omega
      have hb := within_bucket hEq
      simp only [treeDist]
      unfold delta at *
      omega

theorem fin_injection_bound {p q : Nat} (f : Fin p → Fin q)
    (hf : Function.Injective f) : p ≤ q := by
  have hn : ((List.finRange p).map f).Nodup :=
    List.Pairwise.map f (fun a b ne e => ne (hf e)) (List.nodup_finRange p)
  have hs : (List.finRange p).map f ⊆ List.finRange q := fun {x} _ => List.mem_finRange x
  have hlen := hn.length_le_of_subset hs
  simpa only [List.length_map,List.length_finRange] using hlen

theorem packing_from_distance {V : Type} {G : SimpleGraph V} (M : ShortestDistances G)
    (k p : Nat) (a b : V) (hab : (k+1)*(p-1) ≤ M.dist a b) :
    ∃ f : Fin p → V, IsPacking M k f := by
  let w := M.geodesic a b
  let f : Fin p → V := fun i => w.point ((k+1)*i.val)
  refine ⟨f,?_⟩
  have step (i j : Fin p) (hij : i.val < j.val) : k < M.dist (f i) (f j) := by
    have hi : i.val+1 ≤ j.val := by omega
    have hle : i.val ≤ j.val := by omega
    have hj : j.val ≤ p-1 := by omega
    have hs := Nat.mul_le_mul_left (k+1) hi
    rw [Nat.mul_add,Nat.mul_one] at hs
    have ht := Nat.le_trans (Nat.mul_le_mul_left (k+1) hj) hab
    have hd := M.geodesic_slice_eq a b _ _ (Nat.mul_le_mul_left (k+1) hle) ht
    change M.dist (f i) (f j) = _ at hd
    omega
  intro i j hij
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hne with hij' | hji'
  · exact step i j hij'
  · rw [M.dist_symm]
    exact step j i hji'

theorem packing_upper_by_coloring {V : Type} {G : SimpleGraph V}
    (M : ShortestDistances G) (k p : Nat) (f : V → Fin p)
    (hf : ∀ x y, f x = f y → M.dist x y ≤ k) :
    ∀ s (g : Fin s → V), IsPacking M k g → s ≤ p := by
  intro s g h
  refine fin_injection_bound (fun i => f (g i)) ?_
  intro i j he
  by_cases hne : i = j
  · exact hne
  · exact (Nat.not_lt_of_ge (hf (g i) (g j) he) (h i j hne)).elim

theorem exact_packing_many {L H : Nat} (anchor : Fin 4 → Fin (L+1))
    (ends : ∀ a, anchor a = leftEnd L ∨ anchor a = rightEnd L)
    (h e k q : Nat) (he : e ≤ 1) (hL : L = 2*h+1+(k+1)*q)
    (hk : 2*h+e = k) (hH : H ≤ h+e)
    (a b : Vertex L H) (hab : (k+1)*(q+2-1) ≤ treeDist anchor e a b) :
    ExactPacking (exactDistances (H:=H) anchor e he) k (q+2) := by
  constructor
  · exact packing_from_distance _ k (q+2) a b hab
  · refine packing_upper_by_coloring _ k (q+2)
      (fun x => ⟨color anchor h k q x,color_bounded anchor h k q hL x⟩) ?_
    intro x y heq
    exact color_diameter anchor ends h e k q hL hk hH x y (congrArg Fin.val heq)

theorem exact_packing_one {L H : Nat} (anchor : Fin 4 → Fin (L+1))
    (h e k : Nat) (he : e ≤ 1) (hk : 2*h+e = k) (hH : H ≤ h+e)
    (c : Fin (L+1)) (all : ∀ x : Vertex L H, cap anchor h c x) :
    ExactPacking (exactDistances (H:=H) anchor e he) k 1 := by
  constructor
  · exact ⟨fun _ => .inl c,fun i j hij => (hij (Subsingleton.elim i j)).elim⟩
  · refine packing_upper_by_coloring _ k 1 (fun _ => 0) ?_
    intro x y _
    exact cap_diameter anchor h e k hk hH c x y (all x) (all y)

end TriameterQ3Attainment

namespace TriameterQ3Attainment
open TriameterQ3Graph TriameterQ3Four

abbrev order (L H : Nat) := L+1+H*4

def encode {L H : Nat} : Vertex L H → Fin (order L H)
  | .inl t => ⟨t.val,by have h := t.isLt; unfold order; omega⟩
  | .inr (a,d) => ⟨L+1+H*a.val+d.val,by
      have ha : a.val+1 ≤ 4 := by have h := a.isLt; omega
      have hm := Nat.mul_le_mul_left H ha
      rw [Nat.mul_add,Nat.mul_one] at hm
      have hd := d.isLt
      unfold order
      omega⟩

def decode {L H : Nat} (t : Fin (order L H)) : Vertex L H :=
  if h : t.val < L+1 then .inl ⟨t.val,h⟩
  else
    let r := t.val-(L+1)
    have hr : r < H*4 := by have ht := t.isLt; unfold order at ht; dsimp [r]; omega
    have hp : 0 < H := by omega
    .inr (⟨r/H, (Nat.div_lt_iff_lt_mul hp).2 (by rw [Nat.mul_comm]; exact hr)⟩,
      ⟨r%H,Nat.mod_lt r hp⟩)

theorem encode_decode {L H : Nat} (t : Fin (order L H)) :
    encode (decode t) = t := by
  classical
  unfold decode
  split
  · apply Fin.ext
    rfl
  · rename_i hn
    have hh := Nat.mod_add_div (t.val-(L+1)) H
    apply Fin.ext
    change L+1+H*((t.val-(L+1))/H)+(t.val-(L+1))%H = t.val
    omega

theorem decode_encode {L H : Nat} (t : Vertex L H) :
    decode (encode t) = t := by
  classical
  rcases t with t | ⟨a,d⟩
  · unfold decode
    have h : (encode (H:=H) (.inl t)).val < L+1 := t.isLt
    rw [dite_eq_left h]
    rfl
  · unfold decode
    have hn : ¬ (encode (L:=L) (.inr (a,d))).val < L+1 := by
      change ¬ L+1+H*a.val+d.val < L+1
      omega
    rw [dite_eq_right hn]
    have hh : L+1 + H*a.val + d.val - (L+1) = d.val+a.val*H := by
      rw [Nat.mul_comm a.val H]
      omega
    have hH : 0 < H := by have h := d.isLt; omega
    have hd : d.val/H = 0 := Nat.div_eq_of_lt d.isLt
    apply congrArg Sum.inr
    apply Prod.ext
    · apply Fin.ext
      change (L+1+H*a.val+d.val-(L+1))/H = a.val
      rw [hh,Nat.add_mul_div_right _ _ hH,hd,Nat.zero_add]
    · apply Fin.ext
      change (L+1+H*a.val+d.val-(L+1))%H = d.val
      rw [hh,Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt d.isLt]

theorem encode_injective {L H : Nat} : Function.Injective (encode (L:=L) (H:=H)) := by
  intro x y hh
  rw [← decode_encode x,← decode_encode y,hh]

def graphFin {L H : Nat} (G : SimpleGraph (Vertex L H)) : SimpleGraph (Fin (order L H)) where
  adj a b := G.adj (decode a) (decode b)
  symm := G.symm
  loopless := fun a => G.loopless (decode a)

def pullWalk {L H : Nat} {G : SimpleGraph (Vertex L H)} {x y : Vertex L H} {n : Nat}
    (w : Walk G x y n) : Walk (graphFin G) (encode x) (encode y) n where
  point := fun i => encode (w.point i)
  first := congrArg encode w.first
  last := congrArg encode w.last
  step := by
    intro i hi
    change G.adj (decode (encode (w.point i))) (decode (encode (w.point (i+1))))
    rw [decode_encode,decode_encode]
    exact w.step i hi

def pushWalk {L H : Nat} {G : SimpleGraph (Vertex L H)} {x y : Fin (order L H)} {n : Nat}
    (w : Walk (graphFin G) x y n) : Walk G (decode x) (decode y) n where
  point := fun i => decode (w.point i)
  first := congrArg decode w.first
  last := congrArg decode w.last
  step := w.step

def distancesFin {L H : Nat} {G : SimpleGraph (Vertex L H)} (M : ShortestDistances G) :
    ShortestDistances (graphFin G) where
  dist x y := M.dist (decode x) (decode y)
  geodesic x y := by
    simpa only [encode_decode] using pullWalk (M.geodesic (decode x) (decode y))
  minimal x y n p := M.minimal (decode x) (decode y) n (pushWalk p)

theorem graphFin_connected {L H : Nat} {G : SimpleGraph (Vertex L H)} (M : ShortestDistances G) :
    Connected (graphFin G) :=
  fun x y => ⟨_,⟨(distancesFin M).geodesic x y⟩⟩

theorem exactPackingFin {L H : Nat} {G : SimpleGraph (Vertex L H)} {M : ShortestDistances G}
    {k p : Nat} (P : ExactPacking M k p) : ExactPacking (distancesFin M) k p := by
  constructor
  · obtain ⟨f,hf⟩ := P.attained
    refine ⟨fun i => encode (f i),?_⟩
    intro i j hij
    change k < M.dist (decode (encode (f i))) (decode (encode (f j)))
    rw [decode_encode,decode_encode]
    exact hf i j hij
  · intro n f hf
    exact P.upper n (fun i => decode (f i)) hf

def terminalsFin {L H : Nat} (T : Terminals (Vertex L H)) : Terminals (Fin (order L H)) :=
  ⟨encode T.a,encode T.b,encode T.c,encode T.d⟩

theorem distinctFin {L H : Nat} {T : Terminals (Vertex L H)} (h : T.Distinct) :
    (terminalsFin T).Distinct := by
  rcases h with ⟨a,b,c,d,e,f⟩
  exact ⟨fun h => a (encode_injective h),fun h => b (encode_injective h),
    fun h => c (encode_injective h),fun h => d (encode_injective h),
    fun h => e (encode_injective h),fun h => f (encode_injective h)⟩

theorem vectorFin {L H : Nat} {G : SimpleGraph (Vertex L H)} (M : ShortestDistances G)
    (T : Terminals (Vertex L H)) :
    distanceVector (distancesFin M) (terminalsFin T) = distanceVector M T := by
  simp [distanceVector,distancesFin,terminalsFin,decode_encode]

theorem unique_exactPacking {V : Type} {G : SimpleGraph V} {M N : ShortestDistances G}
    {k p : Nat} (P : ExactPacking M k p) : ExactPacking N k p := by
  constructor
  · obtain ⟨f,hf⟩ := P.attained
    exact ⟨f,fun i j hij => (N.unique M (f i) (f j)).symm ▸ hf i j hij⟩
  · exact fun n f hf => P.upper n f (fun i j hij => N.unique M (f i) (f j) ▸ hf i j hij)

theorem exactPacking_unique_number {V : Type} {G : SimpleGraph V} {M : ShortestDistances G}
    {k p q : Nat} (P : ExactPacking M k p) (Q : ExactPacking M k q) : p = q := by
  obtain ⟨f,hf⟩ := P.attained
  obtain ⟨g,hg⟩ := Q.attained
  exact Nat.le_antisymm (Q.upper _ f hf) (P.upper _ g hg)

theorem distanceVector_unique {V : Type} {G : SimpleGraph V} (M N : ShortestDistances G)
    (T : Terminals V) : distanceVector M T = distanceVector N T := by
  simp [distanceVector,M.unique N]

end TriameterQ3Attainment

/-! Sharp graph attainment for the four-terminal weighted bound. The
upper bound remains separate in FourGraphTheorem. -/
namespace TriameterQ3Attainment
open TriameterQ3Graph TriameterQ3Four

def side (b : Cut) (i : Fin 4) : Bool :=
  match b with
  | .c000 => false
  | .c001 => i.val == 3
  | .c010 => i.val == 2
  | .c011 => (i.val == 2) || (i.val == 3)
  | .c100 => i.val == 1
  | .c101 => (i.val == 1) || (i.val == 3)
  | .c110 => (i.val == 1) || (i.val == 2)
  | .c111 => !(i.val == 0)

def anchors (b : Cut) (L : Nat) (i : Fin 4) : Fin (L+1) :=
  if side b i then rightEnd L else leftEnd L

theorem anchors_ends (b : Cut) (L : Nat) (i : Fin 4) :
    anchors b L i = leftEnd L ∨ anchors b L i = rightEnd L := by
  unfold anchors
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

def tip (L H : Nat) (hH : 0 < H) (i : Fin 4) : Vertex L H :=
  .inr (i,⟨H-1,by omega⟩)

def tips (L H : Nat) (hH : 0 < H) : Terminals (Vertex L H) :=
  ⟨tip L H hH 0,tip L H hH 1,tip L H hH 2,tip L H hH 3⟩

theorem tips_distinct (L H : Nat) (hH : 0 < H) : (tips L H hH).Distinct := by
  unfold Terminals.Distinct
  dsimp [tips,tip]
  constructor <;> simp

theorem tip_metric (b : Cut) (L H e k R : Nat) (hH : 0 < H)
    (hk : 2*H = k+e) (hL : (L = 0 ∧ R = 0) ∨ (0 < L ∧ L+e = R))
    (a c : Fin 4) (hac : a ≠ c) :
    treeDist (anchors b L) e (tip L H hH a) (tip L H hH c) =
      k + (if side b a = side b c then 0 else R) := by
  have h0 : ∀ x y : Fin (L+1), L = 0 → x = y := by
    intro x y hz
    apply Fin.ext
    have hx := x.isLt
    have hy := y.isLt
    omega
  have hSame (heq : anchors b L a = anchors b L c) :
      treeDist (anchors b L) e (tip L H hH a) (tip L H hH c) = k := by
    simp [treeDist,tip,hac,heq,delta]
    omega
  by_cases hb : side b a = side b c
  · have ha : anchors b L a = anchors b L c := by simp [anchors,hb]
    simpa [hb] using hSame ha
  · rcases hL with ⟨hz,hR⟩ | ⟨hp,hR⟩
    · simpa [hR] using hSame (h0 _ _ hz)
    · have hs : (side b a = true ∧ side b c = false) ∨
          (side b a = false ∧ side b c = true) := by
        cases ha : side b a <;> cases hc : side b c <;> simp_all
      have hz : L ≠ 0 := by omega
      rcases hs with ⟨ha,hc⟩ | ⟨ha,hc⟩ <;>
        simp [treeDist,tip,hac,ha,hc,anchors,delta,leftEnd,rightEnd,hz] <;> omega

theorem terminal_vector (b : Cut) (L H e k R : Nat) (hH : 0 < H) (he : e ≤ 1)
    (hk : 2*H = k+e) (hL : (L = 0 ∧ R = 0) ∨ (0 < L ∧ L+e = R)) :
    distanceVector (exactDistances (anchors b L) e he) (tips L H hH) =
      let x := scaledCut (R : Int) b
      ⟨(k : Int)+x.ab,(k : Int)+x.ac,(k : Int)+x.ad,(k : Int)+x.bc,(k : Int)+x.bd,(k : Int)+x.cd⟩ := by
  have h := tip_metric b L H e k R hH hk hL
  have hab := h 0 1 (by decide)
  have hac := h 0 2 (by decide)
  have had := h 0 3 (by decide)
  have hbc := h 1 2 (by decide)
  have hbd := h 1 3 (by decide)
  have hcd := h 2 3 (by decide)
  unfold distanceVector
  dsimp [exactDistances,tips]
  rw [hab,hac,had,hbc,hbd,hcd]
  cases b <;> rfl

theorem cut_has_opposite_tips (b : Cut) (hb : b ≠ .c000) :
    ∃ a c : Fin 4, side b a ≠ side b c := by
  cases b
  · exact (hb rfl).elim
  · exact ⟨0,3,by decide⟩
  · exact ⟨0,2,by decide⟩
  · exact ⟨0,2,by decide⟩
  · exact ⟨0,1,by decide⟩
  · exact ⟨0,1,by decide⟩
  · exact ⟨0,1,by decide⟩
  · exact ⟨0,1,by decide⟩

theorem maximum_nontrivial_cut (w : Weights) (hw : w.Nonnegative) :
    ∃ b : Cut, b ≠ .c000 ∧ cutMass w = leftWeight w b*rightWeight w b := by
  obtain ⟨hupper,b,hbest⟩ := cutMass_is_maximum w
  by_cases hb : b = .c000
  · subst b
    have hz : cutMass w = 0 := by simpa [leftWeight,rightWeight] using hbest.symm
    have ha : 0 ≤ leftWeight w .c001 := by
      rcases hw with ⟨ha,hb,hc,hd⟩
      simp [leftWeight]
      omega
    have hd : 0 ≤ rightWeight w .c001 := by
      rcases hw with ⟨ha,hb,hc,hd⟩
      simpa [rightWeight] using hd
    have hn := Int.mul_nonneg ha hd
    have hu := hupper .c001
    refine ⟨.c001,?_⟩
    constructor
    · intro h
      cases h
    · omega
  · exact ⟨b,hb,hbest.symm⟩

theorem native_attainment_data (k p : Nat) (hk : 0 < k) (hp : 0 < p) (b : Cut)
    (hb : b ≠ .c000) :
    ∃ L H e : Nat, ∃ hH : 0 < H, ∃ he : e ≤ 1,
      let M := exactDistances (anchors b L) e he
      let T := tips L H hH
      ExactPacking M k p ∧
      distanceVector M T =
        let x := scaledCut (excess k p : Int) b
        ⟨(k : Int)+x.ab,(k : Int)+x.ac,(k : Int)+x.ad,(k : Int)+x.bc,(k : Int)+x.bd,(k : Int)+x.cd⟩ := by
  let h := k/2
  let e := k%2
  let H := h+e
  have he : e ≤ 1 := by dsimp [e]; omega
  have hke : 2*h+e = k := by dsimp [h,e]; omega
  have hH : 0 < H := by dsimp [H]; omega
  have hdepth : 2*H = k+e := by dsimp [H]; omega
  by_cases hp1 : p = 1
  · subst p
    refine ⟨0,H,e,hH,he,?_,?_⟩
    · apply exact_packing_one (anchors b 0) h e k he hke (by exact Nat.le_refl H) (leftEnd 0)
      intro x
      have zeroEnd (t : Fin (0+1)) : t = leftEnd 0 := by
        apply Fin.ext
        have ht := t.isLt
        change t.val = 0
        omega
      rcases x with t | ⟨i,d⟩
      · have ht := zeroEnd t
        simp [ht,cap,delta]
      · exact zeroEnd (anchors b 0 i)
    · apply terminal_vector b 0 H e k (excess k 1) hH he hdepth
      exact Or.inl ⟨rfl,by simp [excess]⟩
  · let q := p-2
    let L := 2*h+1+(k+1)*q
    have hpq : p = q+2 := by dsimp [q]; omega
    have hL : 0 < L := by dsimp [L]; omega
    have hR : L+e = excess k p := by
      unfold excess
      rw [show p-1 = q+1 by omega,Nat.mul_add,Nat.mul_one]
      dsimp [L]
      omega
    have hLt : (L = 0 ∧ excess k p = 0) ∨ (0 < L ∧ L+e = excess k p) :=
      Or.inr ⟨hL,hR⟩
    obtain ⟨a,c,hac⟩ := cut_has_opposite_tips b hb
    have hne : a ≠ c := fun h => hac (congrArg (side b) h)
    have hdist := tip_metric b L H e k (excess k p) hH hdepth hLt a c hne
    rw [ite_eq_right hac] at hdist
    have hbound : (k+1)*(q+2-1) ≤
        treeDist (anchors b L) e (tip L H hH a) (tip L H hH c) := by
      rw [hdist,excess]
      rw [show q+2-1 = p-1 by omega]
      omega
    refine ⟨L,H,e,hH,he,?_,?_⟩
    · rw [hpq]
      exact exact_packing_many (anchors b L) (anchors_ends b L) h e k q he rfl hke
        (Nat.le_refl H) (tip L H hH a) (tip L H hH c) hbound
    · exact terminal_vector b L H e k (excess k p) hH he hdepth hLt

/-- Every integer weight vector with nonnegative coordinates and every positive
packing number attain the sharp upper bound on a finite simple connected graph.
Graph distance and packing number are the same native definitions as in the
universal upper bound. -/
theorem weighted_four_terminal_finite_graph_attains (k p : Nat) (hk : 0 < k) (hp : 0 < p)
    (w : Weights) (hw : w.Nonnegative) :
    ∃ (n : Nat) (G : SimpleGraph (Fin n)) (hC : Connected G) (T : Terminals (Fin n)),
      T.Distinct ∧ packingNumber (distancesOfConnected G hC) k = p ∧
      weightedTerminalSum (distancesOfConnected G hC) T w =
        (k : Int)*pairMass w + (excess k p : Int)*cutMass w := by
  obtain ⟨b,hb,hmax⟩ := maximum_nontrivial_cut w hw
  obtain ⟨L,H,e,hH,he,P,hMetric⟩ := native_attainment_data k p hk hp b hb
  let G := graphFin (graph (H:=H) (anchors b L) e)
  let M := exactDistances (H:=H) (anchors b L) e he
  let hC : Connected G := graphFin_connected M
  let N := distancesOfConnected G hC
  let T := terminalsFin (tips L H hH)
  have P' : ExactPacking N k p := unique_exactPacking (exactPackingFin P)
  have hNum := exactPacking_unique_number (packingNumber_is_exact N k) P'
  have hEq : distanceVector N T = distanceVector M (tips L H hH) :=
    (distanceVector_unique N (distancesFin M) T).trans (vectorFin M _)
  refine ⟨order L H,G,hC,T,distinctFin (tips_distinct L H hH),hNum,?_⟩
  have hscore := exact_score_of_cut_metric N T w (k : Int) (excess k p : Int) b
    (hEq.trans hMetric)
  simpa only [hmax] using hscore

end TriameterQ3Attainment

namespace TriameterQ3Attainment
open TriameterQ3Graph TriameterQ3Four

/-- Exactly the greatest possible terminal pair-distance sum with the given
nonnegative integer vertex weights and the given distance-packing number. -/
theorem weighted_four_terminal_exact (k p : Nat) (hk : 0 < k) (hp : 0 < p)
    (w : Weights) (hw : w.Nonnegative) :
    (∀ (n : Nat) (G : SimpleGraph (Fin n)) (hC : Connected G) (T : Terminals (Fin n)),
      T.Distinct → packingNumber (distancesOfConnected G hC) k = p →
      weightedTerminalSum (distancesOfConnected G hC) T w ≤
        (k : Int)*pairMass w + (excess k p : Int)*cutMass w) ∧
    (∃ (n : Nat) (G : SimpleGraph (Fin n)) (hC : Connected G) (T : Terminals (Fin n)),
      T.Distinct ∧ packingNumber (distancesOfConnected G hC) k = p ∧
      weightedTerminalSum (distancesOfConnected G hC) T w =
        (k : Int)*pairMass w + (excess k p : Int)*cutMass w) := by
  refine ⟨?_,weighted_four_terminal_finite_graph_attains k p hk hp w hw⟩
  intro n G hC T hD hP
  have h := weighted_four_terminal_finite_graph_bound n G hC T hD k hk w hw
  dsimp only at h
  rwa [hP] at h

def unitWeights : Weights := ⟨1,1,1,1⟩
theorem unitWeights_nonnegative : unitWeights.Nonnegative :=
  ⟨by decide,by decide,by decide,by decide⟩
theorem unit_pairMass : pairMass unitWeights = 6 := rfl
theorem unit_cutMass : cutMass unitWeights = 4 := rfl

def terminalPairSum {V : Type} {G : SimpleGraph V} (M : ShortestDistances G)
    (T : Terminals V) : Nat :=
  M.dist T.a T.b + M.dist T.a T.c + M.dist T.a T.d +
  M.dist T.b T.c + M.dist T.b T.d + M.dist T.c T.d

theorem weighted_unit {V : Type} {G : SimpleGraph V} (M : ShortestDistances G)
    (T : Terminals V) : weightedTerminalSum M T unitWeights = (terminalPairSum M T : Int) := by
  simp [weightedTerminalSum,terminalPairSum,unitWeights,terminalCoefficients,distanceVector,dot,
    Int.natCast_add]

/-- Exact unweighted extremum for four prescribed distinct vertices, measured
by the sum over the six unordered pairs. This answers the four-terminal
packing branch, not the higher-terminal finite or separator branches. -/
theorem four_terminal_unweighted_exact (k p : Nat) (hk : 0 < k) (hp : 0 < p) :
    (∀ (n : Nat) (G : SimpleGraph (Fin n)) (hC : Connected G) (T : Terminals (Fin n)),
      T.Distinct → packingNumber (distancesOfConnected G hC) k = p →
      terminalPairSum (distancesOfConnected G hC) T ≤ 6*k+4*(k+1)*(p-1)) ∧
    (∃ (n : Nat) (G : SimpleGraph (Fin n)) (hC : Connected G) (T : Terminals (Fin n)),
      T.Distinct ∧ packingNumber (distancesOfConnected G hC) k = p ∧
      terminalPairSum (distancesOfConnected G hC) T = 6*k+4*(k+1)*(p-1)) := by
  obtain ⟨hu,hl⟩ := weighted_four_terminal_exact k p hk hp unitWeights unitWeights_nonnegative
  have hval : ((6*k+4*(k+1)*(p-1) : Nat) : Int) =
      (k : Int)*6+(excess k p : Int)*4 := by
    have hh : 6*k+4*(k+1)*(p-1) = 6*k+4*excess k p := by
      rw [excess,Nat.mul_assoc]
    rw [hh]
    simp only [Int.natCast_add,Int.natCast_mul]
    omega
  constructor
  · intro n G hC T hD hP
    have h := hu n G hC T hD hP
    rw [weighted_unit,unit_pairMass,unit_cutMass,← hval] at h
    exact Int.ofNat_le.mp h
  · obtain ⟨n,G,hC,T,hD,hP,hs⟩ := hl
    refine ⟨n,G,hC,T,hD,hP,?_⟩
    rw [weighted_unit,unit_pairMass,unit_cutMass,← hval] at hs
    exact Int.ofNat_inj.mp hs

end TriameterQ3Attainment

#print axioms TriameterQ3Attainment.weighted_four_terminal_exact
#print axioms TriameterQ3Attainment.four_terminal_unweighted_exact
