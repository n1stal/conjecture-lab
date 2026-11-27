module

public import Std

@[expose] public section

/-!
# Parallel-pair, support-star, and double-star obstructions in normalized Erdős #617 cores

Assume a balanced r-coloring of complete-graph edges, in the sense that every
r+1 distinct vertices see every one of the r colors. In a fixed color consider
two private rows of a normalized two-support core. They have deficits d_i and
d_j relative to r, and an exception counted in this statement has precisely
the two corresponding anchors as its neighbors amongst all anchors.

For r ≥ 12 and d_i,d_j ≥ 3, the number of such parallel exceptions is at most
d_i+d_j−2. The structure states the exact core assumptions, including its
scoped independence and clique caps and the normalized pair-sum condition.
The subsequent declarations give full palette-counting contradictions for scoped
star and double-star supports. None asserts the full balanced-coloring conjecture.
-/
namespace Erdos617Geometry

universe u v

def Compatible {V : Type u} (adj : V → V → Prop) (x y : V) : Prop :=
  x ≠ y ∧ ¬adj x y

def IndependenceCap {V : Type u} (adj : V → V → Prop) (n : Nat) : Prop :=
  ∀ S : List V, S.Pairwise (Compatible adj) → S.length ≤ n

/-- A private vertex is its anchor, or sees that anchor, and is distinct
from and nonadjacent to every other anchor. -/
structure Private {V : Type u} (adj : V → V → Prop) (C : List V) (a u : V) : Prop where
  anchor_mem : a ∈ C
  own : u = a ∨ adj u a
  away : ∀ c ∈ C, c ≠ a → Compatible adj u c

/-- The exact two-support neighborhood on the anchor list. -/
structure Double {V : Type u} (adj : V → V → Prop) (C : List V) (b i x : V) : Prop where
  owner_mem : b ∈ C
  source_mem : i ∈ C
  distinct : b ≠ i
  outside : x ∉ C
  owner_adj : adj x b
  source_adj : adj x i
  away : ∀ c ∈ C, c ≠ b → c ≠ i → ¬adj x c

def orderedColors {V : Type u} {H : Type v} (col : V → V → H) : List V → List H
  | [] => []
  | x :: W => W.map (col x) ++ orderedColors col W

def Balanced {V : Type u} {H : Type v} [BEq H]
    (col : V → V → H) (r : Nat) : Prop :=
  ∀ W : List V, W.Nodup → W.length = r+1 →
    ∀ c : H, 0 < (orderedColors col W).count c

end Erdos617Geometry

namespace ParallelMantel.Pentagon

open Erdos617Geometry

universe u

variable {V : Type u} {r : Nat}

/-- Scoped data of two private rows and all exceptions sharing their anchors. -/
structure NormalizedPair (col : V→V→Fin r) (t : Fin r) where
  core : List V
  anchors : List V
  p : V
  q : V
  left : List V
  right : List V
  exceptions : List V
  ld : Nat
  rd : Nat
  anchorInd : anchors.Pairwise (Compatible (fun x y=>col x y=t))
  p_mem : p∈anchors
  q_mem : q∈anchors
  pq : p≠q
  p_left : p∈left
  q_right : q∈right
  anchorCore : ∀ a∈anchors, a∈core
  verticesCore : ∀ x∈left++(right++exceptions), x∈core
  disjointLists : (left++(right++exceptions)).Nodup
  privateLeft : ∀ x∈left, Private (fun x y=>col x y=t) anchors p x
  privateRight : ∀ x∈right, Private (fun x y=>col x y=t) anchors q x
  double : ∀ x∈exceptions, Double (fun x y=>col x y=t) anchors p q x
  coreInd : ∀ I : List V, (∀ x∈I, x∈core) →
    I.Pairwise (Compatible (fun x y=>col x y=t)) → I.length≤anchors.length
  coreClique : ∀ I : List V, I.Nodup → (∀ x∈I, x∈core) →
    I.Pairwise (fun x y=>col x y=t) → I.length≤r-1
  leftSize : left.length+ld=r
  rightSize : right.length+rd=r
  normalizedSum : ld+rd≤r-3

variable {col : V→V→Fin r} {t : Fin r}

/-- Two rows of deficit at least three have at most the sum of their deficits
minus two shared exceptions in the normalized, balanced-color setting. -/
theorem NormalizedPair.high_parallel_multiplicity_bound [BEq V] [LawfulBEq V]
    (M : NormalizedPair col t) (symm : ∀ x y, col x y=col y x)
    (bal : Balanced col r) (hr : 12≤r) (hl : 3≤M.ld) (hq : 3≤M.rd) :
    M.exceptions.length ≤ M.ld+M.rd-2 := by
  sorry

end ParallelMantel.Pentagon

namespace ParallelMantel

/-- floor(n²/4), written without dividing a product. -/
def mantelBound (n : Nat) : Nat := (n / 2) * ((n + 1) / 2)

end ParallelMantel

namespace ParallelMantel.Pentagon

open Erdos617Geometry

variable {V : Type u} {r : Nat} {col : V→V→Fin r} {t : Fin r}

def NormalizedPair.residual (M : NormalizedPair col t) : Nat :=
  M.ld + M.rd - M.exceptions.length

def NormalizedPair.exteriorBudget (M : NormalizedPair col t) : Nat :=
  mantelBound (M.residual-1)+1

/-- Number of possible unordered pairs in a list of n elements. -/
def pairSlots : Nat → Nat
  | 0 => 0
  | n+1 => pairSlots n+n

/-- Scoped star with no further non-spoke exceptions and one excess exception
over the total of its actual row deficits. -/
structure NormalizedStar (col : V→V→Fin r) (t : Fin r) where
  hubAnchor : V
  hub : List V
  deficit : Nat
  branches : List (NormalizedPair col t)
  sameHub : ∀ M∈branches, M.p=hubAnchor ∧ M.left=hub ∧ M.ld=deficit
  hubSize : hub.length+deficit=r
  hubClique : hub.Pairwise (fun x y=>col x y=t)
  allDistinct : (hub++(branches.flatMap fun M=>M.exceptions)).Nodup
  overload : (branches.flatMap fun M=>M.exceptions).length =
    deficit+(branches.map fun M=>M.rd).sum+1

/-- Exact numerical budgets under which spoke routes cannot fit in all rows. -/
theorem NormalizedStar.refined_star_impossible [BEq V] [LawfulBEq V]
    (C : NormalizedStar col t) (symm : ∀ x y, col x y=col y x)
    (bal : Balanced col r) (hr : 12≤r) (hd : 3≤C.deficit)
    (K : NormalizedPair col t → Nat)
    (branches : ∀ M∈C.branches,
      3≤M.rd ∧ M.right.Pairwise (fun x y=>col x y=t) ∧
      M.exteriorBudget+1<(2*r-M.residual-5)/2 ∧
      M.exteriorBudget+3<M.left.length ∧ M.exteriorBudget+3<M.right.length ∧
      M.ld+M.rd+3<r ∧ M.exteriorBudget<(K M+1)*(K M+1) ∧
      pairSlots (M.rd+1)+(M.rd+1)+K M<r-1)
    (hubBudget : pairSlots (C.deficit+1)+(C.deficit+1)+(C.branches.map K).sum<r-1) :
    False := by
  sorry

/-- Unbounded family: each leaf of deficit e has e+1 incident exceptions,
3≤e≤D, where D is the hub deficit; r≥(D+1)² excludes this star. -/
theorem NormalizedStar.unit_margin_star_impossible [BEq V] [LawfulBEq V]
    (C : NormalizedStar col t) (symm : ∀ x y, col x y=col y x)
    (bal : Balanced col r) (hd : 3≤C.deficit)
    (many : (C.deficit+1)*(C.deficit+1)≤r)
    (branches : ∀ M∈C.branches,
      3≤M.rd ∧ M.rd≤C.deficit ∧ M.exceptions.length=M.rd+1 ∧
      M.right.Pairwise (fun x y=>col x y=t)) :
    False := by
  sorry

/-- A common two-hub normalized configuration with leaf surplus and one
global exception beyond total row deficits. Each spoke uses its real hub. -/
structure NormalizedDoubleStar (col : V→V→Fin r) (t : Fin r) where
  center : NormalizedPair col t
  leftSpokes : List (NormalizedPair col t)
  rightSpokes : List (NormalizedPair col t)
  sameLeft : ∀ M∈leftSpokes, M.p=center.p ∧ M.left=center.left ∧ M.ld=center.ld
  sameRight : ∀ M∈rightSpokes, M.p=center.q ∧ M.left=center.right ∧ M.ld=center.rd
  leftSurplus : ∀ M∈leftSpokes, M.rd<M.exceptions.length
  rightSurplus : ∀ M∈rightSpokes, M.rd<M.exceptions.length
  distinct : ((center.left++center.right)++
    ((leftSpokes.flatMap fun M=>M.exceptions)++
     ((rightSpokes.flatMap fun M=>M.exceptions)++center.exceptions))).Nodup
  overload : (leftSpokes.flatMap fun M=>M.exceptions).length+
    (rightSpokes.flatMap fun M=>M.exceptions).length+center.exceptions.length=
    center.ld+center.rd+
    (leftSpokes.map fun M=>M.rd).sum+(rightSpokes.map fun M=>M.rd).sum+1

/-- Uniform two-hub exclusion for all row deficits in [3,D], under the
exact inequality equivalent to r≥ceil(49D²/64)+6D+10. -/
theorem NormalizedDoubleStar.uniform_impossible [BEq V] [LawfulBEq V]
    (C : NormalizedDoubleStar col t) (symm : ∀ x y, col x y=col y x)
    (bal : Balanced col r)
    (D : Nat) (radius : 49*(D*D)+64*(6*D+10)≤64*r)
    (leftHigh : 3≤C.center.ld) (leftSmall : C.center.ld≤D)
    (rightHigh : 3≤C.center.rd) (rightSmall : C.center.rd≤D)
    (leftClique : C.center.left.Pairwise (fun x y=>col x y=t))
    (rightClique : C.center.right.Pairwise (fun x y=>col x y=t))
    (leaves : ∀ M∈C.leftSpokes++C.rightSpokes,
      3≤M.rd ∧ M.rd≤D ∧ M.right.Pairwise (fun x y=>col x y=t)) :
    False := by
  sorry

end ParallelMantel.Pentagon
