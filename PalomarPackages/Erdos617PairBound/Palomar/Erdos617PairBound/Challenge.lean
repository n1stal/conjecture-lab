module

public import Std

@[expose] public section

/-!
# A bound on parallel exception multiplicity in a normalized Erdős #617 core

Assume a balanced r-coloring of complete-graph edges, in the sense that every
r+1 distinct vertices see every one of the r colors. In a fixed color consider
two private rows of a normalized two-support core. They have deficits d_i and
d_j relative to r, and an exception counted in this statement has precisely
the two corresponding anchors as its neighbors amongst all anchors.

For r ≥ 12 and d_i,d_j ≥ 3, the number of such parallel exceptions is at most
d_i+d_j−2. The structure states the exact core assumptions, including its
scoped independence and clique caps and the normalized pair-sum condition.
It does not assert the full balanced-coloring conjecture.
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
