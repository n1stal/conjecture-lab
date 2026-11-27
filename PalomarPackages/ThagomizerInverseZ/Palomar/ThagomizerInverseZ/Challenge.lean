module

public import Std

@[expose] public section

namespace InverseZ.ThagomizerRows


def bitWords : Nat → List (List Bool) :=
  Nat.rec [[]] (fun _ xs => xs.map (false::·) ++ xs.map (true::·))

end InverseZ.ThagomizerRows

namespace InverseZ.ThagomizerFlatCounts
open InverseZ.ThagomizerRows

def assignments : Nat → List (List (Option Bool)) :=
  Nat.rec [[]] (fun _ xs =>
    xs.map ((none : Option Bool)::·) ++
    xs.map ((some false)::·) ++ xs.map ((some true)::·))

end InverseZ.ThagomizerFlatCounts

namespace InverseZ.ThagomizerMarker
open InverseZ.ThagomizerRows

abbrev Row := Nat → Int → Nat

def A (f : Row) (h : Nat) (i : Int) : Nat :=
  f h i + f (h+1) i + (if h=0 then 0 else f (h-1) (i-1))

def unmarked : Nat → Row :=
  Nat.rec (fun _ i => if i=0 then 1 else 0) (fun _ f => A f)

def Qmodel (n i : Nat) : Nat := unmarked n 0 (i:Int)

end InverseZ.ThagomizerMarker

namespace InverseZ.ThagomizerMobius
open InverseZ.ThagomizerRows

def boolMu (k : Nat) : Int := (-1)^k

def thagMu (k : Nat) : Int := -((-2)^k)

end InverseZ.ThagomizerMobius

namespace InverseZ.ThagomizerFlat

inductive Edge (n : Nat)
  | spine
  | spoke (side : Bool) (i : Fin n)

def ofJoined (S : Fin n → Bool) : Edge n → Bool :=
  fun e => Edge.casesOn e true (fun _ i => S i)

def ofSplit (S : Fin n → Option Bool) : Edge n → Bool :=
  fun e => Edge.casesOn e false (fun side i => S i == some side)

end InverseZ.ThagomizerFlat

namespace InverseZ.ThagomizerRank
open InverseZ.ThagomizerFlat

def bit (b : Bool) : Nat := if b then 1 else 0

def countOn (L : List α) (f : α → Nat) : Nat := (L.map f).sum

def finSum (f : Fin n → Nat) : Nat := countOn (List.finRange n) f

def active (f : Edge n → Bool) (i : Fin n) : Nat :=
  bit (f (.spoke false i) || f (.spoke true i))

def double (f : Edge n → Bool) (i : Fin n) : Nat :=
  bit (f (.spoke false i) && f (.spoke true i))

def S (f : Edge n → Bool) : Nat := finSum (active f)

def E (f : Edge n → Bool) : Nat := bit (f .spine) + finSum (double f)

def rank (f : Edge n → Bool) : Nat := S f + min 1 (E f)

end InverseZ.ThagomizerRank

namespace InverseZ.ThagomizerLiteral
open InverseZ.ThagomizerRows
open InverseZ.ThagomizerFlatCounts
open InverseZ.ThagomizerMobius
open InverseZ.ThagomizerMarker
open InverseZ.ThagomizerFlat
open InverseZ.ThagomizerRank

abbrev FullList (α : Type) (n : Nat) := {l : List α // l.length=n}

abbrev FlatCode (n : Nat) := FullList Bool n ⊕ FullList (Option Bool) n

theorem readCodeBound (l : FullList α n) (i : Fin n) : i.val < l.val.length :=
  Eq.mpr (congrArg (fun m => i.val < m) l.property) i.isLt

def readCode (l : FullList α n) (i : Fin n) : α :=
  l.val.get ⟨i.val, readCodeBound l i⟩

def graphOfCode : FlatCode n → (Edge n → Bool) :=
  Sum.elim (fun bs => ofJoined (readCode bs)) (fun bs => ofSplit (readCode bs))

def rankedSummand (Q : Nat → Nat → Nat) (n i : Nat) (c : FlatCode n) : Nat :=
  let r := rank (graphOfCode c)
  let d := rank (fun _ : Edge n => true)-r
  Sum.elim (fun _ => if d≤i then (boolMu d).natAbs*Q (r-1) (i-d) else 0)
    (fun _ => if i=d then (thagMu (d-1)).natAbs else 0) c

def graphicRankFlatCoeff (Q : Nat → Nat → Nat) (n i : Nat) : Nat :=
  ((bitWords n).map (fun l=>if h : l.length=n then rankedSummand Q n i (.inl ⟨l,h⟩) else 0)).sum +
  ((assignments n).map (fun l=>if h : l.length=n then rankedSummand Q n i (.inr ⟨l,h⟩) else 0)).sum

def inverseZCoeff (n i : Nat) : Nat := graphicRankFlatCoeff Qmodel n i

theorem inverseZCoeff_strict_and_positive :
    (∀ n i : Nat, i≤n+1 → 0<inverseZCoeff n i) ∧
    (∀ n i : Nat, i+1≤n →
      inverseZCoeff n i*inverseZCoeff n (i+2) <
      inverseZCoeff n (i+1)*inverseZCoeff n (i+1)) :=
  by sorry

end InverseZ.ThagomizerLiteral
