module

public import Palomar.FourTerminalSeparators.Support.FourGraphCeiling

@[expose] public section

namespace HakKozerenkoSeparatorGraph
open TriameterQ3Graph HakKozerenkoFourSeparator

/-- Any separator contains a nonterminal: take the promised hit of a
shortest walk between its separated pair. Disjoint separators give a list
of distinct such vertices, disjoint from the four marked labels. -/
theorem cap_of_order {n : Nat} {G : SimpleGraph (Fin n)} (M : ShortestDistances G)
    (a b c d : Fin n) (neq : FourApart a b c d) :
    PackingCap G (markFour a b c d) (n-4) := by
  classical
  intro q F
  have witness (i : Fin q) : ∃ v, F.part i v := by
    obtain ⟨_,u,v,_,_,sep⟩ := F.each i
    let W := M.geodesic u v
    obtain ⟨j,_,hj⟩ := sep _ W
    exact ⟨W.point j,hj⟩
  let f (i : Fin q) := (witness i).choose
  have good (i : Fin q) : F.part i (f i) := (witness i).choose_spec
  have inj : Function.Injective f := by
    intro i j e
    by_cases h : i=j
    · exact h
    · have hJ := good j
      rw [←e] at hJ
      exact (F.disjoint i j h (f i) (good i) hJ).elim
  let left := (List.finRange q).map f
  let right := [a,b,c,d]
  have nl : left.Nodup :=
    List.Pairwise.map f (fun _ _ h e => h (inj e)) (List.nodup_finRange q)
  have nr : right.Nodup := by
    simp [right,neq.ab,neq.ac,neq.ad,neq.bc,neq.bd,neq.cd]
  have nl' : (left++right).Nodup := by
    refine List.nodup_append.mpr ⟨nl,nr,?_⟩
    intro x hx y hy eq
    subst y
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
    have ismarked : markFour a b c d (f i) := by
      simpa [right,markFour] using hy
    exact (F.each i).1 _ (good i) ismarked
  have hsub : left++right ⊆ List.finRange n := fun {_} _ => List.mem_finRange _
  have B := nl'.length_le_of_subset hsub
  simp only [List.length_append,left,right,List.length_map,List.length_finRange,
    List.length_cons,List.length_nil] at B
  omega

def pathGraph (n : Nat) : SimpleGraph (Fin n) where
  adj x y := x.val+1=y.val ∨ y.val+1=x.val
  symm := Or.symm
  loopless := by intro x h; rcases h with h|h <;> omega

def pathForward {n : Nat} (a b : Fin n) (ordered : a.val≤b.val) :
    Walk (pathGraph n) a b (b.val-a.val) := by
  refine ⟨fun i => ⟨min (a.val+i) b.val,Nat.lt_of_le_of_lt (Nat.min_le_right _ _) b.isLt⟩,?_,?_,?_⟩
  · apply Fin.ext
    change min (a.val+0) b.val=a.val
    simpa using Nat.min_eq_left ordered
  · apply Fin.ext
    change min (a.val+(b.val-a.val)) b.val=b.val
    omega
  · intro i hi
    change min (a.val+i) b.val+1=min (a.val+(i+1)) b.val ∨ _
    exact Or.inl (by omega)

theorem path_walk_upper {n : Nat} {a b : Fin n} {k : Nat} (W : Walk (pathGraph n) a b k) :
    b.val≤a.val+k := by
  have go (i : Nat) (hi : i≤k) : (W.point i).val≤a.val+i := by
    induction i with
    | zero => rw [W.first]; omega
    | succ i ih =>
      have p := ih (by omega)
      have e := W.step i (by omega)
      change (W.point i).val+1=(W.point (i+1)).val ∨
        (W.point (i+1)).val+1=(W.point i).val at e
      rcases e with e|e <;> omega
  have h := go k (Nat.le_refl k)
  rwa [W.last] at h

def pathD {n : Nat} (a b : Fin n) : Nat :=
  max (a.val-b.val) (b.val-a.val)

def pathDistance (n : Nat) : ShortestDistances (pathGraph n) where
  dist := pathD
  geodesic := by
    intro a b
    by_cases h : a.val≤b.val
    · have r : pathD a b=b.val-a.val := by unfold pathD; omega
      rw [r]
      exact pathForward a b h
    · have r : pathD a b=a.val-b.val := by unfold pathD; omega
      rw [r]
      exact (pathForward b a (by omega)).reverse
  minimal := by
    intro a b k W
    have h := path_walk_upper W
    have h' := path_walk_upper W.reverse
    unfold pathD
    omega

/-- A realization witnessing the exact four-terminal vertex bound at S. -/
def VertexAttains (S : Nat) : Prop :=
  ∃ n : Nat, ∃ G : SimpleGraph (Fin n), ∃ M : ShortestDistances G,
    ∃ a b c d : Fin n, FourApart a b c d ∧ fourSum M a b c d=S ∧
      PackingCap G (markFour a b c d) ((S-7)/4)

theorem path_attains_vertex (q j : Nat) (hj : j≤q) (j3 : j≤3) :
    VertexAttains (4*q+10-j) := by
  let n := q+4
  let a : Fin n := ⟨0,by omega⟩
  let b : Fin n := ⟨1,by omega⟩
  let c : Fin n := ⟨q+2-j,by omega⟩
  let d : Fin n := ⟨q+3,by omega⟩
  have neq : FourApart a b c d := by
    constructor
    all_goals
      intro eq
      have he := congrArg (fun z : Fin n => z.val) eq
      dsimp [a,b,c,d] at he
      omega
  refine ⟨n,pathGraph n,pathDistance n,a,b,c,d,neq,?_,?_⟩
  · change pathD a b + pathD c d + pathD a c + pathD b d + pathD a d + pathD b c
        =4*q+10-j
    dsimp [pathD,a,b,c,d]
    omega
  · have R := cap_of_order (pathDistance n) a b c d neq
    have he : (4*q+10-j-7)/4=n-4 := by dsimp [n]; omega
    rw [he]
    exact R

end HakKozerenkoSeparatorGraph

#print axioms HakKozerenkoSeparatorGraph.cap_of_order
#print axioms HakKozerenkoSeparatorGraph.path_attains_vertex
