module

public import Palomar.FourTerminalSeparators.Support.SeparatorGraphMetric

@[expose] public section

namespace HakKozerenkoSeparatorGraph
open TriameterQ3Graph

universe u
variable {V : Type u} {G : SimpleGraph V}

/-- A walk is blocked exactly when it meets S. This includes endpoint
indices, harmless when S excludes all terminals. -/
def Separates (G : SimpleGraph V) (S : V → Prop) (a b : V) : Prop :=
  ∀ (n : Nat) (W : Walk G a b n), ∃ j, j ≤ n ∧ S (W.point j)

def TSeparator (G : SimpleGraph V) (T S : V → Prop) : Prop :=
  (∀ v, S v → ¬T v) ∧ ∃ a b, T a ∧ T b ∧ Separates G S a b

structure VertexFamily (G : SimpleGraph V) (T : V → Prop) (q : Nat) where
  part : Fin q → V → Prop
  each : ∀ i, TSeparator G T (part i)
  disjoint : ∀ i j, i ≠ j → ∀ v, part i v → part j v → False

def PackingCap (G : SimpleGraph V) (T : V → Prop) (c : Nat) : Prop :=
  ∀ q, VertexFamily G T q → q ≤ c

/-- The increment is the cost of the vertex reached, not the vertex left. -/
noncomputable def charge (T : V → Prop) (v : V) : Nat := by
  classical
  exact if T v then 0 else 1

theorem charge_le_one (T : V → Prop) (v : V) : charge T v ≤ 1 := by
  by_cases h : T v <;> simp [charge,h]

theorem charge_eq_zero (T : V → Prop) {v : V} (hv : T v) :
    charge T v = 0 := by simp [charge,hv]

theorem charge_eq_one (T : V → Prop) {v : V} (hv : ¬ T v) :
    charge T v = 1 := by simp [charge,hv]

/-- A reachable integral cost obtained from actual edges. -/
inductive ChargedReach (G : SimpleGraph V) (T : V → Prop) (start : V) : V → Nat → Prop
  | start : ChargedReach G T start start 0
  | add {x y : V} {k : Nat} : ChargedReach G T start x k → G.adj x y →
      ChargedReach G T start y (k + charge T y)

def unitWalk {x y : V} (h : G.adj x y) : Walk G x y 1 := by
  refine ⟨fun i => if i=0 then x else y, by simp, by simp, ?_⟩
  intro i hi
  have e : i=0 := by omega
  subst i
  simpa using h

theorem chargedReach_of_walk (T : V → Prop) {s t : V} (n : Nat)
    (W : Walk G s t n) : ∃ q, ChargedReach G T s t q := by
  induction n generalizing t with
  | zero =>
      have h := W.zero_endpoints
      subst t
      exact ⟨0,ChargedReach.start⟩
  | succ n ih =>
      have P := W.slice 0 n (by omega) (by omega)
      rw [W.first, Nat.sub_zero] at P
      obtain ⟨k,K⟩ := ih P
      have e := W.step n (by omega)
      rw [W.last] at e
      exact ⟨_,ChargedReach.add K e⟩

theorem least_charge (M : ShortestDistances G) (T : V → Prop) (s v : V) :
    ∃ q, ChargedReach G T s v q ∧
      ∀ k, ChargedReach G T s v k → q ≤ k := by
  obtain ⟨k,H⟩ := chargedReach_of_walk T _ (M.geodesic s v)
  exact smallest_witness _ _ H

/-- Distance in the 0/1 vertex-cost model. Unlike BFS levels of ordinary
distance, its threshold can only be entered at a nonterminal vertex. -/
noncomputable def potential (M : ShortestDistances G) (T : V → Prop) (s v : V) : Nat :=
  (least_charge M T s v).choose

theorem potential_witness (M : ShortestDistances G) (T : V → Prop) (s v : V) :
    ChargedReach G T s v (potential M T s v) :=
  (least_charge M T s v).choose_spec.1

theorem potential_le (M : ShortestDistances G) (T : V → Prop) (s v : V)
    (k : Nat) (H : ChargedReach G T s v k) :
    potential M T s v ≤ k :=
  (least_charge M T s v).choose_spec.2 k H

theorem potential_start (M : ShortestDistances G) (T : V → Prop) (s : V) :
    potential M T s s = 0 :=
  Nat.eq_zero_of_le_zero (potential_le M T s s 0 ChargedReach.start)

theorem potential_step (M : ShortestDistances G) (T : V → Prop) (s : V)
    {x y : V} (edge : G.adj x y) :
    potential M T s y ≤ potential M T s x + charge T y :=
  potential_le M T s y _ ((potential_witness M T s x).add edge)

/-- The first upward threshold-crossing has value exactly j and incurs
one unit at its entering (therefore nonterminal) endpoint. -/
theorem hit_weighted_layer (values tolls : Nat → Nat) (N j : Nat)
    (start : values 0 < j) (finish : j ≤ values N)
    (growth : ∀ i, i<N → values (i+1) ≤ values i + tolls (i+1))
    (unit : ∀ i, tolls i ≤ 1) :
    ∃ i, i<N ∧ values (i+1)=j ∧ tolls (i+1)=1 := by
  induction N with
  | zero => omega
  | succ N ih =>
      by_cases h : j ≤ values N
      · obtain ⟨i,hi,hv,ht⟩ := ih h (fun i hi => growth i (by omega))
        exact ⟨i,by omega,hv,ht⟩
      · have hs := growth N (by omega)
        have hunit := unit (N+1)
        exact ⟨N,by omega,by omega,by omega⟩

theorem hit_potential_level (M : ShortestDistances G) (T : V → Prop)
    (s t : V) (j : Nat) (hj : 0<j) (finish : j≤potential M T s t) :
    Separates G (fun v => ¬T v ∧ potential M T s v=j) s t := by
  intro n W
  let f := fun i => potential M T s (W.point i)
  let c := fun i => charge T (W.point i)
  have hstart : f 0 < j := by
    dsimp [f]
    rw [W.first,potential_start]
    exact hj
  have hend : j≤f n := by
    rwa [show f n = potential M T s t from congrArg (potential M T s) W.last]
  obtain ⟨i,hi,he,hc⟩ := hit_weighted_layer f c n j hstart hend
    (fun i hi => potential_step M T s (W.step i hi)) (fun i => charge_le_one T (W.point i))
  refine ⟨i+1,by omega,?_,he⟩
  intro ht
  change charge T (W.point (i+1)) = 1 at hc
  rw [charge_eq_zero T ht] at hc
  omega

/-- Every reached nonterminal toll level gives a different actual
separator for the same original terminal pair. -/
def fixedPairFamily (M : ShortestDistances G) (T : V → Prop) (s t : V)
    (hs : T s) (ht : T t) : VertexFamily G T (potential M T s t) where
  part := fun i v => ¬T v ∧ potential M T s v=(i.val+1)
  each := fun i => ⟨fun _ h => h.1,s,t,hs,ht,
    hit_potential_level M T s t (i.val+1) (by omega) (by have q := i.isLt; omega)⟩
  disjoint := by
    intro i j ne v hi hj
    exact ne (Fin.ext (by omega))

theorem potential_le_packing_cap (M : ShortestDistances G) (T : V → Prop)
    (s t : V) (hs : T s) (ht : T t) (c : Nat) (cap : PackingCap G T c) :
    potential M T s t ≤ c :=
  cap _ (fixedPairFamily M T s t hs ht)

/-- Complete-terminal route, charging ordinary interior length lower
bounds between consecutive visited terminals. -/
inductive TerminalRoute (M : ShortestDistances G) (T : V → Prop) (s : V) : V → Nat → Prop
  | start : T s → TerminalRoute M T s s 0
  | add {x y : V} {k : Nat} : TerminalRoute M T s x k → T y →
      TerminalRoute M T s y (k+(M.dist x y-1))

theorem charge_to_terminal_route_aux (M : ShortestDistances G) (T : V → Prop)
    (s : V) (hs : T s) {v : V} {k : Nat} (R : ChargedReach G T s v k) :
    ∃ u : V, ∃ budget tail : Nat, T u ∧ TerminalRoute M T s u budget ∧
      Nonempty (Walk G u v tail) ∧ budget+tail≤k ∧ (T v→tail=0) := by
  induction R with
  | start =>
      exact ⟨s,0,0,hs,TerminalRoute.start hs,⟨Walk.trivial G s⟩,by omega,fun _ => rfl⟩
  | @add x y k _ edge ih =>
      obtain ⟨u,budget,tail,hu,route,⟨walk⟩,hb,_⟩ := ih
      have joined := walk.concat (unitWalk edge)
      by_cases terminal : T y
      · have ell := M.minimal u y (tail+1) joined
        refine ⟨y,budget+(M.dist u y-1),0,terminal,route.add terminal,
          ⟨Walk.trivial G y⟩,?_,fun _ => rfl⟩
        rw [charge_eq_zero T terminal]
        omega
      · refine ⟨u,budget,tail+1,hu,route,⟨joined⟩,?_,fun h => (terminal h).elim⟩
        rw [charge_eq_one T terminal]
        omega

theorem potential_gives_terminal_route (M : ShortestDistances G) (T : V → Prop)
    (s t : V) (hs : T s) (ht : T t) :
    ∃ budget, TerminalRoute M T s t budget ∧ budget ≤ potential M T s t := by
  obtain ⟨u,budget,tail,_,route,⟨walk⟩,hb,hterm⟩ :=
    charge_to_terminal_route_aux M T s hs (potential_witness M T s t)
  have htail := hterm ht
  subst tail
  have e := walk.zero_endpoints
  subst u
  exact ⟨budget,route,by omega⟩

theorem terminal_route_of_cap (M : ShortestDistances G) (T : V → Prop)
    (s t : V) (hs : T s) (ht : T t) (c : Nat) (cap : PackingCap G T c) :
    ∃ budget, TerminalRoute M T s t budget ∧ budget≤c := by
  obtain ⟨budget,route,hb⟩ := potential_gives_terminal_route M T s t hs ht
  exact ⟨budget,route,Nat.le_trans hb (potential_le_packing_cap M T s t hs ht c cap)⟩

end HakKozerenkoSeparatorGraph

#print axioms HakKozerenkoSeparatorGraph.hit_potential_level
#print axioms HakKozerenkoSeparatorGraph.potential_le_packing_cap
#print axioms HakKozerenkoSeparatorGraph.terminal_route_of_cap
