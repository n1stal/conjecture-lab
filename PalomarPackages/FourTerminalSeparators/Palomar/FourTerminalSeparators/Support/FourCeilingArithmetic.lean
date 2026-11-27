module

public import Std
public import Lean.Elab.Tactic.Omega

@[expose] public section

namespace HakKozerenkoFourSeparator

/-- For a fixed endpoint pair z with opposite distance z', the 1-, 2-
and 3-edge simple complete-terminal routes. The distance-minus-one
weight is expressed without truncated subtraction: add the number of edges
to the right side instead. The other opposite pairs are x,x' and y,y'. -/
def ShortRoute (c z z' x x' y y' : Nat) : Prop :=
  z ≤ c+1 ∨ x+y' ≤ c+2 ∨ y+x' ≤ c+2 ∨
    x+z'+x' ≤ c+3 ∨ y+z'+y' ≤ c+3

/-- For differences at most one in opposing entries, even the three-edge
route bounds give the improved diameter ceiling. -/
theorem pair_cap_from_short_route (c z z' x x' y y' : Nat)
    (near : z ≤ z'+1) (hx : 0<x) (hx' : 0<x') (hy : 0<y) (hy' : 0<y')
    (tri₀ : z ≤ x+y') (tri₁ : z ≤ y+x')
    (route : ShortRoute c z z' x x' y y') : z ≤ c+2 := by
  rcases route with h|h|h|h|h <;> omega

def TripleCaps (c a A b B d D : Nat) : Prop :=
  a+b+D ≤ 2*c+6 ∧ a+d+B ≤ 2*c+6 ∧
  b+d+A ≤ 2*c+6 ∧ D+B+A ≤ 2*c+6

/-- Opposite pairs (a,A), (b,B), (d,D) are (01,23), (02,13), (03,12).
Each row lists the relabelled complete-terminal route costs. -/
def AllShortRoutes (c a A b B d D : Nat) : Prop :=
  ShortRoute c a A b B d D ∧ ShortRoute c A a b B D d ∧
  ShortRoute c b B a A d D ∧ ShortRoute c B b a A D d ∧
  ShortRoute c d D a A b B ∧ ShortRoute c D d a A B b

def Triangles (a A b B d D : Nat) : Prop :=
  a ≤ b+D ∧ a ≤ d+B ∧ A ≤ b+d ∧ A ≤ D+B ∧
  b ≤ a+D ∧ b ≤ d+A ∧ B ≤ a+d ∧ B ≤ D+A ∧
  d ≤ a+B ∧ d ≤ b+A ∧ D ≤ a+b ∧ D ≤ B+A

/-- The full finite six-distance implication for the vertex separator
ceiling. Graph arguments (triple caps, every fixed-pair route, and the
ball/group lower bound) are explicit hypotheses. -/
theorem vertex_ceiling_arithmetic (c a A b B d D : Nat)
    (positive : 0<a ∧ 0<A ∧ 0<b ∧ 0<B ∧ 0<d ∧ 0<D)
    (triple : TripleCaps c a A b B d D)
    (tri : Triangles a A b B d D)
    (routes : AllShortRoutes c a A b B d D)
    (order : min a A ≤ min b B ∧ min b B ≤ min d D)
    (cluster : min a A + min b B ≤ c+3) :
    a+A+b+B+d+D ≤ 4*c+10 := by
  by_cases goal : a+A+b+B+d+D ≤ 4*c+10
  · exact goal
  · rcases positive with ⟨ha,hA,hb,hB,hd,hD⟩
    rcases triple with ⟨t₁,t₂,t₃,t₄⟩
    rcases tri with ⟨t_a₀,t_a₁,t_A₀,t_A₁,t_b₀,t_b₁,t_B₀,t_B₁,t_d₀,t_d₁,t_D₀,t_D₁⟩
    rcases routes with ⟨r_a,r_A,r_b,r_B,r_d,r_D⟩
    have u_a : a≤A+1 := by omega
    have u_A : A≤a+1 := by omega
    have u_b : b≤B+1 := by omega
    have u_B : B≤b+1 := by omega
    have u_d : d≤D+1 := by omega
    have u_D : D≤d+1 := by omega
    have s_a := pair_cap_from_short_route c a A b B d D u_a hb hB hd hD t_a₀ t_a₁ r_a
    have s_A := pair_cap_from_short_route c A a b B D d u_A hb hB hD hd t_A₀ t_A₁ r_A
    have s_b := pair_cap_from_short_route c b B a A d D u_b ha hA hd hD t_b₀ t_b₁ r_b
    have s_B := pair_cap_from_short_route c B b a A D d u_B ha hA hD hd t_B₀ t_B₁ r_B
    have s_d := pair_cap_from_short_route c d D a A b B u_d ha hA hb hB t_d₀ t_d₁ r_d
    have s_D := pair_cap_from_short_route c D d a A B b u_D ha hA hB hb t_D₀ t_D₁ r_D
    by_cases ia : a≤A <;> by_cases ib : b≤B <;> by_cases id : d≤D
    all_goals simp [Nat.min_def,ia,ib,id] at order cluster
    all_goals first
      | have hh : d≤D := by assumption
        rcases r_D with h|h|h|h|h <;> omega
      | rcases r_d with h|h|h|h|h <;> omega

theorem triple_vertex_rounding (c P : Nat) (h : (P-3)/2 ≤ c+1) :
    P≤2*c+6 := by omega

theorem ball_group_rounding (a b : Nat) (ha : 0<a) (hab : a≤b) :
    a+b-3 ≤ 4*((a-1)/2)+(b-2*((a-1)/2)-1) := by omega

/-- Natural-number form of max(0, ceil((S-10)/4)). -/
theorem vertex_ceiling_as_minimum (S c : Nat) :
    (S-7)/4 ≤ c ↔ S ≤ 4*c+10 := by omega

/-- The three successive positive gaps 1, c+1-j, 1+j on the
tree witness have the advertised nonterminal count and distance sum. -/
theorem path_witness_arithmetic (c j : Nat) (hj : j≤c) :
    1+(c+1-j)+(1+j)-3=c ∧
      3+4*(c+1-j)+3*(1+j)=4*c+10-j := by omega

end HakKozerenkoFourSeparator

#print axioms HakKozerenkoFourSeparator.vertex_ceiling_arithmetic
#print axioms HakKozerenkoFourSeparator.triple_vertex_rounding
#print axioms HakKozerenkoFourSeparator.ball_group_rounding
#print axioms HakKozerenkoFourSeparator.vertex_ceiling_as_minimum
#print axioms HakKozerenkoFourSeparator.path_witness_arithmetic
