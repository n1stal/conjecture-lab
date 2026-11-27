module

public import Palomar.WeightedTerminalPacking.Data.Step14

@[expose] public section

namespace Q3K5Hull
open TriameterQ3PackingWindows TriameterQ3SmallPacking
set_option maxRecDepth 20000
set_option maxHeartbeats 0

def stages : List (Stage 26) :=
  [stage00, stage01, stage02, stage03, stage04, stage05, stage06, stage07, stage08, stage09, stage10, stage11, stage12, stage13, stage14]

theorem stages_valid : checkedChain initialSystem stages := by
  exact ⟨check00, check01, check02, check03, check04, check05, check06, check07, check08, check09, check10, check11, check12, check13, check14,trivial⟩

def initialVals (R : Nat) (x : Fin 5 → Fin 5 → Nat) (i : Fin 26) : Int :=
  ((#v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, x 0 1, x 0 2, x 0 3, x 0 4, x 1 2, x 1 3, x 1 4, x 2 3, x 2 4, x 3 4, R] : Vector Nat 26).get i : Int)

theorem terminal_facets_valid (R : Nat) (x : Fin 5 → Fin 5 → Nat)
    (F : FiveFacets R x) : systemValid stage14.keep (initialVals R x) := by
  intro r hr
  change r ∈ [
    #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1],
    #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1],
    #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1],
    #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1],
    #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1],
    #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1],
    #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1],
    #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1],
    #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1],
    #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1],
    #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, -2],
    #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, -2],
    #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, -2],
    #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, -2],
    #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, -2],
    #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, -2],
    #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, -2],
    #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, -2],
    #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, -2],
    #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, -2],
    #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0, -4],
    #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, -4],
    #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, -4],
    #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 1, -4],
    #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, -4],
    #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, -4],
    #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, -4],
    #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, -4],
    #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 1, 0, -4],
    #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1, -4],
    #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, -4],
    #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, -4],
    #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -6]] at hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst r
  · change ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*((x 0 1 : Int)) + ((0 : Int)*((x 0 2 : Int)) + ((0 : Int)*((x 0 3 : Int)) + ((0 : Int)*((x 0 4 : Int)) + ((0 : Int)*((x 1 2 : Int)) + ((0 : Int)*((x 1 3 : Int)) + ((0 : Int)*((x 1 4 : Int)) + ((0 : Int)*((x 2 3 : Int)) + ((0 : Int)*((x 2 4 : Int)) + ((1 : Int)*((x 3 4 : Int)) + ((-1 : Int)*((R : Int)) + 0)))))))))))))))))))))))))) ≤ (0 : Int)
    have h := F.box 3 4
    omega
  · change ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*((x 0 1 : Int)) + ((0 : Int)*((x 0 2 : Int)) + ((0 : Int)*((x 0 3 : Int)) + ((0 : Int)*((x 0 4 : Int)) + ((0 : Int)*((x 1 2 : Int)) + ((0 : Int)*((x 1 3 : Int)) + ((0 : Int)*((x 1 4 : Int)) + ((0 : Int)*((x 2 3 : Int)) + ((1 : Int)*((x 2 4 : Int)) + ((0 : Int)*((x 3 4 : Int)) + ((-1 : Int)*((R : Int)) + 0)))))))))))))))))))))))))) ≤ (0 : Int)
    have h := F.box 2 4
    omega
  · change ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*((x 0 1 : Int)) + ((0 : Int)*((x 0 2 : Int)) + ((0 : Int)*((x 0 3 : Int)) + ((0 : Int)*((x 0 4 : Int)) + ((0 : Int)*((x 1 2 : Int)) + ((0 : Int)*((x 1 3 : Int)) + ((0 : Int)*((x 1 4 : Int)) + ((1 : Int)*((x 2 3 : Int)) + ((0 : Int)*((x 2 4 : Int)) + ((0 : Int)*((x 3 4 : Int)) + ((-1 : Int)*((R : Int)) + 0)))))))))))))))))))))))))) ≤ (0 : Int)
    have h := F.box 2 3
    omega
  · change ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*((x 0 1 : Int)) + ((0 : Int)*((x 0 2 : Int)) + ((0 : Int)*((x 0 3 : Int)) + ((0 : Int)*((x 0 4 : Int)) + ((0 : Int)*((x 1 2 : Int)) + ((0 : Int)*((x 1 3 : Int)) + ((1 : Int)*((x 1 4 : Int)) + ((0 : Int)*((x 2 3 : Int)) + ((0 : Int)*((x 2 4 : Int)) + ((0 : Int)*((x 3 4 : Int)) + ((-1 : Int)*((R : Int)) + 0)))))))))))))))))))))))))) ≤ (0 : Int)
    have h := F.box 1 4
    omega
  · change ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*((x 0 1 : Int)) + ((0 : Int)*((x 0 2 : Int)) + ((0 : Int)*((x 0 3 : Int)) + ((0 : Int)*((x 0 4 : Int)) + ((0 : Int)*((x 1 2 : Int)) + ((1 : Int)*((x 1 3 : Int)) + ((0 : Int)*((x 1 4 : Int)) + ((0 : Int)*((x 2 3 : Int)) + ((0 : Int)*((x 2 4 : Int)) + ((0 : Int)*((x 3 4 : Int)) + ((-1 : Int)*((R : Int)) + 0)))))))))))))))))))))))))) ≤ (0 : Int)
    have h := F.box 1 3
    omega
  · change ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*((x 0 1 : Int)) + ((0 : Int)*((x 0 2 : Int)) + ((0 : Int)*((x 0 3 : Int)) + ((0 : Int)*((x 0 4 : Int)) + ((1 : Int)*((x 1 2 : Int)) + ((0 : Int)*((x 1 3 : Int)) + ((0 : Int)*((x 1 4 : Int)) + ((0 : Int)*((x 2 3 : Int)) + ((0 : Int)*((x 2 4 : Int)) + ((0 : Int)*((x 3 4 : Int)) + ((-1 : Int)*((R : Int)) + 0)))))))))))))))))))))))))) ≤ (0 : Int)
    have h := F.box 1 2
    omega
  · change ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*((x 0 1 : Int)) + ((0 : Int)*((x 0 2 : Int)) + ((0 : Int)*((x 0 3 : Int)) + ((1 : Int)*((x 0 4 : Int)) + ((0 : Int)*((x 1 2 : Int)) + ((0 : Int)*((x 1 3 : Int)) + ((0 : Int)*((x 1 4 : Int)) + ((0 : Int)*((x 2 3 : Int)) + ((0 : Int)*((x 2 4 : Int)) + ((0 : Int)*((x 3 4 : Int)) + ((-1 : Int)*((R : Int)) + 0)))))))))))))))))))))))))) ≤ (0 : Int)
    have h := F.box 0 4
    omega
  · change ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*((x 0 1 : Int)) + ((0 : Int)*((x 0 2 : Int)) + ((1 : Int)*((x 0 3 : Int)) + ((0 : Int)*((x 0 4 : Int)) + ((0 : Int)*((x 1 2 : Int)) + ((0 : Int)*((x 1 3 : Int)) + ((0 : Int)*((x 1 4 : Int)) + ((0 : Int)*((x 2 3 : Int)) + ((0 : Int)*((x 2 4 : Int)) + ((0 : Int)*((x 3 4 : Int)) + ((-1 : Int)*((R : Int)) + 0)))))))))))))))))))))))))) ≤ (0 : Int)
    have h := F.box 0 3
    omega
  · change ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*((x 0 1 : Int)) + ((1 : Int)*((x 0 2 : Int)) + ((0 : Int)*((x 0 3 : Int)) + ((0 : Int)*((x 0 4 : Int)) + ((0 : Int)*((x 1 2 : Int)) + ((0 : Int)*((x 1 3 : Int)) + ((0 : Int)*((x 1 4 : Int)) + ((0 : Int)*((x 2 3 : Int)) + ((0 : Int)*((x 2 4 : Int)) + ((0 : Int)*((x 3 4 : Int)) + ((-1 : Int)*((R : Int)) + 0)))))))))))))))))))))))))) ≤ (0 : Int)
    have h := F.box 0 2
    omega
  · change ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((1 : Int)*((x 0 1 : Int)) + ((0 : Int)*((x 0 2 : Int)) + ((0 : Int)*((x 0 3 : Int)) + ((0 : Int)*((x 0 4 : Int)) + ((0 : Int)*((x 1 2 : Int)) + ((0 : Int)*((x 1 3 : Int)) + ((0 : Int)*((x 1 4 : Int)) + ((0 : Int)*((x 2 3 : Int)) + ((0 : Int)*((x 2 4 : Int)) + ((0 : Int)*((x 3 4 : Int)) + ((-1 : Int)*((R : Int)) + 0)))))))))))))))))))))))))) ≤ (0 : Int)
    have h := F.box 0 1
    omega
  · change ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*((x 0 1 : Int)) + ((0 : Int)*((x 0 2 : Int)) + ((0 : Int)*((x 0 3 : Int)) + ((0 : Int)*((x 0 4 : Int)) + ((0 : Int)*((x 1 2 : Int)) + ((0 : Int)*((x 1 3 : Int)) + ((0 : Int)*((x 1 4 : Int)) + ((1 : Int)*((x 2 3 : Int)) + ((1 : Int)*((x 2 4 : Int)) + ((1 : Int)*((x 3 4 : Int)) + ((-2 : Int)*((R : Int)) + 0)))))))))))))))))))))))))) ≤ (0 : Int)
    have h := F.triangle 2 3 4
    omega
  · change ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*((x 0 1 : Int)) + ((0 : Int)*((x 0 2 : Int)) + ((0 : Int)*((x 0 3 : Int)) + ((0 : Int)*((x 0 4 : Int)) + ((0 : Int)*((x 1 2 : Int)) + ((1 : Int)*((x 1 3 : Int)) + ((1 : Int)*((x 1 4 : Int)) + ((0 : Int)*((x 2 3 : Int)) + ((0 : Int)*((x 2 4 : Int)) + ((1 : Int)*((x 3 4 : Int)) + ((-2 : Int)*((R : Int)) + 0)))))))))))))))))))))))))) ≤ (0 : Int)
    have h := F.triangle 1 3 4
    omega
  · change ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*((x 0 1 : Int)) + ((0 : Int)*((x 0 2 : Int)) + ((0 : Int)*((x 0 3 : Int)) + ((0 : Int)*((x 0 4 : Int)) + ((1 : Int)*((x 1 2 : Int)) + ((0 : Int)*((x 1 3 : Int)) + ((1 : Int)*((x 1 4 : Int)) + ((0 : Int)*((x 2 3 : Int)) + ((1 : Int)*((x 2 4 : Int)) + ((0 : Int)*((x 3 4 : Int)) + ((-2 : Int)*((R : Int)) + 0)))))))))))))))))))))))))) ≤ (0 : Int)
    have h := F.triangle 1 2 4
    omega
  · change ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*((x 0 1 : Int)) + ((0 : Int)*((x 0 2 : Int)) + ((0 : Int)*((x 0 3 : Int)) + ((0 : Int)*((x 0 4 : Int)) + ((1 : Int)*((x 1 2 : Int)) + ((1 : Int)*((x 1 3 : Int)) + ((0 : Int)*((x 1 4 : Int)) + ((1 : Int)*((x 2 3 : Int)) + ((0 : Int)*((x 2 4 : Int)) + ((0 : Int)*((x 3 4 : Int)) + ((-2 : Int)*((R : Int)) + 0)))))))))))))))))))))))))) ≤ (0 : Int)
    have h := F.triangle 1 2 3
    omega
  · change ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*((x 0 1 : Int)) + ((0 : Int)*((x 0 2 : Int)) + ((1 : Int)*((x 0 3 : Int)) + ((1 : Int)*((x 0 4 : Int)) + ((0 : Int)*((x 1 2 : Int)) + ((0 : Int)*((x 1 3 : Int)) + ((0 : Int)*((x 1 4 : Int)) + ((0 : Int)*((x 2 3 : Int)) + ((0 : Int)*((x 2 4 : Int)) + ((1 : Int)*((x 3 4 : Int)) + ((-2 : Int)*((R : Int)) + 0)))))))))))))))))))))))))) ≤ (0 : Int)
    have h := F.triangle 0 3 4
    omega
  · change ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*((x 0 1 : Int)) + ((1 : Int)*((x 0 2 : Int)) + ((0 : Int)*((x 0 3 : Int)) + ((1 : Int)*((x 0 4 : Int)) + ((0 : Int)*((x 1 2 : Int)) + ((0 : Int)*((x 1 3 : Int)) + ((0 : Int)*((x 1 4 : Int)) + ((0 : Int)*((x 2 3 : Int)) + ((1 : Int)*((x 2 4 : Int)) + ((0 : Int)*((x 3 4 : Int)) + ((-2 : Int)*((R : Int)) + 0)))))))))))))))))))))))))) ≤ (0 : Int)
    have h := F.triangle 0 2 4
    omega
  · change ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*((x 0 1 : Int)) + ((1 : Int)*((x 0 2 : Int)) + ((1 : Int)*((x 0 3 : Int)) + ((0 : Int)*((x 0 4 : Int)) + ((0 : Int)*((x 1 2 : Int)) + ((0 : Int)*((x 1 3 : Int)) + ((0 : Int)*((x 1 4 : Int)) + ((1 : Int)*((x 2 3 : Int)) + ((0 : Int)*((x 2 4 : Int)) + ((0 : Int)*((x 3 4 : Int)) + ((-2 : Int)*((R : Int)) + 0)))))))))))))))))))))))))) ≤ (0 : Int)
    have h := F.triangle 0 2 3
    omega
  · change ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((1 : Int)*((x 0 1 : Int)) + ((0 : Int)*((x 0 2 : Int)) + ((0 : Int)*((x 0 3 : Int)) + ((1 : Int)*((x 0 4 : Int)) + ((0 : Int)*((x 1 2 : Int)) + ((0 : Int)*((x 1 3 : Int)) + ((1 : Int)*((x 1 4 : Int)) + ((0 : Int)*((x 2 3 : Int)) + ((0 : Int)*((x 2 4 : Int)) + ((0 : Int)*((x 3 4 : Int)) + ((-2 : Int)*((R : Int)) + 0)))))))))))))))))))))))))) ≤ (0 : Int)
    have h := F.triangle 0 1 4
    omega
  · change ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((1 : Int)*((x 0 1 : Int)) + ((0 : Int)*((x 0 2 : Int)) + ((1 : Int)*((x 0 3 : Int)) + ((0 : Int)*((x 0 4 : Int)) + ((0 : Int)*((x 1 2 : Int)) + ((1 : Int)*((x 1 3 : Int)) + ((0 : Int)*((x 1 4 : Int)) + ((0 : Int)*((x 2 3 : Int)) + ((0 : Int)*((x 2 4 : Int)) + ((0 : Int)*((x 3 4 : Int)) + ((-2 : Int)*((R : Int)) + 0)))))))))))))))))))))))))) ≤ (0 : Int)
    have h := F.triangle 0 1 3
    omega
  · change ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((1 : Int)*((x 0 1 : Int)) + ((1 : Int)*((x 0 2 : Int)) + ((0 : Int)*((x 0 3 : Int)) + ((0 : Int)*((x 0 4 : Int)) + ((1 : Int)*((x 1 2 : Int)) + ((0 : Int)*((x 1 3 : Int)) + ((0 : Int)*((x 1 4 : Int)) + ((0 : Int)*((x 2 3 : Int)) + ((0 : Int)*((x 2 4 : Int)) + ((0 : Int)*((x 3 4 : Int)) + ((-2 : Int)*((R : Int)) + 0)))))))))))))))))))))))))) ≤ (0 : Int)
    have h := F.triangle 0 1 2
    omega
  · change ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*((x 0 1 : Int)) + ((0 : Int)*((x 0 2 : Int)) + ((1 : Int)*((x 0 3 : Int)) + ((1 : Int)*((x 0 4 : Int)) + ((1 : Int)*((x 1 2 : Int)) + ((0 : Int)*((x 1 3 : Int)) + ((1 : Int)*((x 1 4 : Int)) + ((1 : Int)*((x 2 3 : Int)) + ((0 : Int)*((x 2 4 : Int)) + ((0 : Int)*((x 3 4 : Int)) + ((-4 : Int)*((R : Int)) + 0)))))))))))))))))))))))))) ≤ (0 : Int)
    let p : Fin 5 → Fin 5 := fun i => if i = 0 then 4 else if i = 1 then 1 else if i = 2 then 2 else if i = 3 then 3 else 0
    have hp : ∀ i j : Fin 5, i ≠ j → p i ≠ p j := by dsimp [p]; decide
    have h := F.cycle p (fun a b he => by by_cases hb : a=b; exact hb; exact (hp a b hb he).elim)
    change x 4 1+x 1 2+x 2 3+x 3 0+x 4 0 ≤ _ at h
    rw [F.symmetric 4 1] at h
    rw [F.symmetric 3 0] at h
    rw [F.symmetric 4 0] at h
    omega
  · change ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*((x 0 1 : Int)) + ((0 : Int)*((x 0 2 : Int)) + ((1 : Int)*((x 0 3 : Int)) + ((1 : Int)*((x 0 4 : Int)) + ((1 : Int)*((x 1 2 : Int)) + ((1 : Int)*((x 1 3 : Int)) + ((0 : Int)*((x 1 4 : Int)) + ((0 : Int)*((x 2 3 : Int)) + ((1 : Int)*((x 2 4 : Int)) + ((0 : Int)*((x 3 4 : Int)) + ((-4 : Int)*((R : Int)) + 0)))))))))))))))))))))))))) ≤ (0 : Int)
    let p : Fin 5 → Fin 5 := fun i => if i = 0 then 4 else if i = 1 then 2 else if i = 2 then 1 else if i = 3 then 3 else 0
    have hp : ∀ i j : Fin 5, i ≠ j → p i ≠ p j := by dsimp [p]; decide
    have h := F.cycle p (fun a b he => by by_cases hb : a=b; exact hb; exact (hp a b hb he).elim)
    change x 4 2+x 2 1+x 1 3+x 3 0+x 4 0 ≤ _ at h
    rw [F.symmetric 4 2] at h
    rw [F.symmetric 2 1] at h
    rw [F.symmetric 3 0] at h
    rw [F.symmetric 4 0] at h
    omega
  · change ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*((x 0 1 : Int)) + ((1 : Int)*((x 0 2 : Int)) + ((0 : Int)*((x 0 3 : Int)) + ((1 : Int)*((x 0 4 : Int)) + ((0 : Int)*((x 1 2 : Int)) + ((1 : Int)*((x 1 3 : Int)) + ((1 : Int)*((x 1 4 : Int)) + ((1 : Int)*((x 2 3 : Int)) + ((0 : Int)*((x 2 4 : Int)) + ((0 : Int)*((x 3 4 : Int)) + ((-4 : Int)*((R : Int)) + 0)))))))))))))))))))))))))) ≤ (0 : Int)
    let p : Fin 5 → Fin 5 := fun i => if i = 0 then 4 else if i = 1 then 1 else if i = 2 then 3 else if i = 3 then 2 else 0
    have hp : ∀ i j : Fin 5, i ≠ j → p i ≠ p j := by dsimp [p]; decide
    have h := F.cycle p (fun a b he => by by_cases hb : a=b; exact hb; exact (hp a b hb he).elim)
    change x 4 1+x 1 3+x 3 2+x 2 0+x 4 0 ≤ _ at h
    rw [F.symmetric 4 1] at h
    rw [F.symmetric 3 2] at h
    rw [F.symmetric 2 0] at h
    rw [F.symmetric 4 0] at h
    omega
  · change ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*((x 0 1 : Int)) + ((1 : Int)*((x 0 2 : Int)) + ((0 : Int)*((x 0 3 : Int)) + ((1 : Int)*((x 0 4 : Int)) + ((1 : Int)*((x 1 2 : Int)) + ((1 : Int)*((x 1 3 : Int)) + ((0 : Int)*((x 1 4 : Int)) + ((0 : Int)*((x 2 3 : Int)) + ((0 : Int)*((x 2 4 : Int)) + ((1 : Int)*((x 3 4 : Int)) + ((-4 : Int)*((R : Int)) + 0)))))))))))))))))))))))))) ≤ (0 : Int)
    let p : Fin 5 → Fin 5 := fun i => if i = 0 then 4 else if i = 1 then 3 else if i = 2 then 1 else if i = 3 then 2 else 0
    have hp : ∀ i j : Fin 5, i ≠ j → p i ≠ p j := by dsimp [p]; decide
    have h := F.cycle p (fun a b he => by by_cases hb : a=b; exact hb; exact (hp a b hb he).elim)
    change x 4 3+x 3 1+x 1 2+x 2 0+x 4 0 ≤ _ at h
    rw [F.symmetric 4 3] at h
    rw [F.symmetric 3 1] at h
    rw [F.symmetric 2 0] at h
    rw [F.symmetric 4 0] at h
    omega
  · change ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*((x 0 1 : Int)) + ((1 : Int)*((x 0 2 : Int)) + ((1 : Int)*((x 0 3 : Int)) + ((0 : Int)*((x 0 4 : Int)) + ((0 : Int)*((x 1 2 : Int)) + ((1 : Int)*((x 1 3 : Int)) + ((1 : Int)*((x 1 4 : Int)) + ((0 : Int)*((x 2 3 : Int)) + ((1 : Int)*((x 2 4 : Int)) + ((0 : Int)*((x 3 4 : Int)) + ((-4 : Int)*((R : Int)) + 0)))))))))))))))))))))))))) ≤ (0 : Int)
    let p : Fin 5 → Fin 5 := fun i => if i = 0 then 4 else if i = 1 then 2 else if i = 2 then 0 else if i = 3 then 3 else 1
    have hp : ∀ i j : Fin 5, i ≠ j → p i ≠ p j := by dsimp [p]; decide
    have h := F.cycle p (fun a b he => by by_cases hb : a=b; exact hb; exact (hp a b hb he).elim)
    change x 4 2+x 2 0+x 0 3+x 3 1+x 4 1 ≤ _ at h
    rw [F.symmetric 4 2] at h
    rw [F.symmetric 2 0] at h
    rw [F.symmetric 3 1] at h
    rw [F.symmetric 4 1] at h
    omega
  · change ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*((x 0 1 : Int)) + ((1 : Int)*((x 0 2 : Int)) + ((1 : Int)*((x 0 3 : Int)) + ((0 : Int)*((x 0 4 : Int)) + ((1 : Int)*((x 1 2 : Int)) + ((0 : Int)*((x 1 3 : Int)) + ((1 : Int)*((x 1 4 : Int)) + ((0 : Int)*((x 2 3 : Int)) + ((0 : Int)*((x 2 4 : Int)) + ((1 : Int)*((x 3 4 : Int)) + ((-4 : Int)*((R : Int)) + 0)))))))))))))))))))))))))) ≤ (0 : Int)
    let p : Fin 5 → Fin 5 := fun i => if i = 0 then 4 else if i = 1 then 3 else if i = 2 then 0 else if i = 3 then 2 else 1
    have hp : ∀ i j : Fin 5, i ≠ j → p i ≠ p j := by dsimp [p]; decide
    have h := F.cycle p (fun a b he => by by_cases hb : a=b; exact hb; exact (hp a b hb he).elim)
    change x 4 3+x 3 0+x 0 2+x 2 1+x 4 1 ≤ _ at h
    rw [F.symmetric 4 3] at h
    rw [F.symmetric 3 0] at h
    rw [F.symmetric 2 1] at h
    rw [F.symmetric 4 1] at h
    omega
  · change ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((1 : Int)*((x 0 1 : Int)) + ((0 : Int)*((x 0 2 : Int)) + ((0 : Int)*((x 0 3 : Int)) + ((1 : Int)*((x 0 4 : Int)) + ((0 : Int)*((x 1 2 : Int)) + ((1 : Int)*((x 1 3 : Int)) + ((0 : Int)*((x 1 4 : Int)) + ((1 : Int)*((x 2 3 : Int)) + ((1 : Int)*((x 2 4 : Int)) + ((0 : Int)*((x 3 4 : Int)) + ((-4 : Int)*((R : Int)) + 0)))))))))))))))))))))))))) ≤ (0 : Int)
    let p : Fin 5 → Fin 5 := fun i => if i = 0 then 4 else if i = 1 then 2 else if i = 2 then 3 else if i = 3 then 1 else 0
    have hp : ∀ i j : Fin 5, i ≠ j → p i ≠ p j := by dsimp [p]; decide
    have h := F.cycle p (fun a b he => by by_cases hb : a=b; exact hb; exact (hp a b hb he).elim)
    change x 4 2+x 2 3+x 3 1+x 1 0+x 4 0 ≤ _ at h
    rw [F.symmetric 4 2] at h
    rw [F.symmetric 3 1] at h
    rw [F.symmetric 1 0] at h
    rw [F.symmetric 4 0] at h
    omega
  · change ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((1 : Int)*((x 0 1 : Int)) + ((0 : Int)*((x 0 2 : Int)) + ((0 : Int)*((x 0 3 : Int)) + ((1 : Int)*((x 0 4 : Int)) + ((1 : Int)*((x 1 2 : Int)) + ((0 : Int)*((x 1 3 : Int)) + ((0 : Int)*((x 1 4 : Int)) + ((1 : Int)*((x 2 3 : Int)) + ((0 : Int)*((x 2 4 : Int)) + ((1 : Int)*((x 3 4 : Int)) + ((-4 : Int)*((R : Int)) + 0)))))))))))))))))))))))))) ≤ (0 : Int)
    let p : Fin 5 → Fin 5 := fun i => if i = 0 then 4 else if i = 1 then 3 else if i = 2 then 2 else if i = 3 then 1 else 0
    have hp : ∀ i j : Fin 5, i ≠ j → p i ≠ p j := by dsimp [p]; decide
    have h := F.cycle p (fun a b he => by by_cases hb : a=b; exact hb; exact (hp a b hb he).elim)
    change x 4 3+x 3 2+x 2 1+x 1 0+x 4 0 ≤ _ at h
    rw [F.symmetric 4 3] at h
    rw [F.symmetric 3 2] at h
    rw [F.symmetric 2 1] at h
    rw [F.symmetric 1 0] at h
    rw [F.symmetric 4 0] at h
    omega
  · change ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((1 : Int)*((x 0 1 : Int)) + ((0 : Int)*((x 0 2 : Int)) + ((1 : Int)*((x 0 3 : Int)) + ((0 : Int)*((x 0 4 : Int)) + ((0 : Int)*((x 1 2 : Int)) + ((0 : Int)*((x 1 3 : Int)) + ((1 : Int)*((x 1 4 : Int)) + ((1 : Int)*((x 2 3 : Int)) + ((1 : Int)*((x 2 4 : Int)) + ((0 : Int)*((x 3 4 : Int)) + ((-4 : Int)*((R : Int)) + 0)))))))))))))))))))))))))) ≤ (0 : Int)
    let p : Fin 5 → Fin 5 := fun i => if i = 0 then 4 else if i = 1 then 2 else if i = 2 then 3 else if i = 3 then 0 else 1
    have hp : ∀ i j : Fin 5, i ≠ j → p i ≠ p j := by dsimp [p]; decide
    have h := F.cycle p (fun a b he => by by_cases hb : a=b; exact hb; exact (hp a b hb he).elim)
    change x 4 2+x 2 3+x 3 0+x 0 1+x 4 1 ≤ _ at h
    rw [F.symmetric 4 2] at h
    rw [F.symmetric 3 0] at h
    rw [F.symmetric 4 1] at h
    omega
  · change ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((1 : Int)*((x 0 1 : Int)) + ((0 : Int)*((x 0 2 : Int)) + ((1 : Int)*((x 0 3 : Int)) + ((0 : Int)*((x 0 4 : Int)) + ((1 : Int)*((x 1 2 : Int)) + ((0 : Int)*((x 1 3 : Int)) + ((0 : Int)*((x 1 4 : Int)) + ((0 : Int)*((x 2 3 : Int)) + ((1 : Int)*((x 2 4 : Int)) + ((1 : Int)*((x 3 4 : Int)) + ((-4 : Int)*((R : Int)) + 0)))))))))))))))))))))))))) ≤ (0 : Int)
    let p : Fin 5 → Fin 5 := fun i => if i = 0 then 4 else if i = 1 then 3 else if i = 2 then 0 else if i = 3 then 1 else 2
    have hp : ∀ i j : Fin 5, i ≠ j → p i ≠ p j := by dsimp [p]; decide
    have h := F.cycle p (fun a b he => by by_cases hb : a=b; exact hb; exact (hp a b hb he).elim)
    change x 4 3+x 3 0+x 0 1+x 1 2+x 4 2 ≤ _ at h
    rw [F.symmetric 4 3] at h
    rw [F.symmetric 3 0] at h
    rw [F.symmetric 4 2] at h
    omega
  · change ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((1 : Int)*((x 0 1 : Int)) + ((1 : Int)*((x 0 2 : Int)) + ((0 : Int)*((x 0 3 : Int)) + ((0 : Int)*((x 0 4 : Int)) + ((0 : Int)*((x 1 2 : Int)) + ((0 : Int)*((x 1 3 : Int)) + ((1 : Int)*((x 1 4 : Int)) + ((1 : Int)*((x 2 3 : Int)) + ((0 : Int)*((x 2 4 : Int)) + ((1 : Int)*((x 3 4 : Int)) + ((-4 : Int)*((R : Int)) + 0)))))))))))))))))))))))))) ≤ (0 : Int)
    let p : Fin 5 → Fin 5 := fun i => if i = 0 then 4 else if i = 1 then 3 else if i = 2 then 2 else if i = 3 then 0 else 1
    have hp : ∀ i j : Fin 5, i ≠ j → p i ≠ p j := by dsimp [p]; decide
    have h := F.cycle p (fun a b he => by by_cases hb : a=b; exact hb; exact (hp a b hb he).elim)
    change x 4 3+x 3 2+x 2 0+x 0 1+x 4 1 ≤ _ at h
    rw [F.symmetric 4 3] at h
    rw [F.symmetric 3 2] at h
    rw [F.symmetric 2 0] at h
    rw [F.symmetric 4 1] at h
    omega
  · change ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((1 : Int)*((x 0 1 : Int)) + ((1 : Int)*((x 0 2 : Int)) + ((0 : Int)*((x 0 3 : Int)) + ((0 : Int)*((x 0 4 : Int)) + ((0 : Int)*((x 1 2 : Int)) + ((1 : Int)*((x 1 3 : Int)) + ((0 : Int)*((x 1 4 : Int)) + ((0 : Int)*((x 2 3 : Int)) + ((1 : Int)*((x 2 4 : Int)) + ((1 : Int)*((x 3 4 : Int)) + ((-4 : Int)*((R : Int)) + 0)))))))))))))))))))))))))) ≤ (0 : Int)
    let p : Fin 5 → Fin 5 := fun i => if i = 0 then 4 else if i = 1 then 3 else if i = 2 then 1 else if i = 3 then 0 else 2
    have hp : ∀ i j : Fin 5, i ≠ j → p i ≠ p j := by dsimp [p]; decide
    have h := F.cycle p (fun a b he => by by_cases hb : a=b; exact hb; exact (hp a b hb he).elim)
    change x 4 3+x 3 1+x 1 0+x 0 2+x 4 2 ≤ _ at h
    rw [F.symmetric 4 3] at h
    rw [F.symmetric 3 1] at h
    rw [F.symmetric 1 0] at h
    rw [F.symmetric 4 2] at h
    omega
  · change ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((0 : Int)*(0) + ((1 : Int)*((x 0 1 : Int)) + ((1 : Int)*((x 0 2 : Int)) + ((1 : Int)*((x 0 3 : Int)) + ((1 : Int)*((x 0 4 : Int)) + ((1 : Int)*((x 1 2 : Int)) + ((1 : Int)*((x 1 3 : Int)) + ((1 : Int)*((x 1 4 : Int)) + ((1 : Int)*((x 2 3 : Int)) + ((1 : Int)*((x 2 4 : Int)) + ((1 : Int)*((x 3 4 : Int)) + ((-6 : Int)*((R : Int)) + 0)))))))))))))))))))))))))) ≤ (0 : Int)
    have h := F.total
    unfold fullSum5 at h
    omega

def natCut (w : Fin 26 → Int) (s : Fin 32) : Nat :=
  if s.val % 2 = 0 ∧ 0 < s.val then (w ⟨s.val/2-1,by omega⟩).toNat else 0

theorem fin5_all (i : Fin 5) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
  have hi := i.isLt
  have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 := by omega
  rcases h with h|h|h|h|h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext h))))

theorem gate_symm' (s : Fin 32) (i j : Fin 5) (a : Nat) :
    gate s i j a = gate s j i a := by
  unfold gate
  by_cases h : cutBits s i = cutBits s j
  · simp only [ite_eq_left h,ite_eq_left h.symm]
  · simp only [ite_eq_right h,ite_eq_right (Ne.symm h)]

def recover_cut (R : Nat) (x : Fin 5 → Fin 5 → Nat) (F : FiveFacets R x)
    (d : Int) (w : Fin 26 → Int) (hd : 0 < d) (hw : ∀ i, 0 ≤ w i)
    (hcoords : ∀ i : Fin 26, 15 ≤ i.val → w i = d*initialVals R x i)
    (hsol : systemValid initialSystem w) : CutCertificate5 R x := by
  have hd' : (d.toNat : Int) = d := Int.toNat_of_nonneg (Int.le_of_lt hd)
  have hw0 : ((w 0).toNat : Int) = w 0 := Int.toNat_of_nonneg (hw 0)
  have hw1 : ((w 1).toNat : Int) = w 1 := Int.toNat_of_nonneg (hw 1)
  have hw2 : ((w 2).toNat : Int) = w 2 := Int.toNat_of_nonneg (hw 2)
  have hw3 : ((w 3).toNat : Int) = w 3 := Int.toNat_of_nonneg (hw 3)
  have hw4 : ((w 4).toNat : Int) = w 4 := Int.toNat_of_nonneg (hw 4)
  have hw5 : ((w 5).toNat : Int) = w 5 := Int.toNat_of_nonneg (hw 5)
  have hw6 : ((w 6).toNat : Int) = w 6 := Int.toNat_of_nonneg (hw 6)
  have hw7 : ((w 7).toNat : Int) = w 7 := Int.toNat_of_nonneg (hw 7)
  have hw8 : ((w 8).toNat : Int) = w 8 := Int.toNat_of_nonneg (hw 8)
  have hw9 : ((w 9).toNat : Int) = w 9 := Int.toNat_of_nonneg (hw 9)
  have hw10 : ((w 10).toNat : Int) = w 10 := Int.toNat_of_nonneg (hw 10)
  have hw11 : ((w 11).toNat : Int) = w 11 := Int.toNat_of_nonneg (hw 11)
  have hw12 : ((w 12).toNat : Int) = w 12 := Int.toNat_of_nonneg (hw 12)
  have hw13 : ((w 13).toNat : Int) = w 13 := Int.toNat_of_nonneg (hw 13)
  have hw14 : ((w 14).toNat : Int) = w 14 := Int.toNat_of_nonneg (hw 14)

  refine ⟨d.toNat,natCut w,by omega,?_,?_⟩
  · have hi := hsol #v[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1] (by decide)
    change ((1 : Int)*(w 0) + ((1 : Int)*(w 1) + ((1 : Int)*(w 2) + ((1 : Int)*(w 3) + ((1 : Int)*(w 4) + ((1 : Int)*(w 5) + ((1 : Int)*(w 6) + ((1 : Int)*(w 7) + ((1 : Int)*(w 8) + ((1 : Int)*(w 9) + ((1 : Int)*(w 10) + ((1 : Int)*(w 11) + ((1 : Int)*(w 12) + ((1 : Int)*(w 13) + ((1 : Int)*(w 14) + ((0 : Int)*(w 15) + ((0 : Int)*(w 16) + ((0 : Int)*(w 17) + ((0 : Int)*(w 18) + ((0 : Int)*(w 19) + ((0 : Int)*(w 20) + ((0 : Int)*(w 21) + ((0 : Int)*(w 22) + ((0 : Int)*(w 23) + ((0 : Int)*(w 24) + ((-1 : Int)*(w 25) + 0)))))))))))))))))))))))))) ≤ (0 : Int) at hi
    have hr : w 25 = d*(R : Int) := hcoords 25 (by decide)
    have hb : (vsum 32 (natCut w) : Int) ≤ ((d.toNat*R : Nat) : Int) := by
      change (((0 + (0 + ((w 0).toNat + (0 + ((w 1).toNat + (0 + ((w 2).toNat + (0 + ((w 3).toNat + (0 + ((w 4).toNat + (0 + ((w 5).toNat + (0 + ((w 6).toNat + (0 + ((w 7).toNat + (0 + ((w 8).toNat + (0 + ((w 9).toNat + (0 + ((w 10).toNat + (0 + ((w 11).toNat + (0 + ((w 12).toNat + (0 + ((w 13).toNat + (0 + ((w 14).toNat + (0 + 0)))))))))))))))))))))))))))))))) : Nat) : Int) ≤ _
      simp only [Int.natCast_add,Int.natCast_mul,hd',hw0,hw1,hw2,hw3,hw4,hw5,hw6,hw7,hw8,hw9,hw10,hw11,hw12,hw13,hw14]
      omega
    exact Int.ofNat_le.mp hb
  · let H (i j : Fin 5) := d.toNat*x i j ≤ vsum 32 (fun s => gate s i j (natCut w s))
    have Hd (i : Fin 5) : H i i := by unfold H; rw [F.diagonal]; exact Nat.zero_le _
    have Hs (i j : Fin 5) (h : H i j) : H j i := by
      unfold H at h ⊢
      rw [F.symmetric j i]
      have e := vsum_congr (fun s => gate_symm' s j i (natCut w s))
      rw [e]
      exact h

    have H01 : H 0 1 := by
      have hi := hsol #v[-1, 0, -1, 0, -1, 0, -1, 0, -1, 0, -1, 0, -1, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide)
      change ((-1 : Int)*(w 0) + ((0 : Int)*(w 1) + ((-1 : Int)*(w 2) + ((0 : Int)*(w 3) + ((-1 : Int)*(w 4) + ((0 : Int)*(w 5) + ((-1 : Int)*(w 6) + ((0 : Int)*(w 7) + ((-1 : Int)*(w 8) + ((0 : Int)*(w 9) + ((-1 : Int)*(w 10) + ((0 : Int)*(w 11) + ((-1 : Int)*(w 12) + ((0 : Int)*(w 13) + ((-1 : Int)*(w 14) + ((1 : Int)*(w 15) + ((0 : Int)*(w 16) + ((0 : Int)*(w 17) + ((0 : Int)*(w 18) + ((0 : Int)*(w 19) + ((0 : Int)*(w 20) + ((0 : Int)*(w 21) + ((0 : Int)*(w 22) + ((0 : Int)*(w 23) + ((0 : Int)*(w 24) + ((0 : Int)*(w 25) + 0)))))))))))))))))))))))))) ≤ (0 : Int) at hi
      have hr : w 15 = d*(x 0 1 : Int) := hcoords 15 (by decide)
      have hb : ((d.toNat*x 0 1 : Nat) : Int) ≤ (vsum 32 (fun s => gate s 0 1 (natCut w s)) : Int) := by
        change _ ≤ (((0 + (0 + ((w 0).toNat + (0 + (0 + (0 + ((w 2).toNat + (0 + (0 + (0 + ((w 4).toNat + (0 + (0 + (0 + ((w 6).toNat + (0 + (0 + (0 + ((w 8).toNat + (0 + (0 + (0 + ((w 10).toNat + (0 + (0 + (0 + ((w 12).toNat + (0 + (0 + (0 + ((w 14).toNat + (0 + 0)))))))))))))))))))))))))))))))) : Nat) : Int)
        simp only [Int.natCast_add,Int.natCast_mul,hd',hw0,hw2,hw4,hw6,hw8,hw10,hw12,hw14]
        omega
      exact Int.ofNat_le.mp hb

    have H02 : H 0 2 := by
      have hi := hsol #v[0, -1, -1, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0, -1, -1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide)
      change ((0 : Int)*(w 0) + ((-1 : Int)*(w 1) + ((-1 : Int)*(w 2) + ((0 : Int)*(w 3) + ((0 : Int)*(w 4) + ((-1 : Int)*(w 5) + ((-1 : Int)*(w 6) + ((0 : Int)*(w 7) + ((0 : Int)*(w 8) + ((-1 : Int)*(w 9) + ((-1 : Int)*(w 10) + ((0 : Int)*(w 11) + ((0 : Int)*(w 12) + ((-1 : Int)*(w 13) + ((-1 : Int)*(w 14) + ((0 : Int)*(w 15) + ((1 : Int)*(w 16) + ((0 : Int)*(w 17) + ((0 : Int)*(w 18) + ((0 : Int)*(w 19) + ((0 : Int)*(w 20) + ((0 : Int)*(w 21) + ((0 : Int)*(w 22) + ((0 : Int)*(w 23) + ((0 : Int)*(w 24) + ((0 : Int)*(w 25) + 0)))))))))))))))))))))))))) ≤ (0 : Int) at hi
      have hr : w 16 = d*(x 0 2 : Int) := hcoords 16 (by decide)
      have hb : ((d.toNat*x 0 2 : Nat) : Int) ≤ (vsum 32 (fun s => gate s 0 2 (natCut w s)) : Int) := by
        change _ ≤ (((0 + (0 + (0 + (0 + ((w 1).toNat + (0 + ((w 2).toNat + (0 + (0 + (0 + (0 + (0 + ((w 5).toNat + (0 + ((w 6).toNat + (0 + (0 + (0 + (0 + (0 + ((w 9).toNat + (0 + ((w 10).toNat + (0 + (0 + (0 + (0 + (0 + ((w 13).toNat + (0 + ((w 14).toNat + (0 + 0)))))))))))))))))))))))))))))))) : Nat) : Int)
        simp only [Int.natCast_add,Int.natCast_mul,hd',hw1,hw2,hw5,hw6,hw9,hw10,hw13,hw14]
        omega
      exact Int.ofNat_le.mp hb

    have H03 : H 0 3 := by
      have hi := hsol #v[0, 0, 0, -1, -1, -1, -1, 0, 0, 0, 0, -1, -1, -1, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0] (by decide)
      change ((0 : Int)*(w 0) + ((0 : Int)*(w 1) + ((0 : Int)*(w 2) + ((-1 : Int)*(w 3) + ((-1 : Int)*(w 4) + ((-1 : Int)*(w 5) + ((-1 : Int)*(w 6) + ((0 : Int)*(w 7) + ((0 : Int)*(w 8) + ((0 : Int)*(w 9) + ((0 : Int)*(w 10) + ((-1 : Int)*(w 11) + ((-1 : Int)*(w 12) + ((-1 : Int)*(w 13) + ((-1 : Int)*(w 14) + ((0 : Int)*(w 15) + ((0 : Int)*(w 16) + ((1 : Int)*(w 17) + ((0 : Int)*(w 18) + ((0 : Int)*(w 19) + ((0 : Int)*(w 20) + ((0 : Int)*(w 21) + ((0 : Int)*(w 22) + ((0 : Int)*(w 23) + ((0 : Int)*(w 24) + ((0 : Int)*(w 25) + 0)))))))))))))))))))))))))) ≤ (0 : Int) at hi
      have hr : w 17 = d*(x 0 3 : Int) := hcoords 17 (by decide)
      have hb : ((d.toNat*x 0 3 : Nat) : Int) ≤ (vsum 32 (fun s => gate s 0 3 (natCut w s)) : Int) := by
        change _ ≤ (((0 + (0 + (0 + (0 + (0 + (0 + (0 + (0 + ((w 3).toNat + (0 + ((w 4).toNat + (0 + ((w 5).toNat + (0 + ((w 6).toNat + (0 + (0 + (0 + (0 + (0 + (0 + (0 + (0 + (0 + ((w 11).toNat + (0 + ((w 12).toNat + (0 + ((w 13).toNat + (0 + ((w 14).toNat + (0 + 0)))))))))))))))))))))))))))))))) : Nat) : Int)
        simp only [Int.natCast_add,Int.natCast_mul,hd',hw3,hw4,hw5,hw6,hw11,hw12,hw13,hw14]
        omega
      exact Int.ofNat_le.mp hb

    have H04 : H 0 4 := by
      have hi := hsol #v[0, 0, 0, 0, 0, 0, 0, -1, -1, -1, -1, -1, -1, -1, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0] (by decide)
      change ((0 : Int)*(w 0) + ((0 : Int)*(w 1) + ((0 : Int)*(w 2) + ((0 : Int)*(w 3) + ((0 : Int)*(w 4) + ((0 : Int)*(w 5) + ((0 : Int)*(w 6) + ((-1 : Int)*(w 7) + ((-1 : Int)*(w 8) + ((-1 : Int)*(w 9) + ((-1 : Int)*(w 10) + ((-1 : Int)*(w 11) + ((-1 : Int)*(w 12) + ((-1 : Int)*(w 13) + ((-1 : Int)*(w 14) + ((0 : Int)*(w 15) + ((0 : Int)*(w 16) + ((0 : Int)*(w 17) + ((1 : Int)*(w 18) + ((0 : Int)*(w 19) + ((0 : Int)*(w 20) + ((0 : Int)*(w 21) + ((0 : Int)*(w 22) + ((0 : Int)*(w 23) + ((0 : Int)*(w 24) + ((0 : Int)*(w 25) + 0)))))))))))))))))))))))))) ≤ (0 : Int) at hi
      have hr : w 18 = d*(x 0 4 : Int) := hcoords 18 (by decide)
      have hb : ((d.toNat*x 0 4 : Nat) : Int) ≤ (vsum 32 (fun s => gate s 0 4 (natCut w s)) : Int) := by
        change _ ≤ (((0 + (0 + (0 + (0 + (0 + (0 + (0 + (0 + (0 + (0 + (0 + (0 + (0 + (0 + (0 + (0 + ((w 7).toNat + (0 + ((w 8).toNat + (0 + ((w 9).toNat + (0 + ((w 10).toNat + (0 + ((w 11).toNat + (0 + ((w 12).toNat + (0 + ((w 13).toNat + (0 + ((w 14).toNat + (0 + 0)))))))))))))))))))))))))))))))) : Nat) : Int)
        simp only [Int.natCast_add,Int.natCast_mul,hd',hw7,hw8,hw9,hw10,hw11,hw12,hw13,hw14]
        omega
      exact Int.ofNat_le.mp hb

    have H12 : H 1 2 := by
      have hi := hsol #v[-1, -1, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0] (by decide)
      change ((-1 : Int)*(w 0) + ((-1 : Int)*(w 1) + ((0 : Int)*(w 2) + ((0 : Int)*(w 3) + ((-1 : Int)*(w 4) + ((-1 : Int)*(w 5) + ((0 : Int)*(w 6) + ((0 : Int)*(w 7) + ((-1 : Int)*(w 8) + ((-1 : Int)*(w 9) + ((0 : Int)*(w 10) + ((0 : Int)*(w 11) + ((-1 : Int)*(w 12) + ((-1 : Int)*(w 13) + ((0 : Int)*(w 14) + ((0 : Int)*(w 15) + ((0 : Int)*(w 16) + ((0 : Int)*(w 17) + ((0 : Int)*(w 18) + ((1 : Int)*(w 19) + ((0 : Int)*(w 20) + ((0 : Int)*(w 21) + ((0 : Int)*(w 22) + ((0 : Int)*(w 23) + ((0 : Int)*(w 24) + ((0 : Int)*(w 25) + 0)))))))))))))))))))))))))) ≤ (0 : Int) at hi
      have hr : w 19 = d*(x 1 2 : Int) := hcoords 19 (by decide)
      have hb : ((d.toNat*x 1 2 : Nat) : Int) ≤ (vsum 32 (fun s => gate s 1 2 (natCut w s)) : Int) := by
        change _ ≤ (((0 + (0 + ((w 0).toNat + (0 + ((w 1).toNat + (0 + (0 + (0 + (0 + (0 + ((w 4).toNat + (0 + ((w 5).toNat + (0 + (0 + (0 + (0 + (0 + ((w 8).toNat + (0 + ((w 9).toNat + (0 + (0 + (0 + (0 + (0 + ((w 12).toNat + (0 + ((w 13).toNat + (0 + (0 + (0 + 0)))))))))))))))))))))))))))))))) : Nat) : Int)
        simp only [Int.natCast_add,Int.natCast_mul,hd',hw0,hw1,hw4,hw5,hw8,hw9,hw12,hw13]
        omega
      exact Int.ofNat_le.mp hb

    have H13 : H 1 3 := by
      have hi := hsol #v[-1, 0, -1, -1, 0, -1, 0, 0, -1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0] (by decide)
      change ((-1 : Int)*(w 0) + ((0 : Int)*(w 1) + ((-1 : Int)*(w 2) + ((-1 : Int)*(w 3) + ((0 : Int)*(w 4) + ((-1 : Int)*(w 5) + ((0 : Int)*(w 6) + ((0 : Int)*(w 7) + ((-1 : Int)*(w 8) + ((0 : Int)*(w 9) + ((-1 : Int)*(w 10) + ((-1 : Int)*(w 11) + ((0 : Int)*(w 12) + ((-1 : Int)*(w 13) + ((0 : Int)*(w 14) + ((0 : Int)*(w 15) + ((0 : Int)*(w 16) + ((0 : Int)*(w 17) + ((0 : Int)*(w 18) + ((0 : Int)*(w 19) + ((1 : Int)*(w 20) + ((0 : Int)*(w 21) + ((0 : Int)*(w 22) + ((0 : Int)*(w 23) + ((0 : Int)*(w 24) + ((0 : Int)*(w 25) + 0)))))))))))))))))))))))))) ≤ (0 : Int) at hi
      have hr : w 20 = d*(x 1 3 : Int) := hcoords 20 (by decide)
      have hb : ((d.toNat*x 1 3 : Nat) : Int) ≤ (vsum 32 (fun s => gate s 1 3 (natCut w s)) : Int) := by
        change _ ≤ (((0 + (0 + ((w 0).toNat + (0 + (0 + (0 + ((w 2).toNat + (0 + ((w 3).toNat + (0 + (0 + (0 + ((w 5).toNat + (0 + (0 + (0 + (0 + (0 + ((w 8).toNat + (0 + (0 + (0 + ((w 10).toNat + (0 + ((w 11).toNat + (0 + (0 + (0 + ((w 13).toNat + (0 + (0 + (0 + 0)))))))))))))))))))))))))))))))) : Nat) : Int)
        simp only [Int.natCast_add,Int.natCast_mul,hd',hw0,hw2,hw3,hw5,hw8,hw10,hw11,hw13]
        omega
      exact Int.ofNat_le.mp hb

    have H14 : H 1 4 := by
      have hi := hsol #v[-1, 0, -1, 0, -1, 0, -1, -1, 0, -1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0] (by decide)
      change ((-1 : Int)*(w 0) + ((0 : Int)*(w 1) + ((-1 : Int)*(w 2) + ((0 : Int)*(w 3) + ((-1 : Int)*(w 4) + ((0 : Int)*(w 5) + ((-1 : Int)*(w 6) + ((-1 : Int)*(w 7) + ((0 : Int)*(w 8) + ((-1 : Int)*(w 9) + ((0 : Int)*(w 10) + ((-1 : Int)*(w 11) + ((0 : Int)*(w 12) + ((-1 : Int)*(w 13) + ((0 : Int)*(w 14) + ((0 : Int)*(w 15) + ((0 : Int)*(w 16) + ((0 : Int)*(w 17) + ((0 : Int)*(w 18) + ((0 : Int)*(w 19) + ((0 : Int)*(w 20) + ((1 : Int)*(w 21) + ((0 : Int)*(w 22) + ((0 : Int)*(w 23) + ((0 : Int)*(w 24) + ((0 : Int)*(w 25) + 0)))))))))))))))))))))))))) ≤ (0 : Int) at hi
      have hr : w 21 = d*(x 1 4 : Int) := hcoords 21 (by decide)
      have hb : ((d.toNat*x 1 4 : Nat) : Int) ≤ (vsum 32 (fun s => gate s 1 4 (natCut w s)) : Int) := by
        change _ ≤ (((0 + (0 + ((w 0).toNat + (0 + (0 + (0 + ((w 2).toNat + (0 + (0 + (0 + ((w 4).toNat + (0 + (0 + (0 + ((w 6).toNat + (0 + ((w 7).toNat + (0 + (0 + (0 + ((w 9).toNat + (0 + (0 + (0 + ((w 11).toNat + (0 + (0 + (0 + ((w 13).toNat + (0 + (0 + (0 + 0)))))))))))))))))))))))))))))))) : Nat) : Int)
        simp only [Int.natCast_add,Int.natCast_mul,hd',hw0,hw2,hw4,hw6,hw7,hw9,hw11,hw13]
        omega
      exact Int.ofNat_le.mp hb

    have H23 : H 2 3 := by
      have hi := hsol #v[0, -1, -1, -1, -1, 0, 0, 0, 0, -1, -1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0] (by decide)
      change ((0 : Int)*(w 0) + ((-1 : Int)*(w 1) + ((-1 : Int)*(w 2) + ((-1 : Int)*(w 3) + ((-1 : Int)*(w 4) + ((0 : Int)*(w 5) + ((0 : Int)*(w 6) + ((0 : Int)*(w 7) + ((0 : Int)*(w 8) + ((-1 : Int)*(w 9) + ((-1 : Int)*(w 10) + ((-1 : Int)*(w 11) + ((-1 : Int)*(w 12) + ((0 : Int)*(w 13) + ((0 : Int)*(w 14) + ((0 : Int)*(w 15) + ((0 : Int)*(w 16) + ((0 : Int)*(w 17) + ((0 : Int)*(w 18) + ((0 : Int)*(w 19) + ((0 : Int)*(w 20) + ((0 : Int)*(w 21) + ((1 : Int)*(w 22) + ((0 : Int)*(w 23) + ((0 : Int)*(w 24) + ((0 : Int)*(w 25) + 0)))))))))))))))))))))))))) ≤ (0 : Int) at hi
      have hr : w 22 = d*(x 2 3 : Int) := hcoords 22 (by decide)
      have hb : ((d.toNat*x 2 3 : Nat) : Int) ≤ (vsum 32 (fun s => gate s 2 3 (natCut w s)) : Int) := by
        change _ ≤ (((0 + (0 + (0 + (0 + ((w 1).toNat + (0 + ((w 2).toNat + (0 + ((w 3).toNat + (0 + ((w 4).toNat + (0 + (0 + (0 + (0 + (0 + (0 + (0 + (0 + (0 + ((w 9).toNat + (0 + ((w 10).toNat + (0 + ((w 11).toNat + (0 + ((w 12).toNat + (0 + (0 + (0 + (0 + (0 + 0)))))))))))))))))))))))))))))))) : Nat) : Int)
        simp only [Int.natCast_add,Int.natCast_mul,hd',hw1,hw2,hw3,hw4,hw9,hw10,hw11,hw12]
        omega
      exact Int.ofNat_le.mp hb

    have H24 : H 2 4 := by
      have hi := hsol #v[0, -1, -1, 0, 0, -1, -1, -1, -1, 0, 0, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0] (by decide)
      change ((0 : Int)*(w 0) + ((-1 : Int)*(w 1) + ((-1 : Int)*(w 2) + ((0 : Int)*(w 3) + ((0 : Int)*(w 4) + ((-1 : Int)*(w 5) + ((-1 : Int)*(w 6) + ((-1 : Int)*(w 7) + ((-1 : Int)*(w 8) + ((0 : Int)*(w 9) + ((0 : Int)*(w 10) + ((-1 : Int)*(w 11) + ((-1 : Int)*(w 12) + ((0 : Int)*(w 13) + ((0 : Int)*(w 14) + ((0 : Int)*(w 15) + ((0 : Int)*(w 16) + ((0 : Int)*(w 17) + ((0 : Int)*(w 18) + ((0 : Int)*(w 19) + ((0 : Int)*(w 20) + ((0 : Int)*(w 21) + ((0 : Int)*(w 22) + ((1 : Int)*(w 23) + ((0 : Int)*(w 24) + ((0 : Int)*(w 25) + 0)))))))))))))))))))))))))) ≤ (0 : Int) at hi
      have hr : w 23 = d*(x 2 4 : Int) := hcoords 23 (by decide)
      have hb : ((d.toNat*x 2 4 : Nat) : Int) ≤ (vsum 32 (fun s => gate s 2 4 (natCut w s)) : Int) := by
        change _ ≤ (((0 + (0 + (0 + (0 + ((w 1).toNat + (0 + ((w 2).toNat + (0 + (0 + (0 + (0 + (0 + ((w 5).toNat + (0 + ((w 6).toNat + (0 + ((w 7).toNat + (0 + ((w 8).toNat + (0 + (0 + (0 + (0 + (0 + ((w 11).toNat + (0 + ((w 12).toNat + (0 + (0 + (0 + (0 + (0 + 0)))))))))))))))))))))))))))))))) : Nat) : Int)
        simp only [Int.natCast_add,Int.natCast_mul,hd',hw1,hw2,hw5,hw6,hw7,hw8,hw11,hw12]
        omega
      exact Int.ofNat_le.mp hb

    have H34 : H 3 4 := by
      have hi := hsol #v[0, 0, 0, -1, -1, -1, -1, -1, -1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0] (by decide)
      change ((0 : Int)*(w 0) + ((0 : Int)*(w 1) + ((0 : Int)*(w 2) + ((-1 : Int)*(w 3) + ((-1 : Int)*(w 4) + ((-1 : Int)*(w 5) + ((-1 : Int)*(w 6) + ((-1 : Int)*(w 7) + ((-1 : Int)*(w 8) + ((-1 : Int)*(w 9) + ((-1 : Int)*(w 10) + ((0 : Int)*(w 11) + ((0 : Int)*(w 12) + ((0 : Int)*(w 13) + ((0 : Int)*(w 14) + ((0 : Int)*(w 15) + ((0 : Int)*(w 16) + ((0 : Int)*(w 17) + ((0 : Int)*(w 18) + ((0 : Int)*(w 19) + ((0 : Int)*(w 20) + ((0 : Int)*(w 21) + ((0 : Int)*(w 22) + ((0 : Int)*(w 23) + ((1 : Int)*(w 24) + ((0 : Int)*(w 25) + 0)))))))))))))))))))))))))) ≤ (0 : Int) at hi
      have hr : w 24 = d*(x 3 4 : Int) := hcoords 24 (by decide)
      have hb : ((d.toNat*x 3 4 : Nat) : Int) ≤ (vsum 32 (fun s => gate s 3 4 (natCut w s)) : Int) := by
        change _ ≤ (((0 + (0 + (0 + (0 + (0 + (0 + (0 + (0 + ((w 3).toNat + (0 + ((w 4).toNat + (0 + ((w 5).toNat + (0 + ((w 6).toNat + (0 + ((w 7).toNat + (0 + ((w 8).toNat + (0 + ((w 9).toNat + (0 + ((w 10).toNat + (0 + (0 + (0 + (0 + (0 + (0 + (0 + (0 + (0 + 0)))))))))))))))))))))))))))))))) : Nat) : Int)
        simp only [Int.natCast_add,Int.natCast_mul,hd',hw3,hw4,hw5,hw6,hw7,hw8,hw9,hw10]
        omega
      exact Int.ofNat_le.mp hb

    intro i j
    change H i j
    rcases fin5_all i with rfl|rfl|rfl|rfl|rfl <;>
      rcases fin5_all j with rfl|rfl|rfl|rfl|rfl <;>
      first | exact Hd _ | assumption | (apply Hs; assumption)

/-- Exact universal finite certificate; no theorem from the publication
is assumed. The 15 checked stages prove the same small hull result. -/
theorem fiveCutHull_verified : FiveCutHullAssertion := by
  intro R x F
  have hz : ∀ p ∈ stages, ¬ 15 ≤ p.pivot.val := by
    intro p hp
    simp only [stages,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with he | he | he | he | he | he | he | he | he | he | he | he | he | he | he <;>
      subst p <;> decide
  have hf : systemValid (finalSystem initialSystem stages) (initialVals R x) :=
    terminal_facets_valid R x F
  obtain ⟨d,w,hd,hw,hcoords,hsol⟩ := verified_chain_lift
    (fun i : Fin 26 => 15 ≤ i.val) initialSystem stages stages_valid hz (initialVals R x)
    (fun _ => Int.natCast_nonneg _) hf
  exact ⟨recover_cut R x F d w hd hw hcoords hsol⟩

end Q3K5Hull

namespace TriameterQ3Public
open TriameterQ3Graph TriameterQ3SmallPacking

/-- Exact weighted distance sum for arbitrary prescribed terminal count
and packing number at most five. -/
theorem weighted_extremum_up_to_five {r : Nat} (w : Fin r → Nat) (k p : Nat)
    (hk : 0 < k) (hp : 0 < p) (hbound : p ≤ 5) :
    ∃ C : Nat, IsCutMaximum w C ∧
      ExactWeightedValue w k p (k*pairWeight w+packingRadius k p*C) := by
  apply exact_from_upper w k p hk hp
  intro _ _ M T hP
  exact TriameterQ3PackingWindows.weighted_p_le_five_upper Q3K5Hull.fiveCutHull_verified
    M k p hbound hP T w

end TriameterQ3Public

#print axioms Q3K5Hull.fiveCutHull_verified
#print axioms TriameterQ3Public.weighted_extremum_up_to_five


namespace TriameterQ3Public
open TriameterQ3Graph TriameterQ3SmallPacking TriameterQ3PackingWindows

/-- Complementary scope: four prescribed terminals and every positive
packing number, in the same Nat-weight graph model as the p≤5 result. -/
theorem weighted_extremum_four_terminals_all_p (w : Fin 4 → Nat) (k p : Nat)
    (hk : 0 < k) (hp : 0 < p) :
    ∃ C : Nat, IsCutMaximum w C ∧
      ExactWeightedValue w k p (k*pairWeight w+packingRadius k p*C) := by
  apply exact_from_upper w k p hk hp
  intro n G M T P
  let R := packingRadius k p
  let x := clipped M k T
  let y := padFive x
  have hSym (i j : Fin 4) : x i j = x j i := by simp [x,clipped,M.dist_symm (T i) (T j)]
  have hDiag (i : Fin 4) : x i i = 0 := by simp [x,clipped,M.dist_self]
  have hB (i j : Fin 4) : x i j ≤ R := by
    have h := packing_diam M k p P (T i) (T j)
    change M.dist (T i) (T j)-k ≤ packingRadius k p
    omega
  have F : FiveFacets R y := small_support_pad_facets (Nat.le_refl 4) x hSym hDiag hB
    (clipped_triangle_general M k p P T)
  obtain ⟨C⟩ := four_supported_cut_certificate R y F (fun i => by rfl)
  let tag : Fin 4 → Fin 5 := Fin.castLE (by decide)
  apply arbitrary_terminal_weighted_upper_hook M k R T w y tag C
  have hh : (fun i j => y (tag i) (tag j)) = x := by
    funext i j
    exact padFive_cast x (by decide) i j
  rw [hh]
  exact Nat.le_refl _

end TriameterQ3Public

#print axioms TriameterQ3Public.weighted_extremum_four_terminals_all_p
