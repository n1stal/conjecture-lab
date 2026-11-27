module

public import Lean

@[expose] public section


/-! Exact high-deficit transitions over an arbitrary height for §6.2. -/
namespace WalkQuarticPhases

inductive Phase where
  | p2 | p3 | q1 | q0 | m2 | m1 | m0
  deriving DecidableEq

open Phase

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def legal : Phase → Nat → Prop
  | q1, h => h % 3 = 0
  | m2, h => h % 3 = 1
  | _, _ => True

def high (i : Phase) (h j : Nat) : Prop :=
  j ≤ h ∧ (match i with
  | p2 => j % 2 = 0
  | p3 => j % 3 = 0
  | q1 => j % 3 ≠ 1 ∧ j < h
  | q0 => j % 3 ≠ 1
  | m2 => j ≠ 1 ∧ j ≠ h-1
  | m1 => j ≠ 1 ∧ j < h
  | m0 => j ≠ 1)

def advanceA : Phase → Phase
  | p2 => p2
  | p3 => p3
  | q1 => q0
  | q0 => q0
  | m2 => m1
  | m1 => m0
  | m0 => m0

def advanceB : Phase → Nat → Phase
  | p2, _ => p2
  | p3, h => if h%3 = 2 then q1 else q0
  | q1, _ => m2
  | q0, h => if h%3 = 2 then m1 else m0
  | m2, _ => m1
  | m1, _ => m0
  | m0, _ => m0

def advanceC : Phase → Nat → Phase
  | p2, h => if h%2 = 0 then m0 else m1
  | p3, _ => p3
  | q1, _ => q0
  | q0, _ => q0
  | m2, _ => m0
  | m1, _ => m0
  | m0, _ => m0

def up (s : Nat → Prop) (h d j : Nat) : Prop :=
  j ≤ h+1 ∧ (s j ∨ (d ≤ j ∧ s (j-d)))

theorem A_exact (i : Phase) (h j : Nat) (hh : 6 ≤ h) (ok : legal i h) :
    high (advanceA i) (h-1) j ↔ j ≤ h-1 ∧ high i h j := by
  cases i <;> simp only [advanceA, high, legal] at * <;> omega

theorem B_exact (i : Phase) (h j : Nat) (hh : 5 ≤ h) (ok : legal i h) :
    high (advanceB i h) (h+1) j ↔ up (high i h) h 2 j := by
  have hm : (h+1)%3 = (h%3+1)%3 := by simp
  by_cases hj : 2 ≤ j
  · have jm : ((j-2)%3+2)%3 = j%3 := by
      have t := Nat.add_mod (j-2) 2 3
      rw [Nat.sub_add_cancel hj] at t
      simpa using t.symm
    by_cases e : h%3 = 2 <;> cases i <;> simp [legal] at ok <;>
      simp [advanceB, high, up, e] <;> omega
  · have t : j=0 ∨ j=1 := by omega
    rcases t with rfl | rfl <;>
      by_cases e : h%3 = 2 <;> cases i <;> simp [legal] at ok <;>
      simp [advanceB, high, up, e] <;> omega

theorem C_exact (i : Phase) (h j : Nat) (hh : 5 ≤ h) (ok : legal i h) :
    high (advanceC i h) (h+1) j ↔ up (high i h) h 3 j := by
  have hm : (h+1)%2 = (h%2+1)%2 := by simp
  by_cases hj : 3 ≤ j
  · have jm : ((j-3)%2+1)%2 = j%2 := by
      have t := Nat.add_mod (j-3) 3 2
      rw [Nat.sub_add_cancel hj] at t
      simpa using t.symm
    by_cases e : h%2 = 0 <;> cases i <;> simp [legal] at ok <;>
      simp [advanceC, high, up, e] <;> omega
  · have t : j=0 ∨ j=1 ∨ j=2 := by omega
    rcases t with rfl | rfl | rfl <;>
      by_cases e : h%2 = 0 <;> cases i <;> simp [legal] at ok <;>
      simp [advanceC, high, up, e] <;> omega

theorem A_legal (i : Phase) (h : Nat) (hh : 6 ≤ h) (ok : legal i h) :
    legal (advanceA i) (h-1) := by
  cases i <;> simp [advanceA, legal]

theorem B_legal (i : Phase) (h : Nat) (hh : 5 ≤ h) (ok : legal i h) :
    legal (advanceB i h) (h+1) := by
  have hm : (h+1)%3 = (h%3+1)%3 := by simp
  by_cases e : h%3 = 2 <;> cases i <;> simp [legal] at ok <;>
    simp [advanceB, legal, e] <;> omega

theorem C_legal (i : Phase) (h : Nat) (hh : 5 ≤ h) (ok : legal i h) :
    legal (advanceC i h) (h+1) := by
  by_cases e : h%2 = 0 <;> cases i <;> simp [advanceC, legal, e]

def terminal : Phase → Nat → Prop
  | p2, h => h % 2 = 0
  | p3, h => h % 3 = 0
  | q1, _ => False
  | q0, h => h % 3 ≠ 1
  | m2, _ => True
  | m1, _ => False
  | m0, _ => True

theorem terminal_exact (i : Phase) (h : Nat) (hh : 5 ≤ h) :
    terminal i h ↔ high i h h := by
  cases i <;> simp [terminal, high] <;> omega

#print axioms A_exact
#print axioms B_exact
#print axioms C_exact
#print axioms A_legal
#print axioms B_legal
#print axioms C_legal
#print axioms terminal_exact

end WalkQuarticPhases


/-!
Exact nondeterministic-walk semantics: the List is stored latest-letter first.
The representation tracks all nonnegative realizations, not their multiplicity.
-/
namespace WalkQuarticWord
open WalkQuarticPhases

inductive Letter where | A | B | C
  deriving DecidableEq

open Letter

def top : List Letter → Int
  | [] => 0
  | A::w => top w - 1
  | B::w | C::w => top w + 1

def reaches : List Letter → Int → Prop
  | [], x => x = 0
  | A::w, x => 0 ≤ x ∧ reaches w (x+1)
  | B::w, x => 0 ≤ x ∧ (reaches w (x-1) ∨ reaches w (x+1))
  | C::w, x => 0 ≤ x ∧ (reaches w (x-1) ∨ reaches w (x+2))

theorem reaches_bounds (w : List Letter) (x : Int) (hx : reaches w x) :
    0 ≤ x ∧ x ≤ top w := by
  induction w generalizing x with
  | nil => simp [reaches, top] at * <;> omega
  | cons k w ih =>
    cases k with
    | A =>
      obtain ⟨hx, hw⟩ := hx
      have bound := ih _ hw
      simp only [top]
      omega
    | B =>
      obtain ⟨hx, hw⟩ := hx
      simp only [top]
      rcases hw with hw | hw <;> have bound := ih _ hw <;> omega
    | C =>
      obtain ⟨hx, hw⟩ := hx
      simp only [top]
      rcases hw with hw | hw <;> have bound := ih _ hw <;> omega

theorem reaches_top {w : List Letter} {x : Int} (hx : reaches w x) :
    reaches w (top w) := by
  induction w generalizing x with
  | nil => simp [reaches, top]
  | cons k w ih =>
    have bound := reaches_bounds _ _ hx
    cases k with
    | A =>
      obtain ⟨_, hw⟩ := hx
      have ht := ih hw
      have sh : top w - 1 + 1 = top w := by omega
      simp only [reaches, top, sh]
      exact ⟨by simp only [top] at bound; omega, ht⟩
    | B =>
      obtain ⟨_, hw⟩ := hx
      have ht : reaches w (top w) := hw.elim (fun h => ih h) (fun h => ih h)
      have sh : top w + 1 - 1 = top w := by omega
      simp only [reaches, top, sh]
      exact ⟨by simp only [top] at bound; omega, Or.inl ht⟩
    | C =>
      obtain ⟨_, hw⟩ := hx
      have ht : reaches w (top w) := hw.elim (fun h => ih h) (fun h => ih h)
      have sh : top w + 1 - 1 = top w := by omega
      simp only [reaches, top, sh]
      exact ⟨by simp only [top] at bound; omega, Or.inl ht⟩

def deficit (w : List Letter) (h d : Nat) : Prop :=
  d ≤ h ∧ reaches w ((h:Int) - (d:Int))

theorem deficit_empty (d : Nat) : deficit [] 0 d ↔ d = 0 := by
  simp [deficit, reaches]

theorem dead_A {w : List Letter} (ht : top w = 0) (x : Int) :
    ¬reaches (A::w) x := by
  rintro ⟨hx, hw⟩
  have b := reaches_bounds w _ hw
  omega

theorem deficit_A (w : List Letter) (h d : Nat) (hh : 1 ≤ h) :
    deficit (A::w) (h-1) d ↔ d ≤ h-1 ∧ deficit w h d := by
  have e : ((h-1 : Nat):Int) - (d:Int) + 1 = (h:Int)-(d:Int) := by omega
  simp only [deficit, reaches, e]
  constructor
  · intro p
    exact ⟨p.1, by omega, p.2.2⟩
  · intro p
    exact ⟨p.1, by omega, p.2.2⟩

theorem deficit_B (w : List Letter) (h d : Nat) (ht : top w = h) :
    deficit (B::w) (h+1) d ↔ up (deficit w h) h 2 d := by
  have e : ((h+1 : Nat):Int) - (d:Int) - 1 = (h:Int)-(d:Int) := by omega
  have E (q : 2≤d) : ((h+1 : Nat):Int) - (d:Int) + 1 =
                      (h:Int)-((d-2 : Nat):Int) := by omega
  simp only [deficit, reaches, e, up]
  constructor
  · rintro ⟨hd, _, hw | hw⟩
    · refine ⟨hd, Or.inl ⟨?_, hw⟩⟩
      have b := reaches_bounds w _ hw
      omega
    · have b := reaches_bounds w _ hw
      have q : 2≤d := by omega
      rw [E q] at hw
      exact ⟨hd, Or.inr ⟨q, by omega, hw⟩⟩
  · rintro ⟨hd, ⟨_, hw⟩ | ⟨q, _, hw⟩⟩
    · exact ⟨hd, by omega, Or.inl hw⟩
    · exact ⟨hd, by omega, Or.inr (E q ▸ hw)⟩

theorem deficit_C (w : List Letter) (h d : Nat) (ht : top w = h) :
    deficit (C::w) (h+1) d ↔ up (deficit w h) h 3 d := by
  have e : ((h+1 : Nat):Int) - (d:Int) - 1 = (h:Int)-(d:Int) := by omega
  have E (q : 3≤d) : ((h+1 : Nat):Int) - (d:Int) + 2 =
                      (h:Int)-((d-3 : Nat):Int) := by omega
  simp only [deficit, reaches, e, up]
  constructor
  · rintro ⟨hd, _, hw | hw⟩
    · refine ⟨hd, Or.inl ⟨?_, hw⟩⟩
      have b := reaches_bounds w _ hw
      omega
    · have b := reaches_bounds w _ hw
      have q : 3≤d := by omega
      rw [E q] at hw
      exact ⟨hd, Or.inr ⟨q, by omega, hw⟩⟩
  · rintro ⟨hd, ⟨_, hw⟩ | ⟨q, _, hw⟩⟩
    · exact ⟨hd, by omega, Or.inl hw⟩
    · exact ⟨hd, by omega, Or.inr (E q ▸ hw)⟩

theorem excursion_is_terminal (w : List Letter) (h : Nat) :
    reaches w 0 ↔ deficit w h h := by
  simp [deficit]

theorem high_A (w : List Letter) (p : Phase) (h : Nat)
    (hh : 6≤h) (ok : legal p h)
    (matchDef : ∀ d, deficit w h d ↔ high p h d) :
    ∀ d, deficit (A::w) (h-1) d ↔ high (advanceA p) (h-1) d := by
  intro d
  rw [deficit_A _ _ _ (by omega), matchDef, A_exact _ _ _ hh ok]

theorem high_B (w : List Letter) (p : Phase) (h : Nat)
    (hh : 5≤h) (ok : legal p h) (ht : top w = h)
    (matchDef : ∀ d, deficit w h d ↔ high p h d) :
    ∀ d, deficit (B::w) (h+1) d ↔ high (advanceB p h) (h+1) d := by
  intro d
  rw [deficit_B _ _ _ ht, B_exact _ _ _ hh ok]
  simp only [up, matchDef]

theorem high_C (w : List Letter) (p : Phase) (h : Nat)
    (hh : 5≤h) (ok : legal p h) (ht : top w = h)
    (matchDef : ∀ d, deficit w h d ↔ high p h d) :
    ∀ d, deficit (C::w) (h+1) d ↔ high (advanceC p h) (h+1) d := by
  intro d
  rw [deficit_C _ _ _ ht, C_exact _ _ _ hh ok]
  simp only [up, matchDef]

theorem high_terminal (w : List Letter) (p : Phase) (h : Nat) (hh : 5≤h)
    (matchDef : ∀ d, deficit w h d ↔ high p h d) :
    reaches w 0 ↔ terminal p h := by
  rw [excursion_is_terminal w h, matchDef, terminal_exact _ _ hh]

#print axioms high_A
#print axioms high_B
#print axioms high_C
#print axioms high_terminal
#print axioms reaches_bounds
#print axioms reaches_top
#print axioms dead_A
#print axioms deficit_A
#print axioms deficit_B
#print axioms deficit_C
#print axioms excursion_is_terminal
end WalkQuarticWord


/-! Exact deterministic finite-controller recognizer of the source walks. -/
namespace WalkQuarticRecognize
open WalkQuarticPhases WalkQuarticWord
open Letter Phase

inductive Low where
  | s0 | s1 | s2 | s3 | s4 | s5 | s6 | s7 | s8 | s9 | s10
  deriving DecidableEq

inductive Config where
  | low (l : Low)
  | high (p : Phase) (h : Nat)
  deriving DecidableEq

open Config

def lowHeight : Low → Nat
  | .s0 => 0
  | .s1 => 4
  | .s2 => 4
  | .s3 => 4
  | .s4 => 4
  | .s5 => 1
  | .s6 => 3
  | .s7 => 3
  | .s8 => 3
  | .s9 => 2
  | .s10 => 2

def lowDeficits : Low → Nat → Prop
  | .s0, d => d = 0
  | .s1, d => d = 0 ∨ d = 2 ∨ d = 3
  | .s2, d => d = 0 ∨ d = 2 ∨ d = 3 ∨ d = 4
  | .s3, d => d = 0 ∨ d = 2 ∨ d = 4
  | .s4, d => d = 0 ∨ d = 3
  | .s5, d => d = 0
  | .s6, d => d = 0 ∨ d = 2 ∨ d = 3
  | .s7, d => d = 0 ∨ d = 2
  | .s8, d => d = 0 ∨ d = 3
  | .s9, d => d = 0 ∨ d = 2
  | .s10, d => d = 0

def lowestStep : Low → Letter → Option Config
  | .s0, .A => none
  | .s0, .B => some (.low .s5)
  | .s0, .C => some (.low .s5)
  | .s1, .A => some (.low .s6)
  | .s1, .B => some (.high .m0 5)
  | .s1, .C => some (.high .q0 5)
  | .s2, .A => some (.low .s6)
  | .s2, .B => some (.high .m0 5)
  | .s2, .C => some (.high .m0 5)
  | .s3, .A => some (.low .s7)
  | .s3, .B => some (.high .p2 5)
  | .s3, .C => some (.high .m0 5)
  | .s4, .A => some (.low .s8)
  | .s4, .B => some (.high .q0 5)
  | .s4, .C => some (.high .p3 5)
  | .s5, .A => some (.low .s0)
  | .s5, .B => some (.low .s9)
  | .s5, .C => some (.low .s10)
  | .s6, .A => some (.low .s9)
  | .s6, .B => some (.low .s2)
  | .s6, .C => some (.low .s1)
  | .s7, .A => some (.low .s9)
  | .s7, .B => some (.low .s3)
  | .s7, .C => some (.low .s1)
  | .s8, .A => some (.low .s10)
  | .s8, .B => some (.low .s1)
  | .s8, .C => some (.low .s4)
  | .s9, .A => some (.low .s5)
  | .s9, .B => some (.low .s7)
  | .s9, .C => some (.low .s6)
  | .s10, .A => some (.low .s5)
  | .s10, .B => some (.low .s7)
  | .s10, .C => some (.low .s8)

def highExit : Phase → Config
  | .p2 => .low .s3
  | .p3 => .low .s4
  | .q1 => .low .s0
  | .q0 => .low .s1
  | .m2 => .low .s0
  | .m1 => .low .s2
  | .m0 => .low .s2

def height : Config → Nat
  | .low l => lowHeight l
  | .high _ h => h

def dset : Config → Nat → Prop
  | .low l => lowDeficits l
  | .high p h => WalkQuarticPhases.high p h

def legalConfig : Config → Prop
  | .low _ => True
  | .high p h => 5 ≤ h ∧ legal p h

def step : Config → Letter → Option Config
  | .low l, k => lowestStep l k
  | .high p h, A =>
      if h=5 then some (highExit p) else some (.high (advanceA p) (h-1))
  | .high p h, B => some (.high (advanceB p h) (h+1))
  | .high p h, C => some (.high (advanceC p h) (h+1))

def nextHeight (h : Nat) : Letter → Nat
  | A => h-1
  | B | C => h+1

def nextDeficits (s : Config) : Letter → Nat → Prop
  | A, d => d ≤ height s-1 ∧ dset s d
  | B, d => up (dset s) (height s) 2 d
  | C, d => up (dset s) (height s) 3 d

def StepValid (s : Config) (k : Letter) : Prop :=
  match step s k with
  | none => k = A ∧ height s = 0
  | some t => height t = nextHeight (height s) k ∧
      (k = A → 1 ≤ height s) ∧ legalConfig t ∧
      ∀ d, dset t d ↔ nextDeficits s k d

set_option linter.unusedSimpArgs false

theorem low_step_valid (l : Low) (k : Letter) : StepValid (.low l) k := by
  cases l <;> cases k <;>
    simp [StepValid, step, lowestStep, height, lowHeight, nextHeight,
      legalConfig, legal, dset, lowDeficits, WalkQuarticPhases.high, nextDeficits, up] <;>
    intro d <;> omega

theorem high_exit_valid (p : Phase) (ok : legal p 5) : StepValid (.high p 5) A := by
  cases p <;>
    simp [StepValid, step, height, highExit, legal, lowHeight, nextHeight,
      legalConfig, dset, lowDeficits, WalkQuarticPhases.high, nextDeficits, up] at * <;>
    intro d <;> omega

theorem step_valid (s : Config) (k : Letter) (ok : legalConfig s) : StepValid s k := by
  cases s with
  | low l => exact low_step_valid l k
  | high p h =>
    obtain ⟨hh, hp⟩ := ok
    cases k with
    | A =>
      by_cases ph : h=5
      · subst h; exact high_exit_valid p hp
      · have hh' : 6≤h := by omega
        simp only [StepValid, step, ph, ite_false, height, nextHeight,
          legalConfig, dset, nextDeficits]
        refine ⟨trivial, fun _ => by omega, ⟨by omega, A_legal p h hh' hp⟩, ?_⟩
        exact fun d => A_exact p h d hh' hp
    | B =>
      simp only [StepValid, step, height, nextHeight, legalConfig, dset, nextDeficits]
      refine ⟨trivial, by simp, ⟨by omega, B_legal p h hh hp⟩, ?_⟩
      exact fun d => B_exact p h d hh hp
    | C =>
      simp only [StepValid, step, height, nextHeight, legalConfig, dset, nextDeficits]
      refine ⟨trivial, by simp, ⟨by omega, C_legal p h hh hp⟩, ?_⟩
      exact fun d => C_exact p h d hh hp

#print axioms low_step_valid
#print axioms high_exit_valid
#print axioms step_valid


def Matches (w : List Letter) : Option Config → Prop
  | none => ∀ x, ¬reaches w x
  | some s => legalConfig s ∧ top w = (height s : Int) ∧
      ∀ d, deficit w (height s) d ↔ dset s d

theorem all_dead_next {w : List Letter} (dead : ∀ x, ¬reaches w x)
    (k : Letter) : ∀ x, ¬reaches (k::w) x := by
  intro x hx
  cases k with
  | A => exact dead _ hx.2
  | B => exact hx.2.elim (fun p => dead _ p) (fun p => dead _ p)
  | C => exact hx.2.elim (fun p => dead _ p) (fun p => dead _ p)

theorem matches_step (w : List Letter) (s : Option Config) (k : Letter)
    (m : Matches w s) : Matches (k::w) (s.bind (fun t => step t k)) := by
  cases s with
  | none => exact all_dead_next m k
  | some s =>
    obtain ⟨ok, ht, hD⟩ := m
    have hs := step_valid s k ok
    cases eq : step s k with
    | none =>
      simp only [StepValid, eq] at hs
      obtain ⟨rfl, zero⟩ := hs
      simp only [Option.bind_some, eq, Matches]
      rw [zero] at ht
      intro x
      exact dead_A ht x
    | some t =>
      simp only [StepValid, eq] at hs
      obtain ⟨hHeight, aPos, okT, hNext⟩ := hs
      simp only [Option.bind_some, eq, Matches]
      refine ⟨okT, ?_, ?_⟩
      · rw [hHeight]
        cases k with
        | A =>
          have hpos : 1 ≤ height s := aPos rfl
          simp only [top, ht, nextHeight]
          omega
        | B => simp [top, ht, nextHeight]
        | C => simp [top, ht, nextHeight]
      · intro d
        rw [hHeight, hNext]
        cases k with
        | A =>
          have hpos : 1 ≤ height s := aPos rfl
          simp only [nextHeight, nextDeficits, deficit_A _ _ _ hpos, hD]
        | B =>
          simp only [nextHeight, nextDeficits, deficit_B _ _ _ ht, up, hD]
        | C =>
          simp only [nextHeight, nextDeficits, deficit_C _ _ _ ht, up, hD]

def run : List Letter → Option Config
  | [] => some (low .s0)
  | k::w => (run w).bind (fun s => step s k)

theorem run_exact (w : List Letter) : Matches w (run w) := by
  induction w with
  | nil =>
    simp only [run, Matches, legalConfig, top, height, lowHeight, Int.natCast_zero,
      dset, lowDeficits, deficit_empty]
    exact ⟨trivial, trivial, fun _ => trivial⟩
  | cons k w ih => exact matches_step w (run w) k ih

def accepts : Option Config → Prop
  | none => False
  | some s => dset s (height s)

theorem accepts_exact (w : List Letter) :
    accepts (run w) ↔ reaches w 0 := by
  have hr := run_exact w
  cases eq : run w with
  | none =>
    simp only [eq, Matches] at hr
    simp only [accepts, false_iff]
    exact hr 0
  | some s =>
    simp only [eq, Matches] at hr
    simp only [accepts]
    rw [excursion_is_terminal w (height s), hr.2.2]

#print axioms matches_step
#print axioms run_exact
#print axioms accepts_exact
end WalkQuarticRecognize


/-! All-length weighted enumeration with direct use of the checked recognizer. -/
namespace WalkQuarticCounting
open WalkQuarticWord WalkQuarticRecognize
open Letter
open Lean.Grind.Semiring

abbrev State := Option Config

def alphabet : List Letter := [A, B, C]

def words : Nat → List (List Letter)
  | 0 => [[]]
  | n+1 => alphabet.flatMap fun k => (words n).map (fun w => k :: w)

theorem alphabet_complete (k : Letter) : k ∈ alphabet := by
  cases k <;> simp [alphabet]

theorem mem_words_iff_length (n : Nat) (w : List Letter) :
    w ∈ words n ↔ w.length = n := by
  induction n generalizing w with
  | zero => cases w <;> simp [words]
  | succ n ih =>
    cases w with
    | nil => simp [words]
    | cons k w =>
      simp only [words, List.mem_flatMap, List.mem_map, List.cons.injEq,
        List.length_cons, Nat.add_right_cancel_iff]
      constructor
      · rintro ⟨l, _, v, hv, rfl, rfl⟩
        exact (ih v).mp hv
      · intro hw
        exact ⟨k, alphabet_complete k, w, (ih w).mpr hw, rfl, rfl⟩

theorem nodup_consMap {l : List (List Letter)} (h : l.Nodup) (a : Letter) :
    (l.map (fun w => a :: w)).Nodup := by
  induction l with
  | nil => simp
  | cons b l ih =>
    obtain ⟨hb, hl⟩ := List.nodup_cons.mp h
    refine List.nodup_cons.mpr ⟨?_, ih hl⟩
    simp only [List.mem_map, List.cons.injEq, true_and]
    rintro ⟨c, hc, rfl⟩
    exact hb hc

theorem consMap_disjoint {l m : List (List Letter)} {a b : Letter} (h : a ≠ b) :
    ∀ x, x ∈ l.map (fun w => a :: w) → x ∉ m.map (fun w => b :: w) := by
  intro x hx hy
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp hx
  obtain ⟨v, _, h'⟩ := List.mem_map.mp hy
  exact h (List.cons.inj h').1.symm

theorem words_nodup (n : Nat) : (words n).Nodup := by
  induction n with
  | zero => simp [words]
  | succ n ih =>
    simp only [words, alphabet, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.nodup_append]
    refine ⟨nodup_consMap ih A, ⟨nodup_consMap ih B, nodup_consMap ih C, ?_⟩, ?_⟩
    · rintro x hx y hy rfl
      exact consMap_disjoint (by decide : B ≠ C) x hx hy
    · rintro x hx y hy rfl
      rcases List.mem_append.mp hy with h | h
      · exact consMap_disjoint (by decide : A ≠ B) x hx h
      · exact consMap_disjoint (by decide : A ≠ C) x hx h

def transition (s : State) (k : Letter) : State :=
  s.bind (fun q => step q k)

def iter (s : State) : List Letter → State
  | [] => s
  | k::w => iter (transition s k) w

theorem iter_append (s : State) (u v : List Letter) :
    iter s (u ++ v) = iter (iter s u) v := by
  induction u generalizing s with
  | nil => rfl
  | cons k w ih => exact ih (transition s k)

def initial : State := some (.low .s0)

theorem run_eq_iter_rev (w : List Letter) : run w = iter initial w.reverse := by
  induction w with
  | nil => rfl
  | cons k w ih =>
    rw [List.reverse_cons, iter_append, ←ih]
    rfl

theorem reversed_run (w : List Letter) :
    run w.reverse = iter initial w := by
  rw [run_eq_iter_rev, List.reverse_reverse]

theorem chronological_accepts (w : List Letter) :
    accepts (iter initial w) ↔ reaches w.reverse 0 := by
  rw [← reversed_run]
  exact accepts_exact w.reverse

section Weights
universe u
variable {R : Type u} [Lean.Grind.Semiring R]

/-- Sum over a finite list, valid in any core-Lean semiring. -/
def lsum {X : Type v} (f : X → R) : List X → R
  | [] => 0
  | x::xs => f x + lsum f xs

theorem lsum_append {X : Type v} (f : X → R) (xs ys : List X) :
    lsum f (xs ++ ys) = lsum f xs + lsum f ys := by
  induction xs with
  | nil =>
    simp only [List.nil_append, lsum]
    rw [Lean.Grind.Semiring.add_comm 0 _, add_zero]
  | cons x xs ih => simp only [List.cons_append, lsum, ih, add_assoc]

theorem lsum_map {X : Type v} {Y : Type w} (f : Y → R) (g : X → Y) (xs : List X) :
    lsum f (xs.map g) = lsum (fun x => f (g x)) xs := by
  induction xs <;> simp_all [lsum]

theorem lsum_flatMap {X : Type v} {Y : Type w} (f : Y → R)
    (g : X → List Y) (xs : List X) :
    lsum f (xs.flatMap g) = lsum (fun x => lsum f (g x)) xs := by
  induction xs <;> simp_all [lsum, lsum_append]

theorem lsum_mul_left {X : Type v} (f : X → R) (c : R) (xs : List X) :
    lsum (fun x => c * f x) xs = c * lsum f xs := by
  induction xs <;> simp_all [lsum, mul_zero, left_distrib]

def wordWeight (wt : Letter → R) : List Letter → R
  | [] => 1
  | k::w => wt k * wordWeight wt w

/-- Backward-by-length transfer; independently starting at any state. -/
def coefficient (wt : Letter → R) (mark : State → R) : Nat → State → R
  | 0, s => mark s
  | n+1, s => lsum (fun k => wt k * coefficient wt mark n (transition s k)) alphabet

theorem coefficient_recurrence (wt : Letter → R) (mark : State → R) (n : Nat) (s : State) :
    coefficient wt mark (n+1) s =
      wt A * coefficient wt mark n (transition s A) +
      (wt B * coefficient wt mark n (transition s B) +
       wt C * coefficient wt mark n (transition s C)) := by
  simp [coefficient, lsum, alphabet, add_zero]

theorem coefficient_is_word_sum (wt : Letter → R) (mark : State → R)
    (n : Nat) (s : State) :
    coefficient wt mark n s =
      lsum (fun w => wordWeight wt w * mark (iter s w)) (words n) := by
  induction n generalizing s with
  | zero => simp [coefficient, words, wordWeight, iter, lsum, one_mul, add_zero]
  | succ n ih =>
    simp only [coefficient, words, lsum_flatMap, lsum_map, wordWeight, iter]
    simp only [mul_assoc, lsum_mul_left, ←ih]

noncomputable def markProp (P : Prop) : R := by
  classical exact if P then 1 else 0

theorem markProp_congr {P Q : Prop} (h : P ↔ Q) :
    (markProp P : R) = markProp Q := by
  rw [propext h]

/-- Literal weighted coefficient of length-n excursions in the paper. -/
noncomputable def sourceCoeff (wt : Letter → R) (n : Nat) : R :=
  lsum (fun w => wordWeight wt w * markProp (reaches w.reverse 0)) (words n)

/-- Exact all-length weighted GF coefficient bridge; no coefficient range hypothesis. -/
theorem sourceCoeff_eq_transfer (wt : Letter → R) (n : Nat) :
    sourceCoeff wt n = coefficient wt (fun s => markProp (accepts s)) n initial := by
  rw [coefficient_is_word_sum, sourceCoeff]
  congr 1
  funext w
  rw [markProp_congr (chronological_accepts w)]

end Weights

#print axioms words_nodup
#print axioms mem_words_iff_length
#print axioms chronological_accepts
#print axioms coefficient_is_word_sum
#print axioms sourceCoeff_eq_transfer
end WalkQuarticCounting


/-! Sparse, forward-by-length weighted population of recognizer states. -/
namespace WalkQuarticPopulation
open WalkQuarticWord WalkQuarticPhases WalkQuarticRecognize WalkQuarticCounting
open Letter
open Lean.Grind.Semiring

def unique {X : Type u} [DecidableEq X] : List X → List X
  | [] => []
  | x::xs => let ys := unique xs; if x ∈ ys then ys else x :: ys

theorem mem_unique {X : Type u} [DecidableEq X] (x : X) (xs : List X) :
    x ∈ unique xs ↔ x ∈ xs := by
  induction xs generalizing x with
  | nil => simp [unique]
  | cons y ys ih =>
    simp only [unique]
    split
    · rename_i h
      rw [ih y] at h
      rw [ih x]
      exact ⟨List.mem_cons_of_mem _, fun p => by
        rcases List.mem_cons.mp p with q | q
        · simpa [q] using h
        · exact q⟩
    · simp only [List.mem_cons, ih]

theorem unique_nodup {X : Type u} [DecidableEq X] (xs : List X) :
    (unique xs).Nodup := by
  induction xs with
  | nil => simp [unique]
  | cons x xs ih =>
    simp only [unique]
    split
    · exact ih
    · exact List.nodup_cons.mpr ⟨‹_›, ih⟩

def lowStates : List Low :=
  [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10]

def highPhases : List Phase := [.p2, .p3, .q1, .q0, .m2, .m1, .m0]

def stateBound (n : Nat) : List State :=
  unique ([none] ++ lowStates.map (fun l => some (.low l)) ++
    (List.range (n+1)).flatMap fun h => highPhases.map (fun p => some (.high p h)))

theorem stateBound_nodup (n : Nat) : (stateBound n).Nodup := unique_nodup _

theorem live_top_bound (w : List Letter) : top w ≤ (w.length : Int) := by
  induction w with
  | nil => simp [top]
  | cons k w ih =>
    cases k <;> simp only [top, List.length_cons] <;> omega

theorem run_mem_stateBound (n : Nat) (w : List Letter) (hw : w.length = n) :
    run w ∈ stateBound n := by
  have hm := run_exact w
  cases h : run w with
  | none => simp [stateBound, mem_unique]
  | some s =>
    rw [h] at hm
    have hh : height s ≤ n := by
      have htop : top w = (height s : Int) := hm.2.1
      have hbound := live_top_bound w
      omega
    cases s with
    | low l => cases l <;> simp [stateBound, mem_unique, lowStates]
    | high p k =>
      have hk : k < n + 1 := by simpa [height] using Nat.lt_succ_of_le hh
      apply (mem_unique _ _).mpr
      apply List.mem_append_right
      apply List.mem_flatMap.mpr
      refine ⟨k, List.mem_range.mpr hk, List.mem_map.mpr ⟨p, ?_, rfl⟩⟩
      cases p <;> simp [highPhases]

theorem nodup_map_of_inj {X : Type u} {Y : Type v} (f : X → Y)
    (inj : ∀ x y, f x = f y → x = y) (xs : List X) (h : xs.Nodup) :
    (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hx, hs⟩ := List.nodup_cons.mp h
    refine List.nodup_cons.mpr ⟨?_, ih hs⟩
    intro hh
    obtain ⟨y, hy, eq⟩ := List.mem_map.mp hh
    have yx := inj _ _ eq
    exact hx (yx ▸ hy)

theorem words_rev_perm (n : Nat) : List.Perm ((words n).map List.reverse) (words n) := by
  apply (List.perm_ext_iff_of_nodup
    (nodup_map_of_inj _ (fun x y h => by simpa using congrArg List.reverse h) _ (words_nodup n))
    (words_nodup n)).mpr
  intro w
  rw [mem_words_iff_length]
  constructor
  · intro h
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp h
    simpa using (mem_words_iff_length n v).mp hv
  · intro h
    refine List.mem_map.mpr ⟨w.reverse, (mem_words_iff_length n _).mpr ?_,
      List.reverse_reverse w⟩
    simpa using h

section Weights
variable {R : Type u} [Lean.Grind.Semiring R]

private theorem add0 (a : R) : 0 + a = a := by
  rw [Lean.Grind.Semiring.add_comm, add_zero]

theorem lsum_mul_right {X : Type v} (f : X → R) (c : R) (xs : List X) :
    lsum (fun x => f x * c) xs = lsum f xs * c := by
  induction xs <;> simp_all [lsum, zero_mul, right_distrib]

theorem lsum_add {X : Type v} (f g : X → R) (xs : List X) :
    lsum (fun x => f x + g x) xs = lsum f xs + lsum g xs := by
  induction xs with
  | nil => simp [lsum, add_zero]
  | cons x xs ih =>
    simp only [lsum, ih, add_assoc]
    rw [←add_assoc (g x), Lean.Grind.Semiring.add_comm (g x) (lsum f xs), add_assoc]

theorem lsum_zero {X : Type v} (xs : List X) : lsum (fun _ => (0:R)) xs = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [lsum, ih, add_zero]

theorem lsum_swap {X : Type v} {Y : Type w} (f : X → Y → R)
    (xs : List X) (ys : List Y) :
    lsum (fun x => lsum (fun y => f x y) ys) xs =
      lsum (fun y => lsum (fun x => f x y) xs) ys := by
  induction xs with
  | nil => simp only [lsum, lsum_zero]
  | cons x xs ih =>
    simp only [lsum, lsum_add, ih]

theorem lsum_perm {X : Type v} (f : X → R) {xs ys : List X} (h : List.Perm xs ys) :
    lsum f xs = lsum f ys := by
  induction h with
  | nil => rfl
  | cons x h ih => simp [lsum, ih]
  | swap x y xs =>
    simp only [lsum, ←add_assoc]
    rw [Lean.Grind.Semiring.add_comm (f x) (f y)]
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2

theorem lsum_congr_mem {X : Type v} (f g : X → R) (xs : List X)
    (h : ∀ x ∈ xs, f x = g x) : lsum f xs = lsum g xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [lsum]
    rw [h x (List.mem_cons_self), ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem lsum_eq_zero {X : Type v} (f : X → R) (xs : List X)
    (h : ∀ x ∈ xs, f x = 0) : lsum f xs = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [lsum, h _ List.mem_cons_self, ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    exact add_zero _

theorem markProp_true {P : Prop} (h : P) : (markProp P : R) = 1 := by
  classical simp [markProp, h]

theorem markProp_false {P : Prop} (h : ¬P) : (markProp P : R) = 0 := by
  classical simp [markProp, h]

theorem lsum_point {X : Type v} (f : X → R) (a : X) (xs : List X)
    (hm : a ∈ xs) (hn : xs.Nodup) :
    lsum (fun x => markProp (a = x) * f x) xs = f a := by
  induction xs with
  | nil => cases hm
  | cons x xs ih =>
    obtain ⟨hxN, hn'⟩ := List.nodup_cons.mp hn
    by_cases h : a = x
    · subst x
      have hz : lsum (fun x => markProp (a = x) * f x) xs = 0 := by
        apply lsum_eq_zero
        intro y hy
        have hh : a ≠ y := fun e => hxN (e ▸ hy)
        rw [markProp_false hh, zero_mul]
      rw [lsum, markProp_true (rfl : a = a), one_mul, hz, add_zero]
    · have hm' : a ∈ xs := (List.mem_cons.mp hm).resolve_left h
      simp only [lsum, markProp_false h, zero_mul, ih hm' hn', add0]

/-- Letter product for reverse-stored chronological words. -/
def revWeight (wt : Letter → R) : List Letter → R
  | [] => 1
  | k::w => revWeight wt w * wt k

theorem wordWeight_append (wt : Letter → R) (x y : List Letter) :
    wordWeight wt (x ++ y) = wordWeight wt x * wordWeight wt y := by
  induction x with
  | nil => simp [wordWeight, one_mul]
  | cons k x ih => simp [wordWeight, ih, mul_assoc]

theorem revWeight_eq (wt : Letter → R) (w : List Letter) :
    revWeight wt w = wordWeight wt w.reverse := by
  induction w with
  | nil => rfl
  | cons k w ih =>
    simp [List.reverse_cons, revWeight, ih, wordWeight_append, wordWeight, mul_one]

/-- Moment of the weighted population, evaluated at an arbitrary terminal observable. -/
def moment (wt : Letter → R) (n : Nat) (g : State → R) : R :=
  lsum (fun w => revWeight wt w * g (run w)) (words n)

theorem moment_eq_coefficient (wt : Letter → R) (n : Nat) (g : State → R) :
    moment wt n g = coefficient wt g n initial := by
  rw [coefficient_is_word_sum]
  have hr := lsum_perm (fun w => wordWeight wt w * g (iter initial w)) (words_rev_perm n)
  rw [lsum_map] at hr
  simp only [moment, revWeight_eq, run_eq_iter_rev]
  exact hr

def stepMoment (wt : Letter → R) (g : State → R) (s : State) : R :=
  lsum (fun k => wt k * g (transition s k)) alphabet

theorem moment_succ (wt : Letter → R) (n : Nat) (g : State → R) :
    moment wt (n+1) g = moment wt n (stepMoment wt g) := by
  simp only [moment, words, lsum_flatMap, lsum_map, revWeight, run, mul_assoc]
  rw [lsum_swap]
  simp only [stepMoment, transition, lsum_mul_left]

/-- Exactly the total weight that reaches the listed state at length n. -/
noncomputable def population (wt : Letter → R) (n : Nat) (s : State) : R :=
  moment wt n (fun q => markProp (q = s))

theorem moment_is_state_sum (wt : Letter → R) (n : Nat) (g : State → R) :
    moment wt n g = lsum (fun s => population wt n s * g s) (stateBound n) := by
  simp only [population, moment, ←lsum_mul_right]
  rw [lsum_swap]
  apply lsum_congr_mem
  intro w hw
  simp only [mul_assoc, lsum_mul_left]
  rw [lsum_point _ _ _ (run_mem_stateBound n w ((mem_words_iff_length n _).mp hw))
    (stateBound_nodup n)]

theorem population_zero (wt : Letter → R) (s : State) :
    population wt 0 s = markProp (initial = s) := by
  simp [population, moment, revWeight, words, initial, run, lsum, one_mul, add_zero]

theorem population_outside_bound (wt : Letter → R) (n : Nat) (s : State)
    (ho : s ∉ stateBound n) : population wt n s = 0 := by
  apply lsum_eq_zero
  intro w hw
  have hm := run_mem_stateBound n w ((mem_words_iff_length n _).mp hw)
  have neq : run w ≠ s := fun h => ho (h ▸ hm)
  change revWeight wt w * markProp (run w = s) = 0
  rw [markProp_false neq, mul_zero]

theorem population_succ (wt : Letter → R) (n : Nat) (s : State) :
    population wt (n+1) s =
      lsum (fun q => population wt n q *
        lsum (fun k => wt k * markProp (transition q k = s)) alphabet) (stateBound n) := by
  rw [population, moment_succ, moment_is_state_sum]
  rfl

theorem population_unique (wt : Letter → R) (F : Nat → State → R)
    (h0 : ∀ s, F 0 s = markProp (initial = s))
    (hs : ∀ n s, F (n+1) s =
      lsum (fun q => F n q *
        lsum (fun k => wt k * markProp (transition q k = s)) alphabet) (stateBound n)) :
    ∀ n s, F n s = population wt n s := by
  intro n
  induction n with
  | zero => intro s; rw [h0, population_zero]
  | succ n ih =>
    intro s
    rw [hs, population_succ]
    simp only [ih]

theorem sourceCoeff_population (wt : Letter → R) (n : Nat) :
    sourceCoeff wt n =
      lsum (fun s => population wt n s * markProp (accepts s)) (stateBound n) := by
  rw [sourceCoeff_eq_transfer, ←moment_eq_coefficient, moment_is_state_sum]

end Weights

noncomputable def sourceExcursions (n : Nat) : List (List Letter) := by
  classical exact (words n).filter (fun w => decide (reaches w.reverse 0))

theorem sourceExcursions_nodup (n : Nat) : (sourceExcursions n).Nodup := by
  classical
  unfold sourceExcursions
  exact List.Sublist.nodup List.filter_sublist (words_nodup n)

theorem mem_sourceExcursions (n : Nat) (w : List Letter) :
    w ∈ sourceExcursions n ↔ w.length = n ∧ reaches w.reverse 0 := by
  classical
  simp [sourceExcursions, mem_words_iff_length]

private theorem allOne_wordWeight (w : List Letter) :
    wordWeight (fun _ => (1 : Nat)) w = 1 := by
  induction w <;> simp_all [wordWeight]

private theorem nat_sum_indicator_eq_filter_length {X : Type v}
    (p : X → Prop) [DecidablePred p] (xs : List X) :
    lsum (fun x => (markProp (p x) : Nat)) xs =
      (xs.filter (fun x => decide (p x))).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : p x
    · rw [lsum, markProp_true h, ih]
      simp [h, Nat.add_comm]
    · rw [lsum, markProp_false h, ih]
      simp [h]

theorem unweighted_sourceCoeff_is_count (n : Nat) :
    sourceCoeff (fun _ => (1 : Nat)) n = (sourceExcursions n).length := by
  classical
  simp only [sourceCoeff, allOne_wordWeight, Nat.one_mul]
  exact nat_sum_indicator_eq_filter_length (fun w => reaches w.reverse 0) (words n)

#print axioms moment_eq_coefficient
#print axioms moment_succ
#print axioms stateBound_nodup
#print axioms run_mem_stateBound
#print axioms moment_is_state_sum
#print axioms population_zero
#print axioms population_outside_bound
#print axioms population_succ
#print axioms population_unique
#print axioms sourceCoeff_population
#print axioms sourceExcursions_nodup
#print axioms mem_sourceExcursions
#print axioms unweighted_sourceCoeff_is_count
end WalkQuarticPopulation


/-! Canonical first-return and first-descent factorizations for all word lengths. -/
namespace WalkQuarticFirstReturn
open WalkQuarticWord WalkQuarticCounting
open Letter

set_option linter.unusedSimpArgs false

/-- Exact relative height, which rejects the first move below its base. -/
def heightRun (h : Nat) : List Letter → Option Nat
  | [] => some h
  | A::w => if h=0 then none else heightRun (h-1) w
  | B::w | C::w => heightRun (h+1) w

/-- Prefix in the lower band excludes the first downcrossing. -/
inductive Scan where
  | stay (h : Nat)
  | drop (p q : List Letter)

def Scan.prepend (k : Letter) : Scan → Scan
  | .stay h => .stay h
  | .drop p q => .drop (k::p) q

def firstBelow (h : Nat) : List Letter → Scan
  | [] => .stay h
  | A::w => if h=0 then .drop [] w else (firstBelow (h-1) w).prepend A
  | B::w => (firstBelow (h+1) w).prepend B
  | C::w => (firstBelow (h+1) w).prepend C

def Scan.Result (h : Nat) (w : List Letter) : Scan → Prop
  | .stay k => heightRun h w = some k
  | .drop p q => w = p ++ A::q ∧ heightRun h p = some 0

theorem firstBelow_result (h : Nat) (w : List Letter) :
    Scan.Result h w (firstBelow h w) := by
  induction w generalizing h with
  | nil => rfl
  | cons k w ih =>
    cases k with
    | A =>
      by_cases z : h=0
      · subst h; simp [firstBelow, Scan.Result, heightRun]
      · have hh := ih (h-1)
        cases e : firstBelow (h-1) w with
        | stay t => simpa [firstBelow, z, e, Scan.prepend, Scan.Result, heightRun] using hh
        | drop p q =>
          rw [e] at hh
          obtain ⟨eq, run⟩ := hh
          simp [firstBelow, z, e, Scan.prepend, Scan.Result, heightRun, run]
          exact eq
    | B =>
      have hh := ih (h+1)
      cases e : firstBelow (h+1) w with
      | stay t => simpa [firstBelow, e, Scan.prepend, Scan.Result, heightRun] using hh
      | drop p q =>
        rw [e] at hh
        obtain ⟨eq, run⟩ := hh
        simp [firstBelow, e, Scan.prepend, Scan.Result, heightRun, run]
        exact eq
    | C =>
      have hh := ih (h+1)
      cases e : firstBelow (h+1) w with
      | stay t => simpa [firstBelow, e, Scan.prepend, Scan.Result, heightRun] using hh
      | drop p q =>
        rw [e] at hh
        obtain ⟨eq, run⟩ := hh
        simp [firstBelow, e, Scan.prepend, Scan.Result, heightRun, run]
        exact eq

theorem firstBelow_of_prefix (h : Nat) (p q : List Letter)
    (hp : heightRun h p = some 0) :
    firstBelow h (p ++ A::q) = .drop p q := by
  induction p generalizing h with
  | nil =>
    have z : h=0 := by simpa [heightRun] using hp
    subst h
    simp [firstBelow]
  | cons k p ih =>
    cases k with
    | A =>
      have z : h≠0 := by
        intro hz; subst h; simp [heightRun] at hp
      have hp' : heightRun (h-1) p = some 0 := by simpa [heightRun, z] using hp
      simp [firstBelow, z, ih _ hp', Scan.prepend]
    | B =>
      have hp' : heightRun (h+1) p = some 0 := by simpa [heightRun] using hp
      simp [firstBelow, ih _ hp', Scan.prepend]
    | C =>
      have hp' : heightRun (h+1) p = some 0 := by simpa [heightRun] using hp
      simp [firstBelow, ih _ hp', Scan.prepend]

theorem firstBelow_drop_iff (h : Nat) (w p q : List Letter) :
    firstBelow h w = .drop p q ↔ w = p ++ A::q ∧ heightRun h p = some 0 := by
  constructor
  · intro hh
    have e := firstBelow_result h w
    rw [hh] at e
    exact e
  · rintro ⟨rfl, hp⟩
    exact firstBelow_of_prefix h p q hp

/-- Increasing the initial depth by one turns the first downcrossing into
an ordinary step to height zero, or shifts the unbroken path up by one. -/
theorem heightRun_succ_scan (h : Nat) (w : List Letter) :
    heightRun (h+1) w =
      (match firstBelow h w with
       | .stay k => some (k+1)
       | .drop _ q => heightRun 0 q) := by
  induction w generalizing h with
  | nil => rfl
  | cons k w ih =>
    cases k with
    | A =>
      cases h with
      | zero => simp [heightRun, firstBelow]
      | succ h =>
        simp only [heightRun, Nat.succ_ne_zero, Nat.add_one_ne_zero, ite_false,
          Nat.succ_sub_one, Nat.add_sub_cancel, firstBelow]
        rw [ih h]
        cases firstBelow h w <;> rfl
    | B =>
      simp only [heightRun, firstBelow]
      rw [ih (h+1)]
      cases firstBelow (h+1) w <;> rfl
    | C =>
      simp only [heightRun, firstBelow]
      rw [ih (h+1)]
      cases firstBelow (h+1) w <;> rfl

def IsReturn (w : List Letter) : Prop := heightRun 0 w = some 0

/-- A nonempty upper-halfline return has unique first return data:
an up letter, an inner return, its matching A, and the remaining return. -/
theorem return_cons_iff (k : Letter) (w : List Letter) :
    IsReturn (k::w) ↔ k ≠ A ∧
      ∃ p q : List Letter, firstBelow 0 w = .drop p q ∧ IsReturn p ∧ IsReturn q := by
  cases k with
  | A => simp [IsReturn, heightRun]
  | B | C =>
    unfold IsReturn
    simp only [heightRun, reduceCtorEq, not_false_eq_true, true_and]
    rw [heightRun_succ_scan 0 w]
    have h := firstBelow_result 0 w
    cases e : firstBelow 0 w with
    | stay j =>
      simp [Scan.stay.injEq]
    | drop p q =>
      rw [e] at h
      change w = p ++ A::q ∧ heightRun 0 p = some 0 at h
      constructor
      · intro hq
        refine ⟨by decide, p, q, rfl, h.2, hq⟩
      · rintro ⟨_, p', q', eq, _, hq⟩
        cases eq
        exact hq

theorem return_cons_factors (k : Letter) (w : List Letter) :
    IsReturn (k::w) ↔ k ≠ A ∧
      ∃ p q : List Letter, w = p ++ A::q ∧ IsReturn p ∧ IsReturn q := by
  rw [return_cons_iff]
  constructor
  · rintro ⟨ha,p,q,hs,hp,hq⟩
    exact ⟨ha,p,q,(firstBelow_drop_iff 0 w p q).mp hs |>.1,hp,hq⟩
  · rintro ⟨ha,p,q,hs,hp,hq⟩
    exact ⟨ha,p,q,(firstBelow_drop_iff 0 w p q).mpr ⟨hs,hp⟩,hp,hq⟩

theorem return_factors_unique (w p q p' q' : List Letter)
    (h : w = p ++ A::q) (h' : w = p' ++ A::q')
    (hp : IsReturn p) (hp' : IsReturn p') : p = p' ∧ q = q' := by
  have e := (firstBelow_drop_iff 0 w p q).mpr ⟨h, hp⟩
  have e' := (firstBelow_drop_iff 0 w p' q').mpr ⟨h', hp'⟩
  rw [e] at e'
  exact Scan.drop.inj e'

theorem return_weight_factor {R : Type u} [Lean.Grind.Semiring R] (wt : Letter → R)
    (k : Letter) (p q : List Letter) :
    wordWeight wt (k::(p ++ A::q)) =
      wt k * (wordWeight wt p * (wt A * wordWeight wt q)) := by
  induction p with
  | nil =>
    exact congrArg (fun t => wt k * t) (Lean.Grind.Semiring.one_mul _).symm
  | cons t p ih =>
    simp only [List.cons_append, wordWeight] at ih ⊢
    have h : wordWeight wt (p ++ A::q) = wordWeight wt p * (wt A * wordWeight wt q) := by
      clear ih
      induction p with
      | nil => simp [wordWeight, Lean.Grind.Semiring.one_mul]
      | cons x ps hps =>
        simp only [List.cons_append, wordWeight, hps, Lean.Grind.Semiring.mul_assoc]
    rw [h, Lean.Grind.Semiring.mul_assoc]

#print axioms firstBelow_result
#print axioms firstBelow_drop_iff
#print axioms heightRun_succ_scan
#print axioms return_cons_factors
#print axioms return_factors_unique
#print axioms return_weight_factor
end WalkQuarticFirstReturn


/-! Source automaton's high-band return, linked to unique path factorization. -/
namespace WalkQuarticBandReturn
open WalkQuarticWord WalkQuarticPhases WalkQuarticRecognize
open WalkQuarticCounting WalkQuarticFirstReturn
open Letter

set_option linter.unusedSimpArgs false

abbrev Loc := Phase × Nat

def bandStep (base : Nat) (s : Loc) : Letter → Option Loc
  | A => if s.2 = 0 then none else some (advanceA s.1, s.2-1)
  | B => some (advanceB s.1 (base+s.2), s.2+1)
  | C => some (advanceC s.1 (base+s.2), s.2+1)

def bandRun (base : Nat) (s : Loc) : List Letter → Option Loc
  | [] => some s
  | k::w => (bandStep base s k).bind fun t => bandRun base t w

theorem bandRun_append (b : Nat) (s : Loc) (w u : List Letter) :
    bandRun b s (w++u) =
      (bandRun b s w).bind (fun t => bandRun b t u) := by
  induction w generalizing s with
  | nil => rfl
  | cons k w ih =>
    simp only [List.cons_append, bandRun]
    cases h : bandStep b s k <;> simp [ih]

theorem bandRun_height (b : Nat) (s : Loc) (w : List Letter) :
    (bandRun b s w).map Prod.snd = heightRun s.2 w := by
  induction w generalizing s with
  | nil => rfl
  | cons k w ih =>
    cases k with
    | A =>
      by_cases h : s.2=0 <;> simp [bandRun, bandStep, heightRun, h, ih]
    | B => simp [bandRun, bandStep, heightRun, ih]
    | C => simp [bandRun, bandStep, heightRun, ih]

theorem actual_bandRun (b : Nat) (hb : 5≤b) (s t : Loc) (w : List Letter)
    (hs : legal s.1 (b+s.2)) (hr : bandRun b s w=some t) :
    iter (some (.high s.1 (b+s.2))) w = some (.high t.1 (b+t.2)) ∧
    legal t.1 (b+t.2) := by
  induction w generalizing s with
  | nil =>
    simp only [bandRun, Option.some.injEq] at hr
    subst t
    exact ⟨rfl,hs⟩
  | cons k w ih =>
    cases k with
    | A =>
      by_cases h : s.2=0
      · simp [bandRun, bandStep, h] at hr
      · simp only [bandRun, bandStep, h, ite_false, Option.bind_some] at hr
        have hh : 6≤b+s.2 := by omega
        have he : b+s.2-1=b+(s.2-1) := by omega
        have hn : b+s.2≠5 := by omega
        have hl := A_legal s.1 (b+s.2) hh hs
        rw [he] at hl
        simpa [iter, transition, step, hn, he] using ih _ hl hr
    | B =>
      simp only [bandRun, bandStep, Option.bind_some] at hr
      have hh : 5≤b+s.2 := by omega
      have hl := B_legal s.1 (b+s.2) hh hs
      simpa [iter, transition, step, Nat.add_assoc] using ih _ hl hr
    | C =>
      simp only [bandRun, bandStep, Option.bind_some] at hr
      have hh : 5≤b+s.2 := by omega
      have hl := C_legal s.1 (b+s.2) hh hs
      simpa [iter, transition, step, Nat.add_assoc] using ih _ hl hr

def bump (s : Loc) : Loc := (s.1,s.2+1)

/-- A path that stays in the higher band is unaffected by widening the base;
only its recorded distance from the base increases by one. -/
theorem bandRun_shift (b : Nat) (s t : Loc) (w : List Letter)
    (hr : bandRun (b+1) s w=some t) :
    bandRun b (bump s) w = some (bump t) := by
  induction w generalizing s with
  | nil =>
    simp only [bandRun, Option.some.injEq] at hr
    subst t
    rfl
  | cons k w ih =>
    cases k with
    | A =>
      by_cases e : s.2=0
      · simp [bandRun, bandStep, e] at hr
      · simp only [bandRun, bandStep, e, ite_false, Option.bind_some] at hr
        have h : s.2-1+1=s.2 := by omega
        simpa [bandRun, bandStep, bump, h] using ih _ hr
    | B =>
      simp only [bandRun, bandStep, Option.bind_some] at hr
      have h : b+(s.2+1)=(b+1)+s.2 := by omega
      simpa [bandRun, bandStep, bump, h] using ih _ hr
    | C =>
      simp only [bandRun, bandStep, Option.bind_some] at hr
      have h : b+(s.2+1)=(b+1)+s.2 := by omega
      simpa [bandRun, bandStep, bump, h] using ih _ hr

theorem bandStep_period (b : Nat) (s : Loc) (k : Letter) :
    bandStep (b+6) s k = bandStep b s k := by
  obtain ⟨p,d⟩ := s
  have e : b+6+d = b+d+6 := by omega
  cases k with
  | A => rfl
  | B =>
    have h : (b+d+6)%3 = (b+d)%3 := by
      exact Nat.add_mul_mod_self_left (b+d) 3 2
    cases p <;> simp [bandStep, advanceB, e, h]
  | C =>
    have h : (b+d+6)%2 = (b+d)%2 := by
      exact Nat.add_mul_mod_self_left (b+d) 2 3
    cases p <;> simp [bandStep, advanceC, e, h]

theorem bandRun_period (b : Nat) (s : Loc) (w : List Letter) :
    bandRun (b+6) s w = bandRun b s w := by
  induction w generalizing s with
  | nil => rfl
  | cons k w ih =>
    simp only [bandRun, bandStep_period]
    cases bandStep b s k <;> simp [ih]

def IsBandReturn (b : Nat) (i j : Phase) (w : List Letter) : Prop :=
  bandRun b (i,0) w = some (j,0)

def upPhase (b : Nat) (i : Phase) (k : Letter) : Phase :=
  if k=B then advanceB i b else advanceC i b

theorem bandRun_up (b : Nat) (i : Phase) (k : Letter) (h : k≠A)
    (w : List Letter) :
    bandRun b (i,0) (k::w) = bandRun b (upPhase b i k,1) w := by
  cases k with
  | A => exact (h rfl).elim
  | B => simp [bandRun, bandStep, upPhase]
  | C => simp [bandRun, bandStep, upPhase]

theorem realize_return_factor (b : Nat) (i j : Phase) (k : Letter) (p q : List Letter)
    (hk : k≠A) (hp : IsBandReturn (b+1) (upPhase b i k) j p) :
    bandRun b (i,0) (k::(p++A::q)) = bandRun b (advanceA j,0) q := by
  rw [bandRun_up b i k hk, bandRun_append]
  have H := bandRun_shift b (upPhase b i k,0) (j,0) p hp
  rw [show bump (upPhase b i k,0)=(upPhase b i k,1) from rfl,
      show bump (j,0)=(j,1) from rfl] at H
  simp [H, bandRun, bandStep]

/-- There is exactly one cut; the phase reached just inside the cut is
likewise determined by the inner word. -/
theorem nonempty_return_factor (b : Nat) (i j : Phase) (k : Letter)
    (w : List Letter) :
    IsBandReturn b i j (k::w) ↔ k≠A ∧
    ∃ p q : List Letter, ∃ x : Phase,
      w=p++A::q ∧ IsBandReturn (b+1) (upPhase b i k) x p ∧
      IsBandReturn b (advanceA x) j q := by
  constructor
  · intro H
    have hh := bandRun_height b (i,0) (k::w)
    rw [show bandRun b (i,0) (k::w)=some (j,0) from H] at hh
    have ht : IsReturn (k::w) := hh.symm
    obtain ⟨hk,p,q,eq,hp,_hq⟩ := (return_cons_factors k w).mp ht
    have hr := bandRun_height (b+1) (upPhase b i k,0) p
    rw [show heightRun (upPhase b i k,0).2 p = some 0 from hp] at hr
    cases e : bandRun (b+1) (upPhase b i k,0) p with
    | none => simp [e] at hr
    | some t =>
      rw [e] at hr
      obtain ⟨x,d⟩ := t
      have hd : d=0 := Option.some.inj hr
      subst d
      have hres : IsBandReturn (b+1) (upPhase b i k) x p := e
      rw [show w=p++A::q from eq] at H
      have H' := realize_return_factor b i x k p q hk hres
      exact ⟨hk,p,q,x,eq,hres,H'.symm.trans H⟩
  · rintro ⟨hk,p,q,x,rfl,hp,hq⟩
    exact (realize_return_factor b i x k p q hk hp).trans hq

theorem band_return_factors_unique (b : Nat) (i : Phase) (k : Letter)
    (w p q p' q' : List Letter) (x x' : Phase)
    (e : w=p++A::q) (e' : w=p'++A::q')
    (hp : IsBandReturn (b+1) (upPhase b i k) x p)
    (hp' : IsBandReturn (b+1) (upPhase b i k) x' p') :
    p=p' ∧ q=q' ∧ x=x' := by
  have h := bandRun_height (b+1) (upPhase b i k,0) p
  have h' := bandRun_height (b+1) (upPhase b i k,0) p'
  rw [show bandRun (b+1) (upPhase b i k,0) p=some (x,0) from hp] at h
  rw [show bandRun (b+1) (upPhase b i k,0) p'=some (x',0) from hp'] at h'
  obtain ⟨rfl,rfl⟩ := return_factors_unique w p q p' q' e e' h.symm h'.symm
  have eq : some (x,0) = some (x',0) :=
    (show bandRun (b+1) (upPhase b i k,0) p=some (x,0) from hp).symm.trans hp'
  exact ⟨rfl,rfl,congrArg Prod.fst (Option.some.inj eq)⟩

#print axioms bandRun_height
#print axioms actual_bandRun
#print axioms bandRun_shift
#print axioms bandRun_period
#print axioms nonempty_return_factor
#print axioms band_return_factors_unique
end WalkQuarticBandReturn


/-! Exact all-length Cauchy recurrence for the stateful high-band returns. -/
namespace WalkQuarticFirstReturnGF
open WalkQuarticWord WalkQuarticPhases
open WalkQuarticCounting WalkQuarticPopulation WalkQuarticBandReturn
open Letter WalkQuarticFirstReturn
open Lean.Grind.Semiring

set_option linter.unusedSimpArgs false

def upLetters : List Letter := [B,C]

theorem mem_upLetters (k : Letter) : k ∈ upLetters ↔ k≠A := by
  cases k <;> decide

def bandWords (b n : Nat) (i j : Phase) : List (List Letter) :=
  (words n).filter (fun w => decide (bandRun b (i,0) w = some (j,0)))

theorem mem_bandWords (b n : Nat) (i j : Phase) (w : List Letter) :
    w ∈ bandWords b n i j ↔ w.length=n ∧ IsBandReturn b i j w := by
  simp [bandWords, mem_words_iff_length, IsBandReturn]

theorem bandWords_nodup (b n : Nat) (i j : Phase) :
    (bandWords b n i j).Nodup :=
  List.Sublist.nodup List.filter_sublist (words_nodup n)

/-- Dependent product of finite duplicate-free lists, retaining tags. -/
def sigmaList {α : Type u} {β : Type v} (xs : List α) (f : α → List β) : List (α × β) :=
  xs.flatMap (fun x => (f x).map (fun y => (x,y)))

theorem mem_sigmaList {α : Type u} {β : Type v} (xs : List α) (f : α → List β)
    (x : α) (y : β) : (x,y) ∈ sigmaList xs f ↔ x∈xs ∧ y∈f x := by
  simp [sigmaList, List.mem_flatMap]

theorem sigmaList_nodup {α : Type u} {β : Type v} (xs : List α) (f : α → List β)
    (hn : xs.Nodup) (hf : ∀ x∈xs, (f x).Nodup) : (sigmaList xs f).Nodup := by
  induction xs with
  | nil => simp [sigmaList]
  | cons x xs ih =>
    obtain ⟨h₀,h₁⟩ := List.nodup_cons.mp hn
    simp only [sigmaList, List.flatMap_cons, List.nodup_append]
    exact ⟨nodup_map_of_inj _ (fun _ _ h => congrArg Prod.snd h) _ (hf _ List.mem_cons_self),
      ih h₁ (fun a ha => hf a (List.mem_cons_of_mem _ ha)),
      fun a ha b hb eq => by
        obtain ⟨t, _, rfl⟩ := List.mem_map.mp ha
        subst b
        exact h₀ ((mem_sigmaList xs f x t).mp hb).1⟩

theorem nodup_map_of_injOn {α : Type u} {β : Type v} (f : α → β)
    (xs : List α) (hn : xs.Nodup)
    (hi : ∀ x∈xs, ∀ y∈xs, f x=f y → x=y) : (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨h₀,h₁⟩ := List.nodup_cons.mp hn
    refine List.nodup_cons.mpr ⟨?_, ih h₁ (fun a ha b hb => hi a
      (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))⟩
    intro H
    obtain ⟨y,hy,e⟩ := List.mem_map.mp H
    have h := hi y (List.mem_cons_of_mem _ hy) x List.mem_cons_self e
    exact h₀ (h ▸ hy)

abbrev Factor := Nat × Letter × Phase × List Letter × List Letter

def factors (b n : Nat) (i j : Phase) : List Factor :=
  sigmaList (List.range (n+1)) fun m =>
  sigmaList upLetters fun k =>
  sigmaList highPhases fun x =>
  sigmaList (bandWords (b+1) m (upPhase b i k) x) fun _ =>
  bandWords b (n-m) (advanceA x) j

theorem mem_factors (b n : Nat) (i j : Phase) (m : Nat) (k : Letter)
    (x : Phase) (p q : List Letter) :
    (m,k,x,p,q) ∈ factors b n i j ↔
    m≤n ∧ k≠A ∧ p.length=m ∧ IsBandReturn (b+1) (upPhase b i k) x p ∧
       q.length=n-m ∧ IsBandReturn b (advanceA x) j q := by
  have hx : x ∈ highPhases := by cases x <;> decide
  simp [factors, mem_sigmaList, List.mem_range, hx, mem_upLetters, mem_bandWords,
    Nat.lt_succ_iff, and_assoc]

theorem factors_nodup (b n : Nat) (i j : Phase) : (factors b n i j).Nodup := by
  unfold factors
  apply sigmaList_nodup _ _ List.nodup_range
  intro m _
  apply sigmaList_nodup _ _ (by decide)
  intro k _
  apply sigmaList_nodup _ _ (by decide)
  intro x _
  exact sigmaList_nodup _ _ (bandWords_nodup ..) (fun _ _ => bandWords_nodup ..)

def assemble : Factor → List Letter
  | (_,k,_,p,q) => k::(p++A::q)

theorem assemble_injOn (b n : Nat) (i j : Phase) :
    ∀ u ∈ factors b n i j, ∀ v ∈ factors b n i j, assemble u=assemble v → u=v := by
  rintro ⟨m,k,x,p,q⟩ hu ⟨m',k',x',p',q'⟩ hv he
  obtain ⟨_,_,hlen,hp,_,_⟩ := (mem_factors b n i j m k x p q).mp hu
  obtain ⟨_,_,hlen',hp',_,_⟩ := (mem_factors b n i j m' k' x' p' q').mp hv
  obtain ⟨eqK,eqTail⟩ := List.cons.inj
    (show k :: (p ++ A :: q) = k' :: (p' ++ A :: q') from he)
  subst k'
  obtain ⟨rfl,rfl,rfl⟩ := band_return_factors_unique b i k
    (p++A::q) p q p' q' x x' rfl eqTail hp hp'
  have hh := hlen.symm.trans hlen'
  rw [hh]

theorem assemble_factors_perm (b n : Nat) (i j : Phase) :
    List.Perm ((factors b n i j).map assemble) (bandWords b (n+2) i j) := by
  apply (List.perm_ext_iff_of_nodup
    (nodup_map_of_injOn _ _ (factors_nodup b n i j) (assemble_injOn b n i j))
    (bandWords_nodup b (n+2) i j)).mpr
  intro w
  constructor
  · intro hw
    obtain ⟨⟨m,k,x,p,q⟩, hf, rfl⟩ := List.mem_map.mp hw
    obtain ⟨hm,hk,hP,hp,hQ,hq⟩ := (mem_factors b n i j m k x p q).mp hf
    refine (mem_bandWords b (n+2) i j _).mpr ⟨?_, ?_⟩
    · simp only [assemble, List.length_cons, List.length_append]
      omega
    · exact (nonempty_return_factor b i j k _).mpr ⟨hk,p,q,x,rfl,hp,hq⟩
  · intro hw
    obtain ⟨hl,hr⟩ := (mem_bandWords b (n+2) i j w).mp hw
    cases w with
    | nil => simp at hl
    | cons k w =>
      obtain ⟨hk,p,q,x,rfl,hp,hq⟩ := (nonempty_return_factor b i j k _).mp hr
      simp only [List.length_cons, List.length_append] at hl
      refine List.mem_map.mpr ⟨(p.length,k,x,p,q), ?_,rfl⟩
      exact (mem_factors b n i j p.length k x p q).mpr ⟨by omega,hk,rfl,hp,by omega,hq⟩

section Weights
variable {R : Type u} [Lean.Grind.Semiring R]

theorem lsum_sigmaList {α : Type v} {β : Type w} (g : α × β → R)
    (xs : List α) (f : α → List β) :
    lsum g (sigmaList xs f) = lsum (fun x => lsum (fun y => g (x,y)) (f x)) xs := by
  simp only [sigmaList, lsum_flatMap, lsum_map]

def returnCoeff (wt : Letter → R) (b n : Nat) (i j : Phase) : R :=
  lsum (wordWeight wt) (bandWords b n i j)

/-- Word-length coefficient of R_b = I + U_b R_(b+1) D_(b+1) R_b.
The index n counts the internal letters: the up and down add two. -/
theorem returnCoeff_succ_succ (wt : Letter → R) (b n : Nat) (i j : Phase) :
    returnCoeff wt b (n+2) i j =
      lsum (fun m => lsum (fun k => lsum (fun x =>
        wt k * (returnCoeff wt (b+1) m (upPhase b i k) x *
          (wt A * returnCoeff wt b (n-m) (advanceA x) j))) highPhases) upLetters)
        (List.range (n+1)) := by
  rw [returnCoeff, ←lsum_perm (wordWeight wt) (assemble_factors_perm b n i j), lsum_map]
  simp only [factors, lsum_sigmaList, assemble, return_weight_factor, returnCoeff,
    lsum_mul_left, lsum_mul_right, mul_assoc]
  <;> first | rfl | done

theorem returnCoeff_zero (wt : Letter → R) (b : Nat) (i j : Phase) :
    returnCoeff wt b 0 i j = markProp (i=j) := by
  by_cases h : i=j
  · subst j
    simp [returnCoeff, bandWords, words, bandRun, lsum, wordWeight, add_zero,
      markProp_true (rfl : i=i), markProp_true True.intro]
  · simp [returnCoeff, bandWords, words, bandRun, lsum, h,
      markProp_false h, markProp_false (not_false : ¬False)]

theorem returnCoeff_one (wt : Letter → R) (b : Nat) (i j : Phase) :
    returnCoeff wt b 1 i j = 0 := by
  simp [returnCoeff, bandWords, words, alphabet, bandRun, bandStep, lsum]

theorem returnCoeff_period (wt : Letter → R) (b n : Nat) (i j : Phase) :
    returnCoeff wt (b+6) n i j = returnCoeff wt b n i j := by
  simp only [returnCoeff, bandWords, bandRun_period]

/-- The coefficient form uniquely determines all base heights at once. -/
theorem returnCoeff_unique (wt : Letter → R) (F : Nat → Nat → Phase → Phase → R)
    (h0 : ∀ b i j, F b 0 i j = markProp (i=j))
    (h1 : ∀ b i j, F b 1 i j = 0)
    (hstep : ∀ b n i j, F b (n+2) i j =
      lsum (fun m => lsum (fun k => lsum (fun x =>
        wt k * (F (b+1) m (upPhase b i k) x *
          (wt A * F b (n-m) (advanceA x) j))) highPhases) upLetters)
        (List.range (n+1))) :
    ∀ n b i j, F b n i j = returnCoeff wt b n i j := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro b i j
    cases n with
    | zero => rw [h0, returnCoeff_zero]
    | succ n =>
      cases n with
      | zero => rw [h1, returnCoeff_one]
      | succ n =>
        rw [hstep, returnCoeff_succ_succ]
        apply lsum_congr_mem
        intro m hm
        have hm' : m≤n := Nat.le_of_lt_succ (List.mem_range.mp hm)
        apply lsum_congr_mem
        intro k hk
        apply lsum_congr_mem
        intro x hx
        rw [ih m (by omega), ih (n-m) (by omega)]

end Weights

#print axioms assemble_factors_perm
#print axioms returnCoeff_zero
#print axioms returnCoeff_one
#print axioms returnCoeff_succ_succ
#print axioms returnCoeff_period
#print axioms returnCoeff_unique
end WalkQuarticFirstReturnGF


/-! Exact all-length high-band terminal meander decomposition. -/
namespace WalkQuarticMeander
open WalkQuarticWord WalkQuarticPhases WalkQuarticRecognize WalkQuarticCounting
open WalkQuarticFirstReturn WalkQuarticBandReturn WalkQuarticFirstReturnGF
open WalkQuarticPopulation Letter

set_option linter.unusedSimpArgs false

theorem heightRun_append (h : Nat) (p q : List Letter) :
    heightRun h (p++q) = (heightRun h p).bind (fun h' => heightRun h' q) := by
  induction p generalizing h with
  | nil => rfl
  | cons k p ih =>
    cases k with
    | A =>
      by_cases e : h=0 <;> simp [heightRun, e, ih]
    | B | C => simp [heightRun, ih]

theorem heightRun_downcross (h : Nat) (w p q : List Letter)
    (hs : firstBelow h w = .drop p q) : heightRun h w = none := by
  obtain ⟨rfl,hp⟩ := (firstBelow_drop_iff h w p q).mp hs
  simp [heightRun_append, hp, heightRun]

def BandAccept (b : Nat) (i : Phase) (w : List Letter) : Prop :=
  ∃ t : Loc, bandRun b (i,0) w = some t ∧ terminal t.1 (b+t.2)

theorem bandAccept_nonempty (b : Nat) (i : Phase) (k : Letter) (w : List Letter) :
    BandAccept b i (k::w) ↔ k≠A ∧
       (BandAccept (b+1) (upPhase b i k) w ∨
        ∃ p q : List Letter, ∃ x : Phase, w=p++A::q ∧
          IsBandReturn (b+1) (upPhase b i k) x p ∧ BandAccept b (advanceA x) q) := by
  constructor
  · rintro ⟨t,hr,ht⟩
    have hk : k≠A := by
      rintro rfl
      simp [bandRun, bandStep] at hr
    refine ⟨hk,?_⟩
    have hr0 := firstBelow_result 0 w
    cases h : firstBelow 0 w with
    | stay d =>
      rw [h] at hr0
      have hs := bandRun_height (b+1) (upPhase b i k,0) w
      change heightRun 0 w=some d at hr0
      rw [show heightRun (upPhase b i k,0).2 w=some d from hr0] at hs
      cases hrun : bandRun (b+1) (upPhase b i k,0) w with
      | none => simp [hrun] at hs
      | some u =>
        have hu := bandRun_shift b (upPhase b i k,0) u w hrun
        rw [bandRun_up b i k hk] at hr
        have eq : bump u=t := Option.some.inj (hu.symm.trans hr)
        subst t
        exact Or.inl ⟨u,hrun,by simpa [bump, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht⟩
    | drop p q =>
      obtain ⟨eq,hp⟩ := (firstBelow_drop_iff 0 w p q).mp h
      have hr' := bandRun_height (b+1) (upPhase b i k,0) p
      rw [show heightRun (upPhase b i k,0).2 p=some 0 from hp] at hr'
      cases hrun : bandRun (b+1) (upPhase b i k,0) p with
      | none => simp [hrun] at hr'
      | some u =>
        rw [hrun] at hr'
        obtain ⟨x,d⟩ := u
        have e : d=0 := Option.some.inj hr'
        subst d
        have H := realize_return_factor b i x k p q hk hrun
        rw [eq,H] at hr
        exact Or.inr ⟨p,q,x,eq,hrun,t,hr,ht⟩
  · rintro ⟨hk, h | ⟨p,q,x,eq,hp,hq⟩⟩
    · rcases h with ⟨t,hr,ht⟩
      refine ⟨bump t,?_,?_⟩
      · rw [bandRun_up b i k hk]
        exact bandRun_shift b (upPhase b i k,0) t w hr
      · simpa [bump, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht
    · rcases hq with ⟨t,hr,ht⟩
      exact ⟨t,(congrArg (bandRun b (i,0)) (congrArg (List.cons k) eq)).trans
        ((realize_return_factor b i x k p q hk hp).trans hr),ht⟩

theorem bandAccept_ne_drop (b : Nat) (i x : Phase) (k : Letter)
    (w p q : List Letter)
    (hn : BandAccept (b+1) (upPhase b i k) w)
    (eq : w=p++A::q) (hp : IsBandReturn (b+1) (upPhase b i k) x p) : False := by
  obtain ⟨t,ht,_⟩ := hn
  have H := bandRun_height (b+1) (upPhase b i k,0) w
  rw [ht] at H
  have P := bandRun_height (b+1) (upPhase b i k,0) p
  rw [show bandRun (b+1) (upPhase b i k,0) p=some (x,0) from hp] at P
  have hs := (firstBelow_drop_iff 0 w p q).mpr ⟨eq,P.symm⟩
  have hz := heightRun_downcross 0 w p q hs
  rw [show heightRun (upPhase b i k,0).2 w=none from hz] at H
  cases H

/-- This acceptance is exactly the recognizer's acceptance within the high band. -/
theorem bandAccept_actual (b : Nat) (hb : 5≤b) (i : Phase) (hi : legal i b)
    (w : List Letter) :
    BandAccept b i w ↔
      (∃ d : Nat, heightRun 0 w = some d) ∧ accepts (iter (some (.high i b)) w) := by
  constructor
  · rintro ⟨t, hr, ht⟩
    have H := bandRun_height b (i,0) w
    rw [hr] at H
    refine ⟨⟨t.2,H.symm⟩,?_⟩
    have J := actual_bandRun b hb (i,0) t w hi hr
    rw [show iter (some (.high i b)) w = some (.high t.1 (b+t.2)) from J.1]
    exact (terminal_exact t.1 (b+t.2) (by omega)).mp ht
  · rintro ⟨⟨d,hd⟩,hacc⟩
    have H := bandRun_height b (i,0) w
    rw [show heightRun (i,0).2 w=some d from hd] at H
    cases e : bandRun b (i,0) w with
    | none => simp [e] at H
    | some t =>
      have J := actual_bandRun b hb (i,0) t w hi e
      rw [show iter (some (.high i b)) w = some (.high t.1 (b+t.2)) from J.1] at hacc
      exact ⟨t,e,(terminal_exact t.1 (b+t.2) (by omega)).mpr hacc⟩

theorem terminal_period (p : Phase) (h : Nat) :
    terminal p (h+6) ↔ terminal p h := by
  have h2 : (h+6)%2 = h%2 := Nat.add_mul_mod_self_left h 2 3
  have h3 : (h+6)%3 = h%3 := Nat.add_mul_mod_self_left h 3 2
  cases p <;> simp [terminal,h2,h3]

theorem bandAccept_period (b : Nat) (i : Phase) (w : List Letter) :
    BandAccept (b+6) i w ↔ BandAccept b i w := by
  have H (t : Loc) : terminal t.1 (b+6+t.2) ↔ terminal t.1 (b+t.2) := by
    rw [show b+6+t.2 = b+t.2+6 by omega, terminal_period]
  simp only [BandAccept, bandRun_period, H]

#print axioms bandAccept_nonempty
#print axioms bandAccept_ne_drop
#print axioms bandAccept_actual
#print axioms bandAccept_period
end WalkQuarticMeander


/-! Weighted transfer equation for terminal paths that remain in a high band. -/
namespace WalkQuarticMeanderGF
open WalkQuarticWord WalkQuarticPhases WalkQuarticCounting WalkQuarticPopulation
open WalkQuarticFirstReturn WalkQuarticBandReturn WalkQuarticFirstReturnGF WalkQuarticMeander
open Letter Lean.Grind.Semiring

set_option linter.unusedSimpArgs false

noncomputable def meanderWords (b n : Nat) (i : Phase) : List (List Letter) := by
  classical
  exact (words n).filter (fun w => decide (BandAccept b i w))

theorem mem_meanderWords (b n : Nat) (i : Phase) (w : List Letter) :
    w∈meanderWords b n i ↔ w.length=n ∧ BandAccept b i w := by
  classical
  simp [meanderWords, mem_words_iff_length]

theorem meanderWords_nodup (b n : Nat) (i : Phase) : (meanderWords b n i).Nodup := by
  unfold meanderWords
  exact List.Sublist.nodup List.filter_sublist (words_nodup n)

noncomputable def stayFactors (b n : Nat) (i : Phase) : List (Letter × List Letter) :=
  sigmaList upLetters (fun k => meanderWords (b+1) n (upPhase b i k))

noncomputable def stayWords (b n : Nat) (i : Phase) : List (List Letter) :=
  (stayFactors b n i).map (fun t => t.1::t.2)

theorem mem_stayWords (b n : Nat) (i : Phase) (k : Letter) (w : List Letter) :
    k::w∈stayWords b n i ↔ k≠A ∧ w.length=n ∧ BandAccept (b+1) (upPhase b i k) w := by
  constructor
  · intro hw
    obtain ⟨⟨l,v⟩,hh,eq⟩ := List.mem_map.mp hw
    obtain ⟨hk,hv⟩ := List.cons.inj (show l::v=k::w from eq)
    subst l
    subst v
    have hs := (mem_sigmaList upLetters (fun k => meanderWords (b+1) n (upPhase b i k)) k w).mp hh
    exact ⟨(mem_upLetters k).mp hs.1,(mem_meanderWords _ _ _ _).mp hs.2⟩
  · rintro ⟨hk,hw,hm⟩
    exact List.mem_map.mpr ⟨(k,w), (mem_sigmaList _ _ _ _).mpr
      ⟨(mem_upLetters k).mpr hk,(mem_meanderWords _ _ _ _).mpr ⟨hw,hm⟩⟩, rfl⟩

theorem stayWords_nodup (b n : Nat) (i : Phase) : (stayWords b n i).Nodup := by
  unfold stayWords stayFactors
  apply nodup_map_of_inj
  · rintro ⟨k,w⟩ ⟨l,v⟩ eq
    obtain ⟨rfl,rfl⟩ := List.cons.inj eq
    rfl
  · exact sigmaList_nodup _ _ (by decide) (fun _ _ => meanderWords_nodup ..)

noncomputable def dropFactors (b n : Nat) (i : Phase) : List Factor :=
  sigmaList (List.range (n+1)) fun m =>
  sigmaList upLetters fun k =>
  sigmaList highPhases fun x =>
  sigmaList (bandWords (b+1) m (upPhase b i k) x) fun _ =>
  meanderWords b (n-m) (advanceA x)

theorem mem_dropFactors (b n : Nat) (i : Phase) (m : Nat) (k : Letter)
    (x : Phase) (p q : List Letter) :
    (m,k,x,p,q) ∈ dropFactors b n i ↔
    m≤n ∧ k≠A ∧ p.length=m ∧ IsBandReturn (b+1) (upPhase b i k) x p ∧
       q.length=n-m ∧ BandAccept b (advanceA x) q := by
  have hx : x ∈ highPhases := by cases x <;> decide
  simp [dropFactors, mem_sigmaList, List.mem_range, hx, mem_upLetters,
    mem_bandWords, mem_meanderWords, Nat.lt_succ_iff, and_assoc]

theorem dropFactors_nodup (b n : Nat) (i : Phase) : (dropFactors b n i).Nodup := by
  unfold dropFactors
  apply sigmaList_nodup _ _ List.nodup_range
  intro m _
  apply sigmaList_nodup _ _ (by decide)
  intro k _
  apply sigmaList_nodup _ _ (by decide)
  intro x _
  exact sigmaList_nodup _ _ (bandWords_nodup ..) (fun _ _ => meanderWords_nodup ..)

theorem drop_assemble_injOn (b n : Nat) (i : Phase) :
    ∀ u ∈ dropFactors b n i, ∀ v ∈ dropFactors b n i, assemble u=assemble v → u=v := by
  rintro ⟨m,k,x,p,q⟩ hu ⟨m',k',x',p',q'⟩ hv he
  obtain ⟨_,_,hlen,hp,_,_⟩ := (mem_dropFactors b n i m k x p q).mp hu
  obtain ⟨_,_,hlen',hp',_,_⟩ := (mem_dropFactors b n i m' k' x' p' q').mp hv
  obtain ⟨eqK,eqTail⟩ := List.cons.inj
    (show k :: (p ++ A :: q) = k' :: (p' ++ A :: q') from he)
  subst k'
  obtain ⟨rfl,rfl,rfl⟩ := band_return_factors_unique b i k
    (p++A::q) p q p' q' x x' rfl eqTail hp hp'
  have hh := hlen.symm.trans hlen'
  rw [hh]

theorem stay_drop_disjoint (b n : Nat) (i : Phase) :
    ∀ w∈stayWords b (n+1) i, ∀ v∈(dropFactors b n i).map assemble, w≠v := by
  intro w hw v hv e
  obtain ⟨⟨m,k,x,p,q⟩,hf,rfl⟩ := List.mem_map.mp hv
  subst w
  obtain ⟨_,_,hn⟩ := (mem_stayWords b (n+1) i k (p++A::q)).mp hw
  obtain ⟨_,_,_,hp,_,_⟩ := (mem_dropFactors b n i m k x p q).mp hf
  exact bandAccept_ne_drop b i x k (p++A::q) p q hn rfl hp

theorem meanderFactors_perm (b n : Nat) (i : Phase) :
    List.Perm (stayWords b (n+1) i ++ (dropFactors b n i).map assemble)
      (meanderWords b (n+2) i) := by
  apply (List.perm_ext_iff_of_nodup (List.nodup_append.mpr
    ⟨stayWords_nodup b (n+1) i,
     nodup_map_of_injOn _ _ (dropFactors_nodup b n i) (drop_assemble_injOn b n i),
     stay_drop_disjoint b n i⟩) (meanderWords_nodup b (n+2) i)).mpr
  intro w
  constructor
  · intro hw
    rcases List.mem_append.mp hw with hs | hd
    · cases w with
      | nil =>
        obtain ⟨⟨k,q⟩,_,e⟩ := List.mem_map.mp hs
        cases e
      | cons k q =>
        obtain ⟨hk,hl,hm⟩ := (mem_stayWords b (n+1) i k q).mp hs
        exact (mem_meanderWords _ _ _ _).mpr
          ⟨by simp [hl],(bandAccept_nonempty _ _ _ _).mpr ⟨hk,Or.inl hm⟩⟩
    · obtain ⟨⟨m,k,x,p,q⟩,hf,rfl⟩ := List.mem_map.mp hd
      obtain ⟨hm,hk,hP,hp,hQ,hq⟩ := (mem_dropFactors b n i m k x p q).mp hf
      refine (mem_meanderWords _ _ _ _).mpr ⟨?_,?_⟩
      · simp only [assemble, List.length_cons, List.length_append]; omega
      · exact (bandAccept_nonempty _ _ _ _).mpr ⟨hk,Or.inr ⟨p,q,x,rfl,hp,hq⟩⟩
  · intro hw
    obtain ⟨hl,hm⟩ := (mem_meanderWords b (n+2) i w).mp hw
    cases w with
    | nil => simp at hl
    | cons k w =>
      obtain ⟨hk,hu | ⟨p,q,x,rfl,hp,hq⟩⟩ := (bandAccept_nonempty _ _ _ _).mp hm
      · exact List.mem_append_left _ ((mem_stayWords _ _ _ _ _).mpr ⟨hk,by simpa using hl,hu⟩)
      · simp only [List.length_cons, List.length_append] at hl
        apply List.mem_append_right
        refine List.mem_map.mpr ⟨(p.length,k,x,p,q),?_,rfl⟩
        exact (mem_dropFactors _ _ _ _ _ _ _ _).mpr ⟨by omega,hk,rfl,hp,by omega,hq⟩

theorem meander_one_perm (b : Nat) (i : Phase) :
    List.Perm (stayWords b 0 i) (meanderWords b 1 i) := by
  apply (List.perm_ext_iff_of_nodup (stayWords_nodup b 0 i) (meanderWords_nodup b 1 i)).mpr
  intro w
  constructor
  · intro hf
    obtain ⟨⟨k,q⟩,_,rfl⟩ := List.mem_map.mp hf
    obtain ⟨hk,hl,hm⟩ := (mem_stayWords b 0 i k q).mp hf
    exact (mem_meanderWords _ _ _ _).mpr ⟨by simp [hl],(bandAccept_nonempty _ _ _ _).mpr ⟨hk,Or.inl hm⟩⟩
  · intro hf
    obtain ⟨hl,hm⟩ := (mem_meanderWords b 1 i w).mp hf
    cases w with
    | nil => simp at hl
    | cons k w =>
      obtain ⟨hk,hu | ⟨p,q,x,rfl,hp,hq⟩⟩ := (bandAccept_nonempty _ _ _ _).mp hm
      · exact (mem_stayWords _ _ _ _ _).mpr ⟨hk,by simpa using hl,hu⟩
      · simp only [List.length_cons, List.length_append] at hl
        omega

section Weights
variable {R : Type u} [Lean.Grind.Semiring R]

noncomputable def meanderCoeff (wt : Letter → R) (b n : Nat) (i : Phase) : R :=
  lsum (wordWeight wt) (meanderWords b n i)

theorem sum_stayWords (wt : Letter → R) (b n : Nat) (i : Phase) :
    lsum (wordWeight wt) (stayWords b n i) =
      lsum (fun k => wt k * meanderCoeff wt (b+1) n (upPhase b i k)) upLetters := by
  simp only [stayWords, stayFactors, lsum_map, lsum_sigmaList,
    wordWeight, meanderCoeff, lsum_mul_left]

theorem meanderCoeff_zero (wt : Letter → R) (b : Nat) (i : Phase) :
    meanderCoeff wt b 0 i = markProp (terminal i b) := by
  classical
  have he : BandAccept b i [] ↔ terminal i b := by simp [BandAccept, bandRun]
  by_cases h : terminal i b
  · have h' : BandAccept b i [] := he.mpr h
    rw [markProp_true h]
    simp [meanderCoeff, meanderWords, words, h', wordWeight, lsum, add_zero]
  · have h' : ¬BandAccept b i [] := fun H => h (he.mp H)
    rw [markProp_false h]
    simp [meanderCoeff, meanderWords, words, h', lsum]

theorem meanderCoeff_one (wt : Letter → R) (b : Nat) (i : Phase) :
    meanderCoeff wt b 1 i =
      lsum (fun k => wt k * meanderCoeff wt (b+1) 0 (upPhase b i k)) upLetters := by
  rw [meanderCoeff, ←lsum_perm (wordWeight wt) (meander_one_perm b i), sum_stayWords]

/-- Coefficients of M_b = F_b + U_b M_(b+1) + U_b R_(b+1) D_(b+1) M_b. -/
theorem meanderCoeff_succ_succ (wt : Letter → R) (b n : Nat) (i : Phase) :
    meanderCoeff wt b (n+2) i =
      lsum (fun k => wt k * meanderCoeff wt (b+1) (n+1) (upPhase b i k)) upLetters +
      lsum (fun m => lsum (fun k => lsum (fun x =>
        wt k * (returnCoeff wt (b+1) m (upPhase b i k) x *
          (wt A * meanderCoeff wt b (n-m) (advanceA x)))) highPhases) upLetters)
        (List.range (n+1)) := by
  rw [meanderCoeff, ←lsum_perm (wordWeight wt) (meanderFactors_perm b n i),
    lsum_append, sum_stayWords, lsum_map]
  simp only [dropFactors, lsum_sigmaList, assemble, return_weight_factor,
    returnCoeff, meanderCoeff, lsum_mul_left, lsum_mul_right, mul_assoc]

theorem meanderCoeff_period (wt : Letter → R) (b n : Nat) (i : Phase) :
    meanderCoeff wt (b+6) n i = meanderCoeff wt b n i := by
  classical
  have eq (w : List Letter) : BandAccept (b+6) i w = BandAccept b i w :=
    propext (bandAccept_period b i w)
  simp only [meanderCoeff, meanderWords, eq]

theorem meanderCoeff_unique (wt : Letter → R) (F : Nat → Nat → Phase → R)
    (h0 : ∀ b i, F b 0 i = markProp (terminal i b))
    (h1 : ∀ b i, F b 1 i = lsum (fun k => wt k * F (b+1) 0 (upPhase b i k)) upLetters)
    (hs : ∀ b n i, F b (n+2) i =
      lsum (fun k => wt k * F (b+1) (n+1) (upPhase b i k)) upLetters +
      lsum (fun m => lsum (fun k => lsum (fun x =>
        wt k * (returnCoeff wt (b+1) m (upPhase b i k) x *
          (wt A * F b (n-m) (advanceA x)))) highPhases) upLetters)
        (List.range (n+1))) :
    ∀ n b i, F b n i = meanderCoeff wt b n i := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro b i
    cases n with
    | zero => rw [h0, meanderCoeff_zero]
    | succ n =>
      cases n with
      | zero =>
        rw [h1, meanderCoeff_one]
        simp only [h0, meanderCoeff_zero]
      | succ n =>
        rw [hs, meanderCoeff_succ_succ]
        congr 1
        · simp only [ih (n+1) (by omega)]
        · apply lsum_congr_mem
          intro m hm
          apply lsum_congr_mem
          intro k hk
          apply lsum_congr_mem
          intro x hx
          rw [ih (n-m) (by omega)]

end Weights

#print axioms meanderFactors_perm
#print axioms meanderCoeff_zero
#print axioms meanderCoeff_one
#print axioms meanderCoeff_succ_succ
#print axioms meanderCoeff_unique
#print axioms meanderCoeff_period
end WalkQuarticMeanderGF


/-! First exit from the height-five band, with exact source automaton phases. -/
namespace WalkQuarticBoundary
open WalkQuarticWord WalkQuarticPhases WalkQuarticRecognize WalkQuarticCounting
open WalkQuarticFirstReturn WalkQuarticBandReturn WalkQuarticFirstReturnGF
open WalkQuarticMeander WalkQuarticMeanderGF WalkQuarticPopulation
open Letter Lean.Grind.Semiring

set_option linter.unusedSimpArgs false

def exitLow (p : Phase) : Low :=
  match highExit p with
  | .low l => l
  | .high .. => .s0

theorem highExit_eq (p : Phase) : highExit p = .low (exitLow p) := by
  cases p <;> rfl

def LowAccept (l : Low) (w : List Letter) : Prop :=
  accepts (iter (some (.low l)) w)

def EntryAccept (p : Phase) (w : List Letter) : Prop :=
  accepts (iter (some (.high p 5)) w)

theorem entry_path_partition (i : Phase) (hi : legal i 5) (w : List Letter) :
    EntryAccept i w ↔ BandAccept 5 i w ∨
      ∃ p q : List Letter, ∃ x : Phase, w=p++A::q ∧
        IsBandReturn 5 i x p ∧ LowAccept (exitLow x) q := by
  have hS := firstBelow_result 0 w
  cases hscan : firstBelow 0 w with
  | stay k =>
    rw [hscan] at hS
    change heightRun 0 w=some k at hS
    constructor
    · intro hw
      exact Or.inl ((bandAccept_actual 5 (by omega) i hi w).mpr ⟨⟨k,hS⟩,hw⟩)
    · rintro (hc | ⟨p,q,x,eq,hp,hq⟩)
      · exact ((bandAccept_actual 5 (by omega) i hi w).mp hc).2
      · have h := bandRun_height 5 (i,0) p
        rw [show bandRun 5 (i,0) p=some (x,0) from hp] at h
        have hs := (firstBelow_drop_iff 0 w p q).mpr ⟨eq,h.symm⟩
        rw [hscan] at hs
        cases hs
  | drop p q =>
    obtain ⟨eq, hp⟩ := (firstBelow_drop_iff 0 w p q).mp hscan
    have H := bandRun_height 5 (i,0) p
    rw [show heightRun (i,0).2 p=some 0 from hp] at H
    cases bx : bandRun 5 (i,0) p with
    | none => simp [bx] at H
    | some t =>
      rw [bx] at H
      obtain ⟨x,d⟩ := t
      have he : d=0 := Option.some.inj H
      subst d
      have thisRun (y : Phase) (ys zs : List Letter)
          (hw : w=ys++A::zs) (hy : IsBandReturn 5 i y ys) :
          EntryAccept i w ↔ LowAccept (exitLow y) zs := by
        have J := actual_bandRun 5 (by omega) (i,0) (y,0) ys hi hy
        have it : iter (some (.high i 5)) ys = some (.high y 5) := by simpa using J.1
        simp [EntryAccept, LowAccept, hw, iter_append, it, iter, transition, step, highExit_eq]
      constructor
      · intro hw
        exact Or.inr ⟨p,q,x,eq,bx,(thisRun x p q eq bx).mp hw⟩
      · rintro (hc | ⟨p',q',x',e,hx,hq⟩)
        · obtain ⟨t,ht,_⟩ := hc
          have g := bandRun_height 5 (i,0) w
          rw [ht, show heightRun (i,0).2 w=none from heightRun_downcross 0 w p q hscan] at g
          cases g
        · exact (thisRun x' p' q' e hx).mpr hq

theorem entry_band_drop_disjoint (i x : Phase) (w p q : List Letter)
    (ha : BandAccept 5 i w) (eq : w=p++A::q) (hp : IsBandReturn 5 i x p) : False := by
  obtain ⟨t,ht,_⟩ := ha
  have H := bandRun_height 5 (i,0) w
  rw [ht] at H
  have P := bandRun_height 5 (i,0) p
  rw [show bandRun 5 (i,0) p=some (x,0) from hp] at P
  have hs := (firstBelow_drop_iff 0 w p q).mpr ⟨eq,P.symm⟩
  have hz := heightRun_downcross 0 w p q hs
  rw [show heightRun (i,0).2 w=none from hz] at H
  cases H

theorem entry_exit_factors_unique (i x x' : Phase) (w p q p' q' : List Letter)
    (e : w=p++A::q) (e' : w=p'++A::q')
    (hp : IsBandReturn 5 i x p) (hp' : IsBandReturn 5 i x' p') :
    p=p' ∧ q=q' ∧ x=x' := by
  have h := bandRun_height 5 (i,0) p
  have h' := bandRun_height 5 (i,0) p'
  rw [show bandRun 5 (i,0) p=some (x,0) from hp] at h
  rw [show bandRun 5 (i,0) p'=some (x',0) from hp'] at h'
  obtain ⟨rfl,rfl⟩ := return_factors_unique w p q p' q' e e' h.symm h'.symm
  exact ⟨rfl,rfl,congrArg Prod.fst (Option.some.inj
    ((show bandRun 5 (i,0) p=some (x,0) from hp).symm.trans hp'))⟩

theorem step_into_high_exact (l : Low) (k : Letter) (p : Phase) (h : Nat)
    (hs : lowestStep l k = some (.high p h)) : h=5 ∧ legal p 5 := by
  cases l <;> cases k <;> simp [lowestStep] at hs <;> grind [legal]

theorem iter_dead (w : List Letter) : iter none w = none := by
  induction w with
  | nil => rfl
  | cons k w ih => exact ih

#print axioms entry_path_partition
#print axioms entry_exit_factors_unique
#print axioms step_into_high_exact
end WalkQuarticBoundary


/-! Low and high-entry generating-function coefficients by exact first-exit splitting. -/
namespace WalkQuarticBoundaryGF
open WalkQuarticWord WalkQuarticPhases WalkQuarticRecognize WalkQuarticCounting
open WalkQuarticFirstReturn WalkQuarticBandReturn WalkQuarticFirstReturnGF
open WalkQuarticMeander WalkQuarticMeanderGF WalkQuarticPopulation WalkQuarticBoundary
open Letter Lean.Grind.Semiring

set_option linter.unusedSimpArgs false

noncomputable def acceptedWords (n : Nat) (s : State) : List (List Letter) := by
  classical
  exact (words n).filter (fun w => decide (accepts (iter s w)))

theorem mem_acceptedWords (n : Nat) (s : State) (w : List Letter) :
    w ∈ acceptedWords n s ↔ w.length=n ∧ accepts (iter s w) := by
  classical simp [acceptedWords, mem_words_iff_length]

theorem acceptedWords_nodup (n : Nat) (s : State) : (acceptedWords n s).Nodup := by
  unfold acceptedWords
  exact List.Sublist.nodup List.filter_sublist (words_nodup n)

abbrev ExitFactor := Nat × Phase × List Letter × List Letter

noncomputable def entryExits (n : Nat) (i : Phase) : List ExitFactor :=
  sigmaList (List.range (n+1)) fun m =>
  sigmaList highPhases fun x =>
  sigmaList (bandWords 5 m i x) fun _ =>
  acceptedWords (n-m) (some (.low (exitLow x)))

theorem mem_entryExits (n : Nat) (i : Phase) (m : Nat) (x : Phase) (p q : List Letter) :
    (m,x,p,q)∈entryExits n i ↔ m≤n ∧ p.length=m ∧ IsBandReturn 5 i x p ∧
      q.length=n-m ∧ LowAccept (exitLow x) q := by
  have hm : x∈highPhases := by cases x <;> decide
  simp [entryExits, mem_sigmaList, List.mem_range, Nat.lt_succ_iff,
    hm, mem_bandWords, mem_acceptedWords, LowAccept, and_assoc]

theorem entryExits_nodup (n : Nat) (i : Phase) : (entryExits n i).Nodup := by
  unfold entryExits
  apply sigmaList_nodup _ _ List.nodup_range
  intro m _
  apply sigmaList_nodup _ _ (by decide)
  intro x _
  exact sigmaList_nodup _ _ (bandWords_nodup ..) (fun _ _ => acceptedWords_nodup ..)

def assembleExit : ExitFactor → List Letter
  | (_,_,p,q) => p++A::q

theorem exit_assemble_injOn (n : Nat) (i : Phase) :
    ∀ u∈entryExits n i, ∀ v∈entryExits n i, assembleExit u=assembleExit v → u=v := by
  rintro ⟨m,x,p,q⟩ hu ⟨m',x',p',q'⟩ hv e
  obtain ⟨_,hm,hp,_,_⟩ := (mem_entryExits n i m x p q).mp hu
  obtain ⟨_,hm',hp',_,_⟩ := (mem_entryExits n i m' x' p' q').mp hv
  obtain ⟨rfl,rfl,rfl⟩ := entry_exit_factors_unique i x x'
    (p++A::q) p q p' q' rfl e hp hp'
  rw [hm.symm.trans hm']

theorem entryFactors_perm (n : Nat) (i : Phase) (hi : legal i 5) :
    List.Perm (meanderWords 5 (n+1) i ++ (entryExits n i).map assembleExit)
      (acceptedWords (n+1) (some (.high i 5))) := by
  apply (List.perm_ext_iff_of_nodup (List.nodup_append.mpr
    ⟨meanderWords_nodup ..,
     nodup_map_of_injOn _ _ (entryExits_nodup n i) (exit_assemble_injOn n i),?_⟩)
     (acceptedWords_nodup ..)).mpr
  · intro w
    constructor
    · intro hw
      rcases List.mem_append.mp hw with ha | he
      · obtain ⟨hl,hm⟩ := (mem_meanderWords ..).mp ha
        exact (mem_acceptedWords ..).mpr ⟨hl,(entry_path_partition i hi w).mpr (Or.inl hm)⟩
      · obtain ⟨⟨m,x,p,q⟩,hf,rfl⟩ := List.mem_map.mp he
        obtain ⟨hm,hP,hp,hQ,hq⟩ := (mem_entryExits n i m x p q).mp hf
        refine (mem_acceptedWords ..).mpr ⟨?_,?_⟩
        · simp only [assembleExit, List.length_append, List.length_cons]; omega
        · exact (entry_path_partition i hi _).mpr (Or.inr ⟨p,q,x,rfl,hp,hq⟩)
    · intro hw
      obtain ⟨hl,ha⟩ := (mem_acceptedWords ..).mp hw
      rcases (entry_path_partition i hi w).mp ha with hm | ⟨p,q,x,rfl,hp,hq⟩
      · exact List.mem_append_left _ ((mem_meanderWords ..).mpr ⟨hl,hm⟩)
      · simp only [List.length_append, List.length_cons] at hl
        apply List.mem_append_right
        refine List.mem_map.mpr ⟨(p.length,x,p,q),?_,rfl⟩
        exact (mem_entryExits ..).mpr ⟨by omega,rfl,hp,by omega,hq⟩

  · intro w hw v hv e
    obtain ⟨⟨m,x,p,q⟩,hf,rfl⟩ := List.mem_map.mp hv
    subst w
    obtain ⟨_,_,hp,_,_⟩ := (mem_entryExits n i m x p q).mp hf
    exact entry_band_drop_disjoint i x (p++A::q) p q
      ((mem_meanderWords ..).mp hw).2 rfl hp

section Weights
variable {R : Type u} [Lean.Grind.Semiring R]

theorem lsum_filter_mark {X : Type v} (f : X → R) (p : X → Prop) [DecidablePred p]
    (xs : List X) :
    lsum f (xs.filter (fun x => decide (p x))) =
      lsum (fun x => f x * markProp (p x)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change lsum f ((x::xs).filter _) = f x * markProp (p x) +
      lsum (fun y => f y * markProp (p y)) xs
    by_cases h : p x
    · rw [markProp_true h, mul_one]
      simp [h, lsum, ih]
    · rw [markProp_false h, mul_zero]
      simp [h, add0local, ih]
where
  add0local (a : R) : 0+a=a := by rw [Lean.Grind.Semiring.add_comm, add_zero]

noncomputable def acceptingCoeff (wt : Letter → R) (n : Nat) (s : State) : R :=
  coefficient wt (fun q => markProp (accepts q)) n s

theorem acceptingCoeff_sum (wt : Letter → R) (n : Nat) (s : State) :
    acceptingCoeff wt n s = lsum (wordWeight wt) (acceptedWords n s) := by
  unfold acceptingCoeff
  rw [coefficient_is_word_sum]
  classical
  exact (lsum_filter_mark (wordWeight wt) (fun w => accepts (iter s w)) (words n)).symm

theorem acceptingCoeff_dead (wt : Letter → R) (n : Nat) :
    acceptingCoeff wt n none = 0 := by
  rw [acceptingCoeff, coefficient_is_word_sum]
  apply lsum_eq_zero
  intro w _
  rw [iter_dead]
  exact (show wordWeight wt w * markProp False = 0 by
    rw [markProp_false not_false, mul_zero])

noncomputable def lowCoeff (wt : Letter → R) (n : Nat) (l : Low) : R :=
  acceptingCoeff wt n (some (.low l))

noncomputable def entryCoeff (wt : Letter → R) (n : Nat) (i : Phase) : R :=
  acceptingCoeff wt n (some (.high i 5))

theorem loCoeff_zero (wt : Letter → R) (l : Low) :
    lowCoeff wt 0 l = markProp (lowDeficits l (lowHeight l)) := rfl

theorem entryCoeff_zero (wt : Letter → R) (i : Phase) :
    entryCoeff wt 0 i = meanderCoeff wt 5 0 i := by
  rw [meanderCoeff_zero]
  exact markProp_congr (terminal_exact i 5 (by omega)).symm

/-- E = M_5 + R_5 D X, with D the first exit from the high band. -/
theorem entryCoeff_succ (wt : Letter → R) (n : Nat) (i : Phase) (hi : legal i 5) :
    entryCoeff wt (n+1) i =
      meanderCoeff wt 5 (n+1) i +
      lsum (fun m => lsum (fun x => returnCoeff wt 5 m i x *
        (wt A * lowCoeff wt (n-m) (exitLow x))) highPhases) (List.range (n+1)) := by
  rw [entryCoeff, acceptingCoeff_sum, ←lsum_perm (wordWeight wt) (entryFactors_perm n i hi),
      lsum_append, lsum_map]
  simp only [meanderCoeff, entryExits, lsum_sigmaList, assembleExit,
    wordWeight_append, wordWeight, returnCoeff, lowCoeff, acceptingCoeff_sum,
    lsum_mul_left, lsum_mul_right, mul_assoc]

/-- One low step is either dead, still low, or the exact five-height entry. -/
theorem lowCoeff_succ (wt : Letter → R) (n : Nat) (l : Low) :
    lowCoeff wt (n+1) l =
      lsum (fun k => wt k * match lowestStep l k with
        | none => 0
        | some (.low l') => lowCoeff wt n l'
        | some (.high p _) => entryCoeff wt n p) alphabet := by
  simp only [lowCoeff, acceptingCoeff, coefficient, transition, Option.bind_some, step]
  apply lsum_congr_mem
  intro k hk
  cases e : lowestStep l k with
  | none =>
    have hz := acceptingCoeff_dead wt n
    simp only [acceptingCoeff] at hz
    simp [hz]
  | some s =>
    cases s with
    | low l' => rfl
    | high p h =>
      obtain ⟨rfl,_⟩ := step_into_high_exact l k p h e
      rfl

/-- The two remaining blocks are jointly unique coefficient by coefficient.
Only legal height-five entries matter, and every real entry is legal. -/
theorem boundaryCoeff_unique (wt : Letter → R) (X : Nat → Low → R)
    (E : Nat → Phase → R)
    (hx0 : ∀ l, X 0 l = markProp (lowDeficits l (lowHeight l)))
    (he0 : ∀ i, legal i 5 → E 0 i = meanderCoeff wt 5 0 i)
    (hxs : ∀ n l, X (n+1) l =
      lsum (fun k => wt k * match lowestStep l k with
        | none => 0
        | some (.low l') => X n l'
        | some (.high p _) => E n p) alphabet)
    (hes : ∀ n i, legal i 5 → E (n+1) i =
      meanderCoeff wt 5 (n+1) i +
      lsum (fun m => lsum (fun x => returnCoeff wt 5 m i x *
        (wt A * X (n-m) (exitLow x))) highPhases) (List.range (n+1))) :
    ∀ n, (∀ l, X n l = lowCoeff wt n l) ∧
         (∀ i, legal i 5 → E n i = entryCoeff wt n i) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero =>
      exact ⟨fun l => (hx0 l).trans (loCoeff_zero wt l).symm,
        fun i hi => (he0 i hi).trans (entryCoeff_zero wt i).symm⟩
    | succ n =>
      constructor
      · intro l
        rw [hxs, lowCoeff_succ]
        apply lsum_congr_mem
        intro k _
        cases e : lowestStep l k with
        | none => rfl
        | some s =>
          cases s with
          | low l' => exact congrArg (fun y => wt k * y) ((ih n (by omega)).1 l')
          | high i h =>
            have hh := (step_into_high_exact l k i h e).2
            exact congrArg (fun y => wt k * y) ((ih n (by omega)).2 i hh)
      · intro i hi
        rw [hes _ _ hi, entryCoeff_succ _ _ _ hi]
        congr 1
        apply lsum_congr_mem
        intro m _
        apply lsum_congr_mem
        intro x _
        rw [(ih (n-m) (by omega)).1 (exitLow x)]

theorem sourceCoeff_eq_lowCoeff (wt : Letter → R) (n : Nat) :
    sourceCoeff wt n = lowCoeff wt n .s0 := sourceCoeff_eq_transfer wt n

end Weights

#print axioms entryFactors_perm
#print axioms entryCoeff_zero
#print axioms entryCoeff_succ
#print axioms lowCoeff_succ
#print axioms boundaryCoeff_unique
#print axioms sourceCoeff_eq_lowCoeff
end WalkQuarticBoundaryGF


/-! One exact coefficient certificate interface for the complete source series. -/
namespace WalkQuarticTransferSystem
open WalkQuarticWord WalkQuarticPhases WalkQuarticRecognize WalkQuarticCounting
open WalkQuarticFirstReturn WalkQuarticBandReturn WalkQuarticFirstReturnGF
open WalkQuarticMeander WalkQuarticMeanderGF WalkQuarticPopulation WalkQuarticBoundary
open WalkQuarticBoundaryGF Letter Lean.Grind.Semiring

variable {R : Type u} [Lean.Grind.Semiring R]

/-- All four blocks of the exact decomposed generating function, indexed
by ordinary t-coefficients, not finite coefficient prefixes. -/
structure TransferSolution (wt : Letter → R) where
  r : Nat → Nat → Phase → Phase → R
  m : Nat → Nat → Phase → R
  e : Nat → Phase → R
  x : Nat → Low → R
  r0 : ∀ b i j, r b 0 i j = markProp (i=j)
  r1 : ∀ b i j, r b 1 i j = 0
  rs : ∀ b n i j, r b (n+2) i j =
      lsum (fun d => lsum (fun k => lsum (fun p =>
        wt k * (r (b+1) d (upPhase b i k) p *
          (wt A * r b (n-d) (advanceA p) j))) highPhases) upLetters)
        (List.range (n+1))
  m0 : ∀ b i, m b 0 i = markProp (terminal i b)
  m1 : ∀ b i, m b 1 i =
        lsum (fun k => wt k * m (b+1) 0 (upPhase b i k)) upLetters
  ms : ∀ b n i, m b (n+2) i =
      lsum (fun k => wt k * m (b+1) (n+1) (upPhase b i k)) upLetters +
      lsum (fun d => lsum (fun k => lsum (fun p =>
        wt k * (r (b+1) d (upPhase b i k) p *
          (wt A * m b (n-d) (advanceA p)))) highPhases) upLetters)
        (List.range (n+1))
  e0 : ∀ i, legal i 5 → e 0 i = m 5 0 i
  es : ∀ n i, legal i 5 → e (n+1) i =
      m 5 (n+1) i +
      lsum (fun d => lsum (fun p => r 5 d i p *
        (wt A * x (n-d) (exitLow p))) highPhases) (List.range (n+1))
  x0 : ∀ l, x 0 l = markProp (lowDeficits l (lowHeight l))
  xs : ∀ n l, x (n+1) l =
      lsum (fun k => wt k * match lowestStep l k with
        | none => 0
        | some (.low l') => x n l'
        | some (.high i _) => e n i) alphabet

noncomputable def actualTransfer (wt : Letter → R) : TransferSolution wt where
  r := returnCoeff wt
  m := meanderCoeff wt
  e := entryCoeff wt
  x := lowCoeff wt
  r0 := returnCoeff_zero wt
  r1 := returnCoeff_one wt
  rs := returnCoeff_succ_succ wt
  m0 := meanderCoeff_zero wt
  m1 := meanderCoeff_one wt
  ms := meanderCoeff_succ_succ wt
  e0 := fun i _ => entryCoeff_zero wt i
  es := entryCoeff_succ wt
  x0 := loCoeff_zero wt
  xs := lowCoeff_succ wt

theorem solution_return_eq (wt : Letter → R) (S : TransferSolution wt) :
    S.r = returnCoeff wt := by
  funext b n i j
  exact returnCoeff_unique wt S.r S.r0 S.r1 S.rs n b i j

theorem solution_meander_eq (wt : Letter → R) (S : TransferSolution wt) :
    S.m = meanderCoeff wt := by
  funext b n i
  apply meanderCoeff_unique wt S.m S.m0 S.m1 _ n b i
  have H := S.ms
  rw [solution_return_eq wt S] at H
  exact H

theorem solution_boundary_eq (wt : Letter → R) (S : TransferSolution wt) :
    ∀ n, (∀ l, S.x n l=lowCoeff wt n l) ∧
         (∀ i, legal i 5 → S.e n i=entryCoeff wt n i) := by
  apply boundaryCoeff_unique wt S.x S.e S.x0 _ S.xs _
  · have H := S.e0
    rw [solution_meander_eq wt S] at H
    exact H
  · have H := S.es
    rw [solution_meander_eq wt S, solution_return_eq wt S] at H
    exact H

/-- For every length, the source coefficient equals the initial low block
of any solution of the exact transfer. No guessed coefficients are premises. -/
theorem sourceCoeff_eq_solution (wt : Letter → R) (S : TransferSolution wt) (n : Nat) :
    sourceCoeff wt n = S.x n .s0 := by
  exact (sourceCoeff_eq_lowCoeff wt n).trans ((solution_boundary_eq wt S n).1 .s0).symm

#print axioms actualTransfer
#print axioms solution_return_eq
#print axioms solution_meander_eq
#print axioms solution_boundary_eq
#print axioms sourceCoeff_eq_solution
end WalkQuarticTransferSystem

/-!
Arithmetic-only certificate for the exact de Panafieu–Wallner §6.2 quartic.
The formal series meaning and seven-phase counting transfer are not theorems
in this module. No Mathlib or new axiom is used.
-/
namespace WalkQuarticArithmetic

abbrev Poly := List Int

def rawAdd : Poly → Poly → Poly
  | [], bs => bs
  | as, [] => as
  | a :: as, b :: bs => (a+b) :: rawAdd as bs

def rawMul : Poly → Poly → Poly
  | [], _ => []
  | a :: as, bs => rawAdd (bs.map (a * ·)) (0 :: rawMul as bs)

def norm (p : Poly) : Poly :=
  (p.reverse.dropWhile (· == 0)).reverse

def pAdd (a b : Poly) : Poly := norm (rawAdd a b)
def pMul (a b : Poly) : Poly := norm (rawMul a b)
def pPow (a : Poly) : Nat → Poly
  | 0 => [1]
  | k+1 => pMul a (pPow a k)

structure Quad where
  a : Poly
  b : Poly
  c : Poly
  d : Poly
  deriving DecidableEq

def bqAdd (x y : Quad) : Quad :=
  ⟨pAdd x.a y.a, pAdd x.b y.b, pAdd x.c y.c, pAdd x.d y.d⟩

def D1 : Poly := [1,0,-4]
def D2 : Poly := [1,0,-8]
def D3 : Poly := [1,0,-12,0,32]

def bqMul (x y : Quad) : Quad :=
  ⟨pAdd (pAdd (pMul x.a y.a) (pMul D1 (pMul x.b y.b)))
       (pAdd (pMul D2 (pMul x.c y.c)) (pMul D3 (pMul x.d y.d))),
    pAdd (pAdd (pMul x.a y.b) (pMul x.b y.a))
       (pMul D2 (pAdd (pMul x.c y.d) (pMul x.d y.c))),
    pAdd (pAdd (pMul x.a y.c) (pMul x.c y.a))
       (pMul D1 (pAdd (pMul x.b y.d) (pMul x.d y.b))),
    pAdd (pAdd (pMul x.a y.d) (pMul x.d y.a))
       (pAdd (pMul x.b y.c) (pMul x.c y.b))⟩

def constant (a : Poly) : Quad := ⟨a, [], [], []⟩

def horner (a : Quad) (n : Quad) (d c : Poly) (j : Nat) : Quad :=
  bqAdd (bqMul a n) (constant (pMul c (pPow d j)))

def den : Poly := [0, 0, 0, 0, -8, 24, 56, -152, -144, 224, 192]
def numer : Quad := ⟨[0, 0, 1, -1, -23, 44, 71, -210, 84, 240, -304, -160, 192], [2, -2, -33, 25, 167, -74, -245, -10, -92, 32, 160, 96], [0, 0, -1, 1, 11, -16, -35, 58, 16, -40, 48], [-2, 2, 25, -17, -83, 22, 73, 34, 16, 24]⟩
def c4 : Poly := [0, 0, 0, 0, 0, 0, 0, 0, 4, -24, -44, 448, 136, -3728, -120, 18208, 2484, -56216, -23004, 105952, 82624, -99968, -136832, 4608, 83968, 49152, 9216]
def c3 : Poly := [0, 0, 0, 0, 0, 0, 2, -8, -66, 318, 572, -3928, -1588, 24132, -3110, -87024, 35238, 199982, -127032, -315424, 286448, 399296, -407808, -472064, 277504, 402944, 2048, -122880, -36864]
def c2 : Poly := [-1, 2, 42, -74, -775, 1143, 8286, -9420, -56875, 42707, 261575, -86979, -807387, -75318, 1591536, 810509, -1708162, -1591734, 458477, 633356, 332364, 1602176, 1138360, -1559232, -1849024, 34304, 403840, -150016, -4096, 190464, 73728]
def c1 : Poly := [2, -4, -70, 148, 1006, -2356, -7564, 21360, 30760, -123824, -58286, 492616, 6930, -1400744, 52564, 2799150, 536136, -3465494, -1894224, 1721750, 1629810, 614406, 1171032, 251072, -1984304, -1576608, 396288, 566272, -6912, 77824, 40960, -135168, -73728]
def c0 : Poly := [-1, 2, 28, -74, -271, 1157, 564, -10264, 8649, 59127, -74013, -239645, 248181, 697650, -355798, -1379731, 6256, 1624262, 573455, -811202, -588678, -389454, -171788, 771500, 1257532, 286712, -705692, -583264, -186048, 65152, 318720, 304128, 160768, 86016, 36864]
def step1 : Quad := ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -12, 84, 336, -3660, 216, 55944, -67332, -450144, 816276, 2226852, -5065560, -7304748, 19923984, 16339200, -54403188, -24215400, 110014032, 21129024, -175030080, -11180928, 225084672, 26032128, -215841792, -70932480, 119894016, 75841536, -16367616, -23887872, -5308416], [0, 0, 0, 0, 0, 0, 0, 0, 8, -56, -172, 1876, 896, -27916, 7376, 246992, -120476, -1460888, 661604, 6090676, -1566328, -18053564, -667352, 36529384, 14307916, -44026408, -37028464, 15779968, 35841536, 29049472, 10064384, -26429440, -41817088, -14325760, 14602240, 16220160, 6193152, 884736], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4, 28, 64, -820, 72, 10568, -9068, -80288, 95724, 407052, -527096, -1474900, 1792592, 3944944, -3899228, -7730456, 5268160, 10482912, -4139456, -8709888, 2418688, 3750912, -2880512, -1816576, 2211840, 1990656, 442368], [0, 0, 0, 0, 0, 0, 0, 0, -8, 56, 140, -1652, -400, 21756, -8016, -171936, 86428, 917976, -362036, -3480852, 499048, 9394348, 1719736, -17217656, -9520812, 18738568, 19175168, -6918304, -16995968, -6321408, 2014208, 3435520, 3798016, 3115008, 1327104, 221184]⟩
def step2 : Quad := ⟨[0, 0, 0, 0, 0, 0, 0, 0, -32, 256, 1120, -13312, -11264, 316640, -93568, -4592864, 3725184, 45742272, -47493088, -334264480, 360609056, 1868452288, -1820792608, -8185428384, 6200156288, 28319559616, -13196636160, -76585726816, 10796447072, 156953461216, 29098305056, -229317941120, -113555272032, 210512842240, 160805391872, -85129301504, -50212377856, 7115543552, -154001687552, -105323585536, 198664093696, 210377031680, -57248022528, -131001614336, -16393764864, 19052363776, -11653087232, -7958691840, 7927234560, 6681526272, 1358954496], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, -1280, -64, 39808, -89600, -501824, 1898112, 3023808, -19860480, -4185024, 129744000, -73201472, -581500160, 666997184, 1900021760, -3174873280, -4818883200, 10178450880, 10267511232, -23167016256, -19458011392, 36658639232, 31106945920, -36346896896, -34291160576, 15784611840, 13590251520, 2665975808, 20424220672, 5850021888, -29696425984, -21114126336, 10538582016, 15335948288, 2046296064, -3878682624, -2095054848, -339738624], [0, 0, 0, 0, 0, 0, 0, 0, -32, 256, 992, -12288, -7552, 269536, -116736, -3606112, 3223808, 33170112, -35767776, -224119840, 241918112, 1157255872, -1085623072, -4659513120, 3208675840, 14646910912, -5417970304, -35227271136, 623758432, 61659372256, 21710090912, -70036322432, -54319540320, 34186534400, 55685635328, 22458154496, 574162432, -28259477504, -54181040128, -22403186688, 33845747712, 39772028928, 8793292800, -6990987264, -5426249728, -4352114688, -4048551936, -1925185536, -339738624], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -128, 1280, -448, -34688, 86400, 375872, -1547136, -1877184, 14216448, 1101760, -83545600, 45082176, 349015552, -327287232, -1124897408, 1311559104, 3015638400, -3517540800, -7033360960, 6364982848, 13959668352, -6746961280, -21663731712, 1064012288, 23284835328, 7737987072, -14423814144, -9933193216, 3218931712, 4069818368, 28442624, -252051456, 644087808, 452984832, 84934656]⟩
def step3 : Quad := ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -256, 2816, 2816, -136448, 259840, 2865920, -9854976, -33155072, 173664512, 207321344, -1927682560, -252929024, 14953418240, -8087343616, -85577104384, 89841232640, 374845571328, -559046864128, -1299994813440, 2464707062272, 3722811101440, -8258506452224, -9296409045248, 21544862541568, 21232910893824, -43562893646592, -44263103544576, 65811802406656, 78740056718848, -67582781689856, -107399668280064, 35251010250240, 96039699128320, 5412986271744, -35410193285120, -3614204600320, -21174062579712, -39062921183232, 18213781372928, 56145188880384, 13464893915136, -25908355792896, -15830370746368, -94604623872, 974328430592, 1603977347072, 2834728747008, 740479205376, -1003814387712, -695784701952, -130459631616], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -768, 5888, 35328, -363264, -574720, 10080256, 1845504, -169432064, 75708928, 1954475008, -1454945536, -16579700992, 14043488512, 107884978176, -87564413184, -552173005056, 370927485696, 2248413350656, -1024426328320, -7273619110912, 1377145142528, 18409344598528, 1982431913984, -35221497326336, -15210249614848, 47405866421760, 38766889739264, -36907815403520, -54401314393344, 1213630706176, 34949588910080, 26314888820736, 13263020101632, -10231490404352, -39889600151552, -28187744174080, 18405292965888, 35750455410688, 11621542395904, -10364257828864, -11578859585536, -5835453366272, -1592082300928, 1459391299584, 2542452867072, 1632557334528, 510966890496, 65229815808], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -256, 2816, 1792, -125184, 264960, 2387712, -8788480, -24522240, 140660480, 124970240, -1427895296, 109037568, 10147677696, -7185617408, -53223588864, 64207497984, 213807198464, -353972966656, -682400665600, 1413617086976, 1815729704192, -4313813629184, -4277521190656, 10204270284032, 9287404697856, -18412524947200, -18070816932608, 23927215845120, 28602534385152, -19177624446976, -31757880476416, 4346418542080, 17514338464768, 5281943097344, 7022114295808, 3588080410624, -17646927036416, -17797498798080, 7195389526016, 16058591346688, 2923616796672, -4912011280384, -1838800699392, 443168063488, -236822986752, -357254037504, 85161148416, 141331267584, 32614907904], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -768, 5888, 31232, -326400, -486144, 8489472, 1952512, -136297472, 48935936, 1507783680, -979789056, -12213989632, 9306860800, 75312378880, -56112987392, -362359131392, 227366747904, 1378029554432, -597984451840, -4143973007360, 787195174656, 9719497542656, 797638491648, -17213731837696, -6375288245248, 21574097413632, 14783979089920, -16430279828480, -18076404745472, 3754720623104, 8990348274688, 3459279458304, 5335996899328, 1989241708544, -9326157922304, -9066445930496, 2339736977408, 6785066991616, 2406815105024, -856572297216, -845756235776, -572314877952, -608207634432, -398626652160, -127741722624, -16307453952]⟩
def step4 : Quad := ⟨[], [], [], []⟩

set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem check1 : horner (constant c4) numer den c3 1 = step1 := by decide
theorem check2 : horner step1 numer den c2 2 = step2 := by decide
theorem check3 : horner step2 numer den c1 3 = step3 := by decide
theorem check4 : horner step3 numer den c0 4 = step4 := by decide

theorem maple_quartic_cleared_denominator :
    horner (horner (horner (horner (constant c4) numer den c3 1)
      numer den c2 2) numer den c1 3) numer den c0 4 = ⟨[],[],[],[]⟩ := by
  rw [check1, check2, check3, check4]
  rfl

#print axioms maple_quartic_cleared_denominator
end WalkQuarticArithmetic

namespace WalkQuarticSolutionCertificate
open WalkQuarticArithmetic WalkQuarticWord WalkQuarticPhases WalkQuarticRecognize
open WalkQuarticCounting WalkQuarticPopulation WalkQuarticFirstReturnGF
open WalkQuarticBandReturn WalkQuarticBoundary
open Letter

def qzero : Quad := ⟨[],[],[],[]⟩
def qmul (x y : Quad) : Quad :=
  if x=qzero ∨ y=qzero then qzero else bqMul x y
def qsum (l : List Quad) : Quad := l.foldr bqAdd qzero
def degreeOne : Quad := constant [0,1]
def degreeTwo : Quad := constant [0,0,1]
def residueNext (b : Fin 6) : Fin 6 := ⟨(b.val+1)%6, Nat.mod_lt _ (by decide)⟩

def phaseMark : Phase → Nat → Bool
  | .p2,h => h%2 == 0
  | .p3,h => h%3 == 0
  | .q1,_ => false
  | .q0,h => h%3 != 1
  | .m2,_ => true
  | .m1,_ => false
  | .m0,_ => true

theorem phaseMark_spec (p : Phase) (h : Nat) : phaseMark p h = true ↔ terminal p h := by
  cases p <;> simp [phaseMark, terminal]

def lowMark : Low → Bool
  | .s0 | .s2 | .s3 | .s6 | .s8 | .s9 => true
  | _ => false

theorem lowMark_spec (l : Low) :
    lowMark l = true ↔ lowDeficits l (lowHeight l) := by
  cases l <;> simp [lowMark,lowDeficits,lowHeight]

theorem upPhase_period (p : Phase) (k : Letter) (b : Nat) :
    upPhase (b+6) p k = upPhase b p k := by
  have h2 : (b+6)%2=b%2 := Nat.add_mul_mod_self_left b 2 3
  have h3 : (b+6)%3=b%3 := Nat.add_mul_mod_self_left b 3 2
  cases k <;> cases p <;> simp [upPhase, advanceB, advanceC, h2, h3]

def denAll : Poly := [0, 0, 0, 0, 0, 0, 0, 0, 0, -256, 768, 1792, -4864, -4608, 7168, 6144]

def scaledR (b : Fin 6) (i j : Phase) : Quad :=
  match b.val, i, j with
  | 0, .p2, .p2 => ⟨[0, 0, 0, 0, 0, 0, 0, -128, 384, 896, -2432, -2304, 3584, 3072], [0, 0, 0, 0, 0, 0, 0, 128, -384, -896, 2432, 2304, -3584, -3072], [], []⟩
  | 0, .p2, .m0 => ⟨[0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], [0, 0, 0, 0, 0, 0, 0, -128, 384, 896, -2432, -2304, 3584, 3072], [0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], []⟩
  | 0, .p3, .p3 => ⟨[0, 0, 0, 0, 0, 0, 0, -128, 384, 896, -2432, -2304, 3584, 3072], [0, 0, 0, 0, 0, 0, 0, 128, -384, -896, 2432, 2304, -3584, -3072], [], []⟩
  | 0, .p3, .q0 => ⟨[0, 0, 0, 0, 0, 0, 0, 128, -384, -896, 2432, 2304, -3584, -3072], [0, 0, 0, 0, 0, 0, 0, -128, 384, 640, -1664, -1536, 1792, 1536], [], []⟩
  | 0, .p3, .m0 => ⟨[0, 0, 0, 0, 0, 0, 0, -64, 192, 448, -1216, -1152, 1792, 1536], [0, 0, 0, 0, 0, 0, 0, 0, 0, 256, -768, -768, 1792, 1536], [0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], []⟩
  | 0, .q1, .q1 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, -256, 768, 1792, -4864, -4608, 7168, 6144], [], [], []⟩
  | 0, .q1, .q0 => ⟨[0, 0, 0, 0, 0, 0, 0, -128, 384, 1152, -3200, -4096, 8448, 7680, -7168, -6144], [0, 0, 0, 0, 0, 0, 0, 128, -384, -896, 2432, 2304, -3584, -3072], [], []⟩
  | 0, .q1, .m1 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -256, 768, 1792, -4864, -4608, 7168, 6144], [], [], []⟩
  | 0, .q1, .m0 => ⟨[0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1408, -2560, -3328, 4864, 4608, -7168, -6144], [0, 0, 0, 0, 0, 0, 0, -128, 384, 896, -2432, -2304, 3584, 3072], [0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], []⟩
  | 0, .q0, .q0 => ⟨[0, 0, 0, 0, 0, 0, 0, -128, 384, 896, -2432, -2304, 3584, 3072], [0, 0, 0, 0, 0, 0, 0, 128, -384, -896, 2432, 2304, -3584, -3072], [], []⟩
  | 0, .q0, .m0 => ⟨[0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], [0, 0, 0, 0, 0, 0, 0, -128, 384, 896, -2432, -2304, 3584, 3072], [0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], []⟩
  | 0, .m2, .m2 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, -256, 768, 1792, -4864, -4608, 7168, 6144], [], [], []⟩
  | 0, .m2, .m0 => ⟨[0, 0, 0, 0, 0, 0, 0, -64, 192, 704, -1984, -2944, 6656, 6144, -7168, -6144], [], [0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], []⟩
  | 0, .m1, .m1 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, -256, 768, 1792, -4864, -4608, 7168, 6144], [], [], []⟩
  | 0, .m1, .m0 => ⟨[0, 0, 0, 0, 0, 0, 0, -64, 192, 704, -1984, -2944, 6656, 6144, -7168, -6144], [], [0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], []⟩
  | 0, .m0, .m0 => ⟨[0, 0, 0, 0, 0, 0, 0, -64, 192, 448, -1216, -1152, 1792, 1536], [], [0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], []⟩
  | 1, .p2, .p2 => ⟨[0, 0, 0, 0, 0, 0, 0, -128, 384, 896, -2432, -2304, 3584, 3072], [0, 0, 0, 0, 0, 0, 0, 128, -384, -896, 2432, 2304, -3584, -3072], [], []⟩
  | 1, .p2, .m0 => ⟨[0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], [0, 0, 0, 0, 0, 0, 0, -128, 384, 896, -2432, -2304, 3584, 3072], [0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], []⟩
  | 1, .p3, .p3 => ⟨[0, 0, 0, 0, 0, 0, 0, -128, 384, 896, -2432, -2304, 3584, 3072], [0, 0, 0, 0, 0, 0, 0, 128, -384, -896, 2432, 2304, -3584, -3072], [], []⟩
  | 1, .p3, .q0 => ⟨[0, 0, 0, 0, 0, 0, 0, 128, -384, -896, 2432, 2304, -3584, -3072], [0, 0, 0, 0, 0, 0, 0, -128, 384, 640, -1664, -1536, 1792, 1536], [], []⟩
  | 1, .p3, .m0 => ⟨[0, 0, 0, 0, 0, 0, 0, -64, 192, 448, -1216, -1152, 1792, 1536], [0, 0, 0, 0, 0, 0, 0, 0, 0, 256, -768, -768, 1792, 1536], [0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], []⟩
  | 1, .q1, .q1 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, -256, 768, 1792, -4864, -4608, 7168, 6144], [], [], []⟩
  | 1, .q1, .q0 => ⟨[0, 0, 0, 0, 0, 0, 0, -128, 384, 1152, -3200, -4096, 8448, 7680, -7168, -6144], [0, 0, 0, 0, 0, 0, 0, 128, -384, -896, 2432, 2304, -3584, -3072], [], []⟩
  | 1, .q1, .m1 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -256, 768, 1792, -4864, -4608, 7168, 6144], [], [], []⟩
  | 1, .q1, .m0 => ⟨[0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1408, -2560, -3328, 4864, 4608, -7168, -6144], [0, 0, 0, 0, 0, 0, 0, -128, 384, 896, -2432, -2304, 3584, 3072], [0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], []⟩
  | 1, .q0, .q0 => ⟨[0, 0, 0, 0, 0, 0, 0, -128, 384, 896, -2432, -2304, 3584, 3072], [0, 0, 0, 0, 0, 0, 0, 128, -384, -896, 2432, 2304, -3584, -3072], [], []⟩
  | 1, .q0, .m0 => ⟨[0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], [0, 0, 0, 0, 0, 0, 0, -128, 384, 896, -2432, -2304, 3584, 3072], [0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], []⟩
  | 1, .m2, .m2 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, -256, 768, 1792, -4864, -4608, 7168, 6144], [], [], []⟩
  | 1, .m2, .m0 => ⟨[0, 0, 0, 0, 0, 0, 0, -64, 192, 704, -1984, -2944, 6656, 6144, -7168, -6144], [], [0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], []⟩
  | 1, .m1, .m1 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, -256, 768, 1792, -4864, -4608, 7168, 6144], [], [], []⟩
  | 1, .m1, .m0 => ⟨[0, 0, 0, 0, 0, 0, 0, -64, 192, 704, -1984, -2944, 6656, 6144, -7168, -6144], [], [0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], []⟩
  | 1, .m0, .m0 => ⟨[0, 0, 0, 0, 0, 0, 0, -64, 192, 448, -1216, -1152, 1792, 1536], [], [0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], []⟩
  | 2, .p2, .p2 => ⟨[0, 0, 0, 0, 0, 0, 0, -128, 384, 896, -2432, -2304, 3584, 3072], [0, 0, 0, 0, 0, 0, 0, 128, -384, -896, 2432, 2304, -3584, -3072], [], []⟩
  | 2, .p2, .m0 => ⟨[0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], [0, 0, 0, 0, 0, 0, 0, -128, 384, 896, -2432, -2304, 3584, 3072], [0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], []⟩
  | 2, .p3, .p3 => ⟨[0, 0, 0, 0, 0, 0, 0, -128, 384, 896, -2432, -2304, 3584, 3072], [0, 0, 0, 0, 0, 0, 0, 128, -384, -896, 2432, 2304, -3584, -3072], [], []⟩
  | 2, .p3, .q0 => ⟨[0, 0, 0, 0, 0, 0, 0, 128, -384, -896, 2432, 2304, -3584, -3072], [0, 0, 0, 0, 0, 0, 0, -128, 384, 640, -1664, -1536, 1792, 1536], [], []⟩
  | 2, .p3, .m0 => ⟨[0, 0, 0, 0, 0, 0, 0, -64, 192, 448, -1216, -1152, 1792, 1536], [0, 0, 0, 0, 0, 0, 0, 0, 0, 256, -768, -768, 1792, 1536], [0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], []⟩
  | 2, .q1, .q1 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, -256, 768, 1792, -4864, -4608, 7168, 6144], [], [], []⟩
  | 2, .q1, .q0 => ⟨[0, 0, 0, 0, 0, 0, 0, -128, 384, 1152, -3200, -4096, 8448, 7680, -7168, -6144], [0, 0, 0, 0, 0, 0, 0, 128, -384, -896, 2432, 2304, -3584, -3072], [], []⟩
  | 2, .q1, .m1 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -256, 768, 1792, -4864, -4608, 7168, 6144], [], [], []⟩
  | 2, .q1, .m0 => ⟨[0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1408, -2560, -3328, 4864, 4608, -7168, -6144], [0, 0, 0, 0, 0, 0, 0, -128, 384, 896, -2432, -2304, 3584, 3072], [0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], []⟩
  | 2, .q0, .q0 => ⟨[0, 0, 0, 0, 0, 0, 0, -128, 384, 896, -2432, -2304, 3584, 3072], [0, 0, 0, 0, 0, 0, 0, 128, -384, -896, 2432, 2304, -3584, -3072], [], []⟩
  | 2, .q0, .m0 => ⟨[0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], [0, 0, 0, 0, 0, 0, 0, -128, 384, 896, -2432, -2304, 3584, 3072], [0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], []⟩
  | 2, .m2, .m2 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, -256, 768, 1792, -4864, -4608, 7168, 6144], [], [], []⟩
  | 2, .m2, .m0 => ⟨[0, 0, 0, 0, 0, 0, 0, -64, 192, 704, -1984, -2944, 6656, 6144, -7168, -6144], [], [0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], []⟩
  | 2, .m1, .m1 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, -256, 768, 1792, -4864, -4608, 7168, 6144], [], [], []⟩
  | 2, .m1, .m0 => ⟨[0, 0, 0, 0, 0, 0, 0, -64, 192, 704, -1984, -2944, 6656, 6144, -7168, -6144], [], [0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], []⟩
  | 2, .m0, .m0 => ⟨[0, 0, 0, 0, 0, 0, 0, -64, 192, 448, -1216, -1152, 1792, 1536], [], [0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], []⟩
  | 3, .p2, .p2 => ⟨[0, 0, 0, 0, 0, 0, 0, -128, 384, 896, -2432, -2304, 3584, 3072], [0, 0, 0, 0, 0, 0, 0, 128, -384, -896, 2432, 2304, -3584, -3072], [], []⟩
  | 3, .p2, .m0 => ⟨[0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], [0, 0, 0, 0, 0, 0, 0, -128, 384, 896, -2432, -2304, 3584, 3072], [0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], []⟩
  | 3, .p3, .p3 => ⟨[0, 0, 0, 0, 0, 0, 0, -128, 384, 896, -2432, -2304, 3584, 3072], [0, 0, 0, 0, 0, 0, 0, 128, -384, -896, 2432, 2304, -3584, -3072], [], []⟩
  | 3, .p3, .q0 => ⟨[0, 0, 0, 0, 0, 0, 0, 128, -384, -896, 2432, 2304, -3584, -3072], [0, 0, 0, 0, 0, 0, 0, -128, 384, 640, -1664, -1536, 1792, 1536], [], []⟩
  | 3, .p3, .m0 => ⟨[0, 0, 0, 0, 0, 0, 0, -64, 192, 448, -1216, -1152, 1792, 1536], [0, 0, 0, 0, 0, 0, 0, 0, 0, 256, -768, -768, 1792, 1536], [0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], []⟩
  | 3, .q1, .q1 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, -256, 768, 1792, -4864, -4608, 7168, 6144], [], [], []⟩
  | 3, .q1, .q0 => ⟨[0, 0, 0, 0, 0, 0, 0, -128, 384, 1152, -3200, -4096, 8448, 7680, -7168, -6144], [0, 0, 0, 0, 0, 0, 0, 128, -384, -896, 2432, 2304, -3584, -3072], [], []⟩
  | 3, .q1, .m1 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -256, 768, 1792, -4864, -4608, 7168, 6144], [], [], []⟩
  | 3, .q1, .m0 => ⟨[0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1408, -2560, -3328, 4864, 4608, -7168, -6144], [0, 0, 0, 0, 0, 0, 0, -128, 384, 896, -2432, -2304, 3584, 3072], [0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], []⟩
  | 3, .q0, .q0 => ⟨[0, 0, 0, 0, 0, 0, 0, -128, 384, 896, -2432, -2304, 3584, 3072], [0, 0, 0, 0, 0, 0, 0, 128, -384, -896, 2432, 2304, -3584, -3072], [], []⟩
  | 3, .q0, .m0 => ⟨[0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], [0, 0, 0, 0, 0, 0, 0, -128, 384, 896, -2432, -2304, 3584, 3072], [0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], []⟩
  | 3, .m2, .m2 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, -256, 768, 1792, -4864, -4608, 7168, 6144], [], [], []⟩
  | 3, .m2, .m0 => ⟨[0, 0, 0, 0, 0, 0, 0, -64, 192, 704, -1984, -2944, 6656, 6144, -7168, -6144], [], [0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], []⟩
  | 3, .m1, .m1 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, -256, 768, 1792, -4864, -4608, 7168, 6144], [], [], []⟩
  | 3, .m1, .m0 => ⟨[0, 0, 0, 0, 0, 0, 0, -64, 192, 704, -1984, -2944, 6656, 6144, -7168, -6144], [], [0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], []⟩
  | 3, .m0, .m0 => ⟨[0, 0, 0, 0, 0, 0, 0, -64, 192, 448, -1216, -1152, 1792, 1536], [], [0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], []⟩
  | 4, .p2, .p2 => ⟨[0, 0, 0, 0, 0, 0, 0, -128, 384, 896, -2432, -2304, 3584, 3072], [0, 0, 0, 0, 0, 0, 0, 128, -384, -896, 2432, 2304, -3584, -3072], [], []⟩
  | 4, .p2, .m0 => ⟨[0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], [0, 0, 0, 0, 0, 0, 0, -128, 384, 896, -2432, -2304, 3584, 3072], [0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], []⟩
  | 4, .p3, .p3 => ⟨[0, 0, 0, 0, 0, 0, 0, -128, 384, 896, -2432, -2304, 3584, 3072], [0, 0, 0, 0, 0, 0, 0, 128, -384, -896, 2432, 2304, -3584, -3072], [], []⟩
  | 4, .p3, .q0 => ⟨[0, 0, 0, 0, 0, 0, 0, 128, -384, -896, 2432, 2304, -3584, -3072], [0, 0, 0, 0, 0, 0, 0, -128, 384, 640, -1664, -1536, 1792, 1536], [], []⟩
  | 4, .p3, .m0 => ⟨[0, 0, 0, 0, 0, 0, 0, -64, 192, 448, -1216, -1152, 1792, 1536], [0, 0, 0, 0, 0, 0, 0, 0, 0, 256, -768, -768, 1792, 1536], [0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], []⟩
  | 4, .q1, .q1 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, -256, 768, 1792, -4864, -4608, 7168, 6144], [], [], []⟩
  | 4, .q1, .q0 => ⟨[0, 0, 0, 0, 0, 0, 0, -128, 384, 1152, -3200, -4096, 8448, 7680, -7168, -6144], [0, 0, 0, 0, 0, 0, 0, 128, -384, -896, 2432, 2304, -3584, -3072], [], []⟩
  | 4, .q1, .m1 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -256, 768, 1792, -4864, -4608, 7168, 6144], [], [], []⟩
  | 4, .q1, .m0 => ⟨[0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1408, -2560, -3328, 4864, 4608, -7168, -6144], [0, 0, 0, 0, 0, 0, 0, -128, 384, 896, -2432, -2304, 3584, 3072], [0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], []⟩
  | 4, .q0, .q0 => ⟨[0, 0, 0, 0, 0, 0, 0, -128, 384, 896, -2432, -2304, 3584, 3072], [0, 0, 0, 0, 0, 0, 0, 128, -384, -896, 2432, 2304, -3584, -3072], [], []⟩
  | 4, .q0, .m0 => ⟨[0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], [0, 0, 0, 0, 0, 0, 0, -128, 384, 896, -2432, -2304, 3584, 3072], [0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], []⟩
  | 4, .m2, .m2 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, -256, 768, 1792, -4864, -4608, 7168, 6144], [], [], []⟩
  | 4, .m2, .m0 => ⟨[0, 0, 0, 0, 0, 0, 0, -64, 192, 704, -1984, -2944, 6656, 6144, -7168, -6144], [], [0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], []⟩
  | 4, .m1, .m1 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, -256, 768, 1792, -4864, -4608, 7168, 6144], [], [], []⟩
  | 4, .m1, .m0 => ⟨[0, 0, 0, 0, 0, 0, 0, -64, 192, 704, -1984, -2944, 6656, 6144, -7168, -6144], [], [0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], []⟩
  | 4, .m0, .m0 => ⟨[0, 0, 0, 0, 0, 0, 0, -64, 192, 448, -1216, -1152, 1792, 1536], [], [0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], []⟩
  | 5, .p2, .p2 => ⟨[0, 0, 0, 0, 0, 0, 0, -128, 384, 896, -2432, -2304, 3584, 3072], [0, 0, 0, 0, 0, 0, 0, 128, -384, -896, 2432, 2304, -3584, -3072], [], []⟩
  | 5, .p2, .m0 => ⟨[0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], [0, 0, 0, 0, 0, 0, 0, -128, 384, 896, -2432, -2304, 3584, 3072], [0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], []⟩
  | 5, .p3, .p3 => ⟨[0, 0, 0, 0, 0, 0, 0, -128, 384, 896, -2432, -2304, 3584, 3072], [0, 0, 0, 0, 0, 0, 0, 128, -384, -896, 2432, 2304, -3584, -3072], [], []⟩
  | 5, .p3, .q0 => ⟨[0, 0, 0, 0, 0, 0, 0, 128, -384, -896, 2432, 2304, -3584, -3072], [0, 0, 0, 0, 0, 0, 0, -128, 384, 640, -1664, -1536, 1792, 1536], [], []⟩
  | 5, .p3, .m0 => ⟨[0, 0, 0, 0, 0, 0, 0, -64, 192, 448, -1216, -1152, 1792, 1536], [0, 0, 0, 0, 0, 0, 0, 0, 0, 256, -768, -768, 1792, 1536], [0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], []⟩
  | 5, .q1, .q1 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, -256, 768, 1792, -4864, -4608, 7168, 6144], [], [], []⟩
  | 5, .q1, .q0 => ⟨[0, 0, 0, 0, 0, 0, 0, -128, 384, 1152, -3200, -4096, 8448, 7680, -7168, -6144], [0, 0, 0, 0, 0, 0, 0, 128, -384, -896, 2432, 2304, -3584, -3072], [], []⟩
  | 5, .q1, .m1 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -256, 768, 1792, -4864, -4608, 7168, 6144], [], [], []⟩
  | 5, .q1, .m0 => ⟨[0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1408, -2560, -3328, 4864, 4608, -7168, -6144], [0, 0, 0, 0, 0, 0, 0, -128, 384, 896, -2432, -2304, 3584, 3072], [0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], []⟩
  | 5, .q0, .q0 => ⟨[0, 0, 0, 0, 0, 0, 0, -128, 384, 896, -2432, -2304, 3584, 3072], [0, 0, 0, 0, 0, 0, 0, 128, -384, -896, 2432, 2304, -3584, -3072], [], []⟩
  | 5, .q0, .m0 => ⟨[0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], [0, 0, 0, 0, 0, 0, 0, -128, 384, 896, -2432, -2304, 3584, 3072], [0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], []⟩
  | 5, .m2, .m2 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, -256, 768, 1792, -4864, -4608, 7168, 6144], [], [], []⟩
  | 5, .m2, .m0 => ⟨[0, 0, 0, 0, 0, 0, 0, -64, 192, 704, -1984, -2944, 6656, 6144, -7168, -6144], [], [0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], []⟩
  | 5, .m1, .m1 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, -256, 768, 1792, -4864, -4608, 7168, 6144], [], [], []⟩
  | 5, .m1, .m0 => ⟨[0, 0, 0, 0, 0, 0, 0, -64, 192, 704, -1984, -2944, 6656, 6144, -7168, -6144], [], [0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], []⟩
  | 5, .m0, .m0 => ⟨[0, 0, 0, 0, 0, 0, 0, -64, 192, 448, -1216, -1152, 1792, 1536], [], [0, 0, 0, 0, 0, 0, 0, 64, -192, -448, 1216, 1152, -1792, -1536], []⟩
  | _, _, _ => qzero

def scaledM (b : Fin 6) (i : Phase) : Quad :=
  match b.val, i with
  | 0, .p2 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, -64, 0, 832, 128, -3456, -1280, 4608, 3072], [0, 0, 0, 0, 0, 0, 0, 0, 128, -256, -768, 512, 1664, 768], [0, 0, 0, 0, 0, 0, 0, 0, -64, 0, 448, 128, -768, -512], []⟩
  | 0, .p3 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, -64, 128, 704, -1920, -512, 5248, -6912, 0, 7168, 6144], [0, 0, 0, 0, 0, 0, 0, 0, 128, -384, -384, 1536, -768, -2432, 3840, 1024, -3072], [0, 0, 0, 0, 0, 0, 0, 0, -64, 0, 448, 128, -768, -512], []⟩
  | 0, .q1 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 64, -256, -320, 1664, -640, -3328, 7168, 6144, -14336, -12288], [0, 0, 0, 0, 0, 0, 0, 0, 0, 256, -640, -1536, 2944, 2048, -1536], [0, 0, 0, 0, 0, 0, 0, 0, -64, 0, 448, 128, -768, -512], []⟩
  | 0, .q0 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 64, -512, 448, 2944, -3968, -4352, 4608, 3072], [0, 0, 0, 0, 0, 0, 0, 0, 0, 256, -640, -1536, 2944, 2048, -1536], [0, 0, 0, 0, 0, 0, 0, 0, -64, 0, 448, 128, -768, -512], []⟩
  | 0, .m2 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 64, -256, -192, 896, -512, 2304, 2560, -7168, -6144], [], [0, 0, 0, 0, 0, 0, 0, 0, -64, 0, 448, 128, -768, -512], []⟩
  | 0, .m1 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 64, 0, -1216, -128, 6144, 2048, -9216, -6144], [], [0, 0, 0, 0, 0, 0, 0, 0, -64, 0, 448, 128, -768, -512], []⟩
  | 0, .m0 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 64, -256, -448, 1664, 1280, -2560, -2048], [], [0, 0, 0, 0, 0, 0, 0, 0, -64, 0, 448, 128, -768, -512], []⟩
  | 1, .p2 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 64, -256, -448, 1664, 1280, -2560, -2048], [0, 0, 0, 0, 0, 0, 0, 0, 0, 256, -512, -1536, 1024, 3328, 1536], [0, 0, 0, 0, 0, 0, 0, 0, -64, 0, 448, 128, -768, -512], []⟩
  | 1, .p3 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 64, -256, -320, 1664, -768, -1152, 3840, -7168, 1024, 6144], [0, 0, 0, 0, 0, 0, 0, 0, 0, 256, -640, -1024, 2304, -1408, -256, 2048, 3072], [0, 0, 0, 0, 0, 0, 0, 0, -64, 0, 448, 128, -768, -512], []⟩
  | 1, .q1 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 64, -128, -1088, 2304, 2944, -9472, 5120, 12288, -14336, -12288], [0, 0, 0, 0, 0, 0, 0, 0, 0, 128, -128, -1152, 128, 2560, 1536], [0, 0, 0, 0, 0, 0, 0, 0, -64, 0, 448, 128, -768, -512], []⟩
  | 1, .q0 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 64, -128, -1088, 1792, 4480, -5888, -4608, 3072], [0, 0, 0, 0, 0, 0, 0, 0, 0, 128, -128, -1152, 128, 2560, 1536], [0, 0, 0, 0, 0, 0, 0, 0, -64, 0, 448, 128, -768, -512], []⟩
  | 1, .m2 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 64, -256, -192, 896, -512, 2304, 2560, -7168, -6144], [], [0, 0, 0, 0, 0, 0, 0, 0, -64, 0, 448, 128, -768, -512], []⟩
  | 1, .m1 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 64, 0, -1216, -128, 6144, 2048, -9216, -6144], [], [0, 0, 0, 0, 0, 0, 0, 0, -64, 0, 448, 128, -768, -512], []⟩
  | 1, .m0 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 64, -256, -448, 1664, 1280, -2560, -2048], [], [0, 0, 0, 0, 0, 0, 0, 0, -64, 0, 448, 128, -768, -512], []⟩
  | 2, .p2 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, -64, 0, 832, 128, -3456, -1280, 4608, 3072], [0, 0, 0, 0, 0, 0, 0, 0, 128, -256, -768, 512, 1664, 768], [0, 0, 0, 0, 0, 0, 0, 0, -64, 0, 448, 128, -768, -512], []⟩
  | 2, .p3 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 64, -128, -832, 1280, 2560, -3712, -768, 4096, -1024, -6144], [0, 0, 0, 0, 0, 0, 0, 0, 0, 128, -128, -896, -256, 2688, -3328, 2048, 3072], [0, 0, 0, 0, 0, 0, 0, 0, -64, 0, 448, 128, -768, -512], []⟩
  | 2, .q1 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, -64, 384, -448, -1792, 3712, 0, -1536, 7168, -8192, -12288], [0, 0, 0, 0, 0, 0, 0, 0, 128, -384, -512, 1664, -384, -512, 1536], [0, 0, 0, 0, 0, 0, 0, 0, -64, 0, 448, 128, -768, -512], []⟩
  | 2, .q0 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, -64, 128, 576, -1280, -1408, 3840, 512, -3072], [0, 0, 0, 0, 0, 0, 0, 0, 128, -384, -512, 1664, -384, -512, 1536], [0, 0, 0, 0, 0, 0, 0, 0, -64, 0, 448, 128, -768, -512], []⟩
  | 2, .m2 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 64, -256, -192, 896, -512, 2304, 2560, -7168, -6144], [], [0, 0, 0, 0, 0, 0, 0, 0, -64, 0, 448, 128, -768, -512], []⟩
  | 2, .m1 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 64, 0, -1216, -128, 6144, 2048, -9216, -6144], [], [0, 0, 0, 0, 0, 0, 0, 0, -64, 0, 448, 128, -768, -512], []⟩
  | 2, .m0 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 64, -256, -448, 1664, 1280, -2560, -2048], [], [0, 0, 0, 0, 0, 0, 0, 0, -64, 0, 448, 128, -768, -512], []⟩
  | 3, .p2 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 64, -256, -448, 1664, 1280, -2560, -2048], [0, 0, 0, 0, 0, 0, 0, 0, 0, 256, -512, -1536, 1024, 3328, 1536], [0, 0, 0, 0, 0, 0, 0, 0, -64, 0, 448, 128, -768, -512], []⟩
  | 3, .p3 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, -64, 128, 704, -1920, -512, 5248, -6912, 0, 7168, 6144], [0, 0, 0, 0, 0, 0, 0, 0, 128, -384, -384, 1536, -768, -2432, 3840, 1024, -3072], [0, 0, 0, 0, 0, 0, 0, 0, -64, 0, 448, 128, -768, -512], []⟩
  | 3, .q1 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 64, -256, -320, 1664, -640, -3328, 7168, 6144, -14336, -12288], [0, 0, 0, 0, 0, 0, 0, 0, 0, 256, -640, -1536, 2944, 2048, -1536], [0, 0, 0, 0, 0, 0, 0, 0, -64, 0, 448, 128, -768, -512], []⟩
  | 3, .q0 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 64, -512, 448, 2944, -3968, -4352, 4608, 3072], [0, 0, 0, 0, 0, 0, 0, 0, 0, 256, -640, -1536, 2944, 2048, -1536], [0, 0, 0, 0, 0, 0, 0, 0, -64, 0, 448, 128, -768, -512], []⟩
  | 3, .m2 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 64, -256, -192, 896, -512, 2304, 2560, -7168, -6144], [], [0, 0, 0, 0, 0, 0, 0, 0, -64, 0, 448, 128, -768, -512], []⟩
  | 3, .m1 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 64, 0, -1216, -128, 6144, 2048, -9216, -6144], [], [0, 0, 0, 0, 0, 0, 0, 0, -64, 0, 448, 128, -768, -512], []⟩
  | 3, .m0 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 64, -256, -448, 1664, 1280, -2560, -2048], [], [0, 0, 0, 0, 0, 0, 0, 0, -64, 0, 448, 128, -768, -512], []⟩
  | 4, .p2 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, -64, 0, 832, 128, -3456, -1280, 4608, 3072], [0, 0, 0, 0, 0, 0, 0, 0, 128, -256, -768, 512, 1664, 768], [0, 0, 0, 0, 0, 0, 0, 0, -64, 0, 448, 128, -768, -512], []⟩
  | 4, .p3 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 64, -256, -320, 1664, -768, -1152, 3840, -7168, 1024, 6144], [0, 0, 0, 0, 0, 0, 0, 0, 0, 256, -640, -1024, 2304, -1408, -256, 2048, 3072], [0, 0, 0, 0, 0, 0, 0, 0, -64, 0, 448, 128, -768, -512], []⟩
  | 4, .q1 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 64, -128, -1088, 2304, 2944, -9472, 5120, 12288, -14336, -12288], [0, 0, 0, 0, 0, 0, 0, 0, 0, 128, -128, -1152, 128, 2560, 1536], [0, 0, 0, 0, 0, 0, 0, 0, -64, 0, 448, 128, -768, -512], []⟩
  | 4, .q0 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 64, -128, -1088, 1792, 4480, -5888, -4608, 3072], [0, 0, 0, 0, 0, 0, 0, 0, 0, 128, -128, -1152, 128, 2560, 1536], [0, 0, 0, 0, 0, 0, 0, 0, -64, 0, 448, 128, -768, -512], []⟩
  | 4, .m2 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 64, -256, -192, 896, -512, 2304, 2560, -7168, -6144], [], [0, 0, 0, 0, 0, 0, 0, 0, -64, 0, 448, 128, -768, -512], []⟩
  | 4, .m1 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 64, 0, -1216, -128, 6144, 2048, -9216, -6144], [], [0, 0, 0, 0, 0, 0, 0, 0, -64, 0, 448, 128, -768, -512], []⟩
  | 4, .m0 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 64, -256, -448, 1664, 1280, -2560, -2048], [], [0, 0, 0, 0, 0, 0, 0, 0, -64, 0, 448, 128, -768, -512], []⟩
  | 5, .p2 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 64, -256, -448, 1664, 1280, -2560, -2048], [0, 0, 0, 0, 0, 0, 0, 0, 0, 256, -512, -1536, 1024, 3328, 1536], [0, 0, 0, 0, 0, 0, 0, 0, -64, 0, 448, 128, -768, -512], []⟩
  | 5, .p3 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 64, -128, -832, 1280, 2560, -3712, -768, 4096, -1024, -6144], [0, 0, 0, 0, 0, 0, 0, 0, 0, 128, -128, -896, -256, 2688, -3328, 2048, 3072], [0, 0, 0, 0, 0, 0, 0, 0, -64, 0, 448, 128, -768, -512], []⟩
  | 5, .q1 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, -64, 384, -448, -1792, 3712, 0, -1536, 7168, -8192, -12288], [0, 0, 0, 0, 0, 0, 0, 0, 128, -384, -512, 1664, -384, -512, 1536], [0, 0, 0, 0, 0, 0, 0, 0, -64, 0, 448, 128, -768, -512], []⟩
  | 5, .q0 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, -64, 128, 576, -1280, -1408, 3840, 512, -3072], [0, 0, 0, 0, 0, 0, 0, 0, 128, -384, -512, 1664, -384, -512, 1536], [0, 0, 0, 0, 0, 0, 0, 0, -64, 0, 448, 128, -768, -512], []⟩
  | 5, .m2 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 64, -256, -192, 896, -512, 2304, 2560, -7168, -6144], [], [0, 0, 0, 0, 0, 0, 0, 0, -64, 0, 448, 128, -768, -512], []⟩
  | 5, .m1 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 64, 0, -1216, -128, 6144, 2048, -9216, -6144], [], [0, 0, 0, 0, 0, 0, 0, 0, -64, 0, 448, 128, -768, -512], []⟩
  | 5, .m0 => ⟨[0, 0, 0, 0, 0, 0, 0, 0, 64, -256, -448, 1664, 1280, -2560, -2048], [], [0, 0, 0, 0, 0, 0, 0, 0, -64, 0, 448, 128, -768, -512], []⟩
  | _, _ => qzero

def scaledE : Phase → Quad
  | .p2 => ⟨[0, 0, 1, -1, -23, 28, 75, -158, 944, 48, -6484, 376, 12496, 1856, -6592, -640, 768], [2, -2, -49, 41, 455, -298, -1873, 746, 2712, 344, 972, -1736, -4272, -64, 1792, 384], [0, 0, -1, 1, 19, -24, -135, 198, 428, -696, -500, 1016, -192, -480, 576], [-2, 2, 41, -33, -307, 182, 1037, -346, -1564, 16, 748, 216, 192, 288]⟩
  | .p3 => ⟨[0, 0, 1, -1, -23, 28, 75, -670, 2480, 4528, -20180, -11912, 52176, 14656, -47552, -10880, 13056], [2, -2, -49, 41, 455, -298, -1873, 1258, 1176, -3112, 11852, 4152, -25264, -7488, 10496, 6528], [0, 0, -1, 1, 19, -24, -135, 198, 428, -696, -500, 1016, -192, -480, 576], [-2, 2, 41, -33, -307, 182, 1037, -346, -1564, 16, 748, 216, 192, 288]⟩
  | .q1 => ⟨[0, 0, 1, -1, -25, 30, 245, -338, -1274, 1900, 3040, -3040, -4136, -7248, 12416, 20288, -18304, -17408, 6144], [2, -2, -53, 45, 545, -372, -2683, 1274, 6126, -1060, -4448, -2448, -936, 1648, -4608, 832, 5120, 3072], [0, 0, -1, 1, 21, -26, -169, 242, 606, -980, -688, 1408, -936, 432, 1536, -960, 1152], [-2, 2, 45, -37, -381, 240, 1455, -546, -2106, -196, -400, 1104, 2136, 1392, 384, 576]⟩
  | .q0 => ⟨[0, 0, 1, -1, -23, 28, 203, -286, -976, 1200, 3500, -2696, -7984, 3904, 5696, -640, 768], [2, -2, -49, 41, 455, -298, -2001, 874, 4376, -808, -4916, -456, 3152, 1216, 256, 384], [0, 0, -1, 1, 19, -24, -135, 198, 428, -696, -500, 1016, -192, -480, 576], [-2, 2, 41, -33, -307, 182, 1037, -346, -1564, 16, 748, 216, 192, 288]⟩
  | .m2 => ⟨[0, 0, 1, -1, -25, 30, 245, -338, -1146, 1516, 2528, -2272, -2984, 48, 6528, 320, -13184, -5120, 6144], [2, -2, -53, 45, 545, -372, -2683, 1274, 5998, -932, -3168, -2704, -4648, 240, -2048, 2368, 5120, 3072], [0, 0, -1, 1, 21, -26, -169, 242, 606, -980, -688, 1408, -936, 432, 1536, -960, 1152], [-2, 2, 45, -37, -381, 240, 1455, -546, -2106, -196, -400, 1104, 2136, 1392, 384, 576]⟩
  | .m1 => ⟨[0, 0, 1, -1, -23, 28, 203, -286, -848, 1328, 812, -2824, 4816, 3904, -10688, -6784, 768], [2, -2, -49, 41, 455, -298, -2001, 874, 4248, -680, -3764, -584, 592, -320, 256, 384], [0, 0, -1, 1, 19, -24, -135, 198, 428, -696, -500, 1016, -192, -480, 576], [-2, 2, 41, -33, -307, 182, 1037, -346, -1564, 16, 748, 216, 192, 288]⟩
  | .m0 => ⟨[0, 0, 1, -1, -23, 28, 203, -286, -848, 1072, 1580, -1032, -48, -704, -3520, -640, 768], [2, -2, -49, 41, 455, -298, -2001, 874, 4248, -680, -3764, -584, 592, -320, 256, 384], [0, 0, -1, 1, 19, -24, -135, 198, 428, -696, -500, 1016, -192, -480, 576], [-2, 2, 41, -33, -307, 182, 1037, -346, -1564, 16, 748, 216, 192, 288]⟩

def scaledX : Low → Quad
  | .s0 => ⟨[0, 0, 0, 0, 0, 0, 0, 32, -32, -736, 1408, 2272, -6720, 2688, 7680, -9728, -5120, 6144], [0, 0, 0, 0, 0, 64, -64, -1056, 800, 5344, -2368, -7840, -320, -2944, 1024, 5120, 3072], [0, 0, 0, 0, 0, 0, 0, -32, 32, 352, -512, -1120, 1856, 512, -1280, 1536], [0, 0, 0, 0, 0, -64, 64, 800, -544, -2656, 704, 2336, 1088, 512, 768]⟩
  | .s1 => ⟨[0, 0, 0, 2, -2, -42, 52, 330, -476, -1300, 1240, 3544, 592, -6080, -3008, 1152], [0, 4, -4, -90, 74, 746, -464, -2806, 1052, 4876, -376, -3752, -752, 1920, 576], [0, 0, 0, -2, 2, 34, -44, -210, 316, 540, -904, -376, 944, -448, -320, 384], [0, -4, 4, 74, -58, -482, 264, 1342, -332, -1508, -184, 392, -16, 128, 192]⟩
  | .s2 => ⟨[0, 0, 0, 2, -2, -42, 52, 330, -476, -1428, 1880, 3416, -2608, -2752, -448, -1920], [0, 4, -4, -90, 74, 746, -464, -2806, 1052, 4748, -248, -2600, -880, -640, -960], [0, 0, 0, -2, 2, 34, -44, -210, 316, 540, -904, -376, 944, -448, -320, 384], [0, -4, 4, 74, -58, -482, 264, 1342, -332, -1508, -184, 392, -16, 128, 192]⟩
  | .s3 => ⟨[0, 0, 0, 2, -2, -42, 52, 202, -348, 236, 1240, -3752, -3632, 7488, 5696, -1920], [0, 4, -4, -90, 74, 746, -464, -2678, 924, 3340, 648, 728, -1136, -2176, -960], [0, 0, 0, -2, 2, 34, -44, -210, 316, 540, -904, -376, 944, -448, -320, 384], [0, -4, 4, 74, -58, -482, 264, 1342, -332, -1508, -184, 392, -16, 128, 192]⟩
  | .s4 => ⟨[0, 0, 0, 2, -2, -42, 52, 202, -860, 1900, 4312, -14760, -9008, 29632, 12096, -22400, -5120, 6144], [0, 4, -4, -90, 74, 746, -464, -2678, 1436, 1932, -2424, 9176, 2192, -14848, -5312, 5120, 3072], [0, 0, 0, -2, 2, 34, -44, -210, 316, 540, -904, -376, 944, -448, -320, 384], [0, -4, 4, 74, -58, -482, 264, 1342, -332, -1508, -184, 392, -16, 128, 192]⟩
  | .s5 => ⟨[0, 0, 0, 0, 0, 0, 16, -16, -240, 320, 240, -928, 3648, 256, -7936, -2560, 3072], [0, 0, 0, 0, 32, -32, -528, 400, 2672, -1184, -3920, -160, -1472, 512, 2560, 1536], [0, 0, 0, 0, 0, 0, -16, 16, 176, -256, -560, 928, 256, -640, 768], [0, 0, 0, 0, -32, 32, 400, -272, -1328, 352, 1168, 544, 256, 384]⟩
  | .s6 => ⟨[0, 0, 0, 0, 4, -4, -76, 96, 524, -1032, -1536, 4320, 1952, -6208, -1024, 1280, -1536], [0, 0, 8, -8, -164, 132, 1196, -696, -3748, 1112, 4928, 288, -1824, -320, -512, -768], [0, 0, 0, 0, -4, 4, 60, -80, -316, 488, 624, -1088, -64, 640, -768], [0, 0, -8, 8, 132, -100, -732, 360, 1620, -216, -1104, -448, -256, -384]⟩
  | .s7 => ⟨[0, 0, 0, 0, 4, -4, -76, 96, 396, -648, -640, 1888, -352, -2624, 2048, 1280, -1536], [0, 0, 8, -8, -164, 132, 1196, -696, -3620, 984, 3520, 1184, 1504, -576, -2048, -768], [0, 0, 0, 0, -4, 4, 60, -80, -316, 488, 624, -1088, -64, 640, -768], [0, 0, -8, 8, 132, -100, -732, 360, 1620, -216, -1104, -448, -256, -384]⟩
  | .s8 => ⟨[0, 0, 0, 0, 4, -4, -76, 96, 396, -1416, 1920, 5600, -14560, -6464, 19456, 6400, -7680], [0, 0, 8, -8, -164, 132, 1196, -696, -3620, 1496, 2240, -1504, 7264, 960, -5632, -3840], [0, 0, 0, 0, -4, 4, 60, -80, -316, 488, 624, -1088, -64, 640, -768], [0, 0, -8, 8, 132, -100, -732, 360, 1620, -216, -1104, -448, -256, -384]⟩
  | .s9 => ⟨[0, 0, 0, 0, 0, 8, -8, -136, 176, 424, -592, -144, 416, 640, -1408, -768], [0, 0, 0, 16, -16, -296, 232, 1864, -992, -4696, 912, 4528, 1312, -1792, -384], [0, 0, 0, 0, 0, -8, 8, 104, -144, -456, 720, 688, -1248, 128, 640, -768], [0, 0, 0, -16, 16, 232, -168, -1064, 448, 1912, -80, -1040, -352, -256, -384]⟩
  | .s10 => ⟨[0, 0, 0, 0, 0, 8, -8, -136, 176, 552, -1744, 1520, 6560, -11264, -8832, 13568, 5120, -6144], [0, 0, 0, 16, -16, -296, 232, 1864, -992, -4568, 1296, 1840, -480, 7296, 896, -5120, -3072], [0, 0, 0, 0, 0, -8, 8, 104, -144, -456, 720, 688, -1248, 128, 640, -768], [0, 0, 0, -16, 16, 232, -168, -1064, 448, 1912, -80, -1040, -352, -256, -384]⟩

def D : Quad := constant denAll
def Dsq : Quad := qmul D D

def retRHS (b : Fin 6) (i j : Phase) : Quad :=
  bqAdd (if i=j then Dsq else qzero)
    (qmul degreeTwo (qsum <| upLetters.flatMap fun k =>
      highPhases.map fun p => qmul
        (scaledR (residueNext b) (upPhase b.val i k) p)
        (scaledR b (advanceA p) j)))

def meanderRHS (b : Fin 6) (i : Phase) : Quad :=
  bqAdd (if phaseMark i b.val then Dsq else qzero) <|
    bqAdd (qmul (qmul degreeOne D) (qsum <|
      upLetters.map fun k => scaledM (residueNext b) (upPhase b.val i k)))
    (qmul degreeTwo (qsum <| upLetters.flatMap fun k =>
      highPhases.map fun p => qmul
        (scaledR (residueNext b) (upPhase b.val i k) p) (scaledM b (advanceA p))))

def entryRHS (i : Phase) : Quad :=
  bqAdd (qmul D (scaledM 5 i)) (qmul degreeOne (qsum <|
    highPhases.map fun p => qmul (scaledR 5 i p) (scaledX (exitLow p))))

def lowRHS (l : Low) : Quad :=
  bqAdd (if lowMark l then D else qzero) (qmul degreeOne (qsum <|
    alphabet.map fun k => match lowestStep l k with
      | none => qzero
      | some (.low l') => scaledX l'
      | some (.high p _) => scaledE p))

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem scaledReturn_eq (b : Fin 6) (i j : Phase) :
    qmul D (scaledR b i j) = retRHS b i j := by
  obtain ⟨b,hb⟩ := b
  have hc : b=0 ∨ b=1 ∨ b=2 ∨ b=3 ∨ b=4 ∨ b=5 := by omega
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl
  · change qmul D (scaledR 0 i j) = retRHS 0 i j
    cases i <;> cases j <;> decide
  · change qmul D (scaledR 1 i j) = retRHS 1 i j
    cases i <;> cases j <;> decide
  · change qmul D (scaledR 2 i j) = retRHS 2 i j
    cases i <;> cases j <;> decide
  · change qmul D (scaledR 3 i j) = retRHS 3 i j
    cases i <;> cases j <;> decide
  · change qmul D (scaledR 4 i j) = retRHS 4 i j
    cases i <;> cases j <;> decide
  · change qmul D (scaledR 5 i j) = retRHS 5 i j
    cases i <;> cases j <;> decide

theorem scaledMeander_eq (b : Fin 6) (i : Phase) :
    qmul D (scaledM b i) = meanderRHS b i := by
  obtain ⟨b,hb⟩ := b
  have hc : b=0 ∨ b=1 ∨ b=2 ∨ b=3 ∨ b=4 ∨ b=5 := by omega
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl
  · change qmul D (scaledM 0 i) = meanderRHS 0 i
    cases i <;> decide
  · change qmul D (scaledM 1 i) = meanderRHS 1 i
    cases i <;> decide
  · change qmul D (scaledM 2 i) = meanderRHS 2 i
    cases i <;> decide
  · change qmul D (scaledM 3 i) = meanderRHS 3 i
    cases i <;> decide
  · change qmul D (scaledM 4 i) = meanderRHS 4 i
    cases i <;> decide
  · change qmul D (scaledM 5 i) = meanderRHS 5 i
    cases i <;> decide

theorem scaledEntry_eq (i : Phase) : qmul D (scaledE i) = entryRHS i := by
  cases i <;> decide

theorem scaledLow_eq (l : Low) : scaledX l = lowRHS l := by
  cases l <;> decide

theorem scaledInitial_eq :
    qmul (constant den) (scaledX .s0) = qmul D numer := by decide

#print axioms scaledReturn_eq
#print axioms scaledMeander_eq
#print axioms scaledEntry_eq
#print axioms scaledLow_eq
#print axioms scaledInitial_eq
end WalkQuarticSolutionCertificate


namespace WalkQuarticSeries
open Lean.Grind

set_option linter.unusedSimpArgs false

structure Series where
  coeff : Nat → Rat

@[ext] theorem Series.ext {f g : Series} (h : ∀ n, f.coeff n = g.coeff n) : f=g := by
  cases f
  cases g
  congr
  exact funext h

def add (f g : Series) : Series := ⟨fun n => f.coeff n + g.coeff n⟩
def neg (f : Series) : Series := ⟨fun n => -f.coeff n⟩
def scalar (a : Rat) (f : Series) : Series := ⟨fun n => a*f.coeff n⟩
def delta (a : Rat) : Series := ⟨fun n => match n with | 0=>a | _+1=>0⟩
def tail (f : Series) : Series := ⟨fun n => f.coeff (n+1)⟩
def shift (f : Series) : Series := ⟨fun n => match n with | 0=>0 | k+1=>f.coeff k⟩

def cpoint : Nat → Series → Series → Rat
  | 0, f, g => f.coeff 0 * g.coeff 0
  | n+1, f, g => f.coeff 0 * g.coeff (n+1) + cpoint n (tail f) g

def mul (f g : Series) : Series := ⟨fun n => cpoint n f g⟩

theorem cpoint_add_left (n : Nat) (f g h : Series) :
    cpoint n (add f g) h = cpoint n f h + cpoint n g h := by
  induction n generalizing f g with
  | zero => simp only [cpoint, add]; grind
  | succ n ih =>
    have he : tail (add f g)=add (tail f) (tail g) := rfl
    simp only [cpoint, he, ih]
    change (f.coeff 0 + g.coeff 0) * h.coeff (n+1) + _ = _
    grind

theorem cpoint_scalar_left (n : Nat) (a : Rat) (f g : Series) :
    cpoint n (scalar a f) g = a*cpoint n f g := by
  induction n generalizing f with
  | zero => simp only [cpoint, scalar]; grind
  | succ n ih =>
    have he : tail (scalar a f)=scalar a (tail f) := rfl
    simp only [cpoint, he, ih]
    change (a * f.coeff 0) * g.coeff (n+1) + _ = _
    grind

theorem cpoint_tail_right (n : Nat) (f g : Series) :
    cpoint (n+1) f g = f.coeff (n+1) * g.coeff 0 + cpoint n f (tail g) := by
  induction n generalizing f g with
  | zero => simp only [cpoint, tail]; grind
  | succ n ih =>
    change f.coeff 0 * g.coeff (n+2) + cpoint (n+1) (tail f) g =
      f.coeff (n+2) * g.coeff 0 +
        (f.coeff 0 * g.coeff (n+2) + cpoint n (tail f) (tail g))
    rw [ih (tail f) g]
    change _ + (f.coeff (n+2) * g.coeff 0 + _) = _
    grind

theorem cpoint_comm (n : Nat) (f g : Series) : cpoint n f g = cpoint n g f := by
  induction n generalizing f g with
  | zero => simp only [cpoint]; grind
  | succ n ih =>
    rw [cpoint_tail_right n g f]
    change f.coeff 0 * g.coeff (n+1) + cpoint n (tail f) g = _
    rw [ih (tail f) g]
    grind

theorem tail_mul (f g : Series) :
    tail (mul f g) = add (scalar (f.coeff 0) (tail g)) (mul (tail f) g) := rfl

theorem cpoint_assoc (n : Nat) (f g h : Series) :
    cpoint n (mul f g) h = cpoint n f (mul g h) := by
  induction n generalizing f g h with
  | zero => simp only [cpoint, mul]; grind
  | succ n ih =>
    change ((mul f g).coeff 0) * h.coeff (n+1) + cpoint n (tail (mul f g)) h =
        f.coeff 0 * (mul g h).coeff (n+1) + cpoint n (tail f) (mul g h)
    rw [tail_mul, cpoint_add_left, cpoint_scalar_left, ih (tail f) g h]
    change (f.coeff 0*g.coeff 0) * h.coeff (n+1) + _ =
        f.coeff 0 * (g.coeff 0*h.coeff (n+1) + cpoint n (tail g) h) + _
    grind

theorem cpoint_delta_zero (n : Nat) (g : Series) : cpoint n (delta 0) g=0 := by
  induction n with
  | zero => simp [cpoint, delta]
  | succ n ih =>
    have he : tail (delta 0)=delta 0 := by ext j; cases j <;> rfl
    change (0:Rat) * g.coeff (n+1) + cpoint n (tail (delta 0)) g = 0
    simp [he, ih] <;> grind

theorem cpoint_delta (n : Nat) (a : Rat) (g : Series) :
    cpoint n (delta a) g = a*g.coeff n := by
  cases n with
  | zero => rfl
  | succ n =>
    have he : tail (delta a)=delta 0 := by ext j; cases j <;> rfl
    change a*g.coeff (n+1) + cpoint n (tail (delta a)) g = _
    simp [he, cpoint_delta_zero] <;> grind

def spow (a : Series) : Nat → Series
  | 0 => delta 1
  | n+1 => mul (spow a n) a

instance : Lean.Grind.CommRing Series where
  add := add
  mul := mul
  neg := neg
  sub := fun a b => add a (neg b)
  natCast := ⟨fun n => delta (n : Rat)⟩
  ofNat := fun n => ⟨delta (n : Rat)⟩
  intCast := ⟨fun n => delta (n : Rat)⟩
  nsmul := ⟨fun n f => scalar (n : Rat) f⟩
  zsmul := ⟨fun n f => scalar (n : Rat) f⟩
  npow := ⟨spow⟩
  add_zero := by
    intro a; apply Series.ext; intro n
    change a.coeff n + (delta 0).coeff n = a.coeff n
    cases n <;> simp [delta] <;> grind
  add_comm := by
    intro a b; apply Series.ext; intro n
    change a.coeff n + b.coeff n = b.coeff n + a.coeff n
    grind
  add_assoc := by
    intro a b c; apply Series.ext; intro n
    change (a.coeff n + b.coeff n) + c.coeff n = a.coeff n + (b.coeff n + c.coeff n)
    grind
  mul_comm := by intro a b; apply Series.ext; intro n; exact cpoint_comm n a b
  mul_assoc := by intro a b c; apply Series.ext; intro n; exact cpoint_assoc n a b c
  mul_one := by
    intro a; apply Series.ext; intro n
    change cpoint n a (delta 1)=a.coeff n
    rw [cpoint_comm, cpoint_delta]; simp
  one_mul := by
    intro a; apply Series.ext; intro n
    change cpoint n (delta 1) a=a.coeff n
    rw [cpoint_delta]; simp
  left_distrib := by
    intro a b c; apply Series.ext; intro n
    change cpoint n a (add b c) = cpoint n a b + cpoint n a c
    rw [cpoint_comm n a, cpoint_add_left, cpoint_comm n b a, cpoint_comm n c a]
  right_distrib := by intro a b c; apply Series.ext; intro n; exact cpoint_add_left n a b c
  zero_mul := by
    intro a; apply Series.ext; intro n
    change cpoint n (delta 0) a=(delta 0).coeff n
    rw [cpoint_delta_zero]; cases n <;> rfl
  mul_zero := by
    intro a; apply Series.ext; intro n
    change cpoint n a (delta 0)=(delta 0).coeff n
    rw [cpoint_comm, cpoint_delta_zero]; cases n <;> rfl
  pow_zero := by intro a; rfl
  pow_succ := by intros; rfl
  ofNat_succ := by
    intro a; apply Series.ext; intro n
    change (delta ((a+1 : Nat) : Rat)).coeff n = ((delta (a : Rat)).coeff n) + (delta 1).coeff n
    cases n <;> simp [delta] <;> grind
  ofNat_eq_natCast := by intros; rfl
  nsmul_eq_natCast_mul := by
    intro a f; apply Series.ext; intro n; exact (cpoint_delta n (a : Rat) f).symm
  neg_add_cancel := by
    intro a; apply Series.ext; intro n
    change -a.coeff n + a.coeff n = (delta 0).coeff n
    cases n <;> simp [delta] <;> grind
  sub_eq_add_neg := by intros; rfl
  neg_zsmul := by
    intro i f; apply Series.ext; intro n
    change ((-i : Int) : Rat) * f.coeff n = -((i : Rat) * f.coeff n)
    simp [Rat.intCast_neg] <;> grind
  zsmul_natCast_eq_nsmul := by
    intro n f; apply Series.ext; intro i
    change (((n : Int) : Rat) * f.coeff i) = (n : Rat) * f.coeff i
    rw [Rat.intCast_natCast]
  intCast_ofNat := by
    intro n; apply Series.ext; intro i
    change (delta (((OfNat.ofNat (α := Int) n) : Int) : Rat)).coeff i =
      (delta (n : Rat)).coeff i
    cases i with
    | zero =>
      change (((OfNat.ofNat (α := Int) n) : Int) : Rat) = (n : Rat)
      rw [Lean.Grind.Ring.intCast_ofNat, Lean.Grind.Semiring.ofNat_eq_natCast]
    | succ i => rfl
  intCast_neg := by
    intro i; apply Series.ext; intro n
    change (delta ((-i : Int) : Rat)).coeff n = -(delta (i : Rat)).coeff n
    cases n <;> simp [delta,Rat.intCast_neg]

#print axioms cpoint_comm
#print axioms cpoint_assoc
#print axioms instCommRingSeries

end WalkQuarticSeries

namespace WalkQuarticSeries
open Lean.Grind WalkQuarticCounting WalkQuarticPopulation

set_option linter.unusedSimpArgs false

theorem coeff_zero (n : Nat) : (0:Series).coeff n=0 := by
  cases n <;> rfl

theorem coeff_one_zero : (1:Series).coeff 0=1 := rfl
theorem coeff_one_succ (n : Nat) : (1:Series).coeff (n+1)=0 := rfl

theorem coeff_add (f g : Series) (n : Nat) :
    (f+g).coeff n = f.coeff n + g.coeff n := rfl

theorem coeff_sub (f g : Series) (n : Nat) :
    (f-g).coeff n = f.coeff n - g.coeff n := by
  change f.coeff n + -g.coeff n = f.coeff n - g.coeff n
  grind

theorem cpoint_congr (n : Nat) (f f' g g' : Series)
    (hf : ∀ k≤n, f.coeff k=f'.coeff k) (hg : ∀ k≤n, g.coeff k=g'.coeff k) :
    cpoint n f g = cpoint n f' g' := by
  induction n generalizing f f' g g' with
  | zero => simp only [cpoint,hf 0 (by omega),hg 0 (by omega)]
  | succ n ih =>
    simp only [cpoint,hf 0 (by omega),hg (n+1) (by omega)]
    congr 1
    apply ih
    · intro k hk; exact hf (k+1) (by omega)
    · intro k hk; exact hg k (by omega)

theorem coeff_mul_cauchy (f g : Series) (n : Nat) :
    (f*g).coeff n = lsum (fun k => f.coeff k*g.coeff (n-k)) (List.range (n+1)) := by
  change cpoint n f g = _
  induction n generalizing f with
  | zero =>
    change f.coeff 0 * g.coeff 0 = f.coeff 0 * g.coeff 0 + (0:Rat)
    grind
  | succ n ih =>
    rw [List.range_succ_eq_map]
    change f.coeff 0*g.coeff (n+1) + cpoint n (tail f) g =
        f.coeff 0*g.coeff (n+1) +
          lsum (fun k => f.coeff k*g.coeff (n+1-k)) ((List.range (n+1)).map Nat.succ)
    rw [lsum_map, ih]
    congr 1
    apply lsum_congr_mem
    intro k hk
    have h : n+1-Nat.succ k=n-k := by omega
    simp only [h, tail, Nat.succ_eq_add_one]

def T : Series := shift (delta 1)

theorem t_mul_shift (f : Series) : T*f=shift f := by
  apply Series.ext
  intro n
  cases n with
  | zero => change (0:Rat)*f.coeff 0=0; grind
  | succ n =>
    change (0:Rat)*f.coeff (n+1)+cpoint n (delta 1) f = f.coeff n
    rw [cpoint_delta]
    grind

def shiftN : Nat → Series → Series
  | 0,f=>f
  | k+1,f=>shift (shiftN k f)
def dropN : Nat → Series → Series
  | 0,f=>f
  | k+1,f=>dropN k (tail f)

theorem coeff_dropN (k : Nat) (f : Series) (n : Nat) :
    (dropN k f).coeff n=f.coeff (n+k) := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih => rw [dropN, ih]; rfl

theorem tpow_mul_shift (k : Nat) (f : Series) : T^k*f=shiftN k f := by
  induction k with
  | zero => simp only [Semiring.pow_zero, Semiring.one_mul, shiftN]
  | succ k ih =>
    rw [Semiring.pow_succ, CommSemiring.mul_comm (T^k) T, Semiring.mul_assoc, ih,
      t_mul_shift, shiftN]

theorem shift_inj (f g : Series) (h : shift f=shift g) : f=g := by
  apply Series.ext
  intro n
  exact congrArg (fun g : Series => g.coeff (n+1)) h

theorem shiftN_inj (k : Nat) (f g : Series) (h : shiftN k f=shiftN k g) : f=g := by
  induction k with
  | zero => exact h
  | succ k ih => exact ih (shift_inj _ _ h)

theorem shift_drop_factor (k : Nat) (f : Series)
    (hz : ∀ n<k, f.coeff n=0) : shiftN k (dropN k f)=f := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
    have hh : ∀ n<k, (tail f).coeff n=0 := by
      intro n hn; exact hz (n+1) (by omega)
    simp only [shiftN, dropN, ih (tail f) hh]
    apply Series.ext
    intro n
    cases n with
    | zero => exact (hz 0 (by omega)).symm
    | succ n => rfl

def reduceDividend (d f : Series) : Series :=
  add (tail f) (scalar (-(f.coeff 0 / d.coeff 0)) (tail d))

def unitQuotCoeff : Nat → Series → Series → Rat
  | 0,d,f => f.coeff 0 / d.coeff 0
  | n+1,d,f => unitQuotCoeff n d (reduceDividend d f)

def unitQuot (d f : Series) : Series := ⟨fun n => unitQuotCoeff n d f⟩

theorem unitQuot_mul (d f : Series) (hd : d.coeff 0≠0) :
    unitQuot d f*d=f := by
  apply Series.ext
  intro n
  induction n generalizing f with
  | zero =>
    change (f.coeff 0 / d.coeff 0)*d.coeff 0 = f.coeff 0
    exact Rat.div_mul_cancel hd
  | succ n ih =>
    change (f.coeff 0/d.coeff 0)*d.coeff (n+1) +
        cpoint n (unitQuot d (reduceDividend d f)) d = f.coeff (n+1)
    have H : cpoint n (unitQuot d (reduceDividend d f)) d =
        (reduceDividend d f).coeff n := ih _
    rw [H]
    change (f.coeff 0/d.coeff 0)*d.coeff (n+1) +
        (f.coeff (n+1) + -(f.coeff 0/d.coeff 0)*d.coeff (n+1)) = _
    grind

theorem unit_mul_cancel (d f g : Series) (hd : d.coeff 0≠0)
    (h : d*f=d*g) : f=g := by
  have H := unitQuot_mul d (1:Series) hd
  have eq := congrArg (fun x : Series => unitQuot d 1 *x) h
  simp only [←Semiring.mul_assoc, H, Semiring.one_mul] at eq
  exact eq

theorem regularQuot_exact (k : Nat) (d f : Series)
    (hdz : ∀ n<k,d.coeff n=0) (hfz : ∀ n<k,f.coeff n=0) (hd : d.coeff k≠0) :
    d * unitQuot (dropN k d) (dropN k f) = f := by
  let u := dropN k d
  let v := dropN k f
  have hu : u.coeff 0≠0 := by simpa [u,coeff_dropN] using hd
  have he : u * unitQuot u v = v := by
    rw [CommSemiring.mul_comm u,unitQuot_mul u v hu]
  have hd' : T^k*u=d := (tpow_mul_shift _ _).trans (shift_drop_factor _ _ hdz)
  have hf' : T^k*v=f := (tpow_mul_shift _ _).trans (shift_drop_factor _ _ hfz)
  change d*unitQuot u v=f
  rw [←hd',Semiring.mul_assoc,he,hf']

theorem regularDen_cancel (k : Nat) (d f g : Series)
    (hdz : ∀ n<k,d.coeff n=0) (hd : d.coeff k≠0) (h : d*f=d*g) : f=g := by
  let u := dropN k d
  have hu : u.coeff 0≠0 := by simpa [u,coeff_dropN] using hd
  have hd' : T^k*u=d := (tpow_mul_shift _ _).trans (shift_drop_factor _ _ hdz)
  rw [←hd'] at h
  rw [Semiring.mul_assoc, Semiring.mul_assoc, tpow_mul_shift, tpow_mul_shift] at h
  exact unit_mul_cancel u f g hu (shiftN_inj k _ _ h)


theorem coeff_lsum {X : Type u} (f : X → Series) (xs : List X) (n : Nat) :
    (lsum f xs).coeff n = lsum (fun x => (f x).coeff n) xs := by
  induction xs with
  | nil => exact coeff_zero n
  | cons x xs ih =>
    change (f x + lsum f xs).coeff n = _
    rw [coeff_add, ih]
    rfl

theorem coeff_T_mul_zero (f : Series) : (T*f).coeff 0=0 := by rw [t_mul_shift]; rfl

theorem coeff_T_mul_succ (f : Series) (n : Nat) :
    (T*f).coeff (n+1)=f.coeff n := by rw [t_mul_shift]; rfl

theorem coeff_TT_mul_zero (f : Series) : (T*T*f).coeff 0=0 := by
  rw [Semiring.mul_assoc, coeff_T_mul_zero]

theorem coeff_TT_mul_one (f : Series) : (T*T*f).coeff 1=0 := by
  rw [Semiring.mul_assoc, coeff_T_mul_succ, coeff_T_mul_zero]

theorem coeff_TT_mul_succ_succ (f : Series) (n : Nat) :
    (T*T*f).coeff (n+2)=f.coeff n := by
  rw [Semiring.mul_assoc, coeff_T_mul_succ, coeff_T_mul_succ]

#print axioms coeff_mul_cauchy
#print axioms unitQuot_mul
#print axioms regularQuot_exact
#print axioms regularDen_cancel
end WalkQuarticSeries

namespace WalkQuarticSeries
open Lean.Grind

def sqRootCoeff (u : Series) (n : Nat) : Rat :=
  match n with
  | 0 => 1
  | 1 => u.coeff 1 / 2
  | k+2 =>
    let prev : Series := ⟨fun m =>
      if h : m+1<k+2 then sqRootCoeff u (m+1) else 0⟩
    (u.coeff (k+2) - cpoint k prev prev) / 2
termination_by n
decreasing_by
  all_goals omega

def sqrtSeries (u : Series) : Series := ⟨sqRootCoeff u⟩

theorem sqrtSeries_coeff_zero (u : Series) : (sqrtSeries u).coeff 0=1 := by
  change sqRootCoeff u 0=1
  rw [sqRootCoeff]

theorem sqrtSeries_coeff_one (u : Series) : (sqrtSeries u).coeff 1=u.coeff 1/2 := by
  change sqRootCoeff u 1=u.coeff 1/2
  rw [sqRootCoeff]

theorem sqrtSeries_coeff_step (u : Series) (k : Nat) :
    (sqrtSeries u).coeff (k+2) =
      (u.coeff (k+2) - cpoint k (tail (sqrtSeries u)) (tail (sqrtSeries u))) / 2 := by
  change sqRootCoeff u (k+2) = _
  rw [sqRootCoeff]
  congr 1
  congr 1
  apply cpoint_congr
  · intro m hm
    have h : m+1<k+2 := by omega
    change (if _ : m+1<k+2 then sqRootCoeff u (m+1) else 0) = _
    simp only [h, dite_true, tail, sqrtSeries]
  · intro m hm
    have h : m+1<k+2 := by omega
    change (if _ : m+1<k+2 then sqRootCoeff u (m+1) else 0) = _
    simp only [h, dite_true, tail, sqrtSeries]

theorem sqrtSeries_sq (u : Series) (hu : u.coeff 0 = 1) :
    sqrtSeries u * sqrtSeries u = u := by
  apply Series.ext
  intro n
  cases n with
  | zero =>
    change (sqrtSeries u).coeff 0*(sqrtSeries u).coeff 0 = u.coeff 0
    rw [sqrtSeries_coeff_zero,hu]
    grind
  | succ n =>
    cases n with
    | zero =>
      change (sqrtSeries u).coeff 0*(sqrtSeries u).coeff 1 +
        (tail (sqrtSeries u)).coeff 0*(sqrtSeries u).coeff 0 = u.coeff 1
      change (sqrtSeries u).coeff 0*(sqrtSeries u).coeff 1 +
        (sqrtSeries u).coeff 1*(sqrtSeries u).coeff 0 = u.coeff 1
      rw [sqrtSeries_coeff_zero,sqrtSeries_coeff_one]
      grind
    | succ n =>
      let r := sqrtSeries u
      change r.coeff 0 * r.coeff (n+2)+cpoint (n+1) (tail r) r=u.coeff (n+2)
      rw [cpoint_tail_right]
      change r.coeff 0 * r.coeff (n+2) +
        (r.coeff (n+2)*r.coeff 0 + cpoint n (tail r) (tail r)) = u.coeff (n+2)
      have h0 : r.coeff 0 = 1 := sqrtSeries_coeff_zero u
      have hstep := sqrtSeries_coeff_step u n
      change r.coeff (n+2) = _ at hstep
      rw [h0,hstep]
      grind

#print axioms sqrtSeries_coeff_step
#print axioms sqrtSeries_sq
end WalkQuarticSeries

namespace WalkQuarticAlgebra
open WalkQuarticArithmetic Lean.Grind Lean.Grind.Ring
set_option linter.unusedSimpArgs false
attribute [local instance] Lean.Grind.Ring.intCast

variable {R : Type u} [Lean.Grind.CommRing R]

private theorem zero_add (a : R) : 0 + a = a := by rw [Semiring.add_comm, Semiring.add_zero]

def evalP (t : R) : Poly → R
  | [] => 0
  | a::w => (a:R) + t * evalP t w

theorem evalP_append_zero (t : R) (p : Poly) : evalP t (p++[0]) = evalP t p := by
  induction p <;> simp_all [evalP, intCast_zero, Semiring.mul_zero,
    Semiring.add_zero]

theorem evalP_rawAdd (t : R) (p q : Poly) :
    evalP t (rawAdd p q) = evalP t p + evalP t q := by
  induction p generalizing q with
  | nil => simp [evalP, rawAdd, zero_add]
  | cons a p ih =>
    cases q with
    | nil => simp [evalP, rawAdd, Semiring.add_zero]
    | cons b q =>
      simp only [evalP, rawAdd, ih, intCast_add]
      grind

theorem evalP_int_scale (t : R) (a : Int) (p : Poly) :
    evalP t (p.map (a * ·)) = (a:R) * evalP t p := by
  induction p with
  | nil => simp [evalP, Semiring.mul_zero]
  | cons b p ih =>
    simp only [List.map_cons, evalP, intCast_mul, ih]
    grind

theorem evalP_rawMul (t : R) (p q : Poly) :
    evalP t (rawMul p q) = evalP t p * evalP t q := by
  induction p with
  | nil => simp [evalP, rawMul, Semiring.zero_mul]
  | cons a p ih =>
    simp only [rawMul, evalP_rawAdd, evalP_int_scale, evalP, intCast_zero, ih]
    grind

theorem evalP_dropWhile (t : R) (p : Poly) :
    evalP t ((p.dropWhile (· == 0)).reverse) = evalP t p.reverse := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    by_cases h : a=0
    · subst a
      simpa [List.dropWhile_cons, List.reverse_cons, evalP_append_zero] using ih
    · simp [List.dropWhile_cons, h]

theorem evalP_norm (t : R) (p : Poly) : evalP t (norm p) = evalP t p := by
  simpa [norm] using evalP_dropWhile t p.reverse

theorem evalP_pAdd (t : R) (p q : Poly) :
    evalP t (pAdd p q) = evalP t p + evalP t q := by
  rw [pAdd, evalP_norm, evalP_rawAdd]

theorem evalP_pMul (t : R) (p q : Poly) :
    evalP t (pMul p q) = evalP t p * evalP t q := by
  rw [pMul, evalP_norm, evalP_rawMul]

theorem evalP_pPow (t : R) (p : Poly) (n : Nat) :
    evalP t (pPow p n) = evalP t p ^ n := by
  induction n with
  | zero => simp [pPow,evalP,intCast_one,Semiring.mul_zero,Semiring.add_zero,Semiring.pow_zero]
  | succ n ih =>
    rw [pPow, evalP_pMul, ih, Semiring.pow_succ, CommSemiring.mul_comm]

def evalQ (t r s : R) (x : Quad) : R :=
  evalP t x.a + evalP t x.b * r + evalP t x.c * s + evalP t x.d * r * s

theorem evalQ_const (t r s : R) (p : Poly) : evalQ t r s (constant p) = evalP t p := by
  simp [evalQ, constant, evalP, Semiring.zero_mul, Semiring.add_zero]

theorem evalQ_add (t r s : R) (x y : Quad) :
    evalQ t r s (bqAdd x y) = evalQ t r s x + evalQ t r s y := by
  simp only [evalQ, bqAdd, evalP_pAdd]
  grind

theorem evalQ_mul (t r s : R) (x y : Quad)
    (hr : evalP t D1 = r*r) (hs : evalP t D2 = s*s) :
    evalQ t r s (bqMul x y) = evalQ t r s x * evalQ t r s y := by
  have hd : pMul D1 D2 = D3 := by decide
  have h3 : evalP t D3 = (r*r)*(s*s) := by rw [←hd, evalP_pMul, hr, hs]
  simp only [evalQ, bqMul, evalP_pAdd, evalP_pMul, hr, hs, h3]
  grind

theorem evalQ_zero (t r s : R) : evalQ t r s ⟨[],[],[],[]⟩ = 0 := by
  simp [evalQ, evalP, Semiring.zero_mul, Semiring.add_zero]

theorem radicand1_eval (t : R) : evalP t D1 = 1 - (4 : R) * t*t := by
  simp [D1,evalP,intCast_zero,intCast_one,Semiring.mul_zero,Semiring.add_zero,zero_add]
  grind

theorem radicand2_eval (t : R) : evalP t D2 = 1 - (8 : R) * t*t := by
  simp [D2,evalP,intCast_zero,intCast_one,Semiring.mul_zero,Semiring.add_zero,zero_add]
  grind

theorem eval_horner (t r s : R) (a n : Quad) (d c : Poly) (j : Nat)
    (hr : evalP t D1 = r*r) (hs : evalP t D2 = s*s) :
    evalQ t r s (horner a n d c j) =
    evalQ t r s a * evalQ t r s n + evalP t c * (evalP t d)^j := by
  simp only [horner, evalQ_add, evalQ_mul t r s _ _ hr hs, evalQ_const,
    evalP_pMul, evalP_pPow]

theorem maple_identity_in_ring (t r s : R) (u : R)
    (hr : evalP t D1 = r*r) (hs : evalP t D2 = s*s)
    (Hu : evalQ t r s numer = evalP t den * u)
    (Hcancel : ∀ y : R, (evalP t den)^4 * y = 0 → y = 0) :
    (((evalP t c4 * u + evalP t c3) * u + evalP t c2) * u +
       evalP t c1) * u + evalP t c0 = 0 := by
  have h := congrArg (evalQ t r s) maple_quartic_cleared_denominator
  simp only [eval_horner t r s _ _ _ _ _ hr hs, evalQ_zero, evalQ_const, Hu] at h
  apply Hcancel
  grind

#print axioms evalQ_mul
#print axioms radicand1_eval
#print axioms radicand2_eval
#print axioms maple_identity_in_ring
end WalkQuarticAlgebra


namespace WalkQuarticSeriesGeometry
open Lean.Grind WalkQuarticSeries WalkQuarticArithmetic WalkQuarticAlgebra
attribute [local instance] Lean.Grind.Ring.intCast
set_option linter.unusedSimpArgs false

theorem evalP_coeff (p : Poly) (n : Nat) :
    (evalP T p).coeff n = (p[n]?.getD 0 : Int) := by
  induction p generalizing n with
  | nil => simp only [evalP, coeff_zero, List.getElem?_nil, Option.getD_none, Rat.intCast_zero]
  | cons a p ih =>
    simp only [evalP, coeff_add, t_mul_shift]
    cases n with
    | zero =>
      change (a:Rat) + 0 = (a:Rat)
      grind
    | succ n =>
      change (0:Rat) + (evalP T p).coeff n = (p[n]?.getD 0 : Int)
      rw [ih]; grind

def rad1 : Series := sqrtSeries (evalP T D1)
def rad2 : Series := sqrtSeries (evalP T D2)

theorem rad1_sq : evalP T D1=rad1*rad1 :=
  (sqrtSeries_sq _ (by rw [evalP_coeff]; decide)).symm
theorem rad2_sq : evalP T D2=rad2*rad2 :=
  (sqrtSeries_sq _ (by rw [evalP_coeff]; decide)).symm

theorem coeff0_rad1 : rad1.coeff 0=1 := sqrtSeries_coeff_zero _
theorem coeff0_rad2 : rad2.coeff 0=1 := sqrtSeries_coeff_zero _

theorem sq_prefix_unique (K : Nat) (f g : Series)
    (hf : f.coeff 0=1) (hg : g.coeff 0=1)
    (hs : ∀ n<K,(f*f).coeff n=(g*g).coeff n) :
    ∀ n<K, f.coeff n=g.coeff n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro h
    cases n with
    | zero => rw [hf,hg]
    | succ n =>
      cases n with
      | zero =>
        have H := hs 1 h
        change f.coeff 0*f.coeff 1+f.coeff 1*f.coeff 0=
          g.coeff 0*g.coeff 1+g.coeff 1*g.coeff 0 at H
        rw [hf,hg] at H
        grind
      | succ n =>
        have H := hs (n+2) h
        change f.coeff 0*f.coeff (n+2)+cpoint (n+1) (tail f) f =
          g.coeff 0*g.coeff (n+2)+cpoint (n+1) (tail g) g at H
        rw [cpoint_tail_right n (tail f) f,cpoint_tail_right n (tail g) g] at H
        have H' : cpoint n (tail f) (tail f)=cpoint n (tail g) (tail g) := by
          apply cpoint_congr
          all_goals intro j hj; exact ih (j+1) (by omega) (by omega)
        rw [hf,hg,H'] at H
        change 1*f.coeff (n+2)+(f.coeff (n+2)*1+_) =
          1*g.coeff (n+2)+(g.coeff (n+2)*1+_) at H
        grind

def r8 : Poly := [1,0,-2,0,-2,0,-4,0,-10]
def s8 : Poly := [1,0,-4,0,-8,0,-32,0,-160]

private theorem prems1 (n : Nat) (h : n<9) :
    (pMul r8 r8)[n]?.getD 0 = D1[n]?.getD 0 := by
  have h' : n=0 ∨ n=1 ∨ n=2 ∨ n=3 ∨ n=4 ∨ n=5 ∨ n=6 ∨ n=7 ∨ n=8 := by omega
  rcases h' with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

private theorem prems2 (n : Nat) (h : n<9) :
    (pMul s8 s8)[n]?.getD 0 = D2[n]?.getD 0 := by
  have h' : n=0 ∨ n=1 ∨ n=2 ∨ n=3 ∨ n=4 ∨ n=5 ∨ n=6 ∨ n=7 ∨ n=8 := by omega
  rcases h' with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem rad1_coeff8 (n : Nat) (h : n<9) : rad1.coeff n=(evalP T r8).coeff n := by
  have hh : (evalP T r8).coeff 0=1 := by rw [evalP_coeff]; decide
  apply sq_prefix_unique 9 _ _ coeff0_rad1 hh _ n h
  intro k hk
  rw [←rad1_sq, ←evalP_pMul,evalP_coeff,evalP_coeff,prems1 k hk]

theorem rad2_coeff8 (n : Nat) (h : n<9) : rad2.coeff n=(evalP T s8).coeff n := by
  have hh : (evalP T s8).coeff 0=1 := by rw [evalP_coeff]; decide
  apply sq_prefix_unique 9 _ _ coeff0_rad2 hh _ n h
  intro k hk
  rw [←rad2_sq, ←evalP_pMul,evalP_coeff,evalP_coeff,prems2 k hk]

def expand8 (q : Quad) : Poly :=
  pAdd (pAdd (pAdd q.a (pMul q.b r8)) (pMul q.c s8)) (pMul (pMul q.d r8) s8)

theorem evalQ_exp8 (q : Quad) (n : Nat) (hn : n<9) :
    (evalQ T rad1 rad2 q).coeff n = ((expand8 q)[n]?.getD 0 : Int) := by
  rw [←evalP_coeff]
  simp only [expand8,evalP_pAdd,evalP_pMul,evalQ,coeff_add]
  congr 1
  · congr 1
    · congr 1
      apply cpoint_congr
      · exact fun _ _ => rfl
      · exact fun j hj => rad1_coeff8 j (by omega)
    · apply cpoint_congr
      · exact fun _ _ => rfl
      · exact fun j hj => rad2_coeff8 j (by omega)
  · apply cpoint_congr
    · intro j hj
      apply cpoint_congr
      · exact fun _ _ => rfl
      · exact fun k hk => rad1_coeff8 k (by omega)
    · exact fun j hj => rad2_coeff8 j (by omega)

def earlyZero (q : Quad) : Bool :=
  (List.range 9).all (fun n => (expand8 q)[n]?.getD 0 == 0)

theorem earlyZero_sound (q : Quad) (H : earlyZero q = true) :
    ∀ n<9, (evalQ T rad1 rad2 q).coeff n=0 := by
  intro n hn
  rw [evalQ_exp8 q n hn]
  have h := (List.all_eq_true.mp H) n (List.mem_range.mpr hn)
  have hh : (expand8 q)[n]?.getD 0=0 := by simpa using h
  rw [hh,Rat.intCast_zero]

#print axioms evalP_coeff
#print axioms sq_prefix_unique
#print axioms rad1_sq
#print axioms evalQ_exp8
#print axioms earlyZero_sound
end WalkQuarticSeriesGeometry


namespace WalkQuarticRegular
open Lean.Grind WalkQuarticArithmetic WalkQuarticAlgebra WalkQuarticSeries
open WalkQuarticSeriesGeometry WalkQuarticSolutionCertificate
open WalkQuarticPhases WalkQuarticRecognize
attribute [local instance] Lean.Grind.Ring.intCast

set_option maxRecDepth 65536
set_option maxHeartbeats 0

def ve (q : Quad) : Series := evalQ T rad1 rad2 q
def denominator : Series := evalP T denAll

theorem denominator_low (n : Nat) (h : n<9) :
    denominator.coeff n=0 := by
  change (evalP T denAll).coeff n=0
  rw [evalP_coeff]
  have h' : n=0 ∨ n=1 ∨ n=2 ∨ n=3 ∨ n=4 ∨ n=5 ∨ n=6 ∨ n=7 ∨ n=8 := by omega
  rcases h' with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem denominator_nine : denominator.coeff 9≠0 := by
  change (evalP T denAll).coeff 9≠0
  rw [evalP_coeff]
  decide

theorem small_denominator_low (n : Nat) (h : n<4) :
    (evalP T den).coeff n=0 := by
  rw [evalP_coeff]
  have h' : n=0 ∨ n=1 ∨ n=2 ∨ n=3 := by omega
  rcases h' with rfl|rfl|rfl|rfl <;> decide

theorem small_denominator_four : (evalP T den).coeff 4≠0 := by
  rw [evalP_coeff]
  decide

theorem denom_cancel {f g : Series} (h : denominator*f=denominator*g) : f=g :=
  regularDen_cancel 9 _ _ _ denominator_low denominator_nine h

theorem small_denom_cancel {f g : Series}
    (h : evalP T den*f=evalP T den*g) : f=g :=
  regularDen_cancel 4 _ _ _ small_denominator_low small_denominator_four h

theorem small_denominator_kill (n : Nat) (f : Series)
    (h : (evalP T den)^n*f=0) : f=0 := by
  induction n generalizing f with
  | zero => simpa only [Semiring.pow_zero,Semiring.one_mul] using h
  | succ n ih =>
    rw [Semiring.pow_succ,Semiring.mul_assoc] at h
    have H := ih (evalP T den*f) h
    apply small_denom_cancel
    rw [H,Semiring.mul_zero]

def quotient (q : Quad) : Series :=
  unitQuot (dropN 9 denominator) (dropN 9 (ve q))

theorem quotient_exact (q : Quad) (hz : earlyZero q=true) :
    denominator*quotient q=ve q :=
  regularQuot_exact 9 denominator (ve q) denominator_low (earlyZero_sound q hz) denominator_nine

theorem scaledR_regular (b : Fin 6) (i j : Phase) : earlyZero (scaledR b i j)=true := by
  obtain ⟨b,hb⟩ := b
  have hc : b=0 ∨ b=1 ∨ b=2 ∨ b=3 ∨ b=4 ∨ b=5 := by omega
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl
  · change earlyZero (scaledR 0 i j)=true
    cases i <;> cases j <;> decide
  · change earlyZero (scaledR 1 i j)=true
    cases i <;> cases j <;> decide
  · change earlyZero (scaledR 2 i j)=true
    cases i <;> cases j <;> decide
  · change earlyZero (scaledR 3 i j)=true
    cases i <;> cases j <;> decide
  · change earlyZero (scaledR 4 i j)=true
    cases i <;> cases j <;> decide
  · change earlyZero (scaledR 5 i j)=true
    cases i <;> cases j <;> decide

theorem scaledM_regular (b : Fin 6) (i : Phase) : earlyZero (scaledM b i)=true := by
  obtain ⟨b,hb⟩ := b
  have hc : b=0 ∨ b=1 ∨ b=2 ∨ b=3 ∨ b=4 ∨ b=5 := by omega
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl
  · change earlyZero (scaledM 0 i)=true
    cases i <;> decide
  · change earlyZero (scaledM 1 i)=true
    cases i <;> decide
  · change earlyZero (scaledM 2 i)=true
    cases i <;> decide
  · change earlyZero (scaledM 3 i)=true
    cases i <;> decide
  · change earlyZero (scaledM 4 i)=true
    cases i <;> decide
  · change earlyZero (scaledM 5 i)=true
    cases i <;> decide

theorem scaledE_regular (i : Phase) : earlyZero (scaledE i)=true := by cases i <;> decide
theorem scaledX_regular (l : Low) : earlyZero (scaledX l)=true := by cases l <;> decide

def rv (b : Fin 6) (i j : Phase) : Series := quotient (scaledR b i j)
def mv (b : Fin 6) (i : Phase) : Series := quotient (scaledM b i)
def ev (i : Phase) : Series := quotient (scaledE i)
def xv (l : Low) : Series := quotient (scaledX l)

theorem eval_scaledR (b : Fin 6) (i j : Phase) : ve (scaledR b i j)=denominator*rv b i j :=
  (quotient_exact _ (scaledR_regular ..)).symm
theorem eval_scaledM (b : Fin 6) (i : Phase) : ve (scaledM b i)=denominator*mv b i :=
  (quotient_exact _ (scaledM_regular ..)).symm
theorem eval_scaledE (i : Phase) : ve (scaledE i)=denominator*ev i :=
  (quotient_exact _ (scaledE_regular ..)).symm
theorem eval_scaledX (l : Low) : ve (scaledX l)=denominator*xv l :=
  (quotient_exact _ (scaledX_regular ..)).symm

#print axioms denominator_nine
#print axioms small_denominator_kill
#print axioms quotient_exact
#print axioms eval_scaledR
#print axioms eval_scaledM
#print axioms eval_scaledE
#print axioms eval_scaledX
end WalkQuarticRegular

namespace WalkQuarticMatrixSeries
open Lean.Grind WalkQuarticArithmetic WalkQuarticAlgebra WalkQuarticSeries
open WalkQuarticSeriesGeometry WalkQuarticSolutionCertificate WalkQuarticRegular
open WalkQuarticWord WalkQuarticPhases WalkQuarticRecognize WalkQuarticCounting
open WalkQuarticPopulation WalkQuarticBandReturn WalkQuarticFirstReturnGF WalkQuarticBoundary
open Lean.Grind.Semiring
attribute [local instance] Lean.Grind.Ring.intCast
set_option linter.unusedSimpArgs false

private theorem add0 (f : Series) : 0+f=f := by rw [Lean.Grind.Semiring.add_comm,add_zero]

theorem ve_zero : ve qzero=0 := evalQ_zero _ _ _
theorem ve_add (p q : Quad) : ve (bqAdd p q)=ve p+ve q := evalQ_add _ _ _ _ _
theorem ve_mul (p q : Quad) : ve (qmul p q)=ve p*ve q := by
  by_cases h₁ : p=qzero
  · subst p
    simp [qmul,ve_zero,zero_mul]
  · by_cases h₂ : q=qzero
    · subst q
      simp [qmul,ve_zero,mul_zero]
    · simp only [qmul,h₁,h₂,or_self,ite_false,ve,evalQ_mul _ _ _ _ _ rad1_sq rad2_sq]

theorem ve_sum (xs : List Quad) : ve (qsum xs)=lsum ve xs := by
  induction xs with
  | nil => exact ve_zero
  | cons x xs ih =>
    change ve (bqAdd x (qsum xs))=ve x+lsum ve xs
    rw [ve_add,ih]

theorem ve_const (p : Poly) : ve (constant p)=evalP T p := evalQ_const _ _ _ _
theorem ve_D : ve D=denominator := ve_const _
theorem ve_Dsq : ve Dsq=denominator*denominator := by rw [Dsq,ve_mul,ve_D]
theorem ve_t : ve degreeOne=T := by
  rw [degreeOne,ve_const]
  simp [evalP,Lean.Grind.Ring.intCast_zero,Lean.Grind.Ring.intCast_one,mul_zero,add_zero,add0,mul_one]
theorem ve_tt : ve degreeTwo=T*T := by
  rw [degreeTwo,ve_const]
  simp [evalP,Lean.Grind.Ring.intCast_zero,Lean.Grind.Ring.intCast_one,mul_zero,add_zero,add0,mul_one]

theorem ve_mark (P : Prop) [Decidable P] (p : Quad) :
    ve (if P then p else qzero) = (markProp P : Series)*ve p := by
  by_cases h : P
  · rw [ite_eq_left h,markProp_true h,one_mul]
  · rw [ite_eq_right h,markProp_false h,zero_mul,ve_zero]

private theorem scale_prod (a b : Series) :
    (denominator*a)*(denominator*b)=(denominator*denominator)*(a*b) := by grind

def rMove (b : Fin 6) (i j : Phase) : Series :=
  lsum (fun k => lsum (fun p => rv (residueNext b) (upPhase b.val i k) p *
      rv b (advanceA p) j) highPhases) upLetters

def mRise (b : Fin 6) (i : Phase) : Series :=
  lsum (fun k => mv (residueNext b) (upPhase b.val i k)) upLetters

def mReturn (b : Fin 6) (i : Phase) : Series :=
  lsum (fun k => lsum (fun p => rv (residueNext b) (upPhase b.val i k) p *
      mv b (advanceA p)) highPhases) upLetters

def eDrop (i : Phase) : Series :=
  lsum (fun p => rv 5 i p * xv (exitLow p)) highPhases

def lMove (l : Low) : Series := lsum (fun k => match lowestStep l k with
  | none => 0
  | some (.low l') => xv l'
  | some (.high i _) => ev i) alphabet

theorem rEquation (b : Fin 6) (i j : Phase)
    (H : qmul D (scaledR b i j)=retRHS b i j) :
    rv b i j = markProp (i=j)+T*T*rMove b i j := by
  have h := congrArg ve H
  simp only [retRHS,ve_mul,ve_add,ve_sum,ve_mark,ve_D,ve_Dsq,ve_tt,lsum_flatMap,lsum_map,
    eval_scaledR,scale_prod,lsum_mul_left] at h
  change denominator*(denominator*rv b i j) =
      markProp (i=j)*(denominator*denominator) +
        T*T*((denominator*denominator)*rMove b i j) at h
  apply denom_cancel
  apply denom_cancel
  grind

theorem mEquation (b : Fin 6) (i : Phase)
    (H : qmul D (scaledM b i)=meanderRHS b i) :
    mv b i = markProp (terminal i b.val) + (T*mRise b i+T*T*mReturn b i) := by
  have h := congrArg ve H
  simp only [meanderRHS,ve_mul,ve_add,ve_sum,ve_mark,ve_D,ve_Dsq,ve_t,ve_tt,
    lsum_flatMap,lsum_map,eval_scaledM,eval_scaledR,scale_prod,lsum_mul_left,
    markProp_congr (phaseMark_spec i b.val)] at h
  change denominator*(denominator*mv b i) =
      markProp (terminal i b.val)*(denominator*denominator) +
        ((T*denominator)*(denominator*mRise b i) +
        T*T*((denominator*denominator)*mReturn b i)) at h
  apply denom_cancel
  apply denom_cancel
  grind

theorem eEquation (i : Phase) (H : qmul D (scaledE i)=entryRHS i) :
    ev i = mv 5 i + T*eDrop i := by
  have h := congrArg ve H
  simp only [entryRHS,ve_mul,ve_add,ve_sum,ve_D,ve_t,lsum_map,
    eval_scaledE,eval_scaledM,eval_scaledR,eval_scaledX,scale_prod,lsum_mul_left] at h
  change denominator*(denominator*ev i) =
      denominator*(denominator*mv 5 i)+ T*((denominator*denominator)*eDrop i) at h
  apply denom_cancel
  apply denom_cancel
  grind

theorem xEquation (l : Low) (H : scaledX l=lowRHS l) :
    xv l = markProp (lowDeficits l (lowHeight l)) + T*lMove l := by
  have h := congrArg ve H
  have hl (k : Letter) : ve (match lowestStep l k with
      | none => qzero
      | some (.low l') => scaledX l'
      | some (.high p _) => scaledE p) = denominator*(match lowestStep l k with
      | none => 0
      | some (.low l') => xv l'
      | some (.high p _) => ev p) := by
    cases e : lowestStep l k with
    | none => simp [ve_zero,mul_zero]
    | some q =>
      cases q with
      | low l' => exact eval_scaledX l'
      | high p h => exact eval_scaledE p
  simp only [lowRHS,eval_scaledX,ve_add,ve_mul,ve_mark,ve_D,ve_t,ve_sum,lsum_map,hl,
    lsum_mul_left,markProp_congr (lowMark_spec l)] at h
  change denominator*xv l =
    markProp (lowDeficits l (lowHeight l))*denominator + T*(denominator*lMove l) at h
  apply denom_cancel
  grind

theorem initial_quartic_series
    (H : qmul (constant den) (scaledX .s0) = qmul D numer) :
    (((evalP T c4 * xv .s0 + evalP T c3) * xv .s0 + evalP T c2) * xv .s0 +
       evalP T c1) * xv .s0 + evalP T c0 = 0 := by
  apply maple_identity_in_ring T rad1 rad2 (xv .s0) rad1_sq rad2_sq
  · have h := congrArg ve H
    simp only [ve_mul,ve_const,ve_D,eval_scaledX] at h
    change evalP T den*(denominator*xv .s0) = denominator*ve numer at h
    change ve numer = evalP T den*xv .s0
    apply denom_cancel
    grind
  · exact small_denominator_kill 4

#print axioms rEquation
#print axioms mEquation
#print axioms eEquation
#print axioms xEquation
#print axioms initial_quartic_series
end WalkQuarticMatrixSeries

namespace WalkQuarticFinish
open Lean.Grind WalkQuarticArithmetic WalkQuarticAlgebra WalkQuarticSeries WalkQuarticRegular
open WalkQuarticSolutionCertificate WalkQuarticMatrixSeries
open WalkQuarticWord WalkQuarticPhases WalkQuarticRecognize WalkQuarticCounting
open WalkQuarticPopulation WalkQuarticBandReturn WalkQuarticFirstReturnGF WalkQuarticBoundary
open WalkQuarticTransferSystem Lean.Grind.Semiring
set_option linter.unusedSimpArgs false

def bucket (b : Nat) : Fin 6 := ⟨b%6,Nat.mod_lt _ (by decide)⟩

theorem bucket_five : bucket 5=(5:Fin 6) := by
  apply Fin.ext
  decide

theorem next_bucket (b : Nat) : residueNext (bucket b)=bucket (b+1) := by
  apply Fin.ext
  exact Nat.mod_add_mod b 6 1

theorem upPhase_bucket (b : Nat) (p : Phase) (k : Letter) :
    upPhase (bucket b).val p k=upPhase b p k := by
  have h2 : (bucket b).val%2=b%2 := Nat.mod_mod_of_dvd b (by decide)
  have h3 : (bucket b).val%3=b%3 := Nat.mod_mod_of_dvd b (by decide)
  cases k <;> cases p <;> simp [upPhase,advanceB,advanceC,h2,h3]

theorem terminal_bucket (b : Nat) (p : Phase) :
    terminal p (bucket b).val ↔ terminal p b := by
  have h2 : (bucket b).val%2=b%2 := Nat.mod_mod_of_dvd b (by decide)
  have h3 : (bucket b).val%3=b%3 := Nat.mod_mod_of_dvd b (by decide)
  cases p <;> simp [terminal,h2,h3]

theorem coeff_mark_zero (P : Prop) :
    (markProp P : Series).coeff 0=(markProp P : Rat) := by
  by_cases h : P
  · rw [markProp_true h,markProp_true h,coeff_one_zero]
  · rw [markProp_false h,markProp_false h,coeff_zero]
theorem coeff_mark_succ (P : Prop) (n : Nat) :
    (markProp P : Series).coeff (n+1)=0 := by
  by_cases h : P
  · rw [markProp_true h,coeff_one_succ]
  · rw [markProp_false h,coeff_zero]

def ratOne : Letter → Rat := fun _=>1

theorem lsum_rotate3 {α β γ : Type} (f : α → β → γ → Rat) (L : List α)
    (M : List β) (N : List γ) :
    lsum (fun a => lsum (fun b => lsum (f a b) N) M) L =
      lsum (fun c => lsum (fun a => lsum (fun b => f a b c) M) L) N := by
  calc
    _ = lsum (fun a => lsum (fun c => lsum (fun b => f a b c) M) N) L := by
      apply lsum_congr_mem
      intro a ha
      exact lsum_swap (f a) M N
    _ = _ := lsum_swap _ L N

def rC (b n : Nat) (i j : Phase) : Rat := (rv (bucket b) i j).coeff n
def mC (b n : Nat) (i : Phase) : Rat := (mv (bucket b) i).coeff n
def eC (n : Nat) (i : Phase) : Rat := (ev i).coeff n
def xC (n : Nat) (l : Low) : Rat := (xv l).coeff n

theorem rMove_coeff (b n : Nat) (i j : Phase) :
    (rMove (bucket b) i j).coeff n =
      lsum (fun d => lsum (fun k => lsum (fun p =>
        rC (b+1) d (upPhase b i k) p * rC b (n-d) (advanceA p) j)
        highPhases) upLetters) (List.range (n+1)) := by
  simp only [rMove,coeff_lsum,coeff_mul_cauchy,next_bucket,upPhase_bucket, rC]
  exact lsum_rotate3 _ _ _ _

theorem mRise_coeff (b n : Nat) (i : Phase) :
    (mRise (bucket b) i).coeff n =
      lsum (fun k => mC (b+1) n (upPhase b i k)) upLetters := by
  simp only [mRise,coeff_lsum,next_bucket,upPhase_bucket,mC]

theorem mReturn_coeff (b n : Nat) (i : Phase) :
    (mReturn (bucket b) i).coeff n =
      lsum (fun d => lsum (fun k => lsum (fun p =>
        rC (b+1) d (upPhase b i k) p * mC b (n-d) (advanceA p))
        highPhases) upLetters) (List.range (n+1)) := by
  simp only [mReturn,coeff_lsum,coeff_mul_cauchy,next_bucket,upPhase_bucket,rC,mC]
  exact lsum_rotate3 _ _ _ _

theorem eDrop_coeff (n : Nat) (i : Phase) :
    (eDrop i).coeff n =
      lsum (fun d => lsum (fun p => rC 5 d i p * xC (n-d) (exitLow p))
        highPhases) (List.range (n+1)) := by
  simp only [eDrop,coeff_lsum,coeff_mul_cauchy,rC,xC]
  exact lsum_swap _ _ _

theorem lMove_coeff (n : Nat) (l : Low) :
    (lMove l).coeff n =
      lsum (fun k => match lowestStep l k with
        | none => 0
        | some (.low l') => xC n l'
        | some (.high i _) => eC n i) alphabet := by
  simp only [lMove,coeff_lsum]
  apply lsum_congr_mem
  intro k _
  cases e : lowestStep l k with
  | none => exact coeff_zero n
  | some q => cases q <;> rfl

/-- Turn the checked ring identities into the actual all-length coefficient equations. -/
noncomputable def seriesTransfer
    (hR : ∀ b i j, qmul D (scaledR b i j)=retRHS b i j)
    (hM : ∀ b i, qmul D (scaledM b i)=meanderRHS b i)
    (hE : ∀ i, qmul D (scaledE i)=entryRHS i)
    (hX : ∀ l, scaledX l=lowRHS l) :
    TransferSolution ratOne where
  r := rC
  m := mC
  e := eC
  x := xC
  r0 := by
    intro b i j
    have h := congrArg (fun f : Series=>f.coeff 0) (rEquation (bucket b) i j (hR ..))
    simpa only [rC,coeff_add,coeff_mark_zero,coeff_TT_mul_zero,add_zero] using h
  r1 := by
    intro b i j
    have h := congrArg (fun f : Series=>f.coeff 1) (rEquation (bucket b) i j (hR ..))
    simpa only [rC,coeff_add,coeff_mark_succ,coeff_TT_mul_one,add_zero] using h
  rs := by
    intro b n i j
    have h := congrArg (fun f : Series=>f.coeff (n+2)) (rEquation (bucket b) i j (hR ..))
    simp only [coeff_add,coeff_mark_succ,coeff_TT_mul_succ_succ,
      rMove_coeff,ratOne,one_mul] at h ⊢
    have hz (x : Rat) : 0+x=x := by grind
    simpa only [hz,rC] using h
  m0 := by
    intro b i
    have h := congrArg (fun f : Series=>f.coeff 0) (mEquation (bucket b) i (hM ..))
    simpa only [mC,coeff_add,coeff_mark_zero,coeff_T_mul_zero,coeff_TT_mul_zero,
      add_zero,markProp_congr (terminal_bucket b i)] using h
  m1 := by
    intro b i
    have h := congrArg (fun f : Series=>f.coeff 1) (mEquation (bucket b) i (hM ..))
    have hz (x : Rat) : 0+x=x := by grind
    simpa only [mC,coeff_add,coeff_mark_succ,coeff_T_mul_succ,coeff_TT_mul_one,
      mRise_coeff,hz,add_zero,ratOne,one_mul] using h
  ms := by
    intro b n i
    have h := congrArg (fun f : Series=>f.coeff (n+2)) (mEquation (bucket b) i (hM ..))
    have hz (x : Rat) : 0+x=x := by grind
    simpa only [mC,coeff_add,coeff_mark_succ,coeff_T_mul_succ,coeff_TT_mul_succ_succ,
      mRise_coeff,mReturn_coeff,hz,ratOne,one_mul] using h
  e0 := by
    intro i hi
    have h := congrArg (fun f : Series=>f.coeff 0) (eEquation i (hE i))
    simpa only [eC,mC,bucket_five,coeff_add,coeff_T_mul_zero,add_zero] using h
  es := by
    intro n i hi
    have h := congrArg (fun f : Series=>f.coeff (n+1)) (eEquation i (hE i))
    simpa only [eC,mC,bucket_five,coeff_add,coeff_T_mul_succ,eDrop_coeff,ratOne,one_mul] using h
  x0 := by
    intro l
    have h := congrArg (fun f : Series=>f.coeff 0) (xEquation l (hX l))
    simpa only [xC,coeff_add,coeff_mark_zero,coeff_T_mul_zero,add_zero] using h
  xs := by
    intro n l
    have h := congrArg (fun f : Series=>f.coeff (n+1)) (xEquation l (hX l))
    have hz (x : Rat) : 0+x=x := by grind
    simp only [coeff_add,coeff_mark_succ,coeff_T_mul_succ,lMove_coeff,hz] at h
    change (xv l).coeff (n+1) = _
    rw [h]
    apply lsum_congr_mem
    intro k hk
    cases e : lowestStep l k with
    | none => simp [e,ratOne]
    | some s => cases s <;> simp [e,ratOne]

noncomputable def sourceSeries : Series := ⟨fun n => sourceCoeff ratOne n⟩

theorem sourceSeries_eq_initial
    (hR : ∀ b i j, qmul D (scaledR b i j)=retRHS b i j)
    (hM : ∀ b i, qmul D (scaledM b i)=meanderRHS b i)
    (hE : ∀ i, qmul D (scaledE i)=entryRHS i)
    (hX : ∀ l, scaledX l=lowRHS l) :
    sourceSeries=xv .s0 := by
  apply Series.ext
  intro n
  exact sourceCoeff_eq_solution ratOne (seriesTransfer hR hM hE hX) n

#print axioms seriesTransfer
#print axioms sourceSeries_eq_initial
end WalkQuarticFinish

namespace WalkQuarticFinish
open Lean.Grind WalkQuarticArithmetic WalkQuarticAlgebra WalkQuarticSeries
open WalkQuarticSolutionCertificate WalkQuarticMatrixSeries
open WalkQuarticWord WalkQuarticCounting WalkQuarticPopulation WalkQuarticBoundaryGF

/-- A word is counted once if some signed realization is a nonnegative excursion. -/
theorem sourceSeries_counts_words (n : Nat) :
    sourceSeries.coeff n = ((sourceExcursions n).length : Rat) := by
  have all_one (w : List Letter) : wordWeight ratOne w=1 := by
    induction w with
    | nil => rfl
    | cons k w ih => simp [wordWeight,ratOne,ih]
  have word_sum (l : List (List Letter)) : lsum (wordWeight ratOne) l=(l.length : Rat) := by
    induction l with
    | nil => rfl
    | cons w l ih =>
      change wordWeight ratOne w + lsum (wordWeight ratOne) l = ((l.length+1 : Nat) : Rat)
      rw [all_one,ih]
      simp only [Lean.Grind.Semiring.natCast_add]
      grind
  change sourceCoeff ratOne n = _
  rw [sourceCoeff]
  classical
  calc
    _ = lsum (wordWeight ratOne) (sourceExcursions n) :=
      (lsum_filter_mark (wordWeight ratOne) (fun w => reaches w.reverse 0) (words n)).symm
    _ = _ := word_sum _

/-- The exact quartic in de Panafieu–Wallner's §6.2 companion worksheet,
evaluated on the original all-length nondeterministic-excursion series. -/
theorem maple_source_quartic :
    (((evalP T c4 * sourceSeries + evalP T c3) * sourceSeries + evalP T c2) *
       sourceSeries + evalP T c1) * sourceSeries + evalP T c0 = 0 := by
  rw [sourceSeries_eq_initial scaledReturn_eq scaledMeander_eq scaledEntry_eq scaledLow_eq]
  exact initial_quartic_series scaledInitial_eq

#print axioms sourceSeries_counts_words
#print axioms maple_source_quartic
end WalkQuarticFinish


namespace PalomarWalkQuartic
open WalkQuarticSeries WalkQuarticArithmetic WalkQuarticPopulation

/-- Ordinary rational formal power series whose nth coefficient is the
number of distinct length-n excursion words, not their realizations. -/
noncomputable def countSeries : Series :=
  ⟨fun n => ((sourceExcursions n).length : Rat)⟩

/-- Evaluate a low-to-high list of integer coefficients at the series T. -/
def evalPolynomial : Poly → Series
  | [] => delta 0
  | a::p => add (delta (a : Rat)) (mul T (evalPolynomial p))

/-- The author companion's exact quartic in Y, evaluated at a series. -/
def mapleQuarticAt (Y : Series) : Series :=
  let a := add (mul (evalPolynomial c4) Y) (evalPolynomial c3)
  let b := add (mul a Y) (evalPolynomial c2)
  let c := add (mul b Y) (evalPolynomial c1)
  add (mul c Y) (evalPolynomial c0)


open WalkQuarticAlgebra WalkQuarticFinish

theorem evalPolynomial_matches (p : Poly) : evalPolynomial p=evalP T p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    change add (delta (a : Rat)) (mul T (evalPolynomial p)) = _
    rw [ih]
    rfl

theorem countSeries_matches : countSeries=sourceSeries := by
  apply Series.ext
  intro n
  exact (sourceSeries_counts_words n).symm

/-- The literal source word-count series satisfies the companion quartic. -/
theorem exact_quartic : mapleQuarticAt countSeries = delta 0 := by
  unfold mapleQuarticAt
  rw [countSeries_matches]
  simp only [evalPolynomial_matches]
  exact maple_source_quartic

#print axioms exact_quartic
end PalomarWalkQuartic

