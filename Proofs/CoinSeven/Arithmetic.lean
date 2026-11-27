module

public import Std

@[expose] public section

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Coin7Arithmetic

theorem small0 (a b c d e f : Int)
    (o0 : a > 1)
    (o1 : a < b)
    (o2 : b < c)
    (o3 : c < d)
    (o4 : d < e)
    (o5 : e < f)
    (p0 : (2 * b) ≥ c)
    (p1 : ¬ (((2 * b) = (c + 0)) ∨ ((2 * b) = (c + 1)) ∨ ((2 * b) = (c + a)) ∨ ((2 * b) = (c + b)) ∨ ((2 * b) = (c + c))))
    (p2 : (b - a) ≥ (a - 1))
    (hF : f ≤ (a + a))
    (hB : ¬ (((a + a) = (e + 0)) ∨ ((a + a) = (e + 1)) ∨ ((a + a) = (e + a)) ∨ ((a + a) = (e + b)) ∨ ((a + a) = (e + c)) ∨ ((a + a) = (e + d)) ∨ ((a + a) = (e + e))))
    : False := by
  simp only [not_or] at p1
  simp only [not_or] at hB
  omega

theorem small1 (a b c d e f : Int)
    (o0 : a > 1)
    (o1 : a < b)
    (o2 : b < c)
    (o3 : c < d)
    (o4 : d < e)
    (o5 : e < f)
    (p0 : (2 * b) ≥ c)
    (p1 : ¬ (((2 * b) = (c + 0)) ∨ ((2 * b) = (c + 1)) ∨ ((2 * b) = (c + a)) ∨ ((2 * b) = (c + b)) ∨ ((2 * b) = (c + c))))
    (p2 : (b - a) ≥ (a - 1))
    (hF : f ≤ (a + b))
    (hB : ¬ (((a + b) = (e + 0)) ∨ ((a + b) = (e + 1)) ∨ ((a + b) = (e + a)) ∨ ((a + b) = (e + b)) ∨ ((a + b) = (e + c)) ∨ ((a + b) = (e + d)) ∨ ((a + b) = (e + e))))
    (h10 : ((c + d) < f) ∨ ((c + d) = (f + 0)) ∨ ((c + d) = (f + 1)) ∨ ((c + d) = (f + a)) ∨ ((c + d) = (f + b)) ∨ ((c + d) = (f + c)) ∨ ((c + d) = (f + d)) ∨ ((c + d) = (f + e)) ∨ ((c + d) = (f + f)))
    (h13 : ((d + d) < f) ∨ ((d + d) = (f + 0)) ∨ ((d + d) = (f + 1)) ∨ ((d + d) = (f + a)) ∨ ((d + d) = (f + b)) ∨ ((d + d) = (f + c)) ∨ ((d + d) = (f + d)) ∨ ((d + d) = (f + e)) ∨ ((d + d) = (f + f)))
    (h14 : ((d + e) < f) ∨ ((d + e) = (f + 0)) ∨ ((d + e) = (f + 1)) ∨ ((d + e) = (f + a)) ∨ ((d + e) = (f + b)) ∨ ((d + e) = (f + c)) ∨ ((d + e) = (f + d)) ∨ ((d + e) = (f + e)) ∨ ((d + e) = (f + f)))
    : False := by
  simp only [not_or] at p1
  simp only [not_or] at hB
  rcases h10 with hz2_0 | hz2_1 | hz2_2 | hz2_3 | hz2_4 | hz2_5 | hz2_6 | hz2_7 | hz2_8
  · (clear h13 h14; omega)
  · (clear h13 h14; omega)
  · (clear h13 h14; omega)
  · (clear h13 h14; omega)
  · rcases h13 with hz4_0 | hz4_1 | hz4_2 | hz4_3 | hz4_4 | hz4_5 | hz4_6 | hz4_7 | hz4_8
    · (clear h14; omega)
    · (clear h14; omega)
    · (clear h14; omega)
    · (clear h14; omega)
    · (clear h14; omega)
    · rcases h14 with hz6_0 | hz6_1 | hz6_2 | hz6_3 | hz6_4 | hz6_5 | hz6_6 | hz6_7 | hz6_8
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
    · (clear h14; omega)
    · (clear h14; omega)
    · (clear h14; omega)
  · (clear h13 h14; omega)
  · (clear h13 h14; omega)
  · (clear h13 h14; omega)
  · (clear h13 h14; omega)

theorem small2 (a b c d e f : Int)
    (o0 : a > 1)
    (o1 : a < b)
    (o2 : b < c)
    (o3 : c < d)
    (o4 : d < e)
    (o5 : e < f)
    (p0 : (2 * b) ≥ c)
    (p1 : ¬ (((2 * b) = (c + 0)) ∨ ((2 * b) = (c + 1)) ∨ ((2 * b) = (c + a)) ∨ ((2 * b) = (c + b)) ∨ ((2 * b) = (c + c))))
    (p2 : (b - a) ≥ (a - 1))
    (hF : f ≤ (a + c))
    (hB : ¬ (((a + c) = (e + 0)) ∨ ((a + c) = (e + 1)) ∨ ((a + c) = (e + a)) ∨ ((a + c) = (e + b)) ∨ ((a + c) = (e + c)) ∨ ((a + c) = (e + d)) ∨ ((a + c) = (e + e))))
    (h10 : ((c + d) < f) ∨ ((c + d) = (f + 0)) ∨ ((c + d) = (f + 1)) ∨ ((c + d) = (f + a)) ∨ ((c + d) = (f + b)) ∨ ((c + d) = (f + c)) ∨ ((c + d) = (f + d)) ∨ ((c + d) = (f + e)) ∨ ((c + d) = (f + f)))
    (h13 : ((d + d) < f) ∨ ((d + d) = (f + 0)) ∨ ((d + d) = (f + 1)) ∨ ((d + d) = (f + a)) ∨ ((d + d) = (f + b)) ∨ ((d + d) = (f + c)) ∨ ((d + d) = (f + d)) ∨ ((d + d) = (f + e)) ∨ ((d + d) = (f + f)))
    (h14 : ((d + e) < f) ∨ ((d + e) = (f + 0)) ∨ ((d + e) = (f + 1)) ∨ ((d + e) = (f + a)) ∨ ((d + e) = (f + b)) ∨ ((d + e) = (f + c)) ∨ ((d + e) = (f + d)) ∨ ((d + e) = (f + e)) ∨ ((d + e) = (f + f)))
    : False := by
  simp only [not_or] at p1
  simp only [not_or] at hB
  rcases h10 with hz2_0 | hz2_1 | hz2_2 | hz2_3 | hz2_4 | hz2_5 | hz2_6 | hz2_7 | hz2_8
  · (clear h13 h14; omega)
  · (clear h13 h14; omega)
  · (clear h13 h14; omega)
  · (clear h13 h14; omega)
  · rcases h13 with hz4_0 | hz4_1 | hz4_2 | hz4_3 | hz4_4 | hz4_5 | hz4_6 | hz4_7 | hz4_8
    · (clear h14; omega)
    · (clear h14; omega)
    · (clear h14; omega)
    · (clear h14; omega)
    · (clear h14; omega)
    · rcases h14 with hz6_0 | hz6_1 | hz6_2 | hz6_3 | hz6_4 | hz6_5 | hz6_6 | hz6_7 | hz6_8
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
    · (clear h14; omega)
    · (clear h14; omega)
    · (clear h14; omega)
  · (clear h13 h14; omega)
  · (clear h13 h14; omega)
  · (clear h13 h14; omega)
  · (clear h13 h14; omega)

theorem small3 (a b c d e f : Int)
    (o0 : a > 1)
    (o1 : a < b)
    (o2 : b < c)
    (o3 : c < d)
    (o4 : d < e)
    (o5 : e < f)
    (p0 : (2 * b) ≥ c)
    (p1 : ¬ (((2 * b) = (c + 0)) ∨ ((2 * b) = (c + 1)) ∨ ((2 * b) = (c + a)) ∨ ((2 * b) = (c + b)) ∨ ((2 * b) = (c + c))))
    (p2 : (b - a) ≥ (a - 1))
    (hF : f ≤ (a + d))
    (hB : ¬ (((a + d) = (e + 0)) ∨ ((a + d) = (e + 1)) ∨ ((a + d) = (e + a)) ∨ ((a + d) = (e + b)) ∨ ((a + d) = (e + c)) ∨ ((a + d) = (e + d)) ∨ ((a + d) = (e + e))))
    (h10 : ((c + d) < f) ∨ ((c + d) = (f + 0)) ∨ ((c + d) = (f + 1)) ∨ ((c + d) = (f + a)) ∨ ((c + d) = (f + b)) ∨ ((c + d) = (f + c)) ∨ ((c + d) = (f + d)) ∨ ((c + d) = (f + e)) ∨ ((c + d) = (f + f)))
    (h13 : ((d + d) < f) ∨ ((d + d) = (f + 0)) ∨ ((d + d) = (f + 1)) ∨ ((d + d) = (f + a)) ∨ ((d + d) = (f + b)) ∨ ((d + d) = (f + c)) ∨ ((d + d) = (f + d)) ∨ ((d + d) = (f + e)) ∨ ((d + d) = (f + f)))
    (h14 : ((d + e) < f) ∨ ((d + e) = (f + 0)) ∨ ((d + e) = (f + 1)) ∨ ((d + e) = (f + a)) ∨ ((d + e) = (f + b)) ∨ ((d + e) = (f + c)) ∨ ((d + e) = (f + d)) ∨ ((d + e) = (f + e)) ∨ ((d + e) = (f + f)))
    (h15 : ((e + e) < f) ∨ ((e + e) = (f + 0)) ∨ ((e + e) = (f + 1)) ∨ ((e + e) = (f + a)) ∨ ((e + e) = (f + b)) ∨ ((e + e) = (f + c)) ∨ ((e + e) = (f + d)) ∨ ((e + e) = (f + e)) ∨ ((e + e) = (f + f)))
    : False := by
  simp only [not_or] at p1
  simp only [not_or] at hB
  rcases h10 with hz2_0 | hz2_1 | hz2_2 | hz2_3 | hz2_4 | hz2_5 | hz2_6 | hz2_7 | hz2_8
  · (clear h13 h14 h15; omega)
  · (clear h13 h14 h15; omega)
  · (clear h13 h14 h15; omega)
  · rcases h13 with hz4_0 | hz4_1 | hz4_2 | hz4_3 | hz4_4 | hz4_5 | hz4_6 | hz4_7 | hz4_8
    · (clear h14 h15; omega)
    · (clear h14 h15; omega)
    · (clear h14 h15; omega)
    · (clear h14 h15; omega)
    · rcases h14 with hz6_0 | hz6_1 | hz6_2 | hz6_3 | hz6_4 | hz6_5 | hz6_6 | hz6_7 | hz6_8
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · rcases h15 with hz8_0 | hz8_1 | hz8_2 | hz8_3 | hz8_4 | hz8_5 | hz8_6 | hz8_7 | hz8_8
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
    · rcases h14 with hz6_0 | hz6_1 | hz6_2 | hz6_3 | hz6_4 | hz6_5 | hz6_6 | hz6_7 | hz6_8
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
    · (clear h14 h15; omega)
    · (clear h14 h15; omega)
    · (clear h14 h15; omega)
  · rcases h13 with hz4_0 | hz4_1 | hz4_2 | hz4_3 | hz4_4 | hz4_5 | hz4_6 | hz4_7 | hz4_8
    · (clear h14 h15; omega)
    · (clear h14 h15; omega)
    · (clear h14 h15; omega)
    · (clear h14 h15; omega)
    · (clear h14 h15; omega)
    · rcases h14 with hz6_0 | hz6_1 | hz6_2 | hz6_3 | hz6_4 | hz6_5 | hz6_6 | hz6_7 | hz6_8
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
    · (clear h14 h15; omega)
    · (clear h14 h15; omega)
    · (clear h14 h15; omega)
  · (clear h13 h14 h15; omega)
  · (clear h13 h14 h15; omega)
  · (clear h13 h14 h15; omega)
  · (clear h13 h14 h15; omega)

theorem small4 (a b c d e f : Int)
    (o0 : a > 1)
    (o1 : a < b)
    (o2 : b < c)
    (o3 : c < d)
    (o4 : d < e)
    (o5 : e < f)
    (p0 : (2 * b) ≥ c)
    (p1 : ¬ (((2 * b) = (c + 0)) ∨ ((2 * b) = (c + 1)) ∨ ((2 * b) = (c + a)) ∨ ((2 * b) = (c + b)) ∨ ((2 * b) = (c + c))))
    (p2 : (b - a) ≥ (a - 1))
    (hF : f ≤ (b + b))
    (hB : ¬ (((b + b) = (e + 0)) ∨ ((b + b) = (e + 1)) ∨ ((b + b) = (e + a)) ∨ ((b + b) = (e + b)) ∨ ((b + b) = (e + c)) ∨ ((b + b) = (e + d)) ∨ ((b + b) = (e + e))))
    (h10 : ((c + d) < f) ∨ ((c + d) = (f + 0)) ∨ ((c + d) = (f + 1)) ∨ ((c + d) = (f + a)) ∨ ((c + d) = (f + b)) ∨ ((c + d) = (f + c)) ∨ ((c + d) = (f + d)) ∨ ((c + d) = (f + e)) ∨ ((c + d) = (f + f)))
    (h13 : ((d + d) < f) ∨ ((d + d) = (f + 0)) ∨ ((d + d) = (f + 1)) ∨ ((d + d) = (f + a)) ∨ ((d + d) = (f + b)) ∨ ((d + d) = (f + c)) ∨ ((d + d) = (f + d)) ∨ ((d + d) = (f + e)) ∨ ((d + d) = (f + f)))
    (h14 : ((d + e) < f) ∨ ((d + e) = (f + 0)) ∨ ((d + e) = (f + 1)) ∨ ((d + e) = (f + a)) ∨ ((d + e) = (f + b)) ∨ ((d + e) = (f + c)) ∨ ((d + e) = (f + d)) ∨ ((d + e) = (f + e)) ∨ ((d + e) = (f + f)))
    : False := by
  simp only [not_or] at p1
  simp only [not_or] at hB
  rcases h10 with hz2_0 | hz2_1 | hz2_2 | hz2_3 | hz2_4 | hz2_5 | hz2_6 | hz2_7 | hz2_8
  · (clear h13 h14; omega)
  · (clear h13 h14; omega)
  · (clear h13 h14; omega)
  · rcases h13 with hz4_0 | hz4_1 | hz4_2 | hz4_3 | hz4_4 | hz4_5 | hz4_6 | hz4_7 | hz4_8
    · (clear h14; omega)
    · (clear h14; omega)
    · (clear h14; omega)
    · (clear h14; omega)
    · (clear h14; omega)
    · (clear h14; omega)
    · (clear h14; omega)
    · (clear h14; omega)
    · (clear h14; omega)
  · rcases h13 with hz4_0 | hz4_1 | hz4_2 | hz4_3 | hz4_4 | hz4_5 | hz4_6 | hz4_7 | hz4_8
    · (clear h14; omega)
    · (clear h14; omega)
    · (clear h14; omega)
    · (clear h14; omega)
    · (clear h14; omega)
    · rcases h14 with hz6_0 | hz6_1 | hz6_2 | hz6_3 | hz6_4 | hz6_5 | hz6_6 | hz6_7 | hz6_8
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
    · (clear h14; omega)
    · (clear h14; omega)
    · (clear h14; omega)
  · (clear h13 h14; omega)
  · (clear h13 h14; omega)
  · (clear h13 h14; omega)
  · (clear h13 h14; omega)

theorem small5 (a b c d e f : Int)
    (o0 : a > 1)
    (o1 : a < b)
    (o2 : b < c)
    (o3 : c < d)
    (o4 : d < e)
    (o5 : e < f)
    (p0 : (2 * b) ≥ c)
    (p1 : ¬ (((2 * b) = (c + 0)) ∨ ((2 * b) = (c + 1)) ∨ ((2 * b) = (c + a)) ∨ ((2 * b) = (c + b)) ∨ ((2 * b) = (c + c))))
    (p2 : (b - a) ≥ (a - 1))
    (hF : f ≤ (b + c))
    (hB : ¬ (((b + c) = (e + 0)) ∨ ((b + c) = (e + 1)) ∨ ((b + c) = (e + a)) ∨ ((b + c) = (e + b)) ∨ ((b + c) = (e + c)) ∨ ((b + c) = (e + d)) ∨ ((b + c) = (e + e))))
    (h10 : ((c + d) < f) ∨ ((c + d) = (f + 0)) ∨ ((c + d) = (f + 1)) ∨ ((c + d) = (f + a)) ∨ ((c + d) = (f + b)) ∨ ((c + d) = (f + c)) ∨ ((c + d) = (f + d)) ∨ ((c + d) = (f + e)) ∨ ((c + d) = (f + f)))
    (h13 : ((d + d) < f) ∨ ((d + d) = (f + 0)) ∨ ((d + d) = (f + 1)) ∨ ((d + d) = (f + a)) ∨ ((d + d) = (f + b)) ∨ ((d + d) = (f + c)) ∨ ((d + d) = (f + d)) ∨ ((d + d) = (f + e)) ∨ ((d + d) = (f + f)))
    (h14 : ((d + e) < f) ∨ ((d + e) = (f + 0)) ∨ ((d + e) = (f + 1)) ∨ ((d + e) = (f + a)) ∨ ((d + e) = (f + b)) ∨ ((d + e) = (f + c)) ∨ ((d + e) = (f + d)) ∨ ((d + e) = (f + e)) ∨ ((d + e) = (f + f)))
    (h15 : ((e + e) < f) ∨ ((e + e) = (f + 0)) ∨ ((e + e) = (f + 1)) ∨ ((e + e) = (f + a)) ∨ ((e + e) = (f + b)) ∨ ((e + e) = (f + c)) ∨ ((e + e) = (f + d)) ∨ ((e + e) = (f + e)) ∨ ((e + e) = (f + f)))
    : False := by
  simp only [not_or] at p1
  simp only [not_or] at hB
  rcases h10 with hz2_0 | hz2_1 | hz2_2 | hz2_3 | hz2_4 | hz2_5 | hz2_6 | hz2_7 | hz2_8
  · (clear h13 h14 h15; omega)
  · (clear h13 h14 h15; omega)
  · (clear h13 h14 h15; omega)
  · rcases h13 with hz4_0 | hz4_1 | hz4_2 | hz4_3 | hz4_4 | hz4_5 | hz4_6 | hz4_7 | hz4_8
    · (clear h14 h15; omega)
    · (clear h14 h15; omega)
    · (clear h14 h15; omega)
    · (clear h14 h15; omega)
    · rcases h14 with hz6_0 | hz6_1 | hz6_2 | hz6_3 | hz6_4 | hz6_5 | hz6_6 | hz6_7 | hz6_8
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · rcases h15 with hz8_0 | hz8_1 | hz8_2 | hz8_3 | hz8_4 | hz8_5 | hz8_6 | hz8_7 | hz8_8
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
    · (clear h14 h15; omega)
    · (clear h14 h15; omega)
    · (clear h14 h15; omega)
    · (clear h14 h15; omega)
  · rcases h13 with hz4_0 | hz4_1 | hz4_2 | hz4_3 | hz4_4 | hz4_5 | hz4_6 | hz4_7 | hz4_8
    · (clear h14 h15; omega)
    · (clear h14 h15; omega)
    · (clear h14 h15; omega)
    · (clear h14 h15; omega)
    · (clear h14 h15; omega)
    · rcases h14 with hz6_0 | hz6_1 | hz6_2 | hz6_3 | hz6_4 | hz6_5 | hz6_6 | hz6_7 | hz6_8
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
    · (clear h14 h15; omega)
    · (clear h14 h15; omega)
    · (clear h14 h15; omega)
  · (clear h13 h14 h15; omega)
  · (clear h13 h14 h15; omega)
  · (clear h13 h14 h15; omega)
  · (clear h13 h14 h15; omega)

theorem small6 (a b c d e f : Int)
    (o0 : a > 1)
    (o1 : a < b)
    (o2 : b < c)
    (o3 : c < d)
    (o4 : d < e)
    (o5 : e < f)
    (p0 : (2 * b) ≥ c)
    (p1 : ¬ (((2 * b) = (c + 0)) ∨ ((2 * b) = (c + 1)) ∨ ((2 * b) = (c + a)) ∨ ((2 * b) = (c + b)) ∨ ((2 * b) = (c + c))))
    (p2 : (b - a) ≥ (a - 1))
    (hF : f ≤ (b + d))
    (hB : ¬ (((b + d) = (e + 0)) ∨ ((b + d) = (e + 1)) ∨ ((b + d) = (e + a)) ∨ ((b + d) = (e + b)) ∨ ((b + d) = (e + c)) ∨ ((b + d) = (e + d)) ∨ ((b + d) = (e + e))))
    (h10 : ((c + d) < f) ∨ ((c + d) = (f + 0)) ∨ ((c + d) = (f + 1)) ∨ ((c + d) = (f + a)) ∨ ((c + d) = (f + b)) ∨ ((c + d) = (f + c)) ∨ ((c + d) = (f + d)) ∨ ((c + d) = (f + e)) ∨ ((c + d) = (f + f)))
    (h13 : ((d + d) < f) ∨ ((d + d) = (f + 0)) ∨ ((d + d) = (f + 1)) ∨ ((d + d) = (f + a)) ∨ ((d + d) = (f + b)) ∨ ((d + d) = (f + c)) ∨ ((d + d) = (f + d)) ∨ ((d + d) = (f + e)) ∨ ((d + d) = (f + f)))
    (h14 : ((d + e) < f) ∨ ((d + e) = (f + 0)) ∨ ((d + e) = (f + 1)) ∨ ((d + e) = (f + a)) ∨ ((d + e) = (f + b)) ∨ ((d + e) = (f + c)) ∨ ((d + e) = (f + d)) ∨ ((d + e) = (f + e)) ∨ ((d + e) = (f + f)))
    (h15 : ((e + e) < f) ∨ ((e + e) = (f + 0)) ∨ ((e + e) = (f + 1)) ∨ ((e + e) = (f + a)) ∨ ((e + e) = (f + b)) ∨ ((e + e) = (f + c)) ∨ ((e + e) = (f + d)) ∨ ((e + e) = (f + e)) ∨ ((e + e) = (f + f)))
    : False := by
  simp only [not_or] at p1
  simp only [not_or] at hB
  rcases h10 with hz2_0 | hz2_1 | hz2_2 | hz2_3 | hz2_4 | hz2_5 | hz2_6 | hz2_7 | hz2_8
  · (clear h13 h14 h15; omega)
  · (clear h13 h14 h15; omega)
  · rcases h13 with hz4_0 | hz4_1 | hz4_2 | hz4_3 | hz4_4 | hz4_5 | hz4_6 | hz4_7 | hz4_8
    · (clear h14 h15; omega)
    · (clear h14 h15; omega)
    · (clear h14 h15; omega)
    · rcases h14 with hz6_0 | hz6_1 | hz6_2 | hz6_3 | hz6_4 | hz6_5 | hz6_6 | hz6_7 | hz6_8
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · rcases h15 with hz8_0 | hz8_1 | hz8_2 | hz8_3 | hz8_4 | hz8_5 | hz8_6 | hz8_7 | hz8_8
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
    · rcases h14 with hz6_0 | hz6_1 | hz6_2 | hz6_3 | hz6_4 | hz6_5 | hz6_6 | hz6_7 | hz6_8
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · rcases h15 with hz8_0 | hz8_1 | hz8_2 | hz8_3 | hz8_4 | hz8_5 | hz8_6 | hz8_7 | hz8_8
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
    · rcases h14 with hz6_0 | hz6_1 | hz6_2 | hz6_3 | hz6_4 | hz6_5 | hz6_6 | hz6_7 | hz6_8
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
    · (clear h14 h15; omega)
    · (clear h14 h15; omega)
    · (clear h14 h15; omega)
  · rcases h13 with hz4_0 | hz4_1 | hz4_2 | hz4_3 | hz4_4 | hz4_5 | hz4_6 | hz4_7 | hz4_8
    · (clear h14 h15; omega)
    · (clear h14 h15; omega)
    · (clear h14 h15; omega)
    · (clear h14 h15; omega)
    · rcases h14 with hz6_0 | hz6_1 | hz6_2 | hz6_3 | hz6_4 | hz6_5 | hz6_6 | hz6_7 | hz6_8
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · rcases h15 with hz8_0 | hz8_1 | hz8_2 | hz8_3 | hz8_4 | hz8_5 | hz8_6 | hz8_7 | hz8_8
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
    · rcases h14 with hz6_0 | hz6_1 | hz6_2 | hz6_3 | hz6_4 | hz6_5 | hz6_6 | hz6_7 | hz6_8
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
    · (clear h14 h15; omega)
    · (clear h14 h15; omega)
    · (clear h14 h15; omega)
  · rcases h13 with hz4_0 | hz4_1 | hz4_2 | hz4_3 | hz4_4 | hz4_5 | hz4_6 | hz4_7 | hz4_8
    · (clear h14 h15; omega)
    · (clear h14 h15; omega)
    · (clear h14 h15; omega)
    · (clear h14 h15; omega)
    · (clear h14 h15; omega)
    · rcases h14 with hz6_0 | hz6_1 | hz6_2 | hz6_3 | hz6_4 | hz6_5 | hz6_6 | hz6_7 | hz6_8
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
    · (clear h14 h15; omega)
    · (clear h14 h15; omega)
    · (clear h14 h15; omega)
  · (clear h13 h14 h15; omega)
  · (clear h13 h14 h15; omega)
  · (clear h13 h14 h15; omega)
  · (clear h13 h14 h15; omega)

theorem small7 (a b c d e f : Int)
    (o0 : a > 1)
    (o1 : a < b)
    (o2 : b < c)
    (o3 : c < d)
    (o4 : d < e)
    (o5 : e < f)
    (p0 : (2 * b) ≥ c)
    (p1 : ¬ (((2 * b) = (c + 0)) ∨ ((2 * b) = (c + 1)) ∨ ((2 * b) = (c + a)) ∨ ((2 * b) = (c + b)) ∨ ((2 * b) = (c + c))))
    (p2 : (b - a) ≥ (a - 1))
    (hF : f ≤ (c + c))
    (hB : ¬ (((c + c) = (e + 0)) ∨ ((c + c) = (e + 1)) ∨ ((c + c) = (e + a)) ∨ ((c + c) = (e + b)) ∨ ((c + c) = (e + c)) ∨ ((c + c) = (e + d)) ∨ ((c + c) = (e + e))))
    (h10 : ((c + d) < f) ∨ ((c + d) = (f + 0)) ∨ ((c + d) = (f + 1)) ∨ ((c + d) = (f + a)) ∨ ((c + d) = (f + b)) ∨ ((c + d) = (f + c)) ∨ ((c + d) = (f + d)) ∨ ((c + d) = (f + e)) ∨ ((c + d) = (f + f)))
    (h11 : ((c + e) < f) ∨ ((c + e) = (f + 0)) ∨ ((c + e) = (f + 1)) ∨ ((c + e) = (f + a)) ∨ ((c + e) = (f + b)) ∨ ((c + e) = (f + c)) ∨ ((c + e) = (f + d)) ∨ ((c + e) = (f + e)) ∨ ((c + e) = (f + f)))
    (h14 : ((d + e) < f) ∨ ((d + e) = (f + 0)) ∨ ((d + e) = (f + 1)) ∨ ((d + e) = (f + a)) ∨ ((d + e) = (f + b)) ∨ ((d + e) = (f + c)) ∨ ((d + e) = (f + d)) ∨ ((d + e) = (f + e)) ∨ ((d + e) = (f + f)))
    : False := by
  simp only [not_or] at p1
  simp only [not_or] at hB
  rcases h11 with hz2_0 | hz2_1 | hz2_2 | hz2_3 | hz2_4 | hz2_5 | hz2_6 | hz2_7 | hz2_8
  · (clear h10 h14; omega)
  · (clear h10 h14; omega)
  · (clear h10 h14; omega)
  · rcases h10 with hz4_0 | hz4_1 | hz4_2 | hz4_3 | hz4_4 | hz4_5 | hz4_6 | hz4_7 | hz4_8
    · (clear h14; omega)
    · (clear h14; omega)
    · rcases h14 with hz6_0 | hz6_1 | hz6_2 | hz6_3 | hz6_4 | hz6_5 | hz6_6 | hz6_7 | hz6_8
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
    · (clear h14; omega)
    · (clear h14; omega)
    · (clear h14; omega)
    · (clear h14; omega)
    · (clear h14; omega)
    · (clear h14; omega)
  · rcases h14 with hz4_0 | hz4_1 | hz4_2 | hz4_3 | hz4_4 | hz4_5 | hz4_6 | hz4_7 | hz4_8
    · (clear h10; omega)
    · (clear h10; omega)
    · (clear h10; omega)
    · (clear h10; omega)
    · (clear h10; omega)
    · rcases h10 with hz6_0 | hz6_1 | hz6_2 | hz6_3 | hz6_4 | hz6_5 | hz6_6 | hz6_7 | hz6_8
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
    · (clear h10; omega)
    · (clear h10; omega)
    · (clear h10; omega)
  · (clear h10 h14; omega)
  · (clear h10 h14; omega)
  · (clear h10 h14; omega)
  · (clear h10 h14; omega)

theorem small8 (a b c d e f : Int)
    (o0 : a > 1)
    (o1 : a < b)
    (o2 : b < c)
    (o3 : c < d)
    (o4 : d < e)
    (o5 : e < f)
    (p0 : (2 * b) ≥ c)
    (p1 : ¬ (((2 * b) = (c + 0)) ∨ ((2 * b) = (c + 1)) ∨ ((2 * b) = (c + a)) ∨ ((2 * b) = (c + b)) ∨ ((2 * b) = (c + c))))
    (p2 : (b - a) ≥ (a - 1))
    (hF : f ≤ (c + d))
    (hB : ¬ (((c + d) = (e + 0)) ∨ ((c + d) = (e + 1)) ∨ ((c + d) = (e + a)) ∨ ((c + d) = (e + b)) ∨ ((c + d) = (e + c)) ∨ ((c + d) = (e + d)) ∨ ((c + d) = (e + e))))
    (h11 : ((c + e) < f) ∨ ((c + e) = (f + 0)) ∨ ((c + e) = (f + 1)) ∨ ((c + e) = (f + a)) ∨ ((c + e) = (f + b)) ∨ ((c + e) = (f + c)) ∨ ((c + e) = (f + d)) ∨ ((c + e) = (f + e)) ∨ ((c + e) = (f + f)))
    (h14 : ((d + e) < f) ∨ ((d + e) = (f + 0)) ∨ ((d + e) = (f + 1)) ∨ ((d + e) = (f + a)) ∨ ((d + e) = (f + b)) ∨ ((d + e) = (f + c)) ∨ ((d + e) = (f + d)) ∨ ((d + e) = (f + e)) ∨ ((d + e) = (f + f)))
    (h15 : ((e + e) < f) ∨ ((e + e) = (f + 0)) ∨ ((e + e) = (f + 1)) ∨ ((e + e) = (f + a)) ∨ ((e + e) = (f + b)) ∨ ((e + e) = (f + c)) ∨ ((e + e) = (f + d)) ∨ ((e + e) = (f + e)) ∨ ((e + e) = (f + f)))
    : False := by
  simp only [not_or] at p1
  simp only [not_or] at hB
  rcases h11 with hz2_0 | hz2_1 | hz2_2 | hz2_3 | hz2_4 | hz2_5 | hz2_6 | hz2_7 | hz2_8
  · (clear h14 h15; omega)
  · (clear h14 h15; omega)
  · rcases h14 with hz4_0 | hz4_1 | hz4_2 | hz4_3 | hz4_4 | hz4_5 | hz4_6 | hz4_7 | hz4_8
    · (clear h15; omega)
    · (clear h15; omega)
    · (clear h15; omega)
    · rcases h15 with hz6_0 | hz6_1 | hz6_2 | hz6_3 | hz6_4 | hz6_5 | hz6_6 | hz6_7 | hz6_8
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
    · rcases h15 with hz6_0 | hz6_1 | hz6_2 | hz6_3 | hz6_4 | hz6_5 | hz6_6 | hz6_7 | hz6_8
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
    · rcases h15 with hz6_0 | hz6_1 | hz6_2 | hz6_3 | hz6_4 | hz6_5 | hz6_6 | hz6_7 | hz6_8
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
    · (clear h15; omega)
    · (clear h15; omega)
    · (clear h15; omega)
  · rcases h14 with hz4_0 | hz4_1 | hz4_2 | hz4_3 | hz4_4 | hz4_5 | hz4_6 | hz4_7 | hz4_8
    · (clear h15; omega)
    · (clear h15; omega)
    · (clear h15; omega)
    · (clear h15; omega)
    · rcases h15 with hz6_0 | hz6_1 | hz6_2 | hz6_3 | hz6_4 | hz6_5 | hz6_6 | hz6_7 | hz6_8
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
    · rcases h15 with hz6_0 | hz6_1 | hz6_2 | hz6_3 | hz6_4 | hz6_5 | hz6_6 | hz6_7 | hz6_8
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
    · (clear h15; omega)
    · (clear h15; omega)
    · (clear h15; omega)
  · rcases h14 with hz4_0 | hz4_1 | hz4_2 | hz4_3 | hz4_4 | hz4_5 | hz4_6 | hz4_7 | hz4_8
    · (clear h15; omega)
    · (clear h15; omega)
    · (clear h15; omega)
    · (clear h15; omega)
    · (clear h15; omega)
    · rcases h15 with hz6_0 | hz6_1 | hz6_2 | hz6_3 | hz6_4 | hz6_5 | hz6_6 | hz6_7 | hz6_8
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
    · (clear h15; omega)
    · (clear h15; omega)
    · (clear h15; omega)
  · (clear h14 h15; omega)
  · (clear h14 h15; omega)
  · (clear h14 h15; omega)
  · (clear h14 h15; omega)

theorem small9 (a b c d e f : Int)
    (o0 : a > 1)
    (o1 : a < b)
    (o2 : b < c)
    (o3 : c < d)
    (o4 : d < e)
    (o5 : e < f)
    (p0 : (2 * b) ≥ c)
    (p1 : ¬ (((2 * b) = (c + 0)) ∨ ((2 * b) = (c + 1)) ∨ ((2 * b) = (c + a)) ∨ ((2 * b) = (c + b)) ∨ ((2 * b) = (c + c))))
    (p2 : (b - a) ≥ (a - 1))
    (hF : f ≤ (d + d))
    (hB : ¬ (((d + d) = (e + 0)) ∨ ((d + d) = (e + 1)) ∨ ((d + d) = (e + a)) ∨ ((d + d) = (e + b)) ∨ ((d + d) = (e + c)) ∨ ((d + d) = (e + d)) ∨ ((d + d) = (e + e))))
    (h4 : ((b + d) < e) ∨ (f ≤ (b + d)) ∨ ((b + d) = (e + 0)) ∨ ((b + d) = (e + 1)) ∨ ((b + d) = (e + a)) ∨ ((b + d) = (e + b)) ∨ ((b + d) = (e + c)) ∨ ((b + d) = (e + d)) ∨ ((b + d) = (e + e)))
    (h9 : ((c + d) < e) ∨ (f ≤ (c + d)) ∨ ((c + d) = (e + 0)) ∨ ((c + d) = (e + 1)) ∨ ((c + d) = (e + a)) ∨ ((c + d) = (e + b)) ∨ ((c + d) = (e + c)) ∨ ((c + d) = (e + d)) ∨ ((c + d) = (e + e)))
    (h11 : ((c + e) < f) ∨ ((c + e) = (f + 0)) ∨ ((c + e) = (f + 1)) ∨ ((c + e) = (f + a)) ∨ ((c + e) = (f + b)) ∨ ((c + e) = (f + c)) ∨ ((c + e) = (f + d)) ∨ ((c + e) = (f + e)) ∨ ((c + e) = (f + f)))
    (h13 : ((d + d) < f) ∨ ((d + d) = (f + 0)) ∨ ((d + d) = (f + 1)) ∨ ((d + d) = (f + a)) ∨ ((d + d) = (f + b)) ∨ ((d + d) = (f + c)) ∨ ((d + d) = (f + d)) ∨ ((d + d) = (f + e)) ∨ ((d + d) = (f + f)))
    (h14 : ((d + e) < f) ∨ ((d + e) = (f + 0)) ∨ ((d + e) = (f + 1)) ∨ ((d + e) = (f + a)) ∨ ((d + e) = (f + b)) ∨ ((d + e) = (f + c)) ∨ ((d + e) = (f + d)) ∨ ((d + e) = (f + e)) ∨ ((d + e) = (f + f)))
    (h15 : ((e + e) < f) ∨ ((e + e) = (f + 0)) ∨ ((e + e) = (f + 1)) ∨ ((e + e) = (f + a)) ∨ ((e + e) = (f + b)) ∨ ((e + e) = (f + c)) ∨ ((e + e) = (f + d)) ∨ ((e + e) = (f + e)) ∨ ((e + e) = (f + f)))
    : False := by
  simp only [not_or] at p1
  simp only [not_or] at hB
  rcases h14 with hz2_0 | hz2_1 | hz2_2 | hz2_3 | hz2_4 | hz2_5 | hz2_6 | hz2_7 | hz2_8
  · (clear h4 h9 h11 h13 h15; omega)
  · (clear h4 h9 h11 h13 h15; omega)
  · rcases h4 with hz4_0 | hz4_1 | hz4_2 | hz4_3 | hz4_4 | hz4_5 | hz4_6 | hz4_7 | hz4_8
    · (clear h9 h11 h13 h15; omega)
    · (clear h9 h11 h13 h15; omega)
    · (clear h9 h11 h13 h15; omega)
    · (clear h9 h11 h13 h15; omega)
    · (clear h9 h11 h13 h15; omega)
    · (clear h9 h11 h13 h15; omega)
    · (clear h9 h11 h13 h15; omega)
    · (clear h9 h11 h13 h15; omega)
    · (clear h9 h11 h13 h15; omega)
  · rcases h13 with hz4_0 | hz4_1 | hz4_2 | hz4_3 | hz4_4 | hz4_5 | hz4_6 | hz4_7 | hz4_8
    · (clear h4 h9 h11 h15; omega)
    · rcases h4 with hz6_0 | hz6_1 | hz6_2 | hz6_3 | hz6_4 | hz6_5 | hz6_6 | hz6_7 | hz6_8
      · (clear h9 h11 h15; omega)
      · (clear h9 h11 h15; omega)
      · (clear h9 h11 h15; omega)
      · (clear h9 h11 h15; omega)
      · rcases h9 with hz8_0 | hz8_1 | hz8_2 | hz8_3 | hz8_4 | hz8_5 | hz8_6 | hz8_7 | hz8_8
        · (clear h11 h15; omega)
        · (clear h11 h15; omega)
        · (clear h11 h15; omega)
        · (clear h11 h15; omega)
        · (clear h11 h15; omega)
        · (clear h11 h15; omega)
        · (clear h11 h15; omega)
        · (clear h11 h15; omega)
        · (clear h11 h15; omega)
      · (clear h9 h11 h15; omega)
      · (clear h9 h11 h15; omega)
      · (clear h9 h11 h15; omega)
      · (clear h9 h11 h15; omega)
    · rcases h15 with hz6_0 | hz6_1 | hz6_2 | hz6_3 | hz6_4 | hz6_5 | hz6_6 | hz6_7 | hz6_8
      · (clear h4 h9 h11; omega)
      · (clear h4 h9 h11; omega)
      · (clear h4 h9 h11; omega)
      · (clear h4 h9 h11; omega)
      · rcases h4 with hz8_0 | hz8_1 | hz8_2 | hz8_3 | hz8_4 | hz8_5 | hz8_6 | hz8_7 | hz8_8
        · (clear h9 h11; omega)
        · (clear h9 h11; omega)
        · (clear h9 h11; omega)
        · (clear h9 h11; omega)
        · rcases h9 with hz10_0 | hz10_1 | hz10_2 | hz10_3 | hz10_4 | hz10_5 | hz10_6 | hz10_7 | hz10_8
          · (clear h11; omega)
          · rcases h11 with hz12_0 | hz12_1 | hz12_2 | hz12_3 | hz12_4 | hz12_5 | hz12_6 | hz12_7 | hz12_8
            · omega
            · omega
            · omega
            · omega
            · omega
            · omega
            · omega
            · omega
            · omega
          · (clear h11; omega)
          · (clear h11; omega)
          · (clear h11; omega)
          · (clear h11; omega)
          · (clear h11; omega)
          · (clear h11; omega)
          · (clear h11; omega)
        · (clear h9 h11; omega)
        · (clear h9 h11; omega)
        · (clear h9 h11; omega)
        · (clear h9 h11; omega)
      · (clear h4 h9 h11; omega)
      · (clear h4 h9 h11; omega)
      · (clear h4 h9 h11; omega)
      · (clear h4 h9 h11; omega)
    · (clear h4 h9 h11 h15; omega)
    · (clear h4 h9 h11 h15; omega)
    · (clear h4 h9 h11 h15; omega)
    · (clear h4 h9 h11 h15; omega)
    · (clear h4 h9 h11 h15; omega)
    · (clear h4 h9 h11 h15; omega)
  · rcases h15 with hz4_0 | hz4_1 | hz4_2 | hz4_3 | hz4_4 | hz4_5 | hz4_6 | hz4_7 | hz4_8
    · (clear h4 h9 h11 h13; omega)
    · (clear h4 h9 h11 h13; omega)
    · (clear h4 h9 h11 h13; omega)
    · (clear h4 h9 h11 h13; omega)
    · (clear h4 h9 h11 h13; omega)
    · rcases h13 with hz6_0 | hz6_1 | hz6_2 | hz6_3 | hz6_4 | hz6_5 | hz6_6 | hz6_7 | hz6_8
      · (clear h4 h9 h11; omega)
      · (clear h4 h9 h11; omega)
      · (clear h4 h9 h11; omega)
      · (clear h4 h9 h11; omega)
      · (clear h4 h9 h11; omega)
      · (clear h4 h9 h11; omega)
      · (clear h4 h9 h11; omega)
      · (clear h4 h9 h11; omega)
      · (clear h4 h9 h11; omega)
    · (clear h4 h9 h11 h13; omega)
    · (clear h4 h9 h11 h13; omega)
    · (clear h4 h9 h11 h13; omega)
  · rcases h15 with hz4_0 | hz4_1 | hz4_2 | hz4_3 | hz4_4 | hz4_5 | hz4_6 | hz4_7 | hz4_8
    · (clear h4 h9 h11 h13; omega)
    · (clear h4 h9 h11 h13; omega)
    · (clear h4 h9 h11 h13; omega)
    · (clear h4 h9 h11 h13; omega)
    · (clear h4 h9 h11 h13; omega)
    · (clear h4 h9 h11 h13; omega)
    · (clear h4 h9 h11 h13; omega)
    · (clear h4 h9 h11 h13; omega)
    · (clear h4 h9 h11 h13; omega)
  · (clear h4 h9 h11 h13 h15; omega)
  · (clear h4 h9 h11 h13 h15; omega)
  · (clear h4 h9 h11 h13 h15; omega)

theorem large0 (a b c d e f : Int)
    (o0 : a > 1)
    (o1 : a < b)
    (o2 : b < c)
    (o3 : c < d)
    (o4 : d < e)
    (o5 : e < f)
    (p0 : (2 * b) < c)
    (hF : f ≤ (a + a))
    (hB : ¬ (((a + a) = (e + 0)) ∨ ((a + a) = (e + 1)) ∨ ((a + a) = (e + a)) ∨ ((a + a) = (e + b)) ∨ ((a + a) = (e + c)) ∨ ((a + a) = (e + d)) ∨ ((a + a) = (e + e))))
    : False := by
  simp only [not_or] at hB
  omega

theorem large1 (a b c d e f : Int)
    (o0 : a > 1)
    (o1 : a < b)
    (o2 : b < c)
    (o3 : c < d)
    (o4 : d < e)
    (o5 : e < f)
    (p0 : (2 * b) < c)
    (hF : f ≤ (a + b))
    (hB : ¬ (((a + b) = (e + 0)) ∨ ((a + b) = (e + 1)) ∨ ((a + b) = (e + a)) ∨ ((a + b) = (e + b)) ∨ ((a + b) = (e + c)) ∨ ((a + b) = (e + d)) ∨ ((a + b) = (e + e))))
    : False := by
  simp only [not_or] at hB
  omega

theorem large2 (a b c d e f : Int)
    (o0 : a > 1)
    (o1 : a < b)
    (o2 : b < c)
    (o3 : c < d)
    (o4 : d < e)
    (o5 : e < f)
    (p0 : (2 * b) < c)
    (hF : f ≤ (a + c))
    (hB : ¬ (((a + c) = (e + 0)) ∨ ((a + c) = (e + 1)) ∨ ((a + c) = (e + a)) ∨ ((a + c) = (e + b)) ∨ ((a + c) = (e + c)) ∨ ((a + c) = (e + d)) ∨ ((a + c) = (e + e))))
    (h13 : ((d + d) < f) ∨ ((d + d) = (f + 0)) ∨ ((d + d) = (f + 1)) ∨ ((d + d) = (f + a)) ∨ ((d + d) = (f + b)) ∨ ((d + d) = (f + c)) ∨ ((d + d) = (f + d)) ∨ ((d + d) = (f + e)) ∨ ((d + d) = (f + f)))
    (h14 : ((d + e) < f) ∨ ((d + e) = (f + 0)) ∨ ((d + e) = (f + 1)) ∨ ((d + e) = (f + a)) ∨ ((d + e) = (f + b)) ∨ ((d + e) = (f + c)) ∨ ((d + e) = (f + d)) ∨ ((d + e) = (f + e)) ∨ ((d + e) = (f + f)))
    : False := by
  simp only [not_or] at hB
  rcases h13 with hz2_0 | hz2_1 | hz2_2 | hz2_3 | hz2_4 | hz2_5 | hz2_6 | hz2_7 | hz2_8
  · (clear h14; omega)
  · (clear h14; omega)
  · (clear h14; omega)
  · (clear h14; omega)
  · (clear h14; omega)
  · rcases h14 with hz4_0 | hz4_1 | hz4_2 | hz4_3 | hz4_4 | hz4_5 | hz4_6 | hz4_7 | hz4_8
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  · (clear h14; omega)
  · (clear h14; omega)
  · (clear h14; omega)

theorem large3 (a b c d e f : Int)
    (o0 : a > 1)
    (o1 : a < b)
    (o2 : b < c)
    (o3 : c < d)
    (o4 : d < e)
    (o5 : e < f)
    (p0 : (2 * b) < c)
    (hF : f ≤ (a + d))
    (hB : ¬ (((a + d) = (e + 0)) ∨ ((a + d) = (e + 1)) ∨ ((a + d) = (e + a)) ∨ ((a + d) = (e + b)) ∨ ((a + d) = (e + c)) ∨ ((a + d) = (e + d)) ∨ ((a + d) = (e + e))))
    (h13 : ((d + d) < f) ∨ ((d + d) = (f + 0)) ∨ ((d + d) = (f + 1)) ∨ ((d + d) = (f + a)) ∨ ((d + d) = (f + b)) ∨ ((d + d) = (f + c)) ∨ ((d + d) = (f + d)) ∨ ((d + d) = (f + e)) ∨ ((d + d) = (f + f)))
    (h14 : ((d + e) < f) ∨ ((d + e) = (f + 0)) ∨ ((d + e) = (f + 1)) ∨ ((d + e) = (f + a)) ∨ ((d + e) = (f + b)) ∨ ((d + e) = (f + c)) ∨ ((d + e) = (f + d)) ∨ ((d + e) = (f + e)) ∨ ((d + e) = (f + f)))
    : False := by
  simp only [not_or] at hB
  rcases h13 with hz2_0 | hz2_1 | hz2_2 | hz2_3 | hz2_4 | hz2_5 | hz2_6 | hz2_7 | hz2_8
  · (clear h14; omega)
  · (clear h14; omega)
  · (clear h14; omega)
  · (clear h14; omega)
  · (clear h14; omega)
  · rcases h14 with hz4_0 | hz4_1 | hz4_2 | hz4_3 | hz4_4 | hz4_5 | hz4_6 | hz4_7 | hz4_8
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  · (clear h14; omega)
  · (clear h14; omega)
  · (clear h14; omega)

theorem large4 (a b c d e f : Int)
    (o0 : a > 1)
    (o1 : a < b)
    (o2 : b < c)
    (o3 : c < d)
    (o4 : d < e)
    (o5 : e < f)
    (p0 : (2 * b) < c)
    (hF : f ≤ (b + b))
    (hB : ¬ (((b + b) = (e + 0)) ∨ ((b + b) = (e + 1)) ∨ ((b + b) = (e + a)) ∨ ((b + b) = (e + b)) ∨ ((b + b) = (e + c)) ∨ ((b + b) = (e + d)) ∨ ((b + b) = (e + e))))
    : False := by
  simp only [not_or] at hB
  omega

theorem large5 (a b c d e f : Int)
    (o0 : a > 1)
    (o1 : a < b)
    (o2 : b < c)
    (o3 : c < d)
    (o4 : d < e)
    (o5 : e < f)
    (p0 : (2 * b) < c)
    (hF : f ≤ (b + c))
    (hB : ¬ (((b + c) = (e + 0)) ∨ ((b + c) = (e + 1)) ∨ ((b + c) = (e + a)) ∨ ((b + c) = (e + b)) ∨ ((b + c) = (e + c)) ∨ ((b + c) = (e + d)) ∨ ((b + c) = (e + e))))
    (h13 : ((d + d) < f) ∨ ((d + d) = (f + 0)) ∨ ((d + d) = (f + 1)) ∨ ((d + d) = (f + a)) ∨ ((d + d) = (f + b)) ∨ ((d + d) = (f + c)) ∨ ((d + d) = (f + d)) ∨ ((d + d) = (f + e)) ∨ ((d + d) = (f + f)))
    (h14 : ((d + e) < f) ∨ ((d + e) = (f + 0)) ∨ ((d + e) = (f + 1)) ∨ ((d + e) = (f + a)) ∨ ((d + e) = (f + b)) ∨ ((d + e) = (f + c)) ∨ ((d + e) = (f + d)) ∨ ((d + e) = (f + e)) ∨ ((d + e) = (f + f)))
    : False := by
  simp only [not_or] at hB
  rcases h13 with hz2_0 | hz2_1 | hz2_2 | hz2_3 | hz2_4 | hz2_5 | hz2_6 | hz2_7 | hz2_8
  · (clear h14; omega)
  · (clear h14; omega)
  · (clear h14; omega)
  · (clear h14; omega)
  · (clear h14; omega)
  · rcases h14 with hz4_0 | hz4_1 | hz4_2 | hz4_3 | hz4_4 | hz4_5 | hz4_6 | hz4_7 | hz4_8
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  · (clear h14; omega)
  · (clear h14; omega)
  · (clear h14; omega)

theorem large6 (a b c d e f : Int)
    (o0 : a > 1)
    (o1 : a < b)
    (o2 : b < c)
    (o3 : c < d)
    (o4 : d < e)
    (o5 : e < f)
    (p0 : (2 * b) < c)
    (hF : f ≤ (b + d))
    (hB : ¬ (((b + d) = (e + 0)) ∨ ((b + d) = (e + 1)) ∨ ((b + d) = (e + a)) ∨ ((b + d) = (e + b)) ∨ ((b + d) = (e + c)) ∨ ((b + d) = (e + d)) ∨ ((b + d) = (e + e))))
    (h13 : ((d + d) < f) ∨ ((d + d) = (f + 0)) ∨ ((d + d) = (f + 1)) ∨ ((d + d) = (f + a)) ∨ ((d + d) = (f + b)) ∨ ((d + d) = (f + c)) ∨ ((d + d) = (f + d)) ∨ ((d + d) = (f + e)) ∨ ((d + d) = (f + f)))
    (h14 : ((d + e) < f) ∨ ((d + e) = (f + 0)) ∨ ((d + e) = (f + 1)) ∨ ((d + e) = (f + a)) ∨ ((d + e) = (f + b)) ∨ ((d + e) = (f + c)) ∨ ((d + e) = (f + d)) ∨ ((d + e) = (f + e)) ∨ ((d + e) = (f + f)))
    : False := by
  simp only [not_or] at hB
  rcases h13 with hz2_0 | hz2_1 | hz2_2 | hz2_3 | hz2_4 | hz2_5 | hz2_6 | hz2_7 | hz2_8
  · (clear h14; omega)
  · (clear h14; omega)
  · (clear h14; omega)
  · (clear h14; omega)
  · (clear h14; omega)
  · rcases h14 with hz4_0 | hz4_1 | hz4_2 | hz4_3 | hz4_4 | hz4_5 | hz4_6 | hz4_7 | hz4_8
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  · (clear h14; omega)
  · (clear h14; omega)
  · (clear h14; omega)

theorem large7 (a b c d e f : Int)
    (o0 : a > 1)
    (o1 : a < b)
    (o2 : b < c)
    (o3 : c < d)
    (o4 : d < e)
    (o5 : e < f)
    (p0 : (2 * b) < c)
    (hF : f ≤ (c + c))
    (hB : ¬ (((c + c) = (e + 0)) ∨ ((c + c) = (e + 1)) ∨ ((c + c) = (e + a)) ∨ ((c + c) = (e + b)) ∨ ((c + c) = (e + c)) ∨ ((c + c) = (e + d)) ∨ ((c + c) = (e + e))))
    (h13 : ((d + d) < f) ∨ ((d + d) = (f + 0)) ∨ ((d + d) = (f + 1)) ∨ ((d + d) = (f + a)) ∨ ((d + d) = (f + b)) ∨ ((d + d) = (f + c)) ∨ ((d + d) = (f + d)) ∨ ((d + d) = (f + e)) ∨ ((d + d) = (f + f)))
    (h14 : ((d + e) < f) ∨ ((d + e) = (f + 0)) ∨ ((d + e) = (f + 1)) ∨ ((d + e) = (f + a)) ∨ ((d + e) = (f + b)) ∨ ((d + e) = (f + c)) ∨ ((d + e) = (f + d)) ∨ ((d + e) = (f + e)) ∨ ((d + e) = (f + f)))
    (h15 : ((e + e) < f) ∨ ((e + e) = (f + 0)) ∨ ((e + e) = (f + 1)) ∨ ((e + e) = (f + a)) ∨ ((e + e) = (f + b)) ∨ ((e + e) = (f + c)) ∨ ((e + e) = (f + d)) ∨ ((e + e) = (f + e)) ∨ ((e + e) = (f + f)))
    : False := by
  simp only [not_or] at hB
  rcases h13 with hz2_0 | hz2_1 | hz2_2 | hz2_3 | hz2_4 | hz2_5 | hz2_6 | hz2_7 | hz2_8
  · (clear h14 h15; omega)
  · (clear h14 h15; omega)
  · (clear h14 h15; omega)
  · rcases h14 with hz4_0 | hz4_1 | hz4_2 | hz4_3 | hz4_4 | hz4_5 | hz4_6 | hz4_7 | hz4_8
    · (clear h15; omega)
    · (clear h15; omega)
    · (clear h15; omega)
    · (clear h15; omega)
    · rcases h15 with hz6_0 | hz6_1 | hz6_2 | hz6_3 | hz6_4 | hz6_5 | hz6_6 | hz6_7 | hz6_8
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
    · rcases h15 with hz6_0 | hz6_1 | hz6_2 | hz6_3 | hz6_4 | hz6_5 | hz6_6 | hz6_7 | hz6_8
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
    · (clear h15; omega)
    · (clear h15; omega)
    · (clear h15; omega)
  · rcases h14 with hz4_0 | hz4_1 | hz4_2 | hz4_3 | hz4_4 | hz4_5 | hz4_6 | hz4_7 | hz4_8
    · (clear h15; omega)
    · (clear h15; omega)
    · (clear h15; omega)
    · (clear h15; omega)
    · (clear h15; omega)
    · rcases h15 with hz6_0 | hz6_1 | hz6_2 | hz6_3 | hz6_4 | hz6_5 | hz6_6 | hz6_7 | hz6_8
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
    · (clear h15; omega)
    · (clear h15; omega)
    · (clear h15; omega)
  · rcases h14 with hz4_0 | hz4_1 | hz4_2 | hz4_3 | hz4_4 | hz4_5 | hz4_6 | hz4_7 | hz4_8
    · (clear h15; omega)
    · (clear h15; omega)
    · (clear h15; omega)
    · (clear h15; omega)
    · (clear h15; omega)
    · (clear h15; omega)
    · (clear h15; omega)
    · (clear h15; omega)
    · (clear h15; omega)
  · (clear h14 h15; omega)
  · (clear h14 h15; omega)
  · (clear h14 h15; omega)

theorem large8 (a b c d e f : Int)
    (o0 : a > 1)
    (o1 : a < b)
    (o2 : b < c)
    (o3 : c < d)
    (o4 : d < e)
    (o5 : e < f)
    (p0 : (2 * b) < c)
    (hF : f ≤ (c + d))
    (hB : ¬ (((c + d) = (e + 0)) ∨ ((c + d) = (e + 1)) ∨ ((c + d) = (e + a)) ∨ ((c + d) = (e + b)) ∨ ((c + d) = (e + c)) ∨ ((c + d) = (e + d)) ∨ ((c + d) = (e + e))))
    (h7 : ((c + c) < e) ∨ (f ≤ (c + c)) ∨ ((c + c) = (e + 0)) ∨ ((c + c) = (e + 1)) ∨ ((c + c) = (e + a)) ∨ ((c + c) = (e + b)) ∨ ((c + c) = (e + c)) ∨ ((c + c) = (e + d)) ∨ ((c + c) = (e + e)))
    (h13 : ((d + d) < f) ∨ ((d + d) = (f + 0)) ∨ ((d + d) = (f + 1)) ∨ ((d + d) = (f + a)) ∨ ((d + d) = (f + b)) ∨ ((d + d) = (f + c)) ∨ ((d + d) = (f + d)) ∨ ((d + d) = (f + e)) ∨ ((d + d) = (f + f)))
    (h14 : ((d + e) < f) ∨ ((d + e) = (f + 0)) ∨ ((d + e) = (f + 1)) ∨ ((d + e) = (f + a)) ∨ ((d + e) = (f + b)) ∨ ((d + e) = (f + c)) ∨ ((d + e) = (f + d)) ∨ ((d + e) = (f + e)) ∨ ((d + e) = (f + f)))
    (h15 : ((e + e) < f) ∨ ((e + e) = (f + 0)) ∨ ((e + e) = (f + 1)) ∨ ((e + e) = (f + a)) ∨ ((e + e) = (f + b)) ∨ ((e + e) = (f + c)) ∨ ((e + e) = (f + d)) ∨ ((e + e) = (f + e)) ∨ ((e + e) = (f + f)))
    : False := by
  simp only [not_or] at hB
  rcases h14 with hz2_0 | hz2_1 | hz2_2 | hz2_3 | hz2_4 | hz2_5 | hz2_6 | hz2_7 | hz2_8
  · (clear h7 h13 h15; omega)
  · (clear h7 h13 h15; omega)
  · (clear h7 h13 h15; omega)
  · rcases h13 with hz4_0 | hz4_1 | hz4_2 | hz4_3 | hz4_4 | hz4_5 | hz4_6 | hz4_7 | hz4_8
    · (clear h7 h15; omega)
    · (clear h7 h15; omega)
    · rcases h7 with hz6_0 | hz6_1 | hz6_2 | hz6_3 | hz6_4 | hz6_5 | hz6_6 | hz6_7 | hz6_8
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
      · (clear h15; omega)
    · (clear h7 h15; omega)
    · (clear h7 h15; omega)
    · (clear h7 h15; omega)
    · (clear h7 h15; omega)
    · (clear h7 h15; omega)
    · (clear h7 h15; omega)
  · rcases h15 with hz4_0 | hz4_1 | hz4_2 | hz4_3 | hz4_4 | hz4_5 | hz4_6 | hz4_7 | hz4_8
    · (clear h7 h13; omega)
    · (clear h7 h13; omega)
    · (clear h7 h13; omega)
    · (clear h7 h13; omega)
    · (clear h7 h13; omega)
    · (clear h7 h13; omega)
    · (clear h7 h13; omega)
    · (clear h7 h13; omega)
    · (clear h7 h13; omega)
  · rcases h13 with hz4_0 | hz4_1 | hz4_2 | hz4_3 | hz4_4 | hz4_5 | hz4_6 | hz4_7 | hz4_8
    · (clear h7 h15; omega)
    · (clear h7 h15; omega)
    · (clear h7 h15; omega)
    · (clear h7 h15; omega)
    · (clear h7 h15; omega)
    · (clear h7 h15; omega)
    · (clear h7 h15; omega)
    · (clear h7 h15; omega)
    · (clear h7 h15; omega)
  · (clear h7 h13 h15; omega)
  · (clear h7 h13 h15; omega)
  · (clear h7 h13 h15; omega)

theorem large9 (a b c d e f : Int)
    (o0 : a > 1)
    (o1 : a < b)
    (o2 : b < c)
    (o3 : c < d)
    (o4 : d < e)
    (o5 : e < f)
    (p0 : (2 * b) < c)
    (hF : f ≤ (d + d))
    (hB : ¬ (((d + d) = (e + 0)) ∨ ((d + d) = (e + 1)) ∨ ((d + d) = (e + a)) ∨ ((d + d) = (e + b)) ∨ ((d + d) = (e + c)) ∨ ((d + d) = (e + d)) ∨ ((d + d) = (e + e))))
    (h9 : ((c + d) < e) ∨ (f ≤ (c + d)) ∨ ((c + d) = (e + 0)) ∨ ((c + d) = (e + 1)) ∨ ((c + d) = (e + a)) ∨ ((c + d) = (e + b)) ∨ ((c + d) = (e + c)) ∨ ((c + d) = (e + d)) ∨ ((c + d) = (e + e)))
    (h11 : ((c + e) < f) ∨ ((c + e) = (f + 0)) ∨ ((c + e) = (f + 1)) ∨ ((c + e) = (f + a)) ∨ ((c + e) = (f + b)) ∨ ((c + e) = (f + c)) ∨ ((c + e) = (f + d)) ∨ ((c + e) = (f + e)) ∨ ((c + e) = (f + f)))
    (h13 : ((d + d) < f) ∨ ((d + d) = (f + 0)) ∨ ((d + d) = (f + 1)) ∨ ((d + d) = (f + a)) ∨ ((d + d) = (f + b)) ∨ ((d + d) = (f + c)) ∨ ((d + d) = (f + d)) ∨ ((d + d) = (f + e)) ∨ ((d + d) = (f + f)))
    (h14 : ((d + e) < f) ∨ ((d + e) = (f + 0)) ∨ ((d + e) = (f + 1)) ∨ ((d + e) = (f + a)) ∨ ((d + e) = (f + b)) ∨ ((d + e) = (f + c)) ∨ ((d + e) = (f + d)) ∨ ((d + e) = (f + e)) ∨ ((d + e) = (f + f)))
    (h15 : ((e + e) < f) ∨ ((e + e) = (f + 0)) ∨ ((e + e) = (f + 1)) ∨ ((e + e) = (f + a)) ∨ ((e + e) = (f + b)) ∨ ((e + e) = (f + c)) ∨ ((e + e) = (f + d)) ∨ ((e + e) = (f + e)) ∨ ((e + e) = (f + f)))
    : False := by
  simp only [not_or] at hB
  rcases h14 with hz2_0 | hz2_1 | hz2_2 | hz2_3 | hz2_4 | hz2_5 | hz2_6 | hz2_7 | hz2_8
  · (clear h9 h11 h13 h15; omega)
  · (clear h9 h11 h13 h15; omega)
  · rcases h9 with hz4_0 | hz4_1 | hz4_2 | hz4_3 | hz4_4 | hz4_5 | hz4_6 | hz4_7 | hz4_8
    · (clear h11 h13 h15; omega)
    · (clear h11 h13 h15; omega)
    · (clear h11 h13 h15; omega)
    · (clear h11 h13 h15; omega)
    · (clear h11 h13 h15; omega)
    · (clear h11 h13 h15; omega)
    · (clear h11 h13 h15; omega)
    · (clear h11 h13 h15; omega)
    · (clear h11 h13 h15; omega)
  · rcases h15 with hz4_0 | hz4_1 | hz4_2 | hz4_3 | hz4_4 | hz4_5 | hz4_6 | hz4_7 | hz4_8
    · (clear h9 h11 h13; omega)
    · (clear h9 h11 h13; omega)
    · (clear h9 h11 h13; omega)
    · (clear h9 h11 h13; omega)
    · rcases h9 with hz6_0 | hz6_1 | hz6_2 | hz6_3 | hz6_4 | hz6_5 | hz6_6 | hz6_7 | hz6_8
      · (clear h11 h13; omega)
      · rcases h11 with hz8_0 | hz8_1 | hz8_2 | hz8_3 | hz8_4 | hz8_5 | hz8_6 | hz8_7 | hz8_8
        · (clear h13; omega)
        · (clear h13; omega)
        · rcases h13 with hz10_0 | hz10_1 | hz10_2 | hz10_3 | hz10_4 | hz10_5 | hz10_6 | hz10_7 | hz10_8
          · omega
          · omega
          · omega
          · omega
          · omega
          · omega
          · omega
          · omega
          · omega
        · (clear h13; omega)
        · (clear h13; omega)
        · (clear h13; omega)
        · (clear h13; omega)
        · (clear h13; omega)
        · (clear h13; omega)
      · (clear h11 h13; omega)
      · (clear h11 h13; omega)
      · (clear h11 h13; omega)
      · (clear h11 h13; omega)
      · (clear h11 h13; omega)
      · (clear h11 h13; omega)
      · (clear h11 h13; omega)
    · (clear h9 h11 h13; omega)
    · (clear h9 h11 h13; omega)
    · (clear h9 h11 h13; omega)
    · (clear h9 h11 h13; omega)
  · rcases h15 with hz4_0 | hz4_1 | hz4_2 | hz4_3 | hz4_4 | hz4_5 | hz4_6 | hz4_7 | hz4_8
    · (clear h9 h11 h13; omega)
    · (clear h9 h11 h13; omega)
    · (clear h9 h11 h13; omega)
    · (clear h9 h11 h13; omega)
    · (clear h9 h11 h13; omega)
    · (clear h9 h11 h13; omega)
    · (clear h9 h11 h13; omega)
    · (clear h9 h11 h13; omega)
    · (clear h9 h11 h13; omega)
  · rcases h15 with hz4_0 | hz4_1 | hz4_2 | hz4_3 | hz4_4 | hz4_5 | hz4_6 | hz4_7 | hz4_8
    · (clear h9 h11 h13; omega)
    · (clear h9 h11 h13; omega)
    · (clear h9 h11 h13; omega)
    · (clear h9 h11 h13; omega)
    · (clear h9 h11 h13; omega)
    · (clear h9 h11 h13; omega)
    · (clear h9 h11 h13; omega)
    · (clear h9 h11 h13; omega)
    · (clear h9 h11 h13; omega)
  · (clear h9 h11 h13 h15; omega)
  · (clear h9 h11 h13 h15; omega)
  · (clear h9 h11 h13 h15; omega)

end Coin7Arithmetic
