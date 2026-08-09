/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenPellPowerSplit

/-!
# Archimedean bounds on the positive `X₁(13)` Pell-power cover

The power split

`H + cK = 2 r³⁸`, `cK - H = 2 s³⁸`, and `b = rs`

has a useful strict archimedean consequence.  In the positive chamber, the
degree-`19` Pell numerator lies strictly between `a¹⁹` and
`(a + b)¹⁹ - b¹⁹`.  Consequently

`s < r` and `a < r² < a + b`.

These inequalities are checked directly from the displayed coefficients of
the Pell numerator.  They do not assert that the remaining integral cover is
empty.
-/

namespace MazurTorsion.XOneThirteenDescent

/-- In the positive chamber, the homogeneous Pell numerator is strictly
larger than its leading monomial. -/
theorem left_power_lt_pellHHomogeneous
    (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    a ^ 19 < pellHHomogeneous a b := by
  by_cases hab : a ≤ b
  · have hcoefficient : 0 < 2 * b ^ 2 - a ^ 2 := by
      have hsquare : 0 ≤ b ^ 2 - a ^ 2 := by
        have hmul : 0 ≤ (b - a) * (b + a) :=
          mul_nonneg (sub_nonneg.mpr hab) (add_nonneg hb.le ha.le)
        nlinarith
      nlinarith [sq_pos_of_pos hb]
    have hpair :
        0 < 4 * a * b ^ 18 - 2 * a ^ 3 * b ^ 16 := by
      rw [show 4 * a * b ^ 18 - 2 * a ^ 3 * b ^ 16 =
        2 * a * b ^ 16 * (2 * b ^ 2 - a ^ 2) by ring]
      positivity
    rw [← sub_pos]
    rw [show pellHHomogeneous a b - a ^ 19 =
      (4 * a * b ^ 18 - 2 * a ^ 3 * b ^ 16) +
        (3 * a ^ 18 * b + 2 * a ^ 17 * b ^ 2 +
          5 * a ^ 16 * b ^ 3 + 22 * a ^ 15 * b ^ 4 +
          22 * a ^ 14 * b ^ 5 + 10 * a ^ 13 * b ^ 6 +
          54 * a ^ 12 * b ^ 7 + 78 * a ^ 11 * b ^ 8 +
          20 * a ^ 10 * b ^ 9 + 51 * a ^ 9 * b ^ 10 +
          113 * a ^ 8 * b ^ 11 + 36 * a ^ 7 * b ^ 12 +
          13 * a ^ 6 * b ^ 13 + 66 * a ^ 5 * b ^ 14 +
          26 * a ^ 4 * b ^ 15 + 12 * a ^ 2 * b ^ 17) by
      simp only [pellHHomogeneous]
      ring]
    positivity
  · have hba : b < a := lt_of_not_ge hab
    have hcoefficient : 0 < 13 * a - b := by linarith
    have hpair :
        0 < 26 * a ^ 4 * b ^ 15 - 2 * a ^ 3 * b ^ 16 := by
      rw [show 26 * a ^ 4 * b ^ 15 - 2 * a ^ 3 * b ^ 16 =
        2 * a ^ 3 * b ^ 15 * (13 * a - b) by ring]
      positivity
    rw [← sub_pos]
    rw [show pellHHomogeneous a b - a ^ 19 =
      (26 * a ^ 4 * b ^ 15 - 2 * a ^ 3 * b ^ 16) +
        (3 * a ^ 18 * b + 2 * a ^ 17 * b ^ 2 +
          5 * a ^ 16 * b ^ 3 + 22 * a ^ 15 * b ^ 4 +
          22 * a ^ 14 * b ^ 5 + 10 * a ^ 13 * b ^ 6 +
          54 * a ^ 12 * b ^ 7 + 78 * a ^ 11 * b ^ 8 +
          20 * a ^ 10 * b ^ 9 + 51 * a ^ 9 * b ^ 10 +
          113 * a ^ 8 * b ^ 11 + 36 * a ^ 7 * b ^ 12 +
          13 * a ^ 6 * b ^ 13 + 66 * a ^ 5 * b ^ 14 +
          12 * a ^ 2 * b ^ 17 + 4 * a * b ^ 18) by
      simp only [pellHHomogeneous]
      ring]
    positivity

/-- In the positive chamber, adding `b¹⁹` to the homogeneous Pell numerator
still leaves a strict gap below `(a+b)¹⁹`. -/
theorem pellHHomogeneous_add_right_power_lt
    (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    pellHHomogeneous a b + b ^ 19 < (a + b) ^ 19 := by
  rw [← sub_pos]
  rw [show (a + b) ^ 19 - (pellHHomogeneous a b + b ^ 19) =
      16 * a ^ 18 * b + 169 * a ^ 17 * b ^ 2 +
        964 * a ^ 16 * b ^ 3 + 3854 * a ^ 15 * b ^ 4 +
        11606 * a ^ 14 * b ^ 5 + 27122 * a ^ 13 * b ^ 6 +
        50334 * a ^ 12 * b ^ 7 + 75504 * a ^ 11 * b ^ 8 +
        92358 * a ^ 10 * b ^ 9 + 92327 * a ^ 9 * b ^ 10 +
        75469 * a ^ 8 * b ^ 11 + 50352 * a ^ 7 * b ^ 12 +
        27119 * a ^ 6 * b ^ 13 + 11562 * a ^ 5 * b ^ 14 +
        3850 * a ^ 4 * b ^ 15 + 971 * a ^ 3 * b ^ 16 +
        159 * a ^ 2 * b ^ 17 + 15 * a * b ^ 18 by
    simp only [pellHHomogeneous]
    ring]
  positivity

/-- The two positive power-split Pell factors place `r²` strictly inside the
integer interval from `a` to `a+b`. -/
theorem pell_power_split_strict_bounds
    (a b c r s : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (hs : 0 < s)
    (hplus : positivePellFactor a b c = 2 * r ^ 38)
    (hminus : negativePellFactorMagnitude a b c = 2 * s ^ 38)
    (hbSplit : b = r * s) :
    s < r ∧ a < r ^ 2 ∧ r ^ 2 < a + b := by
  have hH : pellHHomogeneous a b = r ^ 38 - s ^ 38 := by
    have hsub := congrArg₂ (· - ·) hplus hminus
    simp only [positivePellFactor, negativePellFactorMagnitude] at hsub
    nlinarith
  have hHPos : 0 < pellHHomogeneous a b :=
    pellHHomogeneous_pos a b ha hb
  have hrsPow : s ^ 38 < r ^ 38 := by
    rw [hH] at hHPos
    linarith
  have hrs : s < r :=
    lt_of_pow_lt_pow_left₀ 38 hr.le hrsPow
  have haPow : a ^ 19 < (r ^ 2) ^ 19 := by
    have hsPowPos : 0 < s ^ 38 := pow_pos hs 38
    have hleft := left_power_lt_pellHHomogeneous a b ha hb
    rw [hH] at hleft
    rw [← pow_mul]
    norm_num
    linarith
  have har : a < r ^ 2 :=
    lt_of_pow_lt_pow_left₀ 19 (by positivity : 0 ≤ r ^ 2) haPow
  have hrPowBelow : (r ^ 2) ^ 19 <
      pellHHomogeneous a b + b ^ 19 := by
    rw [hH, hbSplit, mul_pow, ← pow_mul]
    norm_num
    have hrs19 : s ^ 19 < r ^ 19 :=
      pow_lt_pow_left₀ hrs hs.le (by norm_num)
    have hs19Pos : 0 < s ^ 19 := pow_pos hs 19
    nlinarith
  have hright := pellHHomogeneous_add_right_power_lt a b ha hb
  have hrSumPow : (r ^ 2) ^ 19 < (a + b) ^ 19 :=
    lt_trans hrPowBelow hright
  have habNonneg : 0 ≤ a + b := (add_pos ha hb).le
  have hrSum : r ^ 2 < a + b :=
    lt_of_pow_lt_pow_left₀ 19 habNonneg hrSumPow
  exact ⟨hrs, har, hrSum⟩

end MazurTorsion.XOneThirteenDescent
