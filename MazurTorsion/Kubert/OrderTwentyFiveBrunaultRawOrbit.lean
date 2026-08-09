/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunault
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitCertificate

/-!
# Raw Lécacheux orbit coordinates on Sutherland's order-twenty-five chart

This leaf records the raw Sutherland polynomial, the Tate abscissas used in
Lécacheux's cross-ratios, and the five orbit coordinates.  The separate
relation-certificate leaves consume the normalized numerator/denominator
forms proved here.
-/

namespace MazurTorsion.Kubert

/-- Sutherland's raw `F₂₅(r,s)` equation, arranged by powers of `r`. -/
def orderTwentyFiveRawSutherlandF (r s : ℚ) : ℚ :=
  r ^ 10 +
    (-s ^ 10 + 17 * s ^ 9 - 123 * s ^ 8 + 494 * s ^ 7 - 1205 * s ^ 6 +
      1836 * s ^ 5 - 1732 * s ^ 4 + 968 * s ^ 3 - 294 * s ^ 2 +
      35 * s - 5) * r ^ 9 +
    (-6 * s ^ 10 + 74 * s ^ 9 - 345 * s ^ 8 + 690 * s ^ 7 - 185 * s ^ 6 -
      1659 * s ^ 5 + 3051 * s ^ 4 - 2320 * s ^ 3 + 840 * s ^ 2 -
      105 * s + 10) * r ^ 8 +
    (-21 * s ^ 10 + 161 * s ^ 9 - 351 * s ^ 8 - 144 * s ^ 7 +
      1289 * s ^ 6 - 789 * s ^ 5 - 1551 * s ^ 4 + 2166 * s ^ 3 -
      996 * s ^ 2 + 126 * s - 10) * r ^ 7 +
    (s ^ 15 - 18 * s ^ 14 + 151 * s ^ 13 - 770 * s ^ 12 +
      2655 * s ^ 11 - 6558 * s ^ 10 + 11834 * s ^ 9 - 15408 * s ^ 8 +
      14630 * s ^ 7 - 11195 * s ^ 6 + 7227 * s ^ 5 - 2441 * s ^ 4 -
      388 * s ^ 3 + 555 * s ^ 2 - 70 * s + 5) * r ^ 6 +
    (s ^ 15 - 15 * s ^ 14 + 90 * s ^ 13 - 245 * s ^ 12 + 90 * s ^ 11 +
      1587 * s ^ 10 - 6145 * s ^ 9 + 12270 * s ^ 8 - 15060 * s ^ 7 +
      12520 * s ^ 6 - 8214 * s ^ 5 + 3660 * s ^ 4 - 685 * s ^ 3 -
      120 * s ^ 2 + 15 * s - 1) * r ^ 5 +
    (s ^ 15 - 12 * s ^ 14 + 48 * s ^ 13 - 49 * s ^ 12 - 165 * s ^ 11 +
      609 * s ^ 10 - 433 * s ^ 9 - 1623 * s ^ 8 + 4299 * s ^ 7 -
      4615 * s ^ 6 + 3435 * s ^ 5 - 1740 * s ^ 4 + 455 * s ^ 3) * r ^ 4 +
    (s ^ 15 - 9 * s ^ 14 + 25 * s ^ 13 - 35 * s ^ 12 + 45 * s ^ 11 -
      181 * s ^ 10 + 569 * s ^ 9 - 705 * s ^ 8 + 5 * s ^ 7 +
      470 * s ^ 6 - 540 * s ^ 5 + 340 * s ^ 4 - 105 * s ^ 3) * r ^ 3 +
    (s ^ 15 - 6 * s ^ 14 + 21 * s ^ 13 - 56 * s ^ 12 + 126 * s ^ 11 -
      231 * s ^ 10 + 266 * s ^ 9 - 126 * s ^ 8 + 96 * s ^ 7 -
      91 * s ^ 6 + 75 * s ^ 5 - 45 * s ^ 4 + 15 * s ^ 3) * r ^ 2 +
    (6 * s ^ 10 - 28 * s ^ 9 + 21 * s ^ 8 - 15 * s ^ 7 + 10 * s ^ 6 -
      6 * s ^ 5 + 3 * s ^ 4 - s ^ 3) * r + s ^ 10

def orderTwentyFiveRawOrbitAbscissaTwo (r s : ℚ) : ℚ :=
  r * s * (r - 1)

def orderTwentyFiveRawOrbitAbscissaThree (r s : ℚ) : ℚ :=
  s * (r - 1)

def orderTwentyFiveRawOrbitAbscissaFour (r _s : ℚ) : ℚ :=
  r * (r - 1)

def orderTwentyFiveRawOrbitAbscissaSix (r s : ℚ) : ℚ :=
  s * (r - 1) * (r - s) / (s - 1) ^ 2

def orderTwentyFiveRawOrbitAbscissaSeven (r s : ℚ) : ℚ :=
  r * s * (r - 1) * (s - 1) * (r * s - 2 * r + 1) / (r - s) ^ 2

def orderTwentyFiveRawOrbitAbscissaEight (r s : ℚ) : ℚ :=
  r * (r - 1) * (r - s) * (r - s ^ 2 + s - 1) /
    (r * s - 2 * r + 1) ^ 2

def orderTwentyFiveRawOrbitAbscissaNine (r s : ℚ) : ℚ :=
  s * (r - 1) * (r * s - 2 * r + 1) *
      (r * s ^ 2 - 3 * r * s + r + s ^ 2) /
    (r - s ^ 2 + s - 1) ^ 2

def orderTwentyFiveRawOrbitAbscissaEleven (r s : ℚ) : ℚ :=
  r * s * (r - 1) * (s - 1) *
      (r * s ^ 2 - 3 * r * s + r + s ^ 2) *
      (r ^ 2 * s - 3 * r ^ 2 + r * s + 3 * r - s ^ 2 - 1) /
    (r ^ 2 - r * s ^ 3 + 3 * r * s ^ 2 - 4 * r * s + s) ^ 2

def orderTwentyFiveRawOrbitAbscissaTwelve (r s : ℚ) : ℚ :=
  (r - 1) *
      (r ^ 2 - r * s ^ 3 + 3 * r * s ^ 2 - 4 * r * s + s) *
      (r ^ 3 - r ^ 2 * s ^ 4 + 5 * r ^ 2 * s ^ 3 -
        9 * r ^ 2 * s ^ 2 + 4 * r ^ 2 * s - 2 * r ^ 2 -
        r * s ^ 3 + 6 * r * s ^ 2 - 3 * r * s + r - s ^ 3) /
    ((s - 1) ^ 2 *
      (r ^ 2 * s - 3 * r ^ 2 + r * s + 3 * r - s ^ 2 - 1) ^ 2)

def orderTwentyFiveRawOrbitYOneNumerator (r s : ℚ) : ℚ :=
  (orderTwentyFiveRawOrbitAbscissaSeven r s -
      orderTwentyFiveRawOrbitAbscissaNine r s) *
    (0 - orderTwentyFiveRawOrbitAbscissaTwelve r s)

def orderTwentyFiveRawOrbitYOneDenominator (r s : ℚ) : ℚ :=
  (orderTwentyFiveRawOrbitAbscissaSeven r s -
      orderTwentyFiveRawOrbitAbscissaFour r s) *
    (0 - orderTwentyFiveRawOrbitAbscissaThree r s)

def orderTwentyFiveRawOrbitYOne (r s : ℚ) : ℚ :=
  orderTwentyFiveRawOrbitYOneNumerator r s /
    orderTwentyFiveRawOrbitYOneDenominator r s

theorem orderTwentyFiveRawOrbitYOne_eq_crossRatios
    (r s : ℚ) (hden : orderTwentyFiveRawOrbitYOneDenominator r s ≠ 0) :
    orderTwentyFiveRawOrbitYOne r s =
      ((orderTwentyFiveRawOrbitAbscissaSeven r s -
          orderTwentyFiveRawOrbitAbscissaNine r s) /
        (orderTwentyFiveRawOrbitAbscissaSeven r s -
          orderTwentyFiveRawOrbitAbscissaFour r s)) *
      ((0 - orderTwentyFiveRawOrbitAbscissaTwelve r s) /
        (0 - orderTwentyFiveRawOrbitAbscissaThree r s)) := by
  obtain ⟨hleft, hright⟩ := mul_ne_zero_iff.mp hden
  rw [orderTwentyFiveRawOrbitYOne,
    orderTwentyFiveRawOrbitYOneNumerator,
    orderTwentyFiveRawOrbitYOneDenominator]
  field_simp [hleft, hright]

def orderTwentyFiveRawOrbitYTwoNumerator (r s : ℚ) : ℚ :=
  orderTwentyFiveRawOrbitAbscissaTwo r s *
    (orderTwentyFiveRawOrbitAbscissaEleven r s -
      orderTwentyFiveRawOrbitAbscissaSeven r s)

def orderTwentyFiveRawOrbitYTwoDenominator (r s : ℚ) : ℚ :=
  (orderTwentyFiveRawOrbitAbscissaTwo r s -
      orderTwentyFiveRawOrbitAbscissaSix r s) *
    (orderTwentyFiveRawOrbitAbscissaEleven r s -
      orderTwentyFiveRawOrbitAbscissaEight r s)

def orderTwentyFiveRawOrbitYTwo (r s : ℚ) : ℚ :=
  orderTwentyFiveRawOrbitYTwoNumerator r s /
    orderTwentyFiveRawOrbitYTwoDenominator r s

theorem orderTwentyFiveRawOrbitYTwo_eq_crossRatios
    (r s : ℚ) (hden : orderTwentyFiveRawOrbitYTwoDenominator r s ≠ 0) :
    orderTwentyFiveRawOrbitYTwo r s =
      (orderTwentyFiveRawOrbitAbscissaTwo r s /
        (orderTwentyFiveRawOrbitAbscissaTwo r s -
          orderTwentyFiveRawOrbitAbscissaSix r s)) *
      ((orderTwentyFiveRawOrbitAbscissaEleven r s -
          orderTwentyFiveRawOrbitAbscissaSeven r s) /
        (orderTwentyFiveRawOrbitAbscissaEleven r s -
          orderTwentyFiveRawOrbitAbscissaEight r s)) := by
  obtain ⟨hleft, hright⟩ := mul_ne_zero_iff.mp hden
  rw [orderTwentyFiveRawOrbitYTwo,
    orderTwentyFiveRawOrbitYTwoNumerator,
    orderTwentyFiveRawOrbitYTwoDenominator]
  field_simp [hleft, hright]

def orderTwentyFiveRawOrbitYFourNumerator (r s : ℚ) : ℚ :=
  (orderTwentyFiveRawOrbitAbscissaFour r s -
      orderTwentyFiveRawOrbitAbscissaTwo r s) *
    (orderTwentyFiveRawOrbitAbscissaThree r s -
      orderTwentyFiveRawOrbitAbscissaEleven r s)

def orderTwentyFiveRawOrbitYFourDenominator (r s : ℚ) : ℚ :=
  (orderTwentyFiveRawOrbitAbscissaFour r s -
      orderTwentyFiveRawOrbitAbscissaTwelve r s) *
    (orderTwentyFiveRawOrbitAbscissaThree r s -
      orderTwentyFiveRawOrbitAbscissaNine r s)

def orderTwentyFiveRawOrbitYFour (r s : ℚ) : ℚ :=
  orderTwentyFiveRawOrbitYFourNumerator r s /
    orderTwentyFiveRawOrbitYFourDenominator r s

theorem orderTwentyFiveRawOrbitYFour_eq_crossRatios
    (r s : ℚ) (hden : orderTwentyFiveRawOrbitYFourDenominator r s ≠ 0) :
    orderTwentyFiveRawOrbitYFour r s =
      ((orderTwentyFiveRawOrbitAbscissaFour r s -
          orderTwentyFiveRawOrbitAbscissaTwo r s) /
        (orderTwentyFiveRawOrbitAbscissaFour r s -
          orderTwentyFiveRawOrbitAbscissaTwelve r s)) *
      ((orderTwentyFiveRawOrbitAbscissaThree r s -
          orderTwentyFiveRawOrbitAbscissaEleven r s) /
        (orderTwentyFiveRawOrbitAbscissaThree r s -
          orderTwentyFiveRawOrbitAbscissaNine r s)) := by
  obtain ⟨hleft, hright⟩ := mul_ne_zero_iff.mp hden
  rw [orderTwentyFiveRawOrbitYFour,
    orderTwentyFiveRawOrbitYFourNumerator,
    orderTwentyFiveRawOrbitYFourDenominator]
  field_simp [hleft, hright]

def orderTwentyFiveRawOrbitYEightNumerator (r s : ℚ) : ℚ :=
  (orderTwentyFiveRawOrbitAbscissaEight r s -
      orderTwentyFiveRawOrbitAbscissaFour r s) *
    (orderTwentyFiveRawOrbitAbscissaSix r s -
      orderTwentyFiveRawOrbitAbscissaThree r s)

def orderTwentyFiveRawOrbitYEightDenominator (r s : ℚ) : ℚ :=
  orderTwentyFiveRawOrbitAbscissaEight r s *
    (orderTwentyFiveRawOrbitAbscissaSix r s -
      orderTwentyFiveRawOrbitAbscissaSeven r s)

def orderTwentyFiveRawOrbitYEight (r s : ℚ) : ℚ :=
  orderTwentyFiveRawOrbitYEightNumerator r s /
    orderTwentyFiveRawOrbitYEightDenominator r s

theorem orderTwentyFiveRawOrbitYEight_eq_crossRatios
    (r s : ℚ) (hden : orderTwentyFiveRawOrbitYEightDenominator r s ≠ 0) :
    orderTwentyFiveRawOrbitYEight r s =
      ((orderTwentyFiveRawOrbitAbscissaEight r s -
          orderTwentyFiveRawOrbitAbscissaFour r s) /
        orderTwentyFiveRawOrbitAbscissaEight r s) *
      ((orderTwentyFiveRawOrbitAbscissaSix r s -
          orderTwentyFiveRawOrbitAbscissaThree r s) /
        (orderTwentyFiveRawOrbitAbscissaSix r s -
          orderTwentyFiveRawOrbitAbscissaSeven r s)) := by
  obtain ⟨hleft, hright⟩ := mul_ne_zero_iff.mp hden
  rw [orderTwentyFiveRawOrbitYEight,
    orderTwentyFiveRawOrbitYEightNumerator,
    orderTwentyFiveRawOrbitYEightDenominator]
  field_simp [hleft, hright]

def orderTwentyFiveRawOrbitYNineNumerator (r s : ℚ) : ℚ :=
  (orderTwentyFiveRawOrbitAbscissaNine r s -
      orderTwentyFiveRawOrbitAbscissaEight r s) *
    (orderTwentyFiveRawOrbitAbscissaTwelve r s -
      orderTwentyFiveRawOrbitAbscissaSix r s)

def orderTwentyFiveRawOrbitYNineDenominator (r s : ℚ) : ℚ :=
  (orderTwentyFiveRawOrbitAbscissaNine r s -
      orderTwentyFiveRawOrbitAbscissaTwo r s) *
    (orderTwentyFiveRawOrbitAbscissaTwelve r s -
      orderTwentyFiveRawOrbitAbscissaEleven r s)

def orderTwentyFiveRawOrbitYNine (r s : ℚ) : ℚ :=
  orderTwentyFiveRawOrbitYNineNumerator r s /
    orderTwentyFiveRawOrbitYNineDenominator r s

theorem orderTwentyFiveRawOrbitYNine_eq_crossRatios
    (r s : ℚ) (hden : orderTwentyFiveRawOrbitYNineDenominator r s ≠ 0) :
    orderTwentyFiveRawOrbitYNine r s =
      ((orderTwentyFiveRawOrbitAbscissaNine r s -
          orderTwentyFiveRawOrbitAbscissaEight r s) /
        (orderTwentyFiveRawOrbitAbscissaNine r s -
          orderTwentyFiveRawOrbitAbscissaTwo r s)) *
      ((orderTwentyFiveRawOrbitAbscissaTwelve r s -
          orderTwentyFiveRawOrbitAbscissaSix r s) /
        (orderTwentyFiveRawOrbitAbscissaTwelve r s -
          orderTwentyFiveRawOrbitAbscissaEleven r s)) := by
  obtain ⟨hleft, hright⟩ := mul_ne_zero_iff.mp hden
  rw [orderTwentyFiveRawOrbitYNine,
    orderTwentyFiveRawOrbitYNineNumerator,
    orderTwentyFiveRawOrbitYNineDenominator]
  field_simp [hleft, hright]

/-- The raw orbit coordinate `x₀ = y₁y₄`. -/
def orderTwentyFiveRawOrbitXZero (r s : ℚ) : ℚ :=
  orderTwentyFiveRawOrbitYOne r s * orderTwentyFiveRawOrbitYFour r s

/-- The raw orbit coordinate `x₁ = y₂y₈`. -/
def orderTwentyFiveRawOrbitXOne (r s : ℚ) : ℚ :=
  orderTwentyFiveRawOrbitYTwo r s * orderTwentyFiveRawOrbitYEight r s

/-- The raw orbit coordinate `x₂ = y₄y₉`. -/
def orderTwentyFiveRawOrbitXTwo (r s : ℚ) : ℚ :=
  orderTwentyFiveRawOrbitYFour r s * orderTwentyFiveRawOrbitYNine r s

/-- The raw orbit coordinate `x₃ = y₈y₁`. -/
def orderTwentyFiveRawOrbitXThree (r s : ℚ) : ℚ :=
  orderTwentyFiveRawOrbitYEight r s * orderTwentyFiveRawOrbitYOne r s

/-- The raw orbit coordinate `x₄ = y₉y₂`. -/
def orderTwentyFiveRawOrbitXFour (r s : ℚ) : ℚ :=
  orderTwentyFiveRawOrbitYNine r s * orderTwentyFiveRawOrbitYTwo r s

end MazurTorsion.Kubert
