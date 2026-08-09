/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawOrbit
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Factored certificates for the raw order-twenty-five orbit

This leaf checks the factorizations of Lécacheux's five raw modular units.
Later relation-certificate leaves consume these identities; all auxiliary
polynomials remain implementation details of the checked certificates.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawOrbitFactorCertificate

def A (r s : ℚ) : ℚ :=
  r - s

def B (_r s : ℚ) : ℚ :=
  s - 1

def C (r s : ℚ) : ℚ :=
  r * s - 2 * r + 1

def K (r s : ℚ) : ℚ :=
  r - s ^ 2 + s - 1

def D (r s : ℚ) : ℚ :=
  r ^ 2 - r * s ^ 3 + 3 * r * s ^ 2 - 4 * r * s + s

def E (r s : ℚ) : ℚ :=
  r ^ 2 * s - 3 * r ^ 2 + r * s + 3 * r - s ^ 2 - 1

def G (r s : ℚ) : ℚ :=
  r * s ^ 2 - 3 * r * s + r + s ^ 2

def L (r s : ℚ) : ℚ :=
  r ^ 3 - r ^ 2 * s ^ 4 + 5 * r ^ 2 * s ^ 3 - 9 * r ^ 2 * s ^ 2 +
    4 * r ^ 2 * s - 2 * r ^ 2 - r * s ^ 3 + 6 * r * s ^ 2 -
    3 * r * s + r - s ^ 3

def J (r s : ℚ) : ℚ :=
  r ^ 3 * s ^ 2 - 4 * r ^ 3 * s + 2 * r ^ 3 + 3 * r ^ 2 * s ^ 2 +
    2 * r ^ 2 * s - 2 * r ^ 2 - r * s ^ 5 + 4 * r * s ^ 4 -
    10 * r * s ^ 3 + 6 * r * s ^ 2 - 3 * r * s + r + s ^ 4

def T (r s : ℚ) : ℚ :=
  r ^ 2 * s ^ 3 - 5 * r ^ 2 * s ^ 2 + 6 * r ^ 2 * s - r ^ 2 +
    r * s ^ 4 - 3 * r * s ^ 3 + 6 * r * s ^ 2 - 7 * r * s + r + s

def M (r s : ℚ) : ℚ :=
  r ^ 4 * s ^ 3 - 6 * r ^ 4 * s ^ 2 + 9 * r ^ 4 * s - r ^ 4 +
    r ^ 3 * s ^ 5 - 7 * r ^ 3 * s ^ 4 + 20 * r ^ 3 * s ^ 3 -
    19 * r ^ 3 * s ^ 2 - 8 * r ^ 3 * s + r ^ 3 + r ^ 2 * s ^ 4 -
    11 * r ^ 2 * s ^ 3 + 28 * r ^ 2 * s ^ 2 + r * s ^ 4 -
    5 * r * s ^ 3 - 8 * r * s ^ 2 + s ^ 4 + s ^ 3 + s ^ 2

def N (r s : ℚ) : ℚ :=
  r * A r s * K r s ^ 3 - s * C r s ^ 3 * G r s

def P6 (r s : ℚ) : ℚ :=
  D r s ^ 2 * A r s * K r s -
    C r s ^ 2 * s * B r s * G r s * E r s

def P9 (r s : ℚ) : ℚ :=
  D r s ^ 3 * L r s - r * s * B r s ^ 3 * G r s * E r s ^ 3

theorem p6_identity (r s : ℚ) :
    P6 r s =
      D r s ^ 2 * A r s * K r s -
        C r s ^ 2 * s * B r s * G r s * E r s := by
  rfl


theorem abscissaTwo_sub_six_eq (r s : ℚ) (hB : B r s ≠ 0) :
    orderTwentyFiveRawOrbitAbscissaTwo r s -
        orderTwentyFiveRawOrbitAbscissaSix r s =
      s ^ 2 * (r - 1) * C r s / B r s ^ 2 := by
  have hB' : s - 1 ≠ 0 := by
    simpa only [B] using hB
  rw [orderTwentyFiveRawOrbitAbscissaTwo,
    orderTwentyFiveRawOrbitAbscissaSix]
  field_simp [hB, hB']
  simp only [B, C]
  ring

theorem abscissaEight_eq_factor (r s : ℚ) :
    orderTwentyFiveRawOrbitAbscissaEight r s =
      r * (r - 1) * A r s * K r s / C r s ^ 2 := by
  rfl

theorem abscissaEleven_eq_factor (r s : ℚ) :
    orderTwentyFiveRawOrbitAbscissaEleven r s =
      r * s * (r - 1) * B r s * G r s * E r s / D r s ^ 2 := by
  rfl

theorem abscissaEleven_sub_eight_eq (r s : ℚ)
    (hC : C r s ≠ 0) (hD : D r s ≠ 0) :
    orderTwentyFiveRawOrbitAbscissaEleven r s -
        orderTwentyFiveRawOrbitAbscissaEight r s =
      -(r * (r - 1) * P6 r s) / (C r s ^ 2 * D r s ^ 2) := by
  rw [abscissaEleven_eq_factor, abscissaEight_eq_factor]
  field_simp [hC, hD]
  simp only [P6]
  ring

theorem yTwoDenominator_eq (r s : ℚ)
    (hB : B r s ≠ 0) (hC : C r s ≠ 0) (hD : D r s ≠ 0) :
    orderTwentyFiveRawOrbitYTwoDenominator r s =
      -(r * s ^ 2 * (r - 1) ^ 2 * P6 r s) /
        (B r s ^ 2 * C r s * D r s ^ 2) := by
  rw [orderTwentyFiveRawOrbitYTwoDenominator,
    abscissaTwo_sub_six_eq r s hB,
    abscissaEleven_sub_eight_eq r s hC hD]
  field_simp [hB, hC, hD]

theorem p6_ne_zero_of_yTwoDenominator_ne_zero (r s : ℚ)
    (hB : B r s ≠ 0) (hC : C r s ≠ 0) (hD : D r s ≠ 0)
    (hYTwo : orderTwentyFiveRawOrbitYTwoDenominator r s ≠ 0) :
    P6 r s ≠ 0 := by
  intro hP6
  apply hYTwo
  rw [yTwoDenominator_eq r s hB hC hD]
  simp [hP6]

theorem abscissaNine_sub_two_eq (r s : ℚ) (hK : K r s ≠ 0) :
    orderTwentyFiveRawOrbitAbscissaNine r s -
        orderTwentyFiveRawOrbitAbscissaTwo r s =
      -(s * (r - 1) * A r s * D r s) / K r s ^ 2 := by
  rw [orderTwentyFiveRawOrbitAbscissaNine,
    orderTwentyFiveRawOrbitAbscissaTwo]
  have hK' : r - s ^ 2 + s - 1 ≠ 0 := by
    simpa only [K] using hK
  field_simp [hK, hK']
  simp only [A, D, K]
  ring

theorem abscissaTwelve_eq_factor (r s : ℚ) :
    orderTwentyFiveRawOrbitAbscissaTwelve r s =
      (r - 1) * D r s * L r s / (B r s ^ 2 * E r s ^ 2) := by
  rfl

theorem abscissaTwelve_sub_eleven_eq (r s : ℚ)
    (hB : B r s ≠ 0) (hD : D r s ≠ 0) (hE : E r s ≠ 0) :
    orderTwentyFiveRawOrbitAbscissaTwelve r s -
        orderTwentyFiveRawOrbitAbscissaEleven r s =
      (r - 1) * P9 r s / (B r s ^ 2 * D r s ^ 2 * E r s ^ 2) := by
  rw [abscissaTwelve_eq_factor, abscissaEleven_eq_factor]
  field_simp [hB, hD, hE]
  simp only [P9]
  ring

theorem yNineDenominator_eq (r s : ℚ)
    (hB : B r s ≠ 0) (hD : D r s ≠ 0) (hE : E r s ≠ 0)
    (hK : K r s ≠ 0) :
    orderTwentyFiveRawOrbitYNineDenominator r s =
      -(s * (r - 1) ^ 2 * A r s * P9 r s) /
        (B r s ^ 2 * K r s ^ 2 * D r s * E r s ^ 2) := by
  rw [orderTwentyFiveRawOrbitYNineDenominator,
    abscissaNine_sub_two_eq r s hK,
    abscissaTwelve_sub_eleven_eq r s hB hD hE]
  field_simp [hB, hK, hD, hE]

theorem p9_ne_zero_of_yNineDenominator_ne_zero (r s : ℚ)
    (hB : B r s ≠ 0) (hD : D r s ≠ 0) (hE : E r s ≠ 0)
    (hK : K r s ≠ 0)
    (hYNine : orderTwentyFiveRawOrbitYNineDenominator r s ≠ 0) :
    P9 r s ≠ 0 := by
  intro hP9
  apply hYNine
  rw [yNineDenominator_eq r s hB hD hE hK]
  simp [hP9]

end MazurTorsion.Kubert.OrderTwentyFiveRawOrbitFactorCertificate
