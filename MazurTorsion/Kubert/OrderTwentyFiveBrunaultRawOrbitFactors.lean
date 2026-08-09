/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawOrbit
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
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

theorem d_from_seven_sub_four (r s : ℚ) :
    s * B r s * C r s - A r s ^ 2 = -D r s := by
  simp only [A, B, C, D]
  ring

theorem j_from_seven_sub_nine (r s : ℚ) :
    r * B r s * K r s ^ 2 - A r s ^ 2 * G r s = -J r s := by
  simp only [A, B, G, J, K]
  ring

theorem m_from_eleven_sub_seven (r s : ℚ) :
    A r s ^ 2 * G r s * E r s - C r s * D r s ^ 2 =
      K r s * M r s := by
  simp only [A, C, D, E, G, K, M]
  ring

theorem j_from_four_sub_twelve (r s : ℚ) :
    r * B r s ^ 2 * E r s ^ 2 - D r s * L r s =
      C r s ^ 2 * J r s := by
  simp only [B, C, D, E, J, L]
  ring

theorem t_from_three_sub_eleven (r s : ℚ) :
    D r s ^ 2 - r * B r s * G r s * E r s =
      -(A r s * C r s * T r s) := by
  simp only [A, B, C, D, E, G, T]
  ring

theorem e_from_three_sub_nine (r s : ℚ) :
    K r s ^ 2 - C r s * G r s = -(B r s ^ 2 * E r s) := by
  simp only [B, C, E, G, K]
  ring

theorem e_from_eight_sub_four (r s : ℚ) :
    A r s * K r s - C r s ^ 2 = -(B r s * E r s) := by
  simp only [A, B, C, E, K]
  ring

theorem k_from_six_sub_three (r s : ℚ) :
    A r s - B r s ^ 2 = K r s := by
  simp only [A, B, K]
  ring

theorem l_from_six_sub_seven (r s : ℚ) :
    A r s ^ 3 - r * B r s ^ 3 * C r s = L r s := by
  simp only [A, B, C, L]
  ring

theorem m_from_twelve_sub_six (r s : ℚ) :
    D r s * L r s - s * A r s * E r s ^ 2 = -(K r s * M r s) := by
  simp only [A, D, E, K, L, M]
  ring

theorem d_from_nine_sub_two (r s : ℚ) :
    C r s * G r s - r * K r s ^ 2 = -(A r s * D r s) := by
  simp only [A, C, D, G, K]
  ring

theorem n_from_nine_sub_eight (r s : ℚ) :
    s * C r s ^ 3 * G r s - r * A r s * K r s ^ 3 = -N r s := by
  simp only [N]
  ring

theorem p6_identity (r s : ℚ) :
    P6 r s =
      D r s ^ 2 * A r s * K r s -
        C r s ^ 2 * s * B r s * G r s * E r s := by
  rfl

theorem abscissaTwo_eq_factor (r s : ℚ) :
    orderTwentyFiveRawOrbitAbscissaTwo r s = r * s * (r - 1) := by
  rfl

theorem abscissaThree_eq_factor (r s : ℚ) :
    orderTwentyFiveRawOrbitAbscissaThree r s = s * (r - 1) := by
  rfl

theorem abscissaFour_eq_factor (r s : ℚ) :
    orderTwentyFiveRawOrbitAbscissaFour r s = r * (r - 1) := by
  rfl

theorem abscissaSix_eq_factor (r s : ℚ) :
    orderTwentyFiveRawOrbitAbscissaSix r s =
      s * (r - 1) * A r s / B r s ^ 2 := by
  rfl

theorem abscissaSeven_eq_factor (r s : ℚ) :
    orderTwentyFiveRawOrbitAbscissaSeven r s =
      r * s * (r - 1) * B r s * C r s / A r s ^ 2 := by
  rfl

theorem abscissaNine_eq_factor (r s : ℚ) :
    orderTwentyFiveRawOrbitAbscissaNine r s =
      s * (r - 1) * C r s * G r s / K r s ^ 2 := by
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

theorem abscissaTwelve_eq_factor (r s : ℚ) :
    orderTwentyFiveRawOrbitAbscissaTwelve r s =
      (r - 1) * D r s * L r s / (B r s ^ 2 * E r s ^ 2) := by
  rfl

theorem abscissaSeven_sub_four_eq (r s : ℚ) (hA : A r s ≠ 0) :
    orderTwentyFiveRawOrbitAbscissaSeven r s -
        orderTwentyFiveRawOrbitAbscissaFour r s =
      -(r * (r - 1) * D r s) / A r s ^ 2 := by
  have hD := d_from_seven_sub_four r s
  rw [abscissaSeven_eq_factor, abscissaFour_eq_factor]
  field_simp [hA]
  linear_combination r * (r - 1) * hD

theorem abscissaFour_sub_two_eq (r s : ℚ) :
    orderTwentyFiveRawOrbitAbscissaFour r s -
        orderTwentyFiveRawOrbitAbscissaTwo r s =
      -(r * (r - 1) * B r s) := by
  rw [abscissaFour_eq_factor, abscissaTwo_eq_factor]
  simp only [B]
  ring

theorem abscissaSeven_sub_nine_eq (r s : ℚ)
    (hA : A r s ≠ 0) (hK : K r s ≠ 0) :
    orderTwentyFiveRawOrbitAbscissaSeven r s -
        orderTwentyFiveRawOrbitAbscissaNine r s =
      -(s * (r - 1) * C r s * J r s) / (A r s ^ 2 * K r s ^ 2) := by
  have hJ := j_from_seven_sub_nine r s
  rw [abscissaSeven_eq_factor, abscissaNine_eq_factor]
  field_simp [hA, hK]
  linear_combination s * (r - 1) * C r s * hJ

theorem abscissaEleven_sub_seven_eq (r s : ℚ)
    (hA : A r s ≠ 0) (hD : D r s ≠ 0) :
    orderTwentyFiveRawOrbitAbscissaEleven r s -
        orderTwentyFiveRawOrbitAbscissaSeven r s =
      r * s * (r - 1) * B r s * K r s * M r s /
        (A r s ^ 2 * D r s ^ 2) := by
  have hM := m_from_eleven_sub_seven r s
  rw [abscissaEleven_eq_factor, abscissaSeven_eq_factor]
  field_simp [hA, hD]
  linear_combination r * s * (r - 1) * B r s * hM

theorem abscissaFour_sub_twelve_eq (r s : ℚ)
    (hB : B r s ≠ 0) (hE : E r s ≠ 0) :
    orderTwentyFiveRawOrbitAbscissaFour r s -
        orderTwentyFiveRawOrbitAbscissaTwelve r s =
      (r - 1) * C r s ^ 2 * J r s / (B r s ^ 2 * E r s ^ 2) := by
  have hJ := j_from_four_sub_twelve r s
  rw [abscissaFour_eq_factor, abscissaTwelve_eq_factor]
  field_simp [hB, hE]
  linear_combination (r - 1) * hJ

theorem abscissaThree_sub_eleven_eq (r s : ℚ) (hD : D r s ≠ 0) :
    orderTwentyFiveRawOrbitAbscissaThree r s -
        orderTwentyFiveRawOrbitAbscissaEleven r s =
      -(s * (r - 1) * A r s * C r s * T r s) / D r s ^ 2 := by
  have hT := t_from_three_sub_eleven r s
  rw [abscissaThree_eq_factor, abscissaEleven_eq_factor]
  field_simp [hD]
  linear_combination s * (r - 1) * hT

theorem abscissaThree_sub_nine_eq (r s : ℚ) (hK : K r s ≠ 0) :
    orderTwentyFiveRawOrbitAbscissaThree r s -
        orderTwentyFiveRawOrbitAbscissaNine r s =
      -(s * (r - 1) * B r s ^ 2 * E r s) / K r s ^ 2 := by
  have hE := e_from_three_sub_nine r s
  rw [abscissaThree_eq_factor, abscissaNine_eq_factor]
  field_simp [hK]
  linear_combination s * (r - 1) * hE

theorem abscissaEight_sub_four_eq (r s : ℚ) (hC : C r s ≠ 0) :
    orderTwentyFiveRawOrbitAbscissaEight r s -
        orderTwentyFiveRawOrbitAbscissaFour r s =
      -(r * (r - 1) * B r s * E r s) / C r s ^ 2 := by
  have hE := e_from_eight_sub_four r s
  rw [abscissaEight_eq_factor, abscissaFour_eq_factor]
  field_simp [hC]
  linear_combination r * (r - 1) * hE

theorem abscissaSix_sub_three_eq (r s : ℚ) (hB : B r s ≠ 0) :
    orderTwentyFiveRawOrbitAbscissaSix r s -
        orderTwentyFiveRawOrbitAbscissaThree r s =
      s * (r - 1) * K r s / B r s ^ 2 := by
  have hK := k_from_six_sub_three r s
  rw [abscissaSix_eq_factor, abscissaThree_eq_factor]
  field_simp [hB]
  linear_combination s * (r - 1) * hK

theorem abscissaSix_sub_seven_eq (r s : ℚ)
    (hA : A r s ≠ 0) (hB : B r s ≠ 0) :
    orderTwentyFiveRawOrbitAbscissaSix r s -
        orderTwentyFiveRawOrbitAbscissaSeven r s =
      s * (r - 1) * L r s / (A r s ^ 2 * B r s ^ 2) := by
  have hL := l_from_six_sub_seven r s
  rw [abscissaSix_eq_factor, abscissaSeven_eq_factor]
  field_simp [hA, hB]
  linear_combination s * (r - 1) * hL

theorem abscissaNine_sub_eight_eq (r s : ℚ)
    (hC : C r s ≠ 0) (hK : K r s ≠ 0) :
    orderTwentyFiveRawOrbitAbscissaNine r s -
        orderTwentyFiveRawOrbitAbscissaEight r s =
      -((r - 1) * N r s) / (C r s ^ 2 * K r s ^ 2) := by
  have hN := n_from_nine_sub_eight r s
  rw [abscissaNine_eq_factor, abscissaEight_eq_factor]
  field_simp [hC, hK]
  linear_combination (r - 1) * hN

theorem abscissaTwelve_sub_six_eq (r s : ℚ)
    (hB : B r s ≠ 0) (hE : E r s ≠ 0) :
    orderTwentyFiveRawOrbitAbscissaTwelve r s -
        orderTwentyFiveRawOrbitAbscissaSix r s =
      -((r - 1) * K r s * M r s) / (B r s ^ 2 * E r s ^ 2) := by
  have hM := m_from_twelve_sub_six r s
  rw [abscissaTwelve_eq_factor, abscissaSix_eq_factor]
  field_simp [hB, hE]
  linear_combination (r - 1) * hM

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

theorem yOneDenominator_eq (r s : ℚ) (hA : A r s ≠ 0) :
    orderTwentyFiveRawOrbitYOneDenominator r s =
      r * s * (r - 1) ^ 2 * D r s / A r s ^ 2 := by
  rw [orderTwentyFiveRawOrbitYOneDenominator,
    abscissaSeven_sub_four_eq r s hA,
    abscissaThree_eq_factor]
  field_simp [hA]
  ring

theorem yFourDenominator_eq (r s : ℚ)
    (hB : B r s ≠ 0) (hE : E r s ≠ 0) (hK : K r s ≠ 0) :
    orderTwentyFiveRawOrbitYFourDenominator r s =
      -(s * (r - 1) ^ 2 * C r s ^ 2 * J r s) /
        (K r s ^ 2 * E r s) := by
  rw [orderTwentyFiveRawOrbitYFourDenominator,
    abscissaFour_sub_twelve_eq r s hB hE,
    abscissaThree_sub_nine_eq r s hK]
  field_simp [hB, hE, hK]

theorem j_ne_zero_of_yFourDenominator_ne_zero (r s : ℚ)
    (hB : B r s ≠ 0) (hE : E r s ≠ 0) (hK : K r s ≠ 0)
    (hYFour : orderTwentyFiveRawOrbitYFourDenominator r s ≠ 0) :
    J r s ≠ 0 := by
  intro hJ
  apply hYFour
  rw [yFourDenominator_eq r s hB hE hK]
  simp [hJ]

theorem yEightDenominator_eq (r s : ℚ)
    (hA : A r s ≠ 0) (hB : B r s ≠ 0) (hC : C r s ≠ 0) :
    orderTwentyFiveRawOrbitYEightDenominator r s =
      r * s * (r - 1) ^ 2 * K r s * L r s /
        (A r s * B r s ^ 2 * C r s ^ 2) := by
  rw [orderTwentyFiveRawOrbitYEightDenominator,
    abscissaEight_eq_factor,
    abscissaSix_sub_seven_eq r s hA hB]
  field_simp [hA, hB, hC]

theorem l_ne_zero_of_yEightDenominator_ne_zero (r s : ℚ)
    (hA : A r s ≠ 0) (hB : B r s ≠ 0) (hC : C r s ≠ 0)
    (hYEight : orderTwentyFiveRawOrbitYEightDenominator r s ≠ 0) :
    L r s ≠ 0 := by
  intro hL
  apply hYEight
  rw [yEightDenominator_eq r s hA hB hC]
  simp [hL]

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

theorem yOne_eq_factor (r s : ℚ)
    (hr : r ≠ 0) (hA : A r s ≠ 0) (hB : B r s ≠ 0)
    (hE : E r s ≠ 0) (hK : K r s ≠ 0)
    (hYOne : orderTwentyFiveRawOrbitYOneDenominator r s ≠ 0) :
    orderTwentyFiveRawOrbitYOne r s =
      C r s * L r s * J r s /
        (r * B r s ^ 2 * K r s ^ 2 * E r s ^ 2) := by
  rw [orderTwentyFiveRawOrbitYOne, div_eq_iff hYOne]
  rw [orderTwentyFiveRawOrbitYOneNumerator,
    abscissaSeven_sub_nine_eq r s hA hK,
    abscissaTwelve_eq_factor,
    yOneDenominator_eq r s hA]
  field_simp [hr, hA, hB, hE, hK]
  ring

theorem yTwo_eq_factor (r s : ℚ)
    (hA : A r s ≠ 0) (hB : B r s ≠ 0) (hC : C r s ≠ 0)
    (hD : D r s ≠ 0)
    (hYTwo : orderTwentyFiveRawOrbitYTwoDenominator r s ≠ 0) :
    orderTwentyFiveRawOrbitYTwo r s =
      -(r * B r s ^ 3 * C r s * K r s * M r s) /
        (A r s ^ 2 * P6 r s) := by
  have hP6 := p6_ne_zero_of_yTwoDenominator_ne_zero r s hB hC hD hYTwo
  rw [orderTwentyFiveRawOrbitYTwo, div_eq_iff hYTwo]
  rw [orderTwentyFiveRawOrbitYTwoNumerator,
    abscissaTwo_eq_factor,
    abscissaEleven_sub_seven_eq r s hA hD,
    yTwoDenominator_eq r s hB hC hD]
  field_simp [hA, hB, hC, hD, hP6]

theorem yFour_eq_factor (r s : ℚ)
    (hB : B r s ≠ 0) (hC : C r s ≠ 0) (hD : D r s ≠ 0)
    (hE : E r s ≠ 0) (hK : K r s ≠ 0)
    (hYFour : orderTwentyFiveRawOrbitYFourDenominator r s ≠ 0) :
    orderTwentyFiveRawOrbitYFour r s =
      -(r * A r s * B r s * K r s ^ 2 * E r s * T r s) /
        (C r s * D r s ^ 2 * J r s) := by
  have hJ := j_ne_zero_of_yFourDenominator_ne_zero r s hB hE hK hYFour
  rw [orderTwentyFiveRawOrbitYFour, div_eq_iff hYFour]
  rw [orderTwentyFiveRawOrbitYFourNumerator,
    abscissaFour_sub_two_eq,
    abscissaThree_sub_eleven_eq r s hD,
    yFourDenominator_eq r s hB hE hK]
  field_simp [hB, hC, hD, hE, hJ, hK]

theorem yEight_eq_factor (r s : ℚ)
    (hA : A r s ≠ 0) (hB : B r s ≠ 0) (hC : C r s ≠ 0)
    (hYEight : orderTwentyFiveRawOrbitYEightDenominator r s ≠ 0) :
    orderTwentyFiveRawOrbitYEight r s =
      -(A r s * B r s * E r s) / L r s := by
  have hL := l_ne_zero_of_yEightDenominator_ne_zero r s hA hB hC hYEight
  rw [orderTwentyFiveRawOrbitYEight, div_eq_iff hYEight]
  rw [orderTwentyFiveRawOrbitYEightNumerator,
    abscissaEight_sub_four_eq r s hC,
    abscissaSix_sub_three_eq r s hB,
    yEightDenominator_eq r s hA hB hC]
  field_simp [hA, hB, hC, hL]

theorem yNine_eq_factor (r s : ℚ)
    (hs : s ≠ 0) (hA : A r s ≠ 0) (hB : B r s ≠ 0)
    (hC : C r s ≠ 0) (hD : D r s ≠ 0) (hE : E r s ≠ 0)
    (hK : K r s ≠ 0)
    (hYNine : orderTwentyFiveRawOrbitYNineDenominator r s ≠ 0) :
    orderTwentyFiveRawOrbitYNine r s =
      -(K r s * D r s * M r s * N r s) /
        (s * A r s * C r s ^ 2 * P9 r s) := by
  have hP9 :=
    p9_ne_zero_of_yNineDenominator_ne_zero r s hB hD hE hK hYNine
  rw [orderTwentyFiveRawOrbitYNine, div_eq_iff hYNine]
  rw [orderTwentyFiveRawOrbitYNineNumerator,
    abscissaNine_sub_eight_eq r s hC hK,
    abscissaTwelve_sub_six_eq r s hB hE,
    yNineDenominator_eq r s hB hD hE hK]
  field_simp [hs, hA, hB, hC, hD, hE, hK, hP9]

end MazurTorsion.Kubert.OrderTwentyFiveRawOrbitFactorCertificate
