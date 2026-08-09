/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationFiveDenseCertificate
import Mathlib.Tactic.FieldSimp

/-!
# The norm-one relation for the raw order-twenty-five orbit

The dense certificate proves the only large polynomial identity.  This leaf
then combines the five checked factor formulas, retaining every denominator
hypothesis needed to justify cancellation.
-/

namespace MazurTorsion.Kubert

open OrderTwentyFiveRawOrbitFactorCertificate
open OrderTwentyFiveRelationFiveDenseCertificate

/-- Sutherland's raw equation and the nonvanishing denominators of the five
Lécacheux modular units imply the raw norm-one orbit relation. -/
theorem orderTwentyFiveRawOrbit_relationFive_eq_zero (r s : ℚ)
    (hr : r ≠ 0) (hs : s ≠ 0)
    (hA : r - s ≠ 0)
    (hB : s - 1 ≠ 0)
    (hC : r * s - 2 * r + 1 ≠ 0)
    (hK : r - s ^ 2 + s - 1 ≠ 0)
    (hD : r ^ 2 - r * s ^ 3 + 3 * r * s ^ 2 - 4 * r * s + s ≠ 0)
    (hE : r ^ 2 * s - 3 * r ^ 2 + r * s + 3 * r - s ^ 2 - 1 ≠ 0)
    (hYOne : orderTwentyFiveRawOrbitYOneDenominator r s ≠ 0)
    (hYTwo : orderTwentyFiveRawOrbitYTwoDenominator r s ≠ 0)
    (hYFour : orderTwentyFiveRawOrbitYFourDenominator r s ≠ 0)
    (hYEight : orderTwentyFiveRawOrbitYEightDenominator r s ≠ 0)
    (hYNine : orderTwentyFiveRawOrbitYNineDenominator r s ≠ 0)
    (hF : orderTwentyFiveRawSutherlandF r s = 0) :
    orderTwentyFiveOrbitRelationFive
      (orderTwentyFiveRawOrbitXZero r s)
      (orderTwentyFiveRawOrbitXOne r s)
      (orderTwentyFiveRawOrbitXTwo r s)
      (orderTwentyFiveRawOrbitXThree r s)
      (orderTwentyFiveRawOrbitXFour r s) = 0 := by
  have hA' : A r s ≠ 0 := by simpa only [A] using hA
  have hB' : B r s ≠ 0 := by simpa only [B] using hB
  have hC' : C r s ≠ 0 := by simpa only [C] using hC
  have hK' : K r s ≠ 0 := by simpa only [K] using hK
  have hD' : D r s ≠ 0 := by simpa only [D] using hD
  have hE' : E r s ≠ 0 := by simpa only [E] using hE
  have hJ :=
    j_ne_zero_of_yFourDenominator_ne_zero r s hB' hE' hK' hYFour
  have hL :=
    l_ne_zero_of_yEightDenominator_ne_zero r s hA' hB' hC' hYEight
  have hP6 :=
    p6_ne_zero_of_yTwoDenominator_ne_zero r s hB' hC' hD' hYTwo
  have hP9 :=
    p9_ne_zero_of_yNineDenominator_ne_zero r s hB' hD' hE' hK' hYNine
  have hcleared := clearedProduct_eq_zero_of_sutherland r s hF
  have hden :
      s * A r s * C r s * D r s * P6 r s * P9 r s ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero
            (mul_ne_zero hs hA') hC') hD') hP6) hP9
  have hyproduct :
      orderTwentyFiveRawOrbitYOne r s *
          orderTwentyFiveRawOrbitYTwo r s *
          orderTwentyFiveRawOrbitYFour r s *
          orderTwentyFiveRawOrbitYEight r s *
          orderTwentyFiveRawOrbitYNine r s = 1 := by
    rw [yOne_eq_factor r s hr hA' hB' hE' hK' hYOne,
      yTwo_eq_factor r s hA' hB' hC' hD' hYTwo,
      yFour_eq_factor r s hB' hC' hD' hE' hK' hYFour,
      yEight_eq_factor r s hA' hB' hC' hYEight,
      yNine_eq_factor r s hs hA' hB' hC' hD' hE' hK' hYNine]
    calc
      C r s * L r s * J r s / (r * B r s ^ 2 * K r s ^ 2 * E r s ^ 2) *
            (-(r * B r s ^ 3 * C r s * K r s * M r s) /
              (A r s ^ 2 * P6 r s)) *
            (-(r * A r s * B r s * K r s ^ 2 * E r s * T r s) /
              (C r s * D r s ^ 2 * J r s)) *
            (-(A r s * B r s * E r s) / L r s) *
            (-(K r s * D r s * M r s * N r s) /
              (s * A r s * C r s ^ 2 * P9 r s)) =
          (r * B r s ^ 3 * K r s ^ 2 * M r s ^ 2 * N r s * T r s) /
            (s * A r s * C r s * D r s * P6 r s * P9 r s) := by
              field_simp [hr, hs, hA', hB', hC', hD', hE', hJ, hK', hL,
                hP6, hP9]
      _ = 1 := by
        apply (div_eq_iff hden).2
        simpa only [one_mul] using sub_eq_zero.mp hcleared
  simp only [orderTwentyFiveOrbitRelationFive,
    orderTwentyFiveRawOrbitXZero, orderTwentyFiveRawOrbitXOne,
    orderTwentyFiveRawOrbitXTwo, orderTwentyFiveRawOrbitXThree,
    orderTwentyFiveRawOrbitXFour]
  calc
    orderTwentyFiveRawOrbitYOne r s * orderTwentyFiveRawOrbitYFour r s *
          (orderTwentyFiveRawOrbitYTwo r s * orderTwentyFiveRawOrbitYEight r s) *
          (orderTwentyFiveRawOrbitYFour r s * orderTwentyFiveRawOrbitYNine r s) *
          (orderTwentyFiveRawOrbitYEight r s * orderTwentyFiveRawOrbitYOne r s) *
          (orderTwentyFiveRawOrbitYNine r s * orderTwentyFiveRawOrbitYTwo r s) - 1 =
        (orderTwentyFiveRawOrbitYOne r s *
          orderTwentyFiveRawOrbitYTwo r s *
          orderTwentyFiveRawOrbitYFour r s *
          orderTwentyFiveRawOrbitYEight r s *
          orderTwentyFiveRawOrbitYNine r s) ^ 2 - 1 := by ring
    _ = 0 := by rw [hyproduct]; norm_num

end MazurTorsion.Kubert
