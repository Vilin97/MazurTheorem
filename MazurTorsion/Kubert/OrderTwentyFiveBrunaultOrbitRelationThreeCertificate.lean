/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationThreeDenseBridge
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# The fourth cyclic relation for the raw order-twenty-five orbit

This leaf applies the checked cleared-denominator certificate to the four
modular units that occur in the relation.  The fifth unit is only an outer
factor, so no nonvanishing premise for its denominator is needed.
-/

namespace MazurTorsion.Kubert

open OrderTwentyFiveRawOrbitFactorCertificate
open OrderTwentyFiveRelationThreeDenseCertificate
open OrderTwentyFiveRelationThreeDenseCertificate.Internal

/-- Sutherland's raw equation and the denominator conditions for the four
relevant modular units imply Lécacheux's fourth cyclic orbit relation. -/
theorem orderTwentyFiveRawOrbit_relationThree_eq_zero (r s : ℚ)
    (hs : s ≠ 0)
    (hA : r - s ≠ 0)
    (hB : s - 1 ≠ 0)
    (hC : r * s - 2 * r + 1 ≠ 0)
    (hK : r - s ^ 2 + s - 1 ≠ 0)
    (hD : r ^ 2 - r * s ^ 3 + 3 * r * s ^ 2 - 4 * r * s + s ≠ 0)
    (hE : r ^ 2 * s - 3 * r ^ 2 + r * s + 3 * r - s ^ 2 - 1 ≠ 0)
    (hYTwo : orderTwentyFiveRawOrbitYTwoDenominator r s ≠ 0)
    (hYFour : orderTwentyFiveRawOrbitYFourDenominator r s ≠ 0)
    (hYEight : orderTwentyFiveRawOrbitYEightDenominator r s ≠ 0)
    (hYNine : orderTwentyFiveRawOrbitYNineDenominator r s ≠ 0)
    (hF : orderTwentyFiveRawSutherlandF r s = 0) :
    orderTwentyFiveOrbitRelationThree
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
  have hcleared := clearedRelationThree_eq_zero_of_sutherland r s hF
  simp only [clearedRelationThree, yTwoNumerator, yTwoDenominator,
    yFourNumerator, yFourDenominator, yEightNumerator, yEightDenominator,
    yNineNumerator, yNineDenominator] at hcleared
  have hcore :
      orderTwentyFiveRawOrbitYEight r s -
          orderTwentyFiveRawOrbitYFour r s -
        orderTwentyFiveRawOrbitYEight r s *
          orderTwentyFiveRawOrbitYTwo r s *
          (orderTwentyFiveRawOrbitYNine r s -
            orderTwentyFiveRawOrbitYEight r s) = 0 := by
    rw [yTwo_eq_factor r s hA' hB' hC' hD' hYTwo,
      yFour_eq_factor r s hB' hC' hD' hE' hK' hYFour,
      yEight_eq_factor r s hA' hB' hC' hYEight,
      yNine_eq_factor r s hs hA' hB' hC' hD' hE' hK' hYNine]
    field_simp [hs, hA', hC', hD', hJ, hL, hP6, hP9]
    linear_combination hcleared
  simp only [orderTwentyFiveOrbitRelationThree,
    orderTwentyFiveRawOrbitXZero, orderTwentyFiveRawOrbitXOne,
    orderTwentyFiveRawOrbitXThree, orderTwentyFiveRawOrbitXFour]
  linear_combination orderTwentyFiveRawOrbitYOne r s * hcore

end MazurTorsion.Kubert
