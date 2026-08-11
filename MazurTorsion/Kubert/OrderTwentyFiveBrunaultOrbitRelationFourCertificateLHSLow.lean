/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationFourCertificateLHSData
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Checked RelationFour left-side coefficients of degrees zero through eleven -/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Internal

private theorem lhs_coefficient_0 (s : ℚ) :
    lhsCoefficientEq 0 s := by
  norm_num [lhsCoefficientEq, termZeroCoefficient, termOneCoefficient,
    termTwoCoefficient, termThreeCoefficient, termZeroCoefficientLow,
    termOneCoefficientLow, termTwoCoefficientLow,
    termThreeCoefficientLow, numeratorCoefficient]
  ring

private theorem lhs_coefficient_1 (s : ℚ) :
    lhsCoefficientEq 1 s := by
  norm_num [lhsCoefficientEq, termZeroCoefficient, termOneCoefficient,
    termTwoCoefficient, termThreeCoefficient, termZeroCoefficientLow,
    termOneCoefficientLow, termTwoCoefficientLow,
    termThreeCoefficientLow, numeratorCoefficient]
  ring

private theorem lhs_coefficient_2 (s : ℚ) :
    lhsCoefficientEq 2 s := by
  norm_num [lhsCoefficientEq, termZeroCoefficient, termOneCoefficient,
    termTwoCoefficient, termThreeCoefficient, termZeroCoefficientLow,
    termOneCoefficientLow, termTwoCoefficientLow,
    termThreeCoefficientLow, numeratorCoefficient]
  ring

private theorem lhs_coefficient_3 (s : ℚ) :
    lhsCoefficientEq 3 s := by
  norm_num [lhsCoefficientEq, termZeroCoefficient, termOneCoefficient,
    termTwoCoefficient, termThreeCoefficient, termZeroCoefficientLow,
    termOneCoefficientLow, termTwoCoefficientLow,
    termThreeCoefficientLow, numeratorCoefficient]
  ring

private theorem lhs_coefficient_4 (s : ℚ) :
    lhsCoefficientEq 4 s := by
  norm_num [lhsCoefficientEq, termZeroCoefficient, termOneCoefficient,
    termTwoCoefficient, termThreeCoefficient, termZeroCoefficientLow,
    termOneCoefficientLow, termTwoCoefficientLow,
    termThreeCoefficientLow, numeratorCoefficient]
  ring

private theorem lhs_coefficient_5 (s : ℚ) :
    lhsCoefficientEq 5 s := by
  norm_num [lhsCoefficientEq, termZeroCoefficient, termOneCoefficient,
    termTwoCoefficient, termThreeCoefficient, termZeroCoefficientLow,
    termOneCoefficientLow, termTwoCoefficientLow,
    termThreeCoefficientLow, numeratorCoefficient]
  ring

private theorem lhs_coefficient_6 (s : ℚ) :
    lhsCoefficientEq 6 s := by
  norm_num [lhsCoefficientEq, termZeroCoefficient, termOneCoefficient,
    termTwoCoefficient, termThreeCoefficient, termZeroCoefficientLow,
    termOneCoefficientLow, termTwoCoefficientLow,
    termThreeCoefficientLow, numeratorCoefficient]
  ring

private theorem lhs_coefficient_7 (s : ℚ) :
    lhsCoefficientEq 7 s := by
  norm_num [lhsCoefficientEq, termZeroCoefficient, termOneCoefficient,
    termTwoCoefficient, termThreeCoefficient, termZeroCoefficientLow,
    termOneCoefficientLow, termTwoCoefficientLow,
    termThreeCoefficientLow, numeratorCoefficient]
  ring

private theorem lhs_coefficient_8 (s : ℚ) :
    lhsCoefficientEq 8 s := by
  norm_num [lhsCoefficientEq, termZeroCoefficient, termOneCoefficient,
    termTwoCoefficient, termThreeCoefficient, termZeroCoefficientLow,
    termOneCoefficientLow, termTwoCoefficientLow,
    termThreeCoefficientLow, numeratorCoefficient]
  ring

private theorem lhs_coefficient_9 (s : ℚ) :
    lhsCoefficientEq 9 s := by
  norm_num [lhsCoefficientEq, termZeroCoefficient, termOneCoefficient,
    termTwoCoefficient, termThreeCoefficient, termZeroCoefficientLow,
    termOneCoefficientLow, termTwoCoefficientLow,
    termThreeCoefficientLow, numeratorCoefficient]
  ring

private theorem lhs_coefficient_10 (s : ℚ) :
    lhsCoefficientEq 10 s := by
  norm_num [lhsCoefficientEq, termZeroCoefficient, termOneCoefficient,
    termTwoCoefficient, termThreeCoefficient, termZeroCoefficientLow,
    termOneCoefficientLow, termTwoCoefficientLow,
    termThreeCoefficientLow, numeratorCoefficient]
  ring

private theorem lhs_coefficient_11 (s : ℚ) :
    lhsCoefficientEq 11 s := by
  norm_num [lhsCoefficientEq, termZeroCoefficient, termOneCoefficient,
    termTwoCoefficient, termThreeCoefficient, termZeroCoefficientLow,
    termOneCoefficientLow, termTwoCoefficientLow,
    termThreeCoefficientLow, numeratorCoefficient]
  ring

theorem lhs_coefficients_low (s : ℚ) (n : Nat) (hn : n ≤ 11) :
    lhsCoefficientEq n s := by
  interval_cases n <;>
    simp only [lhs_coefficient_0, lhs_coefficient_1, lhs_coefficient_2,
      lhs_coefficient_3, lhs_coefficient_4, lhs_coefficient_5,
      lhs_coefficient_6, lhs_coefficient_7, lhs_coefficient_8,
      lhs_coefficient_9, lhs_coefficient_10, lhs_coefficient_11]

end MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Internal
