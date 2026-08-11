/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationFourCertificateLHSData
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Checked RelationFour left-side coefficients of degrees twenty-four through thirty-four -/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Internal

private theorem lhs_coefficient_24 (s : ℚ) :
    lhsCoefficientEq 24 s := by
  norm_num [lhsCoefficientEq, termZeroCoefficient, termOneCoefficient,
    termTwoCoefficient, termThreeCoefficient, termZeroCoefficientHigh,
    termOneCoefficientHigh, termTwoCoefficientHigh,
    termThreeCoefficientHigh, numeratorCoefficient]
  ring

private theorem lhs_coefficient_25 (s : ℚ) :
    lhsCoefficientEq 25 s := by
  norm_num [lhsCoefficientEq, termZeroCoefficient, termOneCoefficient,
    termTwoCoefficient, termThreeCoefficient, termZeroCoefficientHigh,
    termOneCoefficientHigh, termTwoCoefficientHigh,
    termThreeCoefficientHigh, numeratorCoefficient]
  ring

private theorem lhs_coefficient_26 (s : ℚ) :
    lhsCoefficientEq 26 s := by
  norm_num [lhsCoefficientEq, termZeroCoefficient, termOneCoefficient,
    termTwoCoefficient, termThreeCoefficient, termZeroCoefficientHigh,
    termOneCoefficientHigh, termTwoCoefficientHigh,
    termThreeCoefficientHigh, numeratorCoefficient]
  ring

private theorem lhs_coefficient_27 (s : ℚ) :
    lhsCoefficientEq 27 s := by
  norm_num [lhsCoefficientEq, termZeroCoefficient, termOneCoefficient,
    termTwoCoefficient, termThreeCoefficient, termZeroCoefficientHigh,
    termOneCoefficientHigh, termTwoCoefficientHigh,
    termThreeCoefficientHigh, numeratorCoefficient]
  ring

private theorem lhs_coefficient_28 (s : ℚ) :
    lhsCoefficientEq 28 s := by
  norm_num [lhsCoefficientEq, termZeroCoefficient, termOneCoefficient,
    termTwoCoefficient, termThreeCoefficient, termZeroCoefficientHigh,
    termOneCoefficientHigh, termTwoCoefficientHigh,
    termThreeCoefficientHigh, numeratorCoefficient]
  ring

private theorem lhs_coefficient_29 (s : ℚ) :
    lhsCoefficientEq 29 s := by
  norm_num [lhsCoefficientEq, termZeroCoefficient, termOneCoefficient,
    termTwoCoefficient, termThreeCoefficient, termZeroCoefficientHigh,
    termOneCoefficientHigh, termTwoCoefficientHigh,
    termThreeCoefficientHigh, numeratorCoefficient]
  ring

private theorem lhs_coefficient_30 (s : ℚ) :
    lhsCoefficientEq 30 s := by
  norm_num [lhsCoefficientEq, termZeroCoefficient, termOneCoefficient,
    termTwoCoefficient, termThreeCoefficient, termZeroCoefficientHigh,
    termOneCoefficientHigh, termTwoCoefficientHigh,
    termThreeCoefficientHigh, numeratorCoefficient]
  ring

private theorem lhs_coefficient_31 (s : ℚ) :
    lhsCoefficientEq 31 s := by
  norm_num [lhsCoefficientEq, termZeroCoefficient, termOneCoefficient,
    termTwoCoefficient, termThreeCoefficient, termZeroCoefficientHigh,
    termOneCoefficientHigh, termTwoCoefficientHigh,
    termThreeCoefficientHigh, numeratorCoefficient]
  ring

private theorem lhs_coefficient_32 (s : ℚ) :
    lhsCoefficientEq 32 s := by
  norm_num [lhsCoefficientEq, termZeroCoefficient, termOneCoefficient,
    termTwoCoefficient, termThreeCoefficient, termZeroCoefficientHigh,
    termOneCoefficientHigh, termTwoCoefficientHigh,
    termThreeCoefficientHigh, numeratorCoefficient]
  ring

private theorem lhs_coefficient_33 (s : ℚ) :
    lhsCoefficientEq 33 s := by
  norm_num [lhsCoefficientEq, termZeroCoefficient, termOneCoefficient,
    termTwoCoefficient, termThreeCoefficient, termZeroCoefficientHigh,
    termOneCoefficientHigh, termTwoCoefficientHigh,
    termThreeCoefficientHigh, numeratorCoefficient]
  ring

private theorem lhs_coefficient_34 (s : ℚ) :
    lhsCoefficientEq 34 s := by
  norm_num [lhsCoefficientEq, termZeroCoefficient, termOneCoefficient,
    termTwoCoefficient, termThreeCoefficient, termZeroCoefficientHigh,
    termOneCoefficientHigh, termTwoCoefficientHigh,
    termThreeCoefficientHigh, numeratorCoefficient]
  ring

theorem lhs_coefficients_high (s : ℚ) (n : Nat)
    (hlo : 24 ≤ n) (hi : n ≤ 34) :
    lhsCoefficientEq n s := by
  interval_cases n <;>
    simp only [lhs_coefficient_24, lhs_coefficient_25, lhs_coefficient_26,
      lhs_coefficient_27, lhs_coefficient_28, lhs_coefficient_29,
      lhs_coefficient_30, lhs_coefficient_31, lhs_coefficient_32,
      lhs_coefficient_33, lhs_coefficient_34]

end MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Internal
