/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationFourCertificateLHSData
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Checked RelationFour left-side coefficients of degrees twelve through twenty-three -/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Internal

private theorem lhs_coefficient_12 (s : ℚ) :
    lhsCoefficientEq 12 s := by
  norm_num [lhsCoefficientEq, termZeroCoefficient, termOneCoefficient,
    termTwoCoefficient, termThreeCoefficient, termZeroCoefficientMid,
    termOneCoefficientMid, termTwoCoefficientMid,
    termThreeCoefficientMid, numeratorCoefficient]
  ring

private theorem lhs_coefficient_13 (s : ℚ) :
    lhsCoefficientEq 13 s := by
  norm_num [lhsCoefficientEq, termZeroCoefficient, termOneCoefficient,
    termTwoCoefficient, termThreeCoefficient, termZeroCoefficientMid,
    termOneCoefficientMid, termTwoCoefficientMid,
    termThreeCoefficientMid, numeratorCoefficient]
  ring

private theorem lhs_coefficient_14 (s : ℚ) :
    lhsCoefficientEq 14 s := by
  norm_num [lhsCoefficientEq, termZeroCoefficient, termOneCoefficient,
    termTwoCoefficient, termThreeCoefficient, termZeroCoefficientMid,
    termOneCoefficientMid, termTwoCoefficientMid,
    termThreeCoefficientMid, numeratorCoefficient]
  ring

private theorem lhs_coefficient_15 (s : ℚ) :
    lhsCoefficientEq 15 s := by
  norm_num [lhsCoefficientEq, termZeroCoefficient, termOneCoefficient,
    termTwoCoefficient, termThreeCoefficient, termZeroCoefficientMid,
    termOneCoefficientMid, termTwoCoefficientMid,
    termThreeCoefficientMid, numeratorCoefficient]
  ring

private theorem lhs_coefficient_16 (s : ℚ) :
    lhsCoefficientEq 16 s := by
  norm_num [lhsCoefficientEq, termZeroCoefficient, termOneCoefficient,
    termTwoCoefficient, termThreeCoefficient, termZeroCoefficientMid,
    termOneCoefficientMid, termTwoCoefficientMid,
    termThreeCoefficientMid, numeratorCoefficient]
  ring

private theorem lhs_coefficient_17 (s : ℚ) :
    lhsCoefficientEq 17 s := by
  norm_num [lhsCoefficientEq, termZeroCoefficient, termOneCoefficient,
    termTwoCoefficient, termThreeCoefficient, termZeroCoefficientMid,
    termOneCoefficientMid, termTwoCoefficientMid,
    termThreeCoefficientMid, numeratorCoefficient]
  ring

private theorem lhs_coefficient_18 (s : ℚ) :
    lhsCoefficientEq 18 s := by
  norm_num [lhsCoefficientEq, termZeroCoefficient, termOneCoefficient,
    termTwoCoefficient, termThreeCoefficient, termZeroCoefficientMid,
    termOneCoefficientMid, termTwoCoefficientMid,
    termThreeCoefficientMid, numeratorCoefficient]
  ring

private theorem lhs_coefficient_19 (s : ℚ) :
    lhsCoefficientEq 19 s := by
  norm_num [lhsCoefficientEq, termZeroCoefficient, termOneCoefficient,
    termTwoCoefficient, termThreeCoefficient, termZeroCoefficientMid,
    termOneCoefficientMid, termTwoCoefficientMid,
    termThreeCoefficientMid, numeratorCoefficient]
  ring

private theorem lhs_coefficient_20 (s : ℚ) :
    lhsCoefficientEq 20 s := by
  norm_num [lhsCoefficientEq, termZeroCoefficient, termOneCoefficient,
    termTwoCoefficient, termThreeCoefficient, termZeroCoefficientMid,
    termOneCoefficientMid, termTwoCoefficientMid,
    termThreeCoefficientMid, numeratorCoefficient]
  ring

private theorem lhs_coefficient_21 (s : ℚ) :
    lhsCoefficientEq 21 s := by
  norm_num [lhsCoefficientEq, termZeroCoefficient, termOneCoefficient,
    termTwoCoefficient, termThreeCoefficient, termZeroCoefficientMid,
    termOneCoefficientMid, termTwoCoefficientMid,
    termThreeCoefficientMid, numeratorCoefficient]
  ring

private theorem lhs_coefficient_22 (s : ℚ) :
    lhsCoefficientEq 22 s := by
  norm_num [lhsCoefficientEq, termZeroCoefficient, termOneCoefficient,
    termTwoCoefficient, termThreeCoefficient, termZeroCoefficientMid,
    termOneCoefficientMid, termTwoCoefficientMid,
    termThreeCoefficientMid, numeratorCoefficient]
  ring

private theorem lhs_coefficient_23 (s : ℚ) :
    lhsCoefficientEq 23 s := by
  norm_num [lhsCoefficientEq, termZeroCoefficient, termOneCoefficient,
    termTwoCoefficient, termThreeCoefficient, termZeroCoefficientMid,
    termOneCoefficientMid, termTwoCoefficientMid,
    termThreeCoefficientMid, numeratorCoefficient]
  ring

theorem lhs_coefficients_mid (s : ℚ) (n : Nat)
    (hlo : 12 ≤ n) (hi : n ≤ 23) :
    lhsCoefficientEq n s := by
  interval_cases n <;>
    simp only [lhs_coefficient_12, lhs_coefficient_13, lhs_coefficient_14,
      lhs_coefficient_15, lhs_coefficient_16, lhs_coefficient_17,
      lhs_coefficient_18, lhs_coefficient_19, lhs_coefficient_20,
      lhs_coefficient_21, lhs_coefficient_22, lhs_coefficient_23]

end MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Internal
