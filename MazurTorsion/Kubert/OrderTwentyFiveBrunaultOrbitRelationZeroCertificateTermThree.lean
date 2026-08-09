/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroCertificateLHSData
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroDenseTermThreeCoefficientsLow
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroDenseTermThreeCoefficientsMid
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroDenseTermThreeCoefficientsHigh
import Mathlib.Tactic.Ring

/-!
# Checked expansion of cleared term three

The factored expression is evaluated through the checked dense multiplication
chain. Its 33 outer coefficients were checked independently against `T3C0`
through `T3C32`.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Dense

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveRelationZeroCertificate.Internal

theorem eval_T3Stage12_eq_term3 (r s : ℚ) :
    Two.eval T3Stage12 r s = term3 r s := by
  rw [← t3_stage12_spec, Two.eval_mul, eval_TData,
    ← t3_stage11_spec, Two.eval_mul, eval_LData,
    ← t3_stage10_spec, Two.eval_mul, eval_JData,
    ← t3_stage9_spec, Two.eval_mul, eval_CData,
    ← t3_stage8_spec, Two.eval_mul, eval_AData,
    ← t3_stage7_spec, Two.eval_mul, eval_AData,
    ← t3_stage6_spec, Two.eval_mul, eval_P9Data,
    ← t3_stage5_spec, Two.eval_mul, eval_P6Data,
    ← t3_stage4_spec, Two.eval_mul, eval_JData,
    ← t3_stage3_spec, Two.eval_mul, eval_CData,
    ← t3_stage2_spec, Two.eval_mul, eval_CData,
    ← t3_stage1_spec, Two.eval_mul, eval_SData, eval_CData]
  simp only [term3]
  ring

theorem eval_T3Stage12_eq_T3 (r s : ℚ) :
    Two.eval T3Stage12 r s = T3 r s := by
  simp only [Two.eval, T3Stage12, evalWith,
    t3_coefficient_0, t3_coefficient_1, t3_coefficient_2,
    t3_coefficient_3, t3_coefficient_4, t3_coefficient_5,
    t3_coefficient_6, t3_coefficient_7, t3_coefficient_8,
    t3_coefficient_9, t3_coefficient_10, t3_coefficient_11,
    t3_coefficient_12, t3_coefficient_13, t3_coefficient_14,
    t3_coefficient_15, t3_coefficient_16, t3_coefficient_17,
    t3_coefficient_18, t3_coefficient_19, t3_coefficient_20,
    t3_coefficient_21, t3_coefficient_22, t3_coefficient_23,
    t3_coefficient_24, t3_coefficient_25, t3_coefficient_26,
    t3_coefficient_27, t3_coefficient_28, t3_coefficient_29,
    t3_coefficient_30, t3_coefficient_31, t3_coefficient_32, T3]
  ring

end MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Dense

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Internal

theorem term3_expansion (r s : ℚ) :
    term3 r s = T3 r s := by
  rw [← Dense.eval_T3Stage12_eq_term3, Dense.eval_T3Stage12_eq_T3]

end MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Internal
