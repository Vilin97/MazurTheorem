/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroCertificateLHSData
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroDenseTermTwoCoefficientsLow
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroDenseTermTwoCoefficientsMid
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroDenseTermTwoCoefficientsHigh
import Mathlib.Tactic.Ring

/-!
# Checked expansion of cleared term two

The factored expression is evaluated through the checked dense multiplication
chain. Its 32 nonzero outer coefficients were checked independently against
`T2C0` through `T2C31`; `T2C32` is definitionally zero.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Dense

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveRelationZeroCertificate.Internal

theorem eval_T2Stage20_eq_term2 (r s : ℚ) :
    Two.eval T2Stage20 r s = term2 r s := by
  rw [← t2_stage20_spec, Two.eval_mul, eval_TData,
    ← t2_stage19_spec, Two.eval_mul, eval_MData,
    ← t2_stage18_spec, Two.eval_mul, eval_KData,
    ← t2_stage17_spec, Two.eval_mul, eval_CData,
    ← t2_stage16_spec, Two.eval_mul, eval_BData,
    ← t2_stage15_spec, Two.eval_mul, eval_BData,
    ← t2_stage14_spec, Two.eval_mul, eval_BData,
    ← t2_stage13_spec, Two.eval_mul, eval_RData,
    ← t2_stage12_spec, Two.eval_mul, eval_P9Data,
    ← t2_stage11_spec, Two.eval_mul, eval_JData,
    ← t2_stage10_spec, Two.eval_mul, eval_EData,
    ← t2_stage9_spec, Two.eval_mul, eval_EData,
    ← t2_stage8_spec, Two.eval_mul, eval_KData,
    ← t2_stage7_spec, Two.eval_mul, eval_KData,
    ← t2_stage6_spec, Two.eval_mul, eval_CData,
    ← t2_stage5_spec, Two.eval_mul, eval_CData,
    ← t2_stage4_spec, Two.eval_mul, eval_CData,
    ← t2_stage3_spec, Two.eval_mul, eval_BData,
    ← t2_stage2_spec, Two.eval_mul, eval_BData,
    ← t2_stage1_spec, Two.eval_mul, eval_RData, eval_SData]
  simp only [term2]
  ring

theorem eval_T2Stage20_eq_T2 (r s : ℚ) :
    Two.eval T2Stage20 r s = T2 r s := by
  simp only [Two.eval, T2Stage20, evalWith,
    t2_coefficient_0, t2_coefficient_1, t2_coefficient_2,
    t2_coefficient_3, t2_coefficient_4, t2_coefficient_5,
    t2_coefficient_6, t2_coefficient_7, t2_coefficient_8,
    t2_coefficient_9, t2_coefficient_10, t2_coefficient_11,
    t2_coefficient_12, t2_coefficient_13, t2_coefficient_14,
    t2_coefficient_15, t2_coefficient_16, t2_coefficient_17,
    t2_coefficient_18, t2_coefficient_19, t2_coefficient_20,
    t2_coefficient_21, t2_coefficient_22, t2_coefficient_23,
    t2_coefficient_24, t2_coefficient_25, t2_coefficient_26,
    t2_coefficient_27, t2_coefficient_28, t2_coefficient_29,
    t2_coefficient_30, t2_coefficient_31, T2, T2C32]
  ring

end MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Dense

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Internal

theorem term2_expansion (r s : ℚ) :
    term2 r s = T2 r s := by
  rw [← Dense.eval_T2Stage20_eq_term2, Dense.eval_T2Stage20_eq_T2]

end MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Internal
