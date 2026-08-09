/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroCertificateLHSData
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroDenseTermOneCoefficientsLow
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroDenseTermOneCoefficientsMid
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroDenseTermOneCoefficientsHigh
import Mathlib.Tactic.Ring

/-!
# Checked expansion of cleared term one

The factored expression is evaluated through the checked dense multiplication
chain. Its 33 outer coefficients were checked independently against `T1C0`
through `T1C32`.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Dense

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveRelationZeroCertificate.Internal

theorem eval_T1Stage18_eq_term1 (r s : ℚ) :
    Two.eval T1Stage18 r s = term1 r s := by
  rw [← t1_stage18_spec, Two.eval_mul, eval_NData,
    ← t1_stage17_spec, Two.eval_mul, eval_MData,
    ← t1_stage16_spec, Two.eval_mul, eval_TData,
    ← t1_stage15_spec, Two.eval_mul, eval_EData,
    ← t1_stage14_spec, Two.eval_mul, eval_KData,
    ← t1_stage13_spec, Two.eval_mul, eval_KData,
    ← t1_stage12_spec, Two.eval_mul, eval_KData,
    ← t1_stage11_spec, Two.eval_mul, eval_BData,
    ← t1_stage10_spec, Two.eval_mul, eval_RData,
    ← t1_stage9_spec, Two.eval_mul, eval_P6Data,
    ← t1_stage8_spec, Two.eval_mul, eval_EData,
    ← t1_stage7_spec, Two.eval_mul, eval_EData,
    ← t1_stage6_spec, Two.eval_mul, eval_DData,
    ← t1_stage5_spec, Two.eval_mul, eval_KData,
    ← t1_stage4_spec, Two.eval_mul, eval_KData,
    ← t1_stage3_spec, Two.eval_mul, eval_BData,
    ← t1_stage2_spec, Two.eval_mul, eval_BData,
    ← t1_stage1_spec, Two.eval_mul, eval_NegData, eval_RData]
  simp only [term1]
  ring

theorem eval_T1Stage18_eq_T1 (r s : ℚ) :
    Two.eval T1Stage18 r s = T1 r s := by
  simp only [Two.eval, T1Stage18, evalWith,
    t1_coefficient_0, t1_coefficient_1, t1_coefficient_2,
    t1_coefficient_3, t1_coefficient_4, t1_coefficient_5,
    t1_coefficient_6, t1_coefficient_7, t1_coefficient_8,
    t1_coefficient_9, t1_coefficient_10, t1_coefficient_11,
    t1_coefficient_12, t1_coefficient_13, t1_coefficient_14,
    t1_coefficient_15, t1_coefficient_16, t1_coefficient_17,
    t1_coefficient_18, t1_coefficient_19, t1_coefficient_20,
    t1_coefficient_21, t1_coefficient_22, t1_coefficient_23,
    t1_coefficient_24, t1_coefficient_25, t1_coefficient_26,
    t1_coefficient_27, t1_coefficient_28, t1_coefficient_29,
    t1_coefficient_30, t1_coefficient_31, t1_coefficient_32, T1]
  ring

end MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Dense

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Internal

theorem term1_expansion (r s : ℚ) :
    term1 r s = T1 r s := by
  rw [← Dense.eval_T1Stage18_eq_term1, Dense.eval_T1Stage18_eq_T1]

end MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Internal
