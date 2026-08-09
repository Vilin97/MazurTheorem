/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroCertificateLHSData
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroDenseTermZeroCoefficientsLow
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroDenseTermZeroCoefficientsMid
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroDenseTermZeroCoefficientsHigh
import Mathlib.Tactic.Ring

/-!
# Checked expansion of cleared term zero

The factored expression is evaluated through the checked dense multiplication
chain.  Its 33 outer coefficients were checked independently against `T0C0`
through `T0C32`.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Dense

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveRelationZeroCertificate.Internal

theorem eval_T0Stage15_eq_term0 (r s : ℚ) :
    Two.eval T0Stage15 r s = term0 r s := by
  rw [← t0_stage15_spec, Two.eval_mul, eval_TData,
    ← t0_stage14_spec, Two.eval_mul, eval_LData,
    ← t0_stage13_spec, Two.eval_mul, eval_AData,
    ← t0_stage12_spec, Two.eval_mul, eval_P9Data,
    ← t0_stage11_spec, Two.eval_mul, eval_P6Data,
    ← t0_stage10_spec, Two.eval_mul, eval_JData,
    ← t0_stage9_spec, Two.eval_mul, eval_EData,
    ← t0_stage8_spec, Two.eval_mul, eval_KData,
    ← t0_stage7_spec, Two.eval_mul, eval_KData,
    ← t0_stage6_spec, Two.eval_mul, eval_CData,
    ← t0_stage5_spec, Two.eval_mul, eval_CData,
    ← t0_stage4_spec, Two.eval_mul, eval_CData,
    ← t0_stage3_spec, Two.eval_mul, eval_BData,
    ← t0_stage2_spec, Two.eval_mul, eval_SData,
    ← t0_stage1_spec, Two.eval_mul, eval_NegData, eval_RData]
  simp only [term0]
  ring

theorem eval_T0Stage15_eq_T0 (r s : ℚ) :
    Two.eval T0Stage15 r s = T0 r s := by
  simp only [Two.eval, T0Stage15, evalWith,
    t0_coefficient_0, t0_coefficient_1, t0_coefficient_2,
    t0_coefficient_3, t0_coefficient_4, t0_coefficient_5,
    t0_coefficient_6, t0_coefficient_7, t0_coefficient_8,
    t0_coefficient_9, t0_coefficient_10, t0_coefficient_11,
    t0_coefficient_12, t0_coefficient_13, t0_coefficient_14,
    t0_coefficient_15, t0_coefficient_16, t0_coefficient_17,
    t0_coefficient_18, t0_coefficient_19, t0_coefficient_20,
    t0_coefficient_21, t0_coefficient_22, t0_coefficient_23,
    t0_coefficient_24, t0_coefficient_25, t0_coefficient_26,
    t0_coefficient_27, t0_coefficient_28, t0_coefficient_29,
    t0_coefficient_30, t0_coefficient_31, t0_coefficient_32, T0]
  ring

end MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Dense

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Internal

theorem term0_expansion (r s : ℚ) :
    term0 r s = T0 r s := by
  rw [← Dense.eval_T0Stage15_eq_term0, Dense.eval_T0Stage15_eq_T0]

end MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Internal
