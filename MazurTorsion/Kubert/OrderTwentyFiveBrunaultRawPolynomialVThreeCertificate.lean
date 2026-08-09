/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialCompositeVData
import MazurTorsion.Kubert.OrderTwentyFiveDensePolynomialRectangular
import Mathlib.Tactic.IntervalCases

/-!
# Checked V cubed table for the raw order-twenty-five certificate

Each generated row is checked in its own theorem.  The final extensional proof
uses every row and separately checks the exact outer lengths.  Since
`rectangularize` only appends zeros, this also checks every possible tail.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveDensePolynomialRectangular

private theorem v3Row0_spec :
    (rectangularize 46 67 (Two.mul VData V2Data)).getD 0 [] =
      (rectangularize 46 67 V3Data).getD 0 [] := by
  decide

private theorem v3Row1_spec :
    (rectangularize 46 67 (Two.mul VData V2Data)).getD 1 [] =
      (rectangularize 46 67 V3Data).getD 1 [] := by
  decide

private theorem v3Row2_spec :
    (rectangularize 46 67 (Two.mul VData V2Data)).getD 2 [] =
      (rectangularize 46 67 V3Data).getD 2 [] := by
  decide

private theorem v3Row3_spec :
    (rectangularize 46 67 (Two.mul VData V2Data)).getD 3 [] =
      (rectangularize 46 67 V3Data).getD 3 [] := by
  decide

private theorem v3Row4_spec :
    (rectangularize 46 67 (Two.mul VData V2Data)).getD 4 [] =
      (rectangularize 46 67 V3Data).getD 4 [] := by
  decide

private theorem v3Row5_spec :
    (rectangularize 46 67 (Two.mul VData V2Data)).getD 5 [] =
      (rectangularize 46 67 V3Data).getD 5 [] := by
  decide

private theorem v3Row6_spec :
    (rectangularize 46 67 (Two.mul VData V2Data)).getD 6 [] =
      (rectangularize 46 67 V3Data).getD 6 [] := by
  decide

private theorem v3Row7_spec :
    (rectangularize 46 67 (Two.mul VData V2Data)).getD 7 [] =
      (rectangularize 46 67 V3Data).getD 7 [] := by
  decide

private theorem v3Row8_spec :
    (rectangularize 46 67 (Two.mul VData V2Data)).getD 8 [] =
      (rectangularize 46 67 V3Data).getD 8 [] := by
  decide

private theorem v3Row9_spec :
    (rectangularize 46 67 (Two.mul VData V2Data)).getD 9 [] =
      (rectangularize 46 67 V3Data).getD 9 [] := by
  decide

private theorem v3Row10_spec :
    (rectangularize 46 67 (Two.mul VData V2Data)).getD 10 [] =
      (rectangularize 46 67 V3Data).getD 10 [] := by
  decide

private theorem v3Row11_spec :
    (rectangularize 46 67 (Two.mul VData V2Data)).getD 11 [] =
      (rectangularize 46 67 V3Data).getD 11 [] := by
  decide

private theorem v3Row12_spec :
    (rectangularize 46 67 (Two.mul VData V2Data)).getD 12 [] =
      (rectangularize 46 67 V3Data).getD 12 [] := by
  decide

private theorem v3Row13_spec :
    (rectangularize 46 67 (Two.mul VData V2Data)).getD 13 [] =
      (rectangularize 46 67 V3Data).getD 13 [] := by
  decide

private theorem v3Row14_spec :
    (rectangularize 46 67 (Two.mul VData V2Data)).getD 14 [] =
      (rectangularize 46 67 V3Data).getD 14 [] := by
  decide

private theorem v3Row15_spec :
    (rectangularize 46 67 (Two.mul VData V2Data)).getD 15 [] =
      (rectangularize 46 67 V3Data).getD 15 [] := by
  decide

private theorem v3Row16_spec :
    (rectangularize 46 67 (Two.mul VData V2Data)).getD 16 [] =
      (rectangularize 46 67 V3Data).getD 16 [] := by
  decide

private theorem v3Row17_spec :
    (rectangularize 46 67 (Two.mul VData V2Data)).getD 17 [] =
      (rectangularize 46 67 V3Data).getD 17 [] := by
  decide

private theorem v3Row18_spec :
    (rectangularize 46 67 (Two.mul VData V2Data)).getD 18 [] =
      (rectangularize 46 67 V3Data).getD 18 [] := by
  decide

private theorem v3Row19_spec :
    (rectangularize 46 67 (Two.mul VData V2Data)).getD 19 [] =
      (rectangularize 46 67 V3Data).getD 19 [] := by
  decide

private theorem v3Row20_spec :
    (rectangularize 46 67 (Two.mul VData V2Data)).getD 20 [] =
      (rectangularize 46 67 V3Data).getD 20 [] := by
  decide

private theorem v3Row21_spec :
    (rectangularize 46 67 (Two.mul VData V2Data)).getD 21 [] =
      (rectangularize 46 67 V3Data).getD 21 [] := by
  decide

private theorem v3Row22_spec :
    (rectangularize 46 67 (Two.mul VData V2Data)).getD 22 [] =
      (rectangularize 46 67 V3Data).getD 22 [] := by
  decide

private theorem v3Row23_spec :
    (rectangularize 46 67 (Two.mul VData V2Data)).getD 23 [] =
      (rectangularize 46 67 V3Data).getD 23 [] := by
  decide

private theorem v3Row24_spec :
    (rectangularize 46 67 (Two.mul VData V2Data)).getD 24 [] =
      (rectangularize 46 67 V3Data).getD 24 [] := by
  decide

private theorem v3Row25_spec :
    (rectangularize 46 67 (Two.mul VData V2Data)).getD 25 [] =
      (rectangularize 46 67 V3Data).getD 25 [] := by
  decide

private theorem v3Row26_spec :
    (rectangularize 46 67 (Two.mul VData V2Data)).getD 26 [] =
      (rectangularize 46 67 V3Data).getD 26 [] := by
  decide

private theorem v3Row27_spec :
    (rectangularize 46 67 (Two.mul VData V2Data)).getD 27 [] =
      (rectangularize 46 67 V3Data).getD 27 [] := by
  decide

private theorem v3Row28_spec :
    (rectangularize 46 67 (Two.mul VData V2Data)).getD 28 [] =
      (rectangularize 46 67 V3Data).getD 28 [] := by
  decide

private theorem v3Row29_spec :
    (rectangularize 46 67 (Two.mul VData V2Data)).getD 29 [] =
      (rectangularize 46 67 V3Data).getD 29 [] := by
  decide

private theorem v3Row30_spec :
    (rectangularize 46 67 (Two.mul VData V2Data)).getD 30 [] =
      (rectangularize 46 67 V3Data).getD 30 [] := by
  decide

private theorem v3Row31_spec :
    (rectangularize 46 67 (Two.mul VData V2Data)).getD 31 [] =
      (rectangularize 46 67 V3Data).getD 31 [] := by
  decide

private theorem v3Row32_spec :
    (rectangularize 46 67 (Two.mul VData V2Data)).getD 32 [] =
      (rectangularize 46 67 V3Data).getD 32 [] := by
  decide

private theorem v3Row33_spec :
    (rectangularize 46 67 (Two.mul VData V2Data)).getD 33 [] =
      (rectangularize 46 67 V3Data).getD 33 [] := by
  decide

private theorem v3Row34_spec :
    (rectangularize 46 67 (Two.mul VData V2Data)).getD 34 [] =
      (rectangularize 46 67 V3Data).getD 34 [] := by
  decide

private theorem v3Row35_spec :
    (rectangularize 46 67 (Two.mul VData V2Data)).getD 35 [] =
      (rectangularize 46 67 V3Data).getD 35 [] := by
  decide

private theorem v3Row36_spec :
    (rectangularize 46 67 (Two.mul VData V2Data)).getD 36 [] =
      (rectangularize 46 67 V3Data).getD 36 [] := by
  decide

private theorem v3Row37_spec :
    (rectangularize 46 67 (Two.mul VData V2Data)).getD 37 [] =
      (rectangularize 46 67 V3Data).getD 37 [] := by
  decide

private theorem v3Row38_spec :
    (rectangularize 46 67 (Two.mul VData V2Data)).getD 38 [] =
      (rectangularize 46 67 V3Data).getD 38 [] := by
  decide

private theorem v3Row39_spec :
    (rectangularize 46 67 (Two.mul VData V2Data)).getD 39 [] =
      (rectangularize 46 67 V3Data).getD 39 [] := by
  decide

private theorem v3Row40_spec :
    (rectangularize 46 67 (Two.mul VData V2Data)).getD 40 [] =
      (rectangularize 46 67 V3Data).getD 40 [] := by
  decide

private theorem v3Row41_spec :
    (rectangularize 46 67 (Two.mul VData V2Data)).getD 41 [] =
      (rectangularize 46 67 V3Data).getD 41 [] := by
  decide

private theorem v3Row42_spec :
    (rectangularize 46 67 (Two.mul VData V2Data)).getD 42 [] =
      (rectangularize 46 67 V3Data).getD 42 [] := by
  decide

private theorem v3Row43_spec :
    (rectangularize 46 67 (Two.mul VData V2Data)).getD 43 [] =
      (rectangularize 46 67 V3Data).getD 43 [] := by
  decide

private theorem v3Row44_spec :
    (rectangularize 46 67 (Two.mul VData V2Data)).getD 44 [] =
      (rectangularize 46 67 V3Data).getD 44 [] := by
  decide

private theorem v3Row45_spec :
    (rectangularize 46 67 (Two.mul VData V2Data)).getD 45 [] =
      (rectangularize 46 67 V3Data).getD 45 [] := by
  decide

private theorem v3Rows_spec (i : ℕ) (hi : i < 46) :
    (rectangularize 46 67 (Two.mul VData V2Data)).getD i [] =
      (rectangularize 46 67 V3Data).getD i [] := by
  have hCases :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨
    i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨
    i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨
    i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨
    i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨
    i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨
    i = 30 ∨ i = 31 ∨ i = 32 ∨ i = 33 ∨ i = 34 ∨
    i = 35 ∨ i = 36 ∨ i = 37 ∨ i = 38 ∨ i = 39 ∨
    i = 40 ∨ i = 41 ∨ i = 42 ∨ i = 43 ∨ i = 44 ∨
    i = 45 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact v3Row0_spec
  · exact v3Row1_spec
  · exact v3Row2_spec
  · exact v3Row3_spec
  · exact v3Row4_spec
  · exact v3Row5_spec
  · exact v3Row6_spec
  · exact v3Row7_spec
  · exact v3Row8_spec
  · exact v3Row9_spec
  · exact v3Row10_spec
  · exact v3Row11_spec
  · exact v3Row12_spec
  · exact v3Row13_spec
  · exact v3Row14_spec
  · exact v3Row15_spec
  · exact v3Row16_spec
  · exact v3Row17_spec
  · exact v3Row18_spec
  · exact v3Row19_spec
  · exact v3Row20_spec
  · exact v3Row21_spec
  · exact v3Row22_spec
  · exact v3Row23_spec
  · exact v3Row24_spec
  · exact v3Row25_spec
  · exact v3Row26_spec
  · exact v3Row27_spec
  · exact v3Row28_spec
  · exact v3Row29_spec
  · exact v3Row30_spec
  · exact v3Row31_spec
  · exact v3Row32_spec
  · exact v3Row33_spec
  · exact v3Row34_spec
  · exact v3Row35_spec
  · exact v3Row36_spec
  · exact v3Row37_spec
  · exact v3Row38_spec
  · exact v3Row39_spec
  · exact v3Row40_spec
  · exact v3Row41_spec
  · exact v3Row42_spec
  · exact v3Row43_spec
  · exact v3Row44_spec
  · exact v3Row45_spec

private theorem v3Left_length :
    (rectangularize 46 67 (Two.mul VData V2Data)).length = 46 := by
  decide

private theorem v3Right_length :
    (rectangularize 46 67 V3Data).length = 46 := by
  decide

-- Exact bidegree bound (45, 66); no row or column is discarded.
private theorem v3Data_spec :
    rectangularize 46 67 (Two.mul VData V2Data) =
      rectangularize 46 67 V3Data := by
  apply List.ext_getElem (v3Left_length.trans v3Right_length.symm)
  intro i hi _
  rw [List.getElem_eq_getD [], List.getElem_eq_getD []]
  rw [v3Left_length] at hi
  exact v3Rows_spec i hi

/-- Evaluation of the checked third-power multiplication table. -/
theorem eval_v3Data (r s : ℚ) :
    Two.eval V3Data r s =
      Two.eval VData r s * Two.eval V2Data r s := by
  have h := congrArg (fun p => Two.eval p r s) v3Data_spec
  simpa only [eval_rectangularize, Two.eval_mul] using h.symm

end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
