/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialCompositeXData
import MazurTorsion.Kubert.OrderTwentyFiveDensePolynomialRectangular
import Mathlib.Tactic.IntervalCases

/-!
# Checked X cubed table for the raw order-twenty-five certificate

Each generated row is checked in its own theorem.  The final extensional proof
uses every row and separately checks the exact outer lengths.  Since
`rectangularize` only appends zeros, this also checks every possible tail.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveDensePolynomialRectangular

private theorem x3Row0_spec :
    (rectangularize 40 55 (Two.mul XData X2Data)).getD 0 [] =
      (rectangularize 40 55 X3Data).getD 0 [] := by
  decide

private theorem x3Row1_spec :
    (rectangularize 40 55 (Two.mul XData X2Data)).getD 1 [] =
      (rectangularize 40 55 X3Data).getD 1 [] := by
  decide

private theorem x3Row2_spec :
    (rectangularize 40 55 (Two.mul XData X2Data)).getD 2 [] =
      (rectangularize 40 55 X3Data).getD 2 [] := by
  decide

private theorem x3Row3_spec :
    (rectangularize 40 55 (Two.mul XData X2Data)).getD 3 [] =
      (rectangularize 40 55 X3Data).getD 3 [] := by
  decide

private theorem x3Row4_spec :
    (rectangularize 40 55 (Two.mul XData X2Data)).getD 4 [] =
      (rectangularize 40 55 X3Data).getD 4 [] := by
  decide

private theorem x3Row5_spec :
    (rectangularize 40 55 (Two.mul XData X2Data)).getD 5 [] =
      (rectangularize 40 55 X3Data).getD 5 [] := by
  decide

private theorem x3Row6_spec :
    (rectangularize 40 55 (Two.mul XData X2Data)).getD 6 [] =
      (rectangularize 40 55 X3Data).getD 6 [] := by
  decide

private theorem x3Row7_spec :
    (rectangularize 40 55 (Two.mul XData X2Data)).getD 7 [] =
      (rectangularize 40 55 X3Data).getD 7 [] := by
  decide

private theorem x3Row8_spec :
    (rectangularize 40 55 (Two.mul XData X2Data)).getD 8 [] =
      (rectangularize 40 55 X3Data).getD 8 [] := by
  decide

private theorem x3Row9_spec :
    (rectangularize 40 55 (Two.mul XData X2Data)).getD 9 [] =
      (rectangularize 40 55 X3Data).getD 9 [] := by
  decide

private theorem x3Row10_spec :
    (rectangularize 40 55 (Two.mul XData X2Data)).getD 10 [] =
      (rectangularize 40 55 X3Data).getD 10 [] := by
  decide

private theorem x3Row11_spec :
    (rectangularize 40 55 (Two.mul XData X2Data)).getD 11 [] =
      (rectangularize 40 55 X3Data).getD 11 [] := by
  decide

private theorem x3Row12_spec :
    (rectangularize 40 55 (Two.mul XData X2Data)).getD 12 [] =
      (rectangularize 40 55 X3Data).getD 12 [] := by
  decide

private theorem x3Row13_spec :
    (rectangularize 40 55 (Two.mul XData X2Data)).getD 13 [] =
      (rectangularize 40 55 X3Data).getD 13 [] := by
  decide

private theorem x3Row14_spec :
    (rectangularize 40 55 (Two.mul XData X2Data)).getD 14 [] =
      (rectangularize 40 55 X3Data).getD 14 [] := by
  decide

private theorem x3Row15_spec :
    (rectangularize 40 55 (Two.mul XData X2Data)).getD 15 [] =
      (rectangularize 40 55 X3Data).getD 15 [] := by
  decide

private theorem x3Row16_spec :
    (rectangularize 40 55 (Two.mul XData X2Data)).getD 16 [] =
      (rectangularize 40 55 X3Data).getD 16 [] := by
  decide

private theorem x3Row17_spec :
    (rectangularize 40 55 (Two.mul XData X2Data)).getD 17 [] =
      (rectangularize 40 55 X3Data).getD 17 [] := by
  decide

private theorem x3Row18_spec :
    (rectangularize 40 55 (Two.mul XData X2Data)).getD 18 [] =
      (rectangularize 40 55 X3Data).getD 18 [] := by
  decide

private theorem x3Row19_spec :
    (rectangularize 40 55 (Two.mul XData X2Data)).getD 19 [] =
      (rectangularize 40 55 X3Data).getD 19 [] := by
  decide

private theorem x3Row20_spec :
    (rectangularize 40 55 (Two.mul XData X2Data)).getD 20 [] =
      (rectangularize 40 55 X3Data).getD 20 [] := by
  decide

private theorem x3Row21_spec :
    (rectangularize 40 55 (Two.mul XData X2Data)).getD 21 [] =
      (rectangularize 40 55 X3Data).getD 21 [] := by
  decide

private theorem x3Row22_spec :
    (rectangularize 40 55 (Two.mul XData X2Data)).getD 22 [] =
      (rectangularize 40 55 X3Data).getD 22 [] := by
  decide

private theorem x3Row23_spec :
    (rectangularize 40 55 (Two.mul XData X2Data)).getD 23 [] =
      (rectangularize 40 55 X3Data).getD 23 [] := by
  decide

private theorem x3Row24_spec :
    (rectangularize 40 55 (Two.mul XData X2Data)).getD 24 [] =
      (rectangularize 40 55 X3Data).getD 24 [] := by
  decide

private theorem x3Row25_spec :
    (rectangularize 40 55 (Two.mul XData X2Data)).getD 25 [] =
      (rectangularize 40 55 X3Data).getD 25 [] := by
  decide

private theorem x3Row26_spec :
    (rectangularize 40 55 (Two.mul XData X2Data)).getD 26 [] =
      (rectangularize 40 55 X3Data).getD 26 [] := by
  decide

private theorem x3Row27_spec :
    (rectangularize 40 55 (Two.mul XData X2Data)).getD 27 [] =
      (rectangularize 40 55 X3Data).getD 27 [] := by
  decide

private theorem x3Row28_spec :
    (rectangularize 40 55 (Two.mul XData X2Data)).getD 28 [] =
      (rectangularize 40 55 X3Data).getD 28 [] := by
  decide

private theorem x3Row29_spec :
    (rectangularize 40 55 (Two.mul XData X2Data)).getD 29 [] =
      (rectangularize 40 55 X3Data).getD 29 [] := by
  decide

private theorem x3Row30_spec :
    (rectangularize 40 55 (Two.mul XData X2Data)).getD 30 [] =
      (rectangularize 40 55 X3Data).getD 30 [] := by
  decide

private theorem x3Row31_spec :
    (rectangularize 40 55 (Two.mul XData X2Data)).getD 31 [] =
      (rectangularize 40 55 X3Data).getD 31 [] := by
  decide

private theorem x3Row32_spec :
    (rectangularize 40 55 (Two.mul XData X2Data)).getD 32 [] =
      (rectangularize 40 55 X3Data).getD 32 [] := by
  decide

private theorem x3Row33_spec :
    (rectangularize 40 55 (Two.mul XData X2Data)).getD 33 [] =
      (rectangularize 40 55 X3Data).getD 33 [] := by
  decide

private theorem x3Row34_spec :
    (rectangularize 40 55 (Two.mul XData X2Data)).getD 34 [] =
      (rectangularize 40 55 X3Data).getD 34 [] := by
  decide

private theorem x3Row35_spec :
    (rectangularize 40 55 (Two.mul XData X2Data)).getD 35 [] =
      (rectangularize 40 55 X3Data).getD 35 [] := by
  decide

private theorem x3Row36_spec :
    (rectangularize 40 55 (Two.mul XData X2Data)).getD 36 [] =
      (rectangularize 40 55 X3Data).getD 36 [] := by
  decide

private theorem x3Row37_spec :
    (rectangularize 40 55 (Two.mul XData X2Data)).getD 37 [] =
      (rectangularize 40 55 X3Data).getD 37 [] := by
  decide

private theorem x3Row38_spec :
    (rectangularize 40 55 (Two.mul XData X2Data)).getD 38 [] =
      (rectangularize 40 55 X3Data).getD 38 [] := by
  decide

private theorem x3Row39_spec :
    (rectangularize 40 55 (Two.mul XData X2Data)).getD 39 [] =
      (rectangularize 40 55 X3Data).getD 39 [] := by
  decide

private theorem x3Rows_spec (i : ℕ) (hi : i < 40) :
    (rectangularize 40 55 (Two.mul XData X2Data)).getD i [] =
      (rectangularize 40 55 X3Data).getD i [] := by
  have hCases :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨
    i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨
    i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨
    i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨
    i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨
    i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨
    i = 30 ∨ i = 31 ∨ i = 32 ∨ i = 33 ∨ i = 34 ∨
    i = 35 ∨ i = 36 ∨ i = 37 ∨ i = 38 ∨ i = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact x3Row0_spec
  · exact x3Row1_spec
  · exact x3Row2_spec
  · exact x3Row3_spec
  · exact x3Row4_spec
  · exact x3Row5_spec
  · exact x3Row6_spec
  · exact x3Row7_spec
  · exact x3Row8_spec
  · exact x3Row9_spec
  · exact x3Row10_spec
  · exact x3Row11_spec
  · exact x3Row12_spec
  · exact x3Row13_spec
  · exact x3Row14_spec
  · exact x3Row15_spec
  · exact x3Row16_spec
  · exact x3Row17_spec
  · exact x3Row18_spec
  · exact x3Row19_spec
  · exact x3Row20_spec
  · exact x3Row21_spec
  · exact x3Row22_spec
  · exact x3Row23_spec
  · exact x3Row24_spec
  · exact x3Row25_spec
  · exact x3Row26_spec
  · exact x3Row27_spec
  · exact x3Row28_spec
  · exact x3Row29_spec
  · exact x3Row30_spec
  · exact x3Row31_spec
  · exact x3Row32_spec
  · exact x3Row33_spec
  · exact x3Row34_spec
  · exact x3Row35_spec
  · exact x3Row36_spec
  · exact x3Row37_spec
  · exact x3Row38_spec
  · exact x3Row39_spec

private theorem x3Left_length :
    (rectangularize 40 55 (Two.mul XData X2Data)).length = 40 := by
  decide

private theorem x3Right_length :
    (rectangularize 40 55 X3Data).length = 40 := by
  decide

-- Exact bidegree bound (39, 54); no row or column is discarded.
private theorem x3Data_spec :
    rectangularize 40 55 (Two.mul XData X2Data) =
      rectangularize 40 55 X3Data := by
  apply List.ext_getElem (x3Left_length.trans x3Right_length.symm)
  intro i hi _
  rw [List.getElem_eq_getD [], List.getElem_eq_getD []]
  rw [x3Left_length] at hi
  exact x3Rows_spec i hi

/-- Evaluation of the checked third-power multiplication table. -/
theorem eval_x3Data (r s : ℚ) :
    Two.eval X3Data r s =
      Two.eval XData r s * Two.eval X2Data r s := by
  have h := congrArg (fun p => Two.eval p r s) x3Data_spec
  simpa only [eval_rectangularize, Two.eval_mul] using h.symm

end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
