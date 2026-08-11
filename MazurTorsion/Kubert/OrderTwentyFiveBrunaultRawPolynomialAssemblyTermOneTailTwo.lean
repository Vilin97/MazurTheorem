/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialAssemblyTermOneTailTwoRowsZeroToSeven
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialAssemblyTermOneTailTwoRowsEightToFifteen
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialAssemblyTermOneTailTwoRowsSixteenToTwentyThree
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialAssemblyTermOneTailTwoRowsTwentyFourToThirtyOne
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialAssemblyTermOneTailTwoRowsThirtyTwoToForty
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialAssemblyTermOneTailTwoRowsFortyOneToFiftySix

/-!
# Checked first staged tail of Brunault assembly term one

The generated table is accepted only through the shared row-assembly
certificate. This module is the compiled downstream consumer of that API.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveDensePolynomialRectangular
open OrderTwentyFiveDensePolynomialRowCertificate
open OrderTwentyFiveDensePolynomialMulCertificate

private theorem termOneTailTwoRows_checked
    (n : ℕ) (hn : n < 57) :
    padOne 81 (mulRow X2Data V2Data n) =
      (rectangularize 57 81 termOneTailTwoData).getD n [] := by
  by_cases h8 : n < 8
  · exact termOneTailTwoRowsZeroToSeven_checked n h8
  by_cases h16 : n < 16
  · exact termOneTailTwoRowsEightToFifteen_checked n (by omega) h16
  by_cases h24 : n < 24
  · exact termOneTailTwoRowsSixteenToTwentyThree_checked n (by omega) h24
  by_cases h32 : n < 32
  · exact termOneTailTwoRowsTwentyFourToThirtyOne_checked n (by omega) h32
  by_cases h41 : n < 41
  · exact termOneTailTwoRowsThirtyTwoToForty_checked n (by omega) h41
  exact termOneTailTwoRowsFortyOneToFiftySix_checked n (by omega) hn

private theorem termOneTailTwo_mulOuterSupport :
    (Two.mul X2Data V2Data).length ≤ 57 := by
  decide

private theorem termOneTailTwo_dataOuterSupport :
    termOneTailTwoData.length ≤ 57 := by
  decide

/-- The generated first tail is exactly the rectangular dense product of
X2Data and V2Data. -/
theorem termOneTailTwoData_checked :
    rectangularize 57 81 (Two.mul X2Data V2Data) =
      rectangularize 57 81 termOneTailTwoData := by
  exact rectangularize_mul_eq_of_rows 57 81 X2Data V2Data
    termOneTailTwoData
    termOneTailTwo_mulOuterSupport
    termOneTailTwo_dataOuterSupport
    termOneTailTwoRows_checked

/-- Evaluation of the checked first right-associated tail of term one. -/
theorem eval_termOneTailTwoData (r s : ℚ) :
    Two.eval termOneTailTwoData r s =
      Two.eval X2Data r s * Two.eval V2Data r s := by
  exact eval_mulData_eq_mul_of_rows 57 81 X2Data V2Data
    termOneTailTwoData
    termOneTailTwo_mulOuterSupport
    termOneTailTwo_dataOuterSupport
    termOneTailTwoRows_checked r s

end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
