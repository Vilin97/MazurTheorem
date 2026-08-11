/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialDivisionData
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialDivisionRowsZeroToSeven
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialDivisionRowEight
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialDivisionRowsNineToSixteen
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialDivisionRowsSeventeenToTwentyFour
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialDivisionRowsTwentyFiveToThirtyTwo
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialDivisionRowsThirtyThreeToForty
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialDivisionRowsFortyOneToFortyEight
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialDivisionRowsFortyNineToFiftySix
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialDivisionRowsFiftySevenToSixtyFour
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialDivisionRowsSixtyFiveToSeventyTwo
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialDivisionRowsSeventyThreeToEightyTwo

/-!
# Checked exact division for the raw order-twenty-five polynomial

The eleven row shards jointly certify every coefficient of the exact
`83 × 121` rectangle.  This facade assembles those row theorems without
duplicating any generated table.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveDensePolynomialRectangular
open OrderTwentyFiveDensePolynomialRowCertificate

private theorem divisionRows_spec (n : ℕ) (hn : n < 83) :
    padOne 121
        (mulRow divisionSutherlandPolynomial divisionQuotientData n) =
      (rectangularize 83 121 divisionReducedData).getD n [] := by
  by_cases h8 : n < 8
  · exact divisionRowsZeroToSeven_spec n h8
  by_cases h9 : n < 9
  · have hn8 : n = 8 := by omega
    subst n
    exact divisionRowEight_spec
  by_cases h17 : n < 17
  · exact divisionRowsNineToSixteen_spec n (by omega) h17
  by_cases h25 : n < 25
  · exact divisionRowsSeventeenToTwentyFour_spec n (by omega) h25
  by_cases h33 : n < 33
  · exact divisionRowsTwentyFiveToThirtyTwo_spec n (by omega) h33
  by_cases h41 : n < 41
  · exact divisionRowsThirtyThreeToForty_spec n (by omega) h41
  by_cases h49 : n < 49
  · exact divisionRowsFortyOneToFortyEight_spec n (by omega) h49
  by_cases h57 : n < 57
  · exact divisionRowsFortyNineToFiftySix_spec n (by omega) h57
  by_cases h65 : n < 65
  · exact divisionRowsFiftySevenToSixtyFour_spec n (by omega) h65
  by_cases h73 : n < 73
  · exact divisionRowsSixtyFiveToSeventyTwo_spec n (by omega) h73
  exact divisionRowsSeventyThreeToEightyTwo_spec n (by omega) hn

private theorem divisionLeft_length :
    (rectangularize 83 121
      (Two.mul divisionSutherlandPolynomial divisionQuotientData)).length =
        83 := by
  apply rectangularize_length_of_le
  change
    (mulWith [] One.add One.mul divisionSutherlandPolynomial
      divisionQuotientData).length ≤ 83
  rw [length_mulWith_of_ne_nil [] One.add One.mul
    divisionSutherlandPolynomial divisionQuotientData
      (by decide) (by decide),
    divisionSutherland_outerSupport, divisionQuotient_outerSupport]

private theorem divisionRight_length :
    (rectangularize 83 121 divisionReducedData).length = 83 := by
  apply rectangularize_length_of_le
  rw [divisionReduced_outerSupport]

private theorem divisionData_spec :
    rectangularize 83 121
        (Two.mul divisionSutherlandPolynomial divisionQuotientData) =
      rectangularize 83 121 divisionReducedData := by
  apply List.ext_getElem (divisionLeft_length.trans divisionRight_length.symm)
  intro n hn _
  rw [List.getElem_eq_getD [], List.getElem_eq_getD []]
  rw [divisionLeft_length] at hn
  rw [getD_rectangularize 83 121
      (Two.mul divisionSutherlandPolynomial divisionQuotientData) n hn,
    ← mulRow_eq_getD]
  exact divisionRows_spec n hn

/-- Evaluation of the complete kernel-checked exact division certificate. -/
theorem eval_divisionReducedData_eq_sutherland_mul_quotient (r s : ℚ) :
    Two.eval divisionReducedData r s =
      Two.eval divisionSutherlandPolynomial r s *
        Two.eval divisionQuotientData r s := by
  have hEval := congrArg (fun z ↦ Two.eval z r s) divisionData_spec
  simpa only [eval_rectangularize, Two.eval_mul] using hEval.symm

end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
