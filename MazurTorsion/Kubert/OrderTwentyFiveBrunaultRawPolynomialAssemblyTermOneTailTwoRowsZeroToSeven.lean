/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialAssemblyTermOneTailTwoData
import MazurTorsion.Kubert.OrderTwentyFiveDensePolynomialMulCertificate
import Mathlib.Tactic.IntervalCases

/-!
# Rows 0 through 7 of the first term-one tail

Every generated coefficient is checked by Lean against the corresponding
row-local dense convolution.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveDensePolynomialRectangular
open OrderTwentyFiveDensePolynomialRowCertificate
private theorem termOneTailTwoRow0_checked :
    padOne 81 (mulRow X2Data V2Data 0) =
      ((rectangularize 57 81 termOneTailTwoData).getD 0 []) := by
  decide

private theorem termOneTailTwoRow1_checked :
    padOne 81 (mulRow X2Data V2Data 1) =
      ((rectangularize 57 81 termOneTailTwoData).getD 1 []) := by
  decide

private theorem termOneTailTwoRow2_checked :
    padOne 81 (mulRow X2Data V2Data 2) =
      ((rectangularize 57 81 termOneTailTwoData).getD 2 []) := by
  decide

private theorem termOneTailTwoRow3_checked :
    padOne 81 (mulRow X2Data V2Data 3) =
      ((rectangularize 57 81 termOneTailTwoData).getD 3 []) := by
  decide

private theorem termOneTailTwoRow4_checked :
    padOne 81 (mulRow X2Data V2Data 4) =
      ((rectangularize 57 81 termOneTailTwoData).getD 4 []) := by
  decide

private theorem termOneTailTwoRow5_checked :
    padOne 81 (mulRow X2Data V2Data 5) =
      ((rectangularize 57 81 termOneTailTwoData).getD 5 []) := by
  decide

private theorem termOneTailTwoRow6_checked :
    padOne 81 (mulRow X2Data V2Data 6) =
      ((rectangularize 57 81 termOneTailTwoData).getD 6 []) := by
  decide

private theorem termOneTailTwoRow7_checked :
    padOne 81 (mulRow X2Data V2Data 7) =
      ((rectangularize 57 81 termOneTailTwoData).getD 7 []) := by
  decide

/-- Checked stage-one rows 0 through 7. -/
theorem termOneTailTwoRowsZeroToSeven_checked
    (n : ℕ) (hUpper : n < 8) :
    padOne 81 (mulRow X2Data V2Data n) =
      (rectangularize 57 81 termOneTailTwoData).getD n [] := by
  interval_cases n
  · exact termOneTailTwoRow0_checked
  · exact termOneTailTwoRow1_checked
  · exact termOneTailTwoRow2_checked
  · exact termOneTailTwoRow3_checked
  · exact termOneTailTwoRow4_checked
  · exact termOneTailTwoRow5_checked
  · exact termOneTailTwoRow6_checked
  · exact termOneTailTwoRow7_checked

end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
