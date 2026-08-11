/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialAssemblyTermOneTailTwoData
import MazurTorsion.Kubert.OrderTwentyFiveDensePolynomialMulCertificate
import Mathlib.Tactic.IntervalCases

/-!
# Rows 41 through 56 of the first term-one tail

Every generated coefficient is checked by Lean against the corresponding
row-local dense convolution.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveDensePolynomialRectangular
open OrderTwentyFiveDensePolynomialRowCertificate
private theorem termOneTailTwoRow41_checked :
    padOne 81 (mulRow X2Data V2Data 41) =
      ((rectangularize 57 81 termOneTailTwoData).getD 41 []) := by
  decide

private theorem termOneTailTwoRow42_checked :
    padOne 81 (mulRow X2Data V2Data 42) =
      ((rectangularize 57 81 termOneTailTwoData).getD 42 []) := by
  decide

private theorem termOneTailTwoRow43_checked :
    padOne 81 (mulRow X2Data V2Data 43) =
      ((rectangularize 57 81 termOneTailTwoData).getD 43 []) := by
  decide

private theorem termOneTailTwoRow44_checked :
    padOne 81 (mulRow X2Data V2Data 44) =
      ((rectangularize 57 81 termOneTailTwoData).getD 44 []) := by
  decide

private theorem termOneTailTwoRow45_checked :
    padOne 81 (mulRow X2Data V2Data 45) =
      ((rectangularize 57 81 termOneTailTwoData).getD 45 []) := by
  decide

private theorem termOneTailTwoRow46_checked :
    padOne 81 (mulRow X2Data V2Data 46) =
      ((rectangularize 57 81 termOneTailTwoData).getD 46 []) := by
  decide

private theorem termOneTailTwoRow47_checked :
    padOne 81 (mulRow X2Data V2Data 47) =
      ((rectangularize 57 81 termOneTailTwoData).getD 47 []) := by
  decide

private theorem termOneTailTwoRow48_checked :
    padOne 81 (mulRow X2Data V2Data 48) =
      ((rectangularize 57 81 termOneTailTwoData).getD 48 []) := by
  decide

private theorem termOneTailTwoRow49_checked :
    padOne 81 (mulRow X2Data V2Data 49) =
      ((rectangularize 57 81 termOneTailTwoData).getD 49 []) := by
  decide

private theorem termOneTailTwoRow50_checked :
    padOne 81 (mulRow X2Data V2Data 50) =
      ((rectangularize 57 81 termOneTailTwoData).getD 50 []) := by
  decide

private theorem termOneTailTwoRow51_checked :
    padOne 81 (mulRow X2Data V2Data 51) =
      ((rectangularize 57 81 termOneTailTwoData).getD 51 []) := by
  decide

private theorem termOneTailTwoRow52_checked :
    padOne 81 (mulRow X2Data V2Data 52) =
      ((rectangularize 57 81 termOneTailTwoData).getD 52 []) := by
  decide

private theorem termOneTailTwoRow53_checked :
    padOne 81 (mulRow X2Data V2Data 53) =
      ((rectangularize 57 81 termOneTailTwoData).getD 53 []) := by
  decide

private theorem termOneTailTwoRow54_checked :
    padOne 81 (mulRow X2Data V2Data 54) =
      ((rectangularize 57 81 termOneTailTwoData).getD 54 []) := by
  decide

private theorem termOneTailTwoRow55_checked :
    padOne 81 (mulRow X2Data V2Data 55) =
      ((rectangularize 57 81 termOneTailTwoData).getD 55 []) := by
  decide

private theorem termOneTailTwoRow56_checked :
    padOne 81 (mulRow X2Data V2Data 56) =
      ((rectangularize 57 81 termOneTailTwoData).getD 56 []) := by
  decide

/-- Checked stage-one rows 41 through 56. -/
theorem termOneTailTwoRowsFortyOneToFiftySix_checked
    (n : ℕ) (hLower : 41 ≤ n) (hUpper : n < 57) :
    padOne 81 (mulRow X2Data V2Data n) =
      (rectangularize 57 81 termOneTailTwoData).getD n [] := by
  interval_cases n
  · exact termOneTailTwoRow41_checked
  · exact termOneTailTwoRow42_checked
  · exact termOneTailTwoRow43_checked
  · exact termOneTailTwoRow44_checked
  · exact termOneTailTwoRow45_checked
  · exact termOneTailTwoRow46_checked
  · exact termOneTailTwoRow47_checked
  · exact termOneTailTwoRow48_checked
  · exact termOneTailTwoRow49_checked
  · exact termOneTailTwoRow50_checked
  · exact termOneTailTwoRow51_checked
  · exact termOneTailTwoRow52_checked
  · exact termOneTailTwoRow53_checked
  · exact termOneTailTwoRow54_checked
  · exact termOneTailTwoRow55_checked
  · exact termOneTailTwoRow56_checked

end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
