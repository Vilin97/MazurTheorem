/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialAssemblyTermOneTailTwoData
import MazurTorsion.Kubert.OrderTwentyFiveDensePolynomialMulCertificate
import Mathlib.Tactic.IntervalCases

/-!
# Rows 24 through 31 of the first term-one tail

Every generated coefficient is checked by Lean against the corresponding
row-local dense convolution.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveDensePolynomialRectangular
open OrderTwentyFiveDensePolynomialRowCertificate
private theorem termOneTailTwo_targetLength
    (n : ℕ) (hLower : 24 ≤ n) (hUpper : n < 32) :
    ((rectangularize 57 81 termOneTailTwoData).getD n []).length = 81 := by
  rw [getD_rectangularize 57 81 termOneTailTwoData n (by omega)]
  simp only [padOne, List.length_append, List.length_replicate]
  have hRow : (termOneTailTwoData.getD n []).length ≤ 81 := by
    interval_cases n <;> decide
  omega
private theorem termOneTailTwoRow24_coefficients
    (j : ℕ) (hj : j < 81) :
    mulCoeffTwo X2Data V2Data 24 j =
      (((rectangularize 57 81 termOneTailTwoData).getD 24 [])).getD j 0 := by
  interval_cases j <;> decide

private theorem termOneTailTwoRow24_checked :
    padOne 81 (mulRow X2Data V2Data 24) =
      ((rectangularize 57 81 termOneTailTwoData).getD 24 []) := by
  apply padOne_mulRow_eq_of_coefficients 81 X2Data V2Data 24
    ((rectangularize 57 81 termOneTailTwoData).getD 24 [])
  · decide
  · exact termOneTailTwo_targetLength 24 (by omega) (by omega)
  · exact termOneTailTwoRow24_coefficients

private theorem termOneTailTwoRow25_coefficients
    (j : ℕ) (hj : j < 81) :
    mulCoeffTwo X2Data V2Data 25 j =
      (((rectangularize 57 81 termOneTailTwoData).getD 25 [])).getD j 0 := by
  interval_cases j <;> decide

private theorem termOneTailTwoRow25_checked :
    padOne 81 (mulRow X2Data V2Data 25) =
      ((rectangularize 57 81 termOneTailTwoData).getD 25 []) := by
  apply padOne_mulRow_eq_of_coefficients 81 X2Data V2Data 25
    ((rectangularize 57 81 termOneTailTwoData).getD 25 [])
  · decide
  · exact termOneTailTwo_targetLength 25 (by omega) (by omega)
  · exact termOneTailTwoRow25_coefficients

private theorem termOneTailTwoRow26_coefficients
    (j : ℕ) (hj : j < 81) :
    mulCoeffTwo X2Data V2Data 26 j =
      (((rectangularize 57 81 termOneTailTwoData).getD 26 [])).getD j 0 := by
  interval_cases j <;> decide

private theorem termOneTailTwoRow26_checked :
    padOne 81 (mulRow X2Data V2Data 26) =
      ((rectangularize 57 81 termOneTailTwoData).getD 26 []) := by
  apply padOne_mulRow_eq_of_coefficients 81 X2Data V2Data 26
    ((rectangularize 57 81 termOneTailTwoData).getD 26 [])
  · decide
  · exact termOneTailTwo_targetLength 26 (by omega) (by omega)
  · exact termOneTailTwoRow26_coefficients

private theorem termOneTailTwoRow27_coefficients
    (j : ℕ) (hj : j < 81) :
    mulCoeffTwo X2Data V2Data 27 j =
      (((rectangularize 57 81 termOneTailTwoData).getD 27 [])).getD j 0 := by
  interval_cases j <;> decide

private theorem termOneTailTwoRow27_checked :
    padOne 81 (mulRow X2Data V2Data 27) =
      ((rectangularize 57 81 termOneTailTwoData).getD 27 []) := by
  apply padOne_mulRow_eq_of_coefficients 81 X2Data V2Data 27
    ((rectangularize 57 81 termOneTailTwoData).getD 27 [])
  · decide
  · exact termOneTailTwo_targetLength 27 (by omega) (by omega)
  · exact termOneTailTwoRow27_coefficients

private theorem termOneTailTwoRow28_coefficients
    (j : ℕ) (hj : j < 81) :
    mulCoeffTwo X2Data V2Data 28 j =
      (((rectangularize 57 81 termOneTailTwoData).getD 28 [])).getD j 0 := by
  interval_cases j <;> decide

private theorem termOneTailTwoRow28_checked :
    padOne 81 (mulRow X2Data V2Data 28) =
      ((rectangularize 57 81 termOneTailTwoData).getD 28 []) := by
  apply padOne_mulRow_eq_of_coefficients 81 X2Data V2Data 28
    ((rectangularize 57 81 termOneTailTwoData).getD 28 [])
  · decide
  · exact termOneTailTwo_targetLength 28 (by omega) (by omega)
  · exact termOneTailTwoRow28_coefficients

private theorem termOneTailTwoRow29_coefficients
    (j : ℕ) (hj : j < 81) :
    mulCoeffTwo X2Data V2Data 29 j =
      (((rectangularize 57 81 termOneTailTwoData).getD 29 [])).getD j 0 := by
  interval_cases j <;> decide

private theorem termOneTailTwoRow29_checked :
    padOne 81 (mulRow X2Data V2Data 29) =
      ((rectangularize 57 81 termOneTailTwoData).getD 29 []) := by
  apply padOne_mulRow_eq_of_coefficients 81 X2Data V2Data 29
    ((rectangularize 57 81 termOneTailTwoData).getD 29 [])
  · decide
  · exact termOneTailTwo_targetLength 29 (by omega) (by omega)
  · exact termOneTailTwoRow29_coefficients

private theorem termOneTailTwoRow30_coefficients
    (j : ℕ) (hj : j < 81) :
    mulCoeffTwo X2Data V2Data 30 j =
      (((rectangularize 57 81 termOneTailTwoData).getD 30 [])).getD j 0 := by
  interval_cases j <;> decide

private theorem termOneTailTwoRow30_checked :
    padOne 81 (mulRow X2Data V2Data 30) =
      ((rectangularize 57 81 termOneTailTwoData).getD 30 []) := by
  apply padOne_mulRow_eq_of_coefficients 81 X2Data V2Data 30
    ((rectangularize 57 81 termOneTailTwoData).getD 30 [])
  · decide
  · exact termOneTailTwo_targetLength 30 (by omega) (by omega)
  · exact termOneTailTwoRow30_coefficients

private theorem termOneTailTwoRow31_coefficients
    (j : ℕ) (hj : j < 81) :
    mulCoeffTwo X2Data V2Data 31 j =
      (((rectangularize 57 81 termOneTailTwoData).getD 31 [])).getD j 0 := by
  interval_cases j <;> decide

private theorem termOneTailTwoRow31_checked :
    padOne 81 (mulRow X2Data V2Data 31) =
      ((rectangularize 57 81 termOneTailTwoData).getD 31 []) := by
  apply padOne_mulRow_eq_of_coefficients 81 X2Data V2Data 31
    ((rectangularize 57 81 termOneTailTwoData).getD 31 [])
  · decide
  · exact termOneTailTwo_targetLength 31 (by omega) (by omega)
  · exact termOneTailTwoRow31_coefficients

/-- Checked stage-one rows 24 through 31. -/
theorem termOneTailTwoRowsTwentyFourToThirtyOne_checked
    (n : ℕ) (hLower : 24 ≤ n) (hUpper : n < 32) :
    padOne 81 (mulRow X2Data V2Data n) =
      (rectangularize 57 81 termOneTailTwoData).getD n [] := by
  interval_cases n
  · exact termOneTailTwoRow24_checked
  · exact termOneTailTwoRow25_checked
  · exact termOneTailTwoRow26_checked
  · exact termOneTailTwoRow27_checked
  · exact termOneTailTwoRow28_checked
  · exact termOneTailTwoRow29_checked
  · exact termOneTailTwoRow30_checked
  · exact termOneTailTwoRow31_checked

end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
