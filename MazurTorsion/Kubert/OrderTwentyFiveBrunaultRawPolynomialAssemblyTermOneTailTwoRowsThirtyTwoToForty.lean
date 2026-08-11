/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialAssemblyTermOneTailTwoData
import MazurTorsion.Kubert.OrderTwentyFiveDensePolynomialMulCertificate
import Mathlib.Tactic.IntervalCases

/-!
# Rows 32 through 40 of the first term-one tail

Every generated coefficient is checked by Lean against the corresponding
row-local dense convolution.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveDensePolynomialRectangular
open OrderTwentyFiveDensePolynomialRowCertificate
private theorem termOneTailTwo_targetLength
    (n : ℕ) (hLower : 32 ≤ n) (hUpper : n < 41) :
    ((rectangularize 57 81 termOneTailTwoData).getD n []).length = 81 := by
  rw [getD_rectangularize 57 81 termOneTailTwoData n (by omega)]
  simp only [padOne, List.length_append, List.length_replicate]
  have hRow : (termOneTailTwoData.getD n []).length ≤ 81 := by
    interval_cases n <;> decide
  omega
private theorem termOneTailTwoRow32_coefficients
    (j : ℕ) (hj : j < 81) :
    mulCoeffTwo X2Data V2Data 32 j =
      (((rectangularize 57 81 termOneTailTwoData).getD 32 [])).getD j 0 := by
  interval_cases j <;> decide

private theorem termOneTailTwoRow32_checked :
    padOne 81 (mulRow X2Data V2Data 32) =
      ((rectangularize 57 81 termOneTailTwoData).getD 32 []) := by
  apply padOne_mulRow_eq_of_coefficients 81 X2Data V2Data 32
    ((rectangularize 57 81 termOneTailTwoData).getD 32 [])
  · decide
  · exact termOneTailTwo_targetLength 32 (by omega) (by omega)
  · exact termOneTailTwoRow32_coefficients

private theorem termOneTailTwoRow33_coefficients
    (j : ℕ) (hj : j < 81) :
    mulCoeffTwo X2Data V2Data 33 j =
      (((rectangularize 57 81 termOneTailTwoData).getD 33 [])).getD j 0 := by
  interval_cases j <;> decide

private theorem termOneTailTwoRow33_checked :
    padOne 81 (mulRow X2Data V2Data 33) =
      ((rectangularize 57 81 termOneTailTwoData).getD 33 []) := by
  apply padOne_mulRow_eq_of_coefficients 81 X2Data V2Data 33
    ((rectangularize 57 81 termOneTailTwoData).getD 33 [])
  · decide
  · exact termOneTailTwo_targetLength 33 (by omega) (by omega)
  · exact termOneTailTwoRow33_coefficients

private theorem termOneTailTwoRow34_coefficients
    (j : ℕ) (hj : j < 81) :
    mulCoeffTwo X2Data V2Data 34 j =
      (((rectangularize 57 81 termOneTailTwoData).getD 34 [])).getD j 0 := by
  interval_cases j <;> decide

private theorem termOneTailTwoRow34_checked :
    padOne 81 (mulRow X2Data V2Data 34) =
      ((rectangularize 57 81 termOneTailTwoData).getD 34 []) := by
  apply padOne_mulRow_eq_of_coefficients 81 X2Data V2Data 34
    ((rectangularize 57 81 termOneTailTwoData).getD 34 [])
  · decide
  · exact termOneTailTwo_targetLength 34 (by omega) (by omega)
  · exact termOneTailTwoRow34_coefficients

private theorem termOneTailTwoRow35_coefficients
    (j : ℕ) (hj : j < 81) :
    mulCoeffTwo X2Data V2Data 35 j =
      (((rectangularize 57 81 termOneTailTwoData).getD 35 [])).getD j 0 := by
  interval_cases j <;> decide

private theorem termOneTailTwoRow35_checked :
    padOne 81 (mulRow X2Data V2Data 35) =
      ((rectangularize 57 81 termOneTailTwoData).getD 35 []) := by
  apply padOne_mulRow_eq_of_coefficients 81 X2Data V2Data 35
    ((rectangularize 57 81 termOneTailTwoData).getD 35 [])
  · decide
  · exact termOneTailTwo_targetLength 35 (by omega) (by omega)
  · exact termOneTailTwoRow35_coefficients

private theorem termOneTailTwoRow36_coefficients
    (j : ℕ) (hj : j < 81) :
    mulCoeffTwo X2Data V2Data 36 j =
      (((rectangularize 57 81 termOneTailTwoData).getD 36 [])).getD j 0 := by
  interval_cases j <;> decide

private theorem termOneTailTwoRow36_checked :
    padOne 81 (mulRow X2Data V2Data 36) =
      ((rectangularize 57 81 termOneTailTwoData).getD 36 []) := by
  apply padOne_mulRow_eq_of_coefficients 81 X2Data V2Data 36
    ((rectangularize 57 81 termOneTailTwoData).getD 36 [])
  · decide
  · exact termOneTailTwo_targetLength 36 (by omega) (by omega)
  · exact termOneTailTwoRow36_coefficients

private theorem termOneTailTwoRow37_coefficients
    (j : ℕ) (hj : j < 81) :
    mulCoeffTwo X2Data V2Data 37 j =
      (((rectangularize 57 81 termOneTailTwoData).getD 37 [])).getD j 0 := by
  interval_cases j <;> decide

private theorem termOneTailTwoRow37_checked :
    padOne 81 (mulRow X2Data V2Data 37) =
      ((rectangularize 57 81 termOneTailTwoData).getD 37 []) := by
  apply padOne_mulRow_eq_of_coefficients 81 X2Data V2Data 37
    ((rectangularize 57 81 termOneTailTwoData).getD 37 [])
  · decide
  · exact termOneTailTwo_targetLength 37 (by omega) (by omega)
  · exact termOneTailTwoRow37_coefficients

private theorem termOneTailTwoRow38_coefficients
    (j : ℕ) (hj : j < 81) :
    mulCoeffTwo X2Data V2Data 38 j =
      (((rectangularize 57 81 termOneTailTwoData).getD 38 [])).getD j 0 := by
  interval_cases j <;> decide

private theorem termOneTailTwoRow38_checked :
    padOne 81 (mulRow X2Data V2Data 38) =
      ((rectangularize 57 81 termOneTailTwoData).getD 38 []) := by
  apply padOne_mulRow_eq_of_coefficients 81 X2Data V2Data 38
    ((rectangularize 57 81 termOneTailTwoData).getD 38 [])
  · decide
  · exact termOneTailTwo_targetLength 38 (by omega) (by omega)
  · exact termOneTailTwoRow38_coefficients

private theorem termOneTailTwoRow39_coefficients
    (j : ℕ) (hj : j < 81) :
    mulCoeffTwo X2Data V2Data 39 j =
      (((rectangularize 57 81 termOneTailTwoData).getD 39 [])).getD j 0 := by
  interval_cases j <;> decide

private theorem termOneTailTwoRow39_checked :
    padOne 81 (mulRow X2Data V2Data 39) =
      ((rectangularize 57 81 termOneTailTwoData).getD 39 []) := by
  apply padOne_mulRow_eq_of_coefficients 81 X2Data V2Data 39
    ((rectangularize 57 81 termOneTailTwoData).getD 39 [])
  · decide
  · exact termOneTailTwo_targetLength 39 (by omega) (by omega)
  · exact termOneTailTwoRow39_coefficients

private theorem termOneTailTwoRow40_coefficients
    (j : ℕ) (hj : j < 81) :
    mulCoeffTwo X2Data V2Data 40 j =
      (((rectangularize 57 81 termOneTailTwoData).getD 40 [])).getD j 0 := by
  interval_cases j <;> decide

private theorem termOneTailTwoRow40_checked :
    padOne 81 (mulRow X2Data V2Data 40) =
      ((rectangularize 57 81 termOneTailTwoData).getD 40 []) := by
  apply padOne_mulRow_eq_of_coefficients 81 X2Data V2Data 40
    ((rectangularize 57 81 termOneTailTwoData).getD 40 [])
  · decide
  · exact termOneTailTwo_targetLength 40 (by omega) (by omega)
  · exact termOneTailTwoRow40_coefficients

/-- Checked stage-one rows 32 through 40. -/
theorem termOneTailTwoRowsThirtyTwoToForty_checked
    (n : ℕ) (hLower : 32 ≤ n) (hUpper : n < 41) :
    padOne 81 (mulRow X2Data V2Data n) =
      (rectangularize 57 81 termOneTailTwoData).getD n [] := by
  interval_cases n
  · exact termOneTailTwoRow32_checked
  · exact termOneTailTwoRow33_checked
  · exact termOneTailTwoRow34_checked
  · exact termOneTailTwoRow35_checked
  · exact termOneTailTwoRow36_checked
  · exact termOneTailTwoRow37_checked
  · exact termOneTailTwoRow38_checked
  · exact termOneTailTwoRow39_checked
  · exact termOneTailTwoRow40_checked

end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
