/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialAssemblyTermOneTailTwoData
import MazurTorsion.Kubert.OrderTwentyFiveDensePolynomialMulCertificate
import Mathlib.Tactic.IntervalCases

/-!
# Rows 8 through 15 of the first term-one tail

Every generated coefficient is checked by Lean against the corresponding
row-local dense convolution.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveDensePolynomialRectangular
open OrderTwentyFiveDensePolynomialRowCertificate
private theorem termOneTailTwo_targetLength
    (n : ℕ) (hLower : 8 ≤ n) (hUpper : n < 16) :
    ((rectangularize 57 81 termOneTailTwoData).getD n []).length = 81 := by
  rw [getD_rectangularize 57 81 termOneTailTwoData n (by omega)]
  simp only [padOne, List.length_append, List.length_replicate]
  have hRow : (termOneTailTwoData.getD n []).length ≤ 81 := by
    interval_cases n <;> decide
  omega
private theorem termOneTailTwoRow8_coefficients
    (j : ℕ) (hj : j < 81) :
    mulCoeffTwo X2Data V2Data 8 j =
      (((rectangularize 57 81 termOneTailTwoData).getD 8 [])).getD j 0 := by
  interval_cases j <;> decide

private theorem termOneTailTwoRow8_checked :
    padOne 81 (mulRow X2Data V2Data 8) =
      ((rectangularize 57 81 termOneTailTwoData).getD 8 []) := by
  apply padOne_mulRow_eq_of_coefficients 81 X2Data V2Data 8
    ((rectangularize 57 81 termOneTailTwoData).getD 8 [])
  · decide
  · exact termOneTailTwo_targetLength 8 (by omega) (by omega)
  · exact termOneTailTwoRow8_coefficients

private theorem termOneTailTwoRow9_coefficients
    (j : ℕ) (hj : j < 81) :
    mulCoeffTwo X2Data V2Data 9 j =
      (((rectangularize 57 81 termOneTailTwoData).getD 9 [])).getD j 0 := by
  interval_cases j <;> decide

private theorem termOneTailTwoRow9_checked :
    padOne 81 (mulRow X2Data V2Data 9) =
      ((rectangularize 57 81 termOneTailTwoData).getD 9 []) := by
  apply padOne_mulRow_eq_of_coefficients 81 X2Data V2Data 9
    ((rectangularize 57 81 termOneTailTwoData).getD 9 [])
  · decide
  · exact termOneTailTwo_targetLength 9 (by omega) (by omega)
  · exact termOneTailTwoRow9_coefficients

private theorem termOneTailTwoRow10_coefficients
    (j : ℕ) (hj : j < 81) :
    mulCoeffTwo X2Data V2Data 10 j =
      (((rectangularize 57 81 termOneTailTwoData).getD 10 [])).getD j 0 := by
  interval_cases j <;> decide

private theorem termOneTailTwoRow10_checked :
    padOne 81 (mulRow X2Data V2Data 10) =
      ((rectangularize 57 81 termOneTailTwoData).getD 10 []) := by
  apply padOne_mulRow_eq_of_coefficients 81 X2Data V2Data 10
    ((rectangularize 57 81 termOneTailTwoData).getD 10 [])
  · decide
  · exact termOneTailTwo_targetLength 10 (by omega) (by omega)
  · exact termOneTailTwoRow10_coefficients

private theorem termOneTailTwoRow11_coefficients
    (j : ℕ) (hj : j < 81) :
    mulCoeffTwo X2Data V2Data 11 j =
      (((rectangularize 57 81 termOneTailTwoData).getD 11 [])).getD j 0 := by
  interval_cases j <;> decide

private theorem termOneTailTwoRow11_checked :
    padOne 81 (mulRow X2Data V2Data 11) =
      ((rectangularize 57 81 termOneTailTwoData).getD 11 []) := by
  apply padOne_mulRow_eq_of_coefficients 81 X2Data V2Data 11
    ((rectangularize 57 81 termOneTailTwoData).getD 11 [])
  · decide
  · exact termOneTailTwo_targetLength 11 (by omega) (by omega)
  · exact termOneTailTwoRow11_coefficients

private theorem termOneTailTwoRow12_coefficients
    (j : ℕ) (hj : j < 81) :
    mulCoeffTwo X2Data V2Data 12 j =
      (((rectangularize 57 81 termOneTailTwoData).getD 12 [])).getD j 0 := by
  interval_cases j <;> decide

private theorem termOneTailTwoRow12_checked :
    padOne 81 (mulRow X2Data V2Data 12) =
      ((rectangularize 57 81 termOneTailTwoData).getD 12 []) := by
  apply padOne_mulRow_eq_of_coefficients 81 X2Data V2Data 12
    ((rectangularize 57 81 termOneTailTwoData).getD 12 [])
  · decide
  · exact termOneTailTwo_targetLength 12 (by omega) (by omega)
  · exact termOneTailTwoRow12_coefficients

private theorem termOneTailTwoRow13_coefficients
    (j : ℕ) (hj : j < 81) :
    mulCoeffTwo X2Data V2Data 13 j =
      (((rectangularize 57 81 termOneTailTwoData).getD 13 [])).getD j 0 := by
  interval_cases j <;> decide

private theorem termOneTailTwoRow13_checked :
    padOne 81 (mulRow X2Data V2Data 13) =
      ((rectangularize 57 81 termOneTailTwoData).getD 13 []) := by
  apply padOne_mulRow_eq_of_coefficients 81 X2Data V2Data 13
    ((rectangularize 57 81 termOneTailTwoData).getD 13 [])
  · decide
  · exact termOneTailTwo_targetLength 13 (by omega) (by omega)
  · exact termOneTailTwoRow13_coefficients

private theorem termOneTailTwoRow14_coefficients
    (j : ℕ) (hj : j < 81) :
    mulCoeffTwo X2Data V2Data 14 j =
      (((rectangularize 57 81 termOneTailTwoData).getD 14 [])).getD j 0 := by
  interval_cases j <;> decide

private theorem termOneTailTwoRow14_checked :
    padOne 81 (mulRow X2Data V2Data 14) =
      ((rectangularize 57 81 termOneTailTwoData).getD 14 []) := by
  apply padOne_mulRow_eq_of_coefficients 81 X2Data V2Data 14
    ((rectangularize 57 81 termOneTailTwoData).getD 14 [])
  · decide
  · exact termOneTailTwo_targetLength 14 (by omega) (by omega)
  · exact termOneTailTwoRow14_coefficients

private theorem termOneTailTwoRow15_coefficients
    (j : ℕ) (hj : j < 81) :
    mulCoeffTwo X2Data V2Data 15 j =
      (((rectangularize 57 81 termOneTailTwoData).getD 15 [])).getD j 0 := by
  interval_cases j <;> decide

private theorem termOneTailTwoRow15_checked :
    padOne 81 (mulRow X2Data V2Data 15) =
      ((rectangularize 57 81 termOneTailTwoData).getD 15 []) := by
  apply padOne_mulRow_eq_of_coefficients 81 X2Data V2Data 15
    ((rectangularize 57 81 termOneTailTwoData).getD 15 [])
  · decide
  · exact termOneTailTwo_targetLength 15 (by omega) (by omega)
  · exact termOneTailTwoRow15_coefficients

/-- Checked stage-one rows 8 through 15. -/
theorem termOneTailTwoRowsEightToFifteen_checked
    (n : ℕ) (hLower : 8 ≤ n) (hUpper : n < 16) :
    padOne 81 (mulRow X2Data V2Data n) =
      (rectangularize 57 81 termOneTailTwoData).getD n [] := by
  interval_cases n
  · exact termOneTailTwoRow8_checked
  · exact termOneTailTwoRow9_checked
  · exact termOneTailTwoRow10_checked
  · exact termOneTailTwoRow11_checked
  · exact termOneTailTwoRow12_checked
  · exact termOneTailTwoRow13_checked
  · exact termOneTailTwoRow14_checked
  · exact termOneTailTwoRow15_checked

end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
