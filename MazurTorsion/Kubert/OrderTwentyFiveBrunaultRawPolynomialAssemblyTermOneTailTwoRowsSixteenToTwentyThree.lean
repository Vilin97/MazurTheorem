/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialAssemblyTermOneTailTwoData
import MazurTorsion.Kubert.OrderTwentyFiveDensePolynomialMulCertificate
import Mathlib.Tactic.IntervalCases

/-!
# Rows 16 through 23 of the first term-one tail

Every generated coefficient is checked by Lean against the corresponding
row-local dense convolution.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveDensePolynomialRectangular
open OrderTwentyFiveDensePolynomialRowCertificate
private theorem termOneTailTwo_targetLength
    (n : ℕ) (hLower : 16 ≤ n) (hUpper : n < 24) :
    ((rectangularize 57 81 termOneTailTwoData).getD n []).length = 81 := by
  rw [getD_rectangularize 57 81 termOneTailTwoData n (by omega)]
  simp only [padOne, List.length_append, List.length_replicate]
  have hRow : (termOneTailTwoData.getD n []).length ≤ 81 := by
    interval_cases n <;> decide
  omega
private theorem termOneTailTwoRow16_coefficients
    (j : ℕ) (hj : j < 81) :
    mulCoeffTwo X2Data V2Data 16 j =
      (((rectangularize 57 81 termOneTailTwoData).getD 16 [])).getD j 0 := by
  interval_cases j <;> decide

private theorem termOneTailTwoRow16_checked :
    padOne 81 (mulRow X2Data V2Data 16) =
      ((rectangularize 57 81 termOneTailTwoData).getD 16 []) := by
  apply padOne_mulRow_eq_of_coefficients 81 X2Data V2Data 16
    ((rectangularize 57 81 termOneTailTwoData).getD 16 [])
  · decide
  · exact termOneTailTwo_targetLength 16 (by omega) (by omega)
  · exact termOneTailTwoRow16_coefficients

private theorem termOneTailTwoRow17_coefficients
    (j : ℕ) (hj : j < 81) :
    mulCoeffTwo X2Data V2Data 17 j =
      (((rectangularize 57 81 termOneTailTwoData).getD 17 [])).getD j 0 := by
  interval_cases j <;> decide

private theorem termOneTailTwoRow17_checked :
    padOne 81 (mulRow X2Data V2Data 17) =
      ((rectangularize 57 81 termOneTailTwoData).getD 17 []) := by
  apply padOne_mulRow_eq_of_coefficients 81 X2Data V2Data 17
    ((rectangularize 57 81 termOneTailTwoData).getD 17 [])
  · decide
  · exact termOneTailTwo_targetLength 17 (by omega) (by omega)
  · exact termOneTailTwoRow17_coefficients

private theorem termOneTailTwoRow18_coefficients
    (j : ℕ) (hj : j < 81) :
    mulCoeffTwo X2Data V2Data 18 j =
      (((rectangularize 57 81 termOneTailTwoData).getD 18 [])).getD j 0 := by
  interval_cases j <;> decide

private theorem termOneTailTwoRow18_checked :
    padOne 81 (mulRow X2Data V2Data 18) =
      ((rectangularize 57 81 termOneTailTwoData).getD 18 []) := by
  apply padOne_mulRow_eq_of_coefficients 81 X2Data V2Data 18
    ((rectangularize 57 81 termOneTailTwoData).getD 18 [])
  · decide
  · exact termOneTailTwo_targetLength 18 (by omega) (by omega)
  · exact termOneTailTwoRow18_coefficients

private theorem termOneTailTwoRow19_coefficients
    (j : ℕ) (hj : j < 81) :
    mulCoeffTwo X2Data V2Data 19 j =
      (((rectangularize 57 81 termOneTailTwoData).getD 19 [])).getD j 0 := by
  interval_cases j <;> decide

private theorem termOneTailTwoRow19_checked :
    padOne 81 (mulRow X2Data V2Data 19) =
      ((rectangularize 57 81 termOneTailTwoData).getD 19 []) := by
  apply padOne_mulRow_eq_of_coefficients 81 X2Data V2Data 19
    ((rectangularize 57 81 termOneTailTwoData).getD 19 [])
  · decide
  · exact termOneTailTwo_targetLength 19 (by omega) (by omega)
  · exact termOneTailTwoRow19_coefficients

private theorem termOneTailTwoRow20_coefficients
    (j : ℕ) (hj : j < 81) :
    mulCoeffTwo X2Data V2Data 20 j =
      (((rectangularize 57 81 termOneTailTwoData).getD 20 [])).getD j 0 := by
  interval_cases j <;> decide

private theorem termOneTailTwoRow20_checked :
    padOne 81 (mulRow X2Data V2Data 20) =
      ((rectangularize 57 81 termOneTailTwoData).getD 20 []) := by
  apply padOne_mulRow_eq_of_coefficients 81 X2Data V2Data 20
    ((rectangularize 57 81 termOneTailTwoData).getD 20 [])
  · decide
  · exact termOneTailTwo_targetLength 20 (by omega) (by omega)
  · exact termOneTailTwoRow20_coefficients

private theorem termOneTailTwoRow21_coefficients
    (j : ℕ) (hj : j < 81) :
    mulCoeffTwo X2Data V2Data 21 j =
      (((rectangularize 57 81 termOneTailTwoData).getD 21 [])).getD j 0 := by
  interval_cases j <;> decide

private theorem termOneTailTwoRow21_checked :
    padOne 81 (mulRow X2Data V2Data 21) =
      ((rectangularize 57 81 termOneTailTwoData).getD 21 []) := by
  apply padOne_mulRow_eq_of_coefficients 81 X2Data V2Data 21
    ((rectangularize 57 81 termOneTailTwoData).getD 21 [])
  · decide
  · exact termOneTailTwo_targetLength 21 (by omega) (by omega)
  · exact termOneTailTwoRow21_coefficients

private theorem termOneTailTwoRow22_coefficients
    (j : ℕ) (hj : j < 81) :
    mulCoeffTwo X2Data V2Data 22 j =
      (((rectangularize 57 81 termOneTailTwoData).getD 22 [])).getD j 0 := by
  interval_cases j <;> decide

private theorem termOneTailTwoRow22_checked :
    padOne 81 (mulRow X2Data V2Data 22) =
      ((rectangularize 57 81 termOneTailTwoData).getD 22 []) := by
  apply padOne_mulRow_eq_of_coefficients 81 X2Data V2Data 22
    ((rectangularize 57 81 termOneTailTwoData).getD 22 [])
  · decide
  · exact termOneTailTwo_targetLength 22 (by omega) (by omega)
  · exact termOneTailTwoRow22_coefficients

private theorem termOneTailTwoRow23_coefficients
    (j : ℕ) (hj : j < 81) :
    mulCoeffTwo X2Data V2Data 23 j =
      (((rectangularize 57 81 termOneTailTwoData).getD 23 [])).getD j 0 := by
  interval_cases j <;> decide

private theorem termOneTailTwoRow23_checked :
    padOne 81 (mulRow X2Data V2Data 23) =
      ((rectangularize 57 81 termOneTailTwoData).getD 23 []) := by
  apply padOne_mulRow_eq_of_coefficients 81 X2Data V2Data 23
    ((rectangularize 57 81 termOneTailTwoData).getD 23 [])
  · decide
  · exact termOneTailTwo_targetLength 23 (by omega) (by omega)
  · exact termOneTailTwoRow23_coefficients

/-- Checked stage-one rows 16 through 23. -/
theorem termOneTailTwoRowsSixteenToTwentyThree_checked
    (n : ℕ) (hLower : 16 ≤ n) (hUpper : n < 24) :
    padOne 81 (mulRow X2Data V2Data n) =
      (rectangularize 57 81 termOneTailTwoData).getD n [] := by
  interval_cases n
  · exact termOneTailTwoRow16_checked
  · exact termOneTailTwoRow17_checked
  · exact termOneTailTwoRow18_checked
  · exact termOneTailTwoRow19_checked
  · exact termOneTailTwoRow20_checked
  · exact termOneTailTwoRow21_checked
  · exact termOneTailTwoRow22_checked
  · exact termOneTailTwoRow23_checked

end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
