/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialVFourPLeftCertificate
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialVFourPRightCertificate
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroBridge

/-!
# Checked canonical P9 subtraction in the raw V fourth power

The two checked branches are combined coefficient by coefficient as
`D^3 * L - r * s * B^3 * G * E^3`.  The bridge to the named raw `P9`
factor is then used only after this exact dense-polynomial identity is checked.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveRelationZeroCertificate.Dense
open OrderTwentyFiveDensePolynomialRectangular
open OrderTwentyFiveDensePolynomialRowCertificate

private theorem v4SubRow0_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 0 j =
      ((rectangularize 61 89 V4Data).getD 0 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow0_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 0) =
      (rectangularize 61 89 V4Data).getD 0 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 0
    ((rectangularize 61 89 V4Data).getD 0 [])
  · decide
  · have hTargetSupport : (V4Data.getD 0 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 0 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow0_coefficients

private theorem v4SubRow1_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 1 j =
      ((rectangularize 61 89 V4Data).getD 1 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow1_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 1) =
      (rectangularize 61 89 V4Data).getD 1 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 1
    ((rectangularize 61 89 V4Data).getD 1 [])
  · decide
  · have hTargetSupport : (V4Data.getD 1 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 1 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow1_coefficients

private theorem v4SubRow2_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 2 j =
      ((rectangularize 61 89 V4Data).getD 2 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow2_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 2) =
      (rectangularize 61 89 V4Data).getD 2 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 2
    ((rectangularize 61 89 V4Data).getD 2 [])
  · decide
  · have hTargetSupport : (V4Data.getD 2 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 2 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow2_coefficients

private theorem v4SubRow3_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 3 j =
      ((rectangularize 61 89 V4Data).getD 3 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow3_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 3) =
      (rectangularize 61 89 V4Data).getD 3 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 3
    ((rectangularize 61 89 V4Data).getD 3 [])
  · decide
  · have hTargetSupport : (V4Data.getD 3 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 3 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow3_coefficients

private theorem v4SubRow4_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 4 j =
      ((rectangularize 61 89 V4Data).getD 4 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow4_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 4) =
      (rectangularize 61 89 V4Data).getD 4 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 4
    ((rectangularize 61 89 V4Data).getD 4 [])
  · decide
  · have hTargetSupport : (V4Data.getD 4 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 4 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow4_coefficients

private theorem v4SubRow5_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 5 j =
      ((rectangularize 61 89 V4Data).getD 5 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow5_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 5) =
      (rectangularize 61 89 V4Data).getD 5 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 5
    ((rectangularize 61 89 V4Data).getD 5 [])
  · decide
  · have hTargetSupport : (V4Data.getD 5 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 5 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow5_coefficients

private theorem v4SubRow6_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 6 j =
      ((rectangularize 61 89 V4Data).getD 6 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow6_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 6) =
      (rectangularize 61 89 V4Data).getD 6 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 6
    ((rectangularize 61 89 V4Data).getD 6 [])
  · decide
  · have hTargetSupport : (V4Data.getD 6 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 6 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow6_coefficients

private theorem v4SubRow7_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 7 j =
      ((rectangularize 61 89 V4Data).getD 7 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow7_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 7) =
      (rectangularize 61 89 V4Data).getD 7 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 7
    ((rectangularize 61 89 V4Data).getD 7 [])
  · decide
  · have hTargetSupport : (V4Data.getD 7 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 7 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow7_coefficients

private theorem v4SubRow8_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 8 j =
      ((rectangularize 61 89 V4Data).getD 8 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow8_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 8) =
      (rectangularize 61 89 V4Data).getD 8 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 8
    ((rectangularize 61 89 V4Data).getD 8 [])
  · decide
  · have hTargetSupport : (V4Data.getD 8 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 8 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow8_coefficients

private theorem v4SubRow9_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 9 j =
      ((rectangularize 61 89 V4Data).getD 9 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow9_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 9) =
      (rectangularize 61 89 V4Data).getD 9 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 9
    ((rectangularize 61 89 V4Data).getD 9 [])
  · decide
  · have hTargetSupport : (V4Data.getD 9 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 9 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow9_coefficients

private theorem v4SubRow10_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 10 j =
      ((rectangularize 61 89 V4Data).getD 10 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow10_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 10) =
      (rectangularize 61 89 V4Data).getD 10 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 10
    ((rectangularize 61 89 V4Data).getD 10 [])
  · decide
  · have hTargetSupport : (V4Data.getD 10 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 10 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow10_coefficients

private theorem v4SubRow11_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 11 j =
      ((rectangularize 61 89 V4Data).getD 11 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow11_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 11) =
      (rectangularize 61 89 V4Data).getD 11 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 11
    ((rectangularize 61 89 V4Data).getD 11 [])
  · decide
  · have hTargetSupport : (V4Data.getD 11 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 11 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow11_coefficients

private theorem v4SubRow12_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 12 j =
      ((rectangularize 61 89 V4Data).getD 12 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow12_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 12) =
      (rectangularize 61 89 V4Data).getD 12 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 12
    ((rectangularize 61 89 V4Data).getD 12 [])
  · decide
  · have hTargetSupport : (V4Data.getD 12 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 12 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow12_coefficients

private theorem v4SubRow13_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 13 j =
      ((rectangularize 61 89 V4Data).getD 13 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow13_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 13) =
      (rectangularize 61 89 V4Data).getD 13 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 13
    ((rectangularize 61 89 V4Data).getD 13 [])
  · decide
  · have hTargetSupport : (V4Data.getD 13 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 13 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow13_coefficients

private theorem v4SubRow14_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 14 j =
      ((rectangularize 61 89 V4Data).getD 14 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow14_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 14) =
      (rectangularize 61 89 V4Data).getD 14 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 14
    ((rectangularize 61 89 V4Data).getD 14 [])
  · decide
  · have hTargetSupport : (V4Data.getD 14 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 14 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow14_coefficients

private theorem v4SubRow15_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 15 j =
      ((rectangularize 61 89 V4Data).getD 15 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow15_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 15) =
      (rectangularize 61 89 V4Data).getD 15 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 15
    ((rectangularize 61 89 V4Data).getD 15 [])
  · decide
  · have hTargetSupport : (V4Data.getD 15 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 15 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow15_coefficients

private theorem v4SubRow16_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 16 j =
      ((rectangularize 61 89 V4Data).getD 16 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow16_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 16) =
      (rectangularize 61 89 V4Data).getD 16 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 16
    ((rectangularize 61 89 V4Data).getD 16 [])
  · decide
  · have hTargetSupport : (V4Data.getD 16 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 16 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow16_coefficients

private theorem v4SubRow17_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 17 j =
      ((rectangularize 61 89 V4Data).getD 17 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow17_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 17) =
      (rectangularize 61 89 V4Data).getD 17 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 17
    ((rectangularize 61 89 V4Data).getD 17 [])
  · decide
  · have hTargetSupport : (V4Data.getD 17 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 17 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow17_coefficients

private theorem v4SubRow18_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 18 j =
      ((rectangularize 61 89 V4Data).getD 18 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow18_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 18) =
      (rectangularize 61 89 V4Data).getD 18 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 18
    ((rectangularize 61 89 V4Data).getD 18 [])
  · decide
  · have hTargetSupport : (V4Data.getD 18 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 18 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow18_coefficients

private theorem v4SubRow19_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 19 j =
      ((rectangularize 61 89 V4Data).getD 19 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow19_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 19) =
      (rectangularize 61 89 V4Data).getD 19 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 19
    ((rectangularize 61 89 V4Data).getD 19 [])
  · decide
  · have hTargetSupport : (V4Data.getD 19 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 19 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow19_coefficients

private theorem v4SubRow20_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 20 j =
      ((rectangularize 61 89 V4Data).getD 20 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow20_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 20) =
      (rectangularize 61 89 V4Data).getD 20 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 20
    ((rectangularize 61 89 V4Data).getD 20 [])
  · decide
  · have hTargetSupport : (V4Data.getD 20 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 20 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow20_coefficients

private theorem v4SubRow21_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 21 j =
      ((rectangularize 61 89 V4Data).getD 21 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow21_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 21) =
      (rectangularize 61 89 V4Data).getD 21 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 21
    ((rectangularize 61 89 V4Data).getD 21 [])
  · decide
  · have hTargetSupport : (V4Data.getD 21 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 21 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow21_coefficients

private theorem v4SubRow22_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 22 j =
      ((rectangularize 61 89 V4Data).getD 22 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow22_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 22) =
      (rectangularize 61 89 V4Data).getD 22 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 22
    ((rectangularize 61 89 V4Data).getD 22 [])
  · decide
  · have hTargetSupport : (V4Data.getD 22 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 22 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow22_coefficients

private theorem v4SubRow23_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 23 j =
      ((rectangularize 61 89 V4Data).getD 23 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow23_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 23) =
      (rectangularize 61 89 V4Data).getD 23 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 23
    ((rectangularize 61 89 V4Data).getD 23 [])
  · decide
  · have hTargetSupport : (V4Data.getD 23 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 23 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow23_coefficients

private theorem v4SubRow24_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 24 j =
      ((rectangularize 61 89 V4Data).getD 24 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow24_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 24) =
      (rectangularize 61 89 V4Data).getD 24 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 24
    ((rectangularize 61 89 V4Data).getD 24 [])
  · decide
  · have hTargetSupport : (V4Data.getD 24 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 24 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow24_coefficients

private theorem v4SubRow25_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 25 j =
      ((rectangularize 61 89 V4Data).getD 25 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow25_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 25) =
      (rectangularize 61 89 V4Data).getD 25 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 25
    ((rectangularize 61 89 V4Data).getD 25 [])
  · decide
  · have hTargetSupport : (V4Data.getD 25 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 25 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow25_coefficients

private theorem v4SubRow26_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 26 j =
      ((rectangularize 61 89 V4Data).getD 26 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow26_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 26) =
      (rectangularize 61 89 V4Data).getD 26 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 26
    ((rectangularize 61 89 V4Data).getD 26 [])
  · decide
  · have hTargetSupport : (V4Data.getD 26 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 26 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow26_coefficients

private theorem v4SubRow27_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 27 j =
      ((rectangularize 61 89 V4Data).getD 27 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow27_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 27) =
      (rectangularize 61 89 V4Data).getD 27 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 27
    ((rectangularize 61 89 V4Data).getD 27 [])
  · decide
  · have hTargetSupport : (V4Data.getD 27 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 27 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow27_coefficients

private theorem v4SubRow28_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 28 j =
      ((rectangularize 61 89 V4Data).getD 28 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow28_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 28) =
      (rectangularize 61 89 V4Data).getD 28 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 28
    ((rectangularize 61 89 V4Data).getD 28 [])
  · decide
  · have hTargetSupport : (V4Data.getD 28 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 28 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow28_coefficients

private theorem v4SubRow29_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 29 j =
      ((rectangularize 61 89 V4Data).getD 29 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow29_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 29) =
      (rectangularize 61 89 V4Data).getD 29 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 29
    ((rectangularize 61 89 V4Data).getD 29 [])
  · decide
  · have hTargetSupport : (V4Data.getD 29 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 29 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow29_coefficients

private theorem v4SubRow30_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 30 j =
      ((rectangularize 61 89 V4Data).getD 30 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow30_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 30) =
      (rectangularize 61 89 V4Data).getD 30 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 30
    ((rectangularize 61 89 V4Data).getD 30 [])
  · decide
  · have hTargetSupport : (V4Data.getD 30 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 30 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow30_coefficients

private theorem v4SubRow31_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 31 j =
      ((rectangularize 61 89 V4Data).getD 31 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow31_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 31) =
      (rectangularize 61 89 V4Data).getD 31 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 31
    ((rectangularize 61 89 V4Data).getD 31 [])
  · decide
  · have hTargetSupport : (V4Data.getD 31 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 31 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow31_coefficients

private theorem v4SubRow32_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 32 j =
      ((rectangularize 61 89 V4Data).getD 32 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow32_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 32) =
      (rectangularize 61 89 V4Data).getD 32 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 32
    ((rectangularize 61 89 V4Data).getD 32 [])
  · decide
  · have hTargetSupport : (V4Data.getD 32 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 32 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow32_coefficients

private theorem v4SubRow33_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 33 j =
      ((rectangularize 61 89 V4Data).getD 33 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow33_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 33) =
      (rectangularize 61 89 V4Data).getD 33 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 33
    ((rectangularize 61 89 V4Data).getD 33 [])
  · decide
  · have hTargetSupport : (V4Data.getD 33 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 33 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow33_coefficients

private theorem v4SubRow34_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 34 j =
      ((rectangularize 61 89 V4Data).getD 34 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow34_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 34) =
      (rectangularize 61 89 V4Data).getD 34 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 34
    ((rectangularize 61 89 V4Data).getD 34 [])
  · decide
  · have hTargetSupport : (V4Data.getD 34 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 34 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow34_coefficients

private theorem v4SubRow35_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 35 j =
      ((rectangularize 61 89 V4Data).getD 35 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow35_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 35) =
      (rectangularize 61 89 V4Data).getD 35 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 35
    ((rectangularize 61 89 V4Data).getD 35 [])
  · decide
  · have hTargetSupport : (V4Data.getD 35 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 35 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow35_coefficients

private theorem v4SubRow36_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 36 j =
      ((rectangularize 61 89 V4Data).getD 36 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow36_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 36) =
      (rectangularize 61 89 V4Data).getD 36 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 36
    ((rectangularize 61 89 V4Data).getD 36 [])
  · decide
  · have hTargetSupport : (V4Data.getD 36 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 36 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow36_coefficients

private theorem v4SubRow37_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 37 j =
      ((rectangularize 61 89 V4Data).getD 37 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow37_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 37) =
      (rectangularize 61 89 V4Data).getD 37 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 37
    ((rectangularize 61 89 V4Data).getD 37 [])
  · decide
  · have hTargetSupport : (V4Data.getD 37 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 37 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow37_coefficients

private theorem v4SubRow38_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 38 j =
      ((rectangularize 61 89 V4Data).getD 38 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow38_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 38) =
      (rectangularize 61 89 V4Data).getD 38 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 38
    ((rectangularize 61 89 V4Data).getD 38 [])
  · decide
  · have hTargetSupport : (V4Data.getD 38 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 38 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow38_coefficients

private theorem v4SubRow39_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 39 j =
      ((rectangularize 61 89 V4Data).getD 39 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow39_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 39) =
      (rectangularize 61 89 V4Data).getD 39 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 39
    ((rectangularize 61 89 V4Data).getD 39 [])
  · decide
  · have hTargetSupport : (V4Data.getD 39 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 39 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow39_coefficients

private theorem v4SubRow40_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 40 j =
      ((rectangularize 61 89 V4Data).getD 40 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow40_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 40) =
      (rectangularize 61 89 V4Data).getD 40 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 40
    ((rectangularize 61 89 V4Data).getD 40 [])
  · decide
  · have hTargetSupport : (V4Data.getD 40 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 40 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow40_coefficients

private theorem v4SubRow41_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 41 j =
      ((rectangularize 61 89 V4Data).getD 41 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow41_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 41) =
      (rectangularize 61 89 V4Data).getD 41 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 41
    ((rectangularize 61 89 V4Data).getD 41 [])
  · decide
  · have hTargetSupport : (V4Data.getD 41 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 41 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow41_coefficients

private theorem v4SubRow42_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 42 j =
      ((rectangularize 61 89 V4Data).getD 42 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow42_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 42) =
      (rectangularize 61 89 V4Data).getD 42 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 42
    ((rectangularize 61 89 V4Data).getD 42 [])
  · decide
  · have hTargetSupport : (V4Data.getD 42 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 42 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow42_coefficients

private theorem v4SubRow43_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 43 j =
      ((rectangularize 61 89 V4Data).getD 43 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow43_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 43) =
      (rectangularize 61 89 V4Data).getD 43 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 43
    ((rectangularize 61 89 V4Data).getD 43 [])
  · decide
  · have hTargetSupport : (V4Data.getD 43 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 43 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow43_coefficients

private theorem v4SubRow44_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 44 j =
      ((rectangularize 61 89 V4Data).getD 44 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow44_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 44) =
      (rectangularize 61 89 V4Data).getD 44 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 44
    ((rectangularize 61 89 V4Data).getD 44 [])
  · decide
  · have hTargetSupport : (V4Data.getD 44 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 44 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow44_coefficients

private theorem v4SubRow45_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 45 j =
      ((rectangularize 61 89 V4Data).getD 45 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow45_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 45) =
      (rectangularize 61 89 V4Data).getD 45 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 45
    ((rectangularize 61 89 V4Data).getD 45 [])
  · decide
  · have hTargetSupport : (V4Data.getD 45 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 45 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow45_coefficients

private theorem v4SubRow46_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 46 j =
      ((rectangularize 61 89 V4Data).getD 46 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow46_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 46) =
      (rectangularize 61 89 V4Data).getD 46 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 46
    ((rectangularize 61 89 V4Data).getD 46 [])
  · decide
  · have hTargetSupport : (V4Data.getD 46 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 46 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow46_coefficients

private theorem v4SubRow47_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 47 j =
      ((rectangularize 61 89 V4Data).getD 47 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow47_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 47) =
      (rectangularize 61 89 V4Data).getD 47 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 47
    ((rectangularize 61 89 V4Data).getD 47 [])
  · decide
  · have hTargetSupport : (V4Data.getD 47 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 47 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow47_coefficients

private theorem v4SubRow48_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 48 j =
      ((rectangularize 61 89 V4Data).getD 48 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow48_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 48) =
      (rectangularize 61 89 V4Data).getD 48 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 48
    ((rectangularize 61 89 V4Data).getD 48 [])
  · decide
  · have hTargetSupport : (V4Data.getD 48 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 48 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow48_coefficients

private theorem v4SubRow49_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 49 j =
      ((rectangularize 61 89 V4Data).getD 49 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow49_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 49) =
      (rectangularize 61 89 V4Data).getD 49 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 49
    ((rectangularize 61 89 V4Data).getD 49 [])
  · decide
  · have hTargetSupport : (V4Data.getD 49 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 49 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow49_coefficients

private theorem v4SubRow50_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 50 j =
      ((rectangularize 61 89 V4Data).getD 50 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow50_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 50) =
      (rectangularize 61 89 V4Data).getD 50 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 50
    ((rectangularize 61 89 V4Data).getD 50 [])
  · decide
  · have hTargetSupport : (V4Data.getD 50 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 50 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow50_coefficients

private theorem v4SubRow51_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 51 j =
      ((rectangularize 61 89 V4Data).getD 51 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow51_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 51) =
      (rectangularize 61 89 V4Data).getD 51 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 51
    ((rectangularize 61 89 V4Data).getD 51 [])
  · decide
  · have hTargetSupport : (V4Data.getD 51 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 51 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow51_coefficients

private theorem v4SubRow52_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 52 j =
      ((rectangularize 61 89 V4Data).getD 52 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow52_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 52) =
      (rectangularize 61 89 V4Data).getD 52 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 52
    ((rectangularize 61 89 V4Data).getD 52 [])
  · decide
  · have hTargetSupport : (V4Data.getD 52 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 52 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow52_coefficients

private theorem v4SubRow53_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 53 j =
      ((rectangularize 61 89 V4Data).getD 53 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow53_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 53) =
      (rectangularize 61 89 V4Data).getD 53 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 53
    ((rectangularize 61 89 V4Data).getD 53 [])
  · decide
  · have hTargetSupport : (V4Data.getD 53 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 53 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow53_coefficients

private theorem v4SubRow54_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 54 j =
      ((rectangularize 61 89 V4Data).getD 54 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow54_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 54) =
      (rectangularize 61 89 V4Data).getD 54 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 54
    ((rectangularize 61 89 V4Data).getD 54 [])
  · decide
  · have hTargetSupport : (V4Data.getD 54 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 54 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow54_coefficients

private theorem v4SubRow55_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 55 j =
      ((rectangularize 61 89 V4Data).getD 55 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow55_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 55) =
      (rectangularize 61 89 V4Data).getD 55 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 55
    ((rectangularize 61 89 V4Data).getD 55 [])
  · decide
  · have hTargetSupport : (V4Data.getD 55 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 55 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow55_coefficients

private theorem v4SubRow56_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 56 j =
      ((rectangularize 61 89 V4Data).getD 56 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow56_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 56) =
      (rectangularize 61 89 V4Data).getD 56 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 56
    ((rectangularize 61 89 V4Data).getD 56 [])
  · decide
  · have hTargetSupport : (V4Data.getD 56 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 56 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow56_coefficients

private theorem v4SubRow57_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 57 j =
      ((rectangularize 61 89 V4Data).getD 57 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow57_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 57) =
      (rectangularize 61 89 V4Data).getD 57 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 57
    ((rectangularize 61 89 V4Data).getD 57 [])
  · decide
  · have hTargetSupport : (V4Data.getD 57 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 57 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow57_coefficients

private theorem v4SubRow58_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 58 j =
      ((rectangularize 61 89 V4Data).getD 58 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow58_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 58) =
      (rectangularize 61 89 V4Data).getD 58 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 58
    ((rectangularize 61 89 V4Data).getD 58 [])
  · decide
  · have hTargetSupport : (V4Data.getD 58 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 58 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow58_coefficients

private theorem v4SubRow59_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 59 j =
      ((rectangularize 61 89 V4Data).getD 59 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow59_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 59) =
      (rectangularize 61 89 V4Data).getD 59 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 59
    ((rectangularize 61 89 V4Data).getD 59 [])
  · decide
  · have hTargetSupport : (V4Data.getD 59 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 59 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow59_coefficients

private theorem v4SubRow60_coefficients (j : ℕ) (hj : j < 89) :
    addMulCoeffTwo V4PLLData NegData V4PRE3Data 60 j =
      ((rectangularize 61 89 V4Data).getD 60 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4SubRow60_spec :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data 60) =
      (rectangularize 61 89 V4Data).getD 60 [] := by
  apply padOne_addMulRow_eq_of_coefficients 89 V4PLLData NegData V4PRE3Data 60
    ((rectangularize 61 89 V4Data).getD 60 [])
  · decide
  · have hTargetSupport : (V4Data.getD 60 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4Data 60 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4SubRow60_coefficients

private theorem v4SubRows_spec (n : ℕ) (hn : n < 61) :
    padOne 89 (addMulRow V4PLLData NegData V4PRE3Data n) =
      (rectangularize 61 89 V4Data).getD n [] := by
  interval_cases n
  · exact v4SubRow0_spec
  · exact v4SubRow1_spec
  · exact v4SubRow2_spec
  · exact v4SubRow3_spec
  · exact v4SubRow4_spec
  · exact v4SubRow5_spec
  · exact v4SubRow6_spec
  · exact v4SubRow7_spec
  · exact v4SubRow8_spec
  · exact v4SubRow9_spec
  · exact v4SubRow10_spec
  · exact v4SubRow11_spec
  · exact v4SubRow12_spec
  · exact v4SubRow13_spec
  · exact v4SubRow14_spec
  · exact v4SubRow15_spec
  · exact v4SubRow16_spec
  · exact v4SubRow17_spec
  · exact v4SubRow18_spec
  · exact v4SubRow19_spec
  · exact v4SubRow20_spec
  · exact v4SubRow21_spec
  · exact v4SubRow22_spec
  · exact v4SubRow23_spec
  · exact v4SubRow24_spec
  · exact v4SubRow25_spec
  · exact v4SubRow26_spec
  · exact v4SubRow27_spec
  · exact v4SubRow28_spec
  · exact v4SubRow29_spec
  · exact v4SubRow30_spec
  · exact v4SubRow31_spec
  · exact v4SubRow32_spec
  · exact v4SubRow33_spec
  · exact v4SubRow34_spec
  · exact v4SubRow35_spec
  · exact v4SubRow36_spec
  · exact v4SubRow37_spec
  · exact v4SubRow38_spec
  · exact v4SubRow39_spec
  · exact v4SubRow40_spec
  · exact v4SubRow41_spec
  · exact v4SubRow42_spec
  · exact v4SubRow43_spec
  · exact v4SubRow44_spec
  · exact v4SubRow45_spec
  · exact v4SubRow46_spec
  · exact v4SubRow47_spec
  · exact v4SubRow48_spec
  · exact v4SubRow49_spec
  · exact v4SubRow50_spec
  · exact v4SubRow51_spec
  · exact v4SubRow52_spec
  · exact v4SubRow53_spec
  · exact v4SubRow54_spec
  · exact v4SubRow55_spec
  · exact v4SubRow56_spec
  · exact v4SubRow57_spec
  · exact v4SubRow58_spec
  · exact v4SubRow59_spec
  · exact v4SubRow60_spec

private theorem v4SubLeft_length :
    (rectangularize 61 89
      (Two.add V4PLLData (Two.mul NegData V4PRE3Data))).length = 61 := by
  decide

private theorem v4SubRight_length :
    (rectangularize 61 89 V4Data).length = 61 := by
  decide

-- Exact bidegree bound (60, 88); no row or column is discarded.
private theorem v4SubData_spec :
    rectangularize 61 89
        (Two.add V4PLLData (Two.mul NegData V4PRE3Data)) =
      rectangularize 61 89 V4Data := by
  apply List.ext_getElem (v4SubLeft_length.trans v4SubRight_length.symm)
  intro n hn _
  rw [List.getElem_eq_getD [], List.getElem_eq_getD []]
  rw [v4SubLeft_length] at hn
  rw [getD_rectangularize 61 89
    (Two.add V4PLLData (Two.mul NegData V4PRE3Data)) n hn,
    ← addMulRow_eq_getD]
  exact v4SubRows_spec n hn

/-- Evaluation of the checked fourth-power table through the canonical `P9`. -/
theorem eval_v4Data (r s : ℚ) :
    Two.eval V4Data r s =
      Two.eval VData r s * Two.eval V2Data r s *
        (s * OrderTwentyFiveRelationZeroCertificate.Internal.C r s ^ 3 *
          OrderTwentyFiveRelationZeroCertificate.Internal.J r s *
          OrderTwentyFiveRawOrbitFactorCertificate.P9 r s) := by
  have hSub := congrArg (fun p => Two.eval p r s) v4SubData_spec
  simp only [eval_rectangularize, Two.eval_add, Two.eval_mul] at hSub
  calc
    Two.eval V4Data r s =
        Two.eval V4PLLData r s +
          Two.eval NegData r s * Two.eval V4PRE3Data r s := hSub.symm
    _ = OrderTwentyFiveRelationZeroCertificate.Internal.P9 r s *
        Two.eval V4JData r s := by
      have hB : OrderTwentyFiveRelationZeroCertificate.Internal.B r s =
          OrderTwentyFiveRawOrbitFactorCertificate.B r s := rfl
      have hD : OrderTwentyFiveRelationZeroCertificate.Internal.D r s =
          OrderTwentyFiveRawOrbitFactorCertificate.D r s := rfl
      have hE : OrderTwentyFiveRelationZeroCertificate.Internal.E r s =
          OrderTwentyFiveRawOrbitFactorCertificate.E r s := rfl
      have hL : OrderTwentyFiveRelationZeroCertificate.Internal.L r s =
          OrderTwentyFiveRawOrbitFactorCertificate.L r s := rfl
      rw [eval_v4PLeftData, eval_v4PRightData, eval_NegData,
        hB, hD, hE, hL,
        OrderTwentyFiveRelationZeroCertificate.Internal.P9_eq_factor]
      simp only [OrderTwentyFiveRawOrbitFactorCertificate.P9]
      ring
    _ = Two.eval VData r s * Two.eval V2Data r s *
        (s * OrderTwentyFiveRelationZeroCertificate.Internal.C r s ^ 3 *
          OrderTwentyFiveRelationZeroCertificate.Internal.J r s *
          OrderTwentyFiveRawOrbitFactorCertificate.P9 r s) := by
      rw [OrderTwentyFiveRelationZeroCertificate.Internal.P9_eq_factor,
        eval_v4JData]
      ring

end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
