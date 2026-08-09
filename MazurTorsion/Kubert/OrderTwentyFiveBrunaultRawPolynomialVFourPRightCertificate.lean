/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialVFourCoreCertificate
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialAuxiliaryFactorData
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialVFourPRightBData
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialVFourPRightGEData

/-!
# Checked right branch of the canonical P9 factor in raw V fourth power

Each staged dense multiplication is checked row by row within its exact
rectangle, including every possible outer and inner tail.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveRelationZeroCertificate.Dense
open OrderTwentyFiveDensePolynomialRectangular
open OrderTwentyFiveDensePolynomialRowCertificate

private theorem v4PRRRow0_spec :
    padOne 76 (mulRow RData V4JData 0) =
      (rectangularize 53 76 V4PRRData).getD 0 [] := by
  decide

private theorem v4PRRRow1_spec :
    padOne 76 (mulRow RData V4JData 1) =
      (rectangularize 53 76 V4PRRData).getD 1 [] := by
  decide

private theorem v4PRRRow2_spec :
    padOne 76 (mulRow RData V4JData 2) =
      (rectangularize 53 76 V4PRRData).getD 2 [] := by
  decide

private theorem v4PRRRow3_spec :
    padOne 76 (mulRow RData V4JData 3) =
      (rectangularize 53 76 V4PRRData).getD 3 [] := by
  decide

private theorem v4PRRRow4_spec :
    padOne 76 (mulRow RData V4JData 4) =
      (rectangularize 53 76 V4PRRData).getD 4 [] := by
  decide

private theorem v4PRRRow5_spec :
    padOne 76 (mulRow RData V4JData 5) =
      (rectangularize 53 76 V4PRRData).getD 5 [] := by
  decide

private theorem v4PRRRow6_spec :
    padOne 76 (mulRow RData V4JData 6) =
      (rectangularize 53 76 V4PRRData).getD 6 [] := by
  decide

private theorem v4PRRRow7_spec :
    padOne 76 (mulRow RData V4JData 7) =
      (rectangularize 53 76 V4PRRData).getD 7 [] := by
  decide

private theorem v4PRRRow8_spec :
    padOne 76 (mulRow RData V4JData 8) =
      (rectangularize 53 76 V4PRRData).getD 8 [] := by
  decide

private theorem v4PRRRow9_spec :
    padOne 76 (mulRow RData V4JData 9) =
      (rectangularize 53 76 V4PRRData).getD 9 [] := by
  decide

private theorem v4PRRRow10_spec :
    padOne 76 (mulRow RData V4JData 10) =
      (rectangularize 53 76 V4PRRData).getD 10 [] := by
  decide

private theorem v4PRRRow11_spec :
    padOne 76 (mulRow RData V4JData 11) =
      (rectangularize 53 76 V4PRRData).getD 11 [] := by
  decide

private theorem v4PRRRow12_spec :
    padOne 76 (mulRow RData V4JData 12) =
      (rectangularize 53 76 V4PRRData).getD 12 [] := by
  decide

private theorem v4PRRRow13_spec :
    padOne 76 (mulRow RData V4JData 13) =
      (rectangularize 53 76 V4PRRData).getD 13 [] := by
  decide

private theorem v4PRRRow14_spec :
    padOne 76 (mulRow RData V4JData 14) =
      (rectangularize 53 76 V4PRRData).getD 14 [] := by
  decide

private theorem v4PRRRow15_spec :
    padOne 76 (mulRow RData V4JData 15) =
      (rectangularize 53 76 V4PRRData).getD 15 [] := by
  decide

private theorem v4PRRRow16_spec :
    padOne 76 (mulRow RData V4JData 16) =
      (rectangularize 53 76 V4PRRData).getD 16 [] := by
  decide

private theorem v4PRRRow17_spec :
    padOne 76 (mulRow RData V4JData 17) =
      (rectangularize 53 76 V4PRRData).getD 17 [] := by
  decide

private theorem v4PRRRow18_coefficients (j : ℕ) (hj : j < 76) :
    mulCoeffTwo RData V4JData 18 j =
      ((rectangularize 53 76 V4PRRData).getD 18 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRRRow18_spec :
    padOne 76 (mulRow RData V4JData 18) =
      (rectangularize 53 76 V4PRRData).getD 18 [] := by
  apply padOne_mulRow_eq_of_coefficients 76 RData V4JData 18
    ((rectangularize 53 76 V4PRRData).getD 18 [])
  · decide
  · have hTargetSupport : (V4PRRData.getD 18 []).length ≤ 76 := by
      decide
    rw [getD_rectangularize 53 76 V4PRRData 18 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRRRow18_coefficients

private theorem v4PRRRow19_coefficients (j : ℕ) (hj : j < 76) :
    mulCoeffTwo RData V4JData 19 j =
      ((rectangularize 53 76 V4PRRData).getD 19 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRRRow19_spec :
    padOne 76 (mulRow RData V4JData 19) =
      (rectangularize 53 76 V4PRRData).getD 19 [] := by
  apply padOne_mulRow_eq_of_coefficients 76 RData V4JData 19
    ((rectangularize 53 76 V4PRRData).getD 19 [])
  · decide
  · have hTargetSupport : (V4PRRData.getD 19 []).length ≤ 76 := by
      decide
    rw [getD_rectangularize 53 76 V4PRRData 19 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRRRow19_coefficients

private theorem v4PRRRow20_coefficients (j : ℕ) (hj : j < 76) :
    mulCoeffTwo RData V4JData 20 j =
      ((rectangularize 53 76 V4PRRData).getD 20 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRRRow20_spec :
    padOne 76 (mulRow RData V4JData 20) =
      (rectangularize 53 76 V4PRRData).getD 20 [] := by
  apply padOne_mulRow_eq_of_coefficients 76 RData V4JData 20
    ((rectangularize 53 76 V4PRRData).getD 20 [])
  · decide
  · have hTargetSupport : (V4PRRData.getD 20 []).length ≤ 76 := by
      decide
    rw [getD_rectangularize 53 76 V4PRRData 20 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRRRow20_coefficients

private theorem v4PRRRow21_coefficients (j : ℕ) (hj : j < 76) :
    mulCoeffTwo RData V4JData 21 j =
      ((rectangularize 53 76 V4PRRData).getD 21 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRRRow21_spec :
    padOne 76 (mulRow RData V4JData 21) =
      (rectangularize 53 76 V4PRRData).getD 21 [] := by
  apply padOne_mulRow_eq_of_coefficients 76 RData V4JData 21
    ((rectangularize 53 76 V4PRRData).getD 21 [])
  · decide
  · have hTargetSupport : (V4PRRData.getD 21 []).length ≤ 76 := by
      decide
    rw [getD_rectangularize 53 76 V4PRRData 21 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRRRow21_coefficients

private theorem v4PRRRow22_coefficients (j : ℕ) (hj : j < 76) :
    mulCoeffTwo RData V4JData 22 j =
      ((rectangularize 53 76 V4PRRData).getD 22 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRRRow22_spec :
    padOne 76 (mulRow RData V4JData 22) =
      (rectangularize 53 76 V4PRRData).getD 22 [] := by
  apply padOne_mulRow_eq_of_coefficients 76 RData V4JData 22
    ((rectangularize 53 76 V4PRRData).getD 22 [])
  · decide
  · have hTargetSupport : (V4PRRData.getD 22 []).length ≤ 76 := by
      decide
    rw [getD_rectangularize 53 76 V4PRRData 22 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRRRow22_coefficients

private theorem v4PRRRow23_coefficients (j : ℕ) (hj : j < 76) :
    mulCoeffTwo RData V4JData 23 j =
      ((rectangularize 53 76 V4PRRData).getD 23 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRRRow23_spec :
    padOne 76 (mulRow RData V4JData 23) =
      (rectangularize 53 76 V4PRRData).getD 23 [] := by
  apply padOne_mulRow_eq_of_coefficients 76 RData V4JData 23
    ((rectangularize 53 76 V4PRRData).getD 23 [])
  · decide
  · have hTargetSupport : (V4PRRData.getD 23 []).length ≤ 76 := by
      decide
    rw [getD_rectangularize 53 76 V4PRRData 23 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRRRow23_coefficients

private theorem v4PRRRow24_coefficients (j : ℕ) (hj : j < 76) :
    mulCoeffTwo RData V4JData 24 j =
      ((rectangularize 53 76 V4PRRData).getD 24 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRRRow24_spec :
    padOne 76 (mulRow RData V4JData 24) =
      (rectangularize 53 76 V4PRRData).getD 24 [] := by
  apply padOne_mulRow_eq_of_coefficients 76 RData V4JData 24
    ((rectangularize 53 76 V4PRRData).getD 24 [])
  · decide
  · have hTargetSupport : (V4PRRData.getD 24 []).length ≤ 76 := by
      decide
    rw [getD_rectangularize 53 76 V4PRRData 24 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRRRow24_coefficients

private theorem v4PRRRow25_coefficients (j : ℕ) (hj : j < 76) :
    mulCoeffTwo RData V4JData 25 j =
      ((rectangularize 53 76 V4PRRData).getD 25 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRRRow25_spec :
    padOne 76 (mulRow RData V4JData 25) =
      (rectangularize 53 76 V4PRRData).getD 25 [] := by
  apply padOne_mulRow_eq_of_coefficients 76 RData V4JData 25
    ((rectangularize 53 76 V4PRRData).getD 25 [])
  · decide
  · have hTargetSupport : (V4PRRData.getD 25 []).length ≤ 76 := by
      decide
    rw [getD_rectangularize 53 76 V4PRRData 25 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRRRow25_coefficients

private theorem v4PRRRow26_coefficients (j : ℕ) (hj : j < 76) :
    mulCoeffTwo RData V4JData 26 j =
      ((rectangularize 53 76 V4PRRData).getD 26 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRRRow26_spec :
    padOne 76 (mulRow RData V4JData 26) =
      (rectangularize 53 76 V4PRRData).getD 26 [] := by
  apply padOne_mulRow_eq_of_coefficients 76 RData V4JData 26
    ((rectangularize 53 76 V4PRRData).getD 26 [])
  · decide
  · have hTargetSupport : (V4PRRData.getD 26 []).length ≤ 76 := by
      decide
    rw [getD_rectangularize 53 76 V4PRRData 26 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRRRow26_coefficients

private theorem v4PRRRow27_coefficients (j : ℕ) (hj : j < 76) :
    mulCoeffTwo RData V4JData 27 j =
      ((rectangularize 53 76 V4PRRData).getD 27 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRRRow27_spec :
    padOne 76 (mulRow RData V4JData 27) =
      (rectangularize 53 76 V4PRRData).getD 27 [] := by
  apply padOne_mulRow_eq_of_coefficients 76 RData V4JData 27
    ((rectangularize 53 76 V4PRRData).getD 27 [])
  · decide
  · have hTargetSupport : (V4PRRData.getD 27 []).length ≤ 76 := by
      decide
    rw [getD_rectangularize 53 76 V4PRRData 27 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRRRow27_coefficients

private theorem v4PRRRow28_coefficients (j : ℕ) (hj : j < 76) :
    mulCoeffTwo RData V4JData 28 j =
      ((rectangularize 53 76 V4PRRData).getD 28 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRRRow28_spec :
    padOne 76 (mulRow RData V4JData 28) =
      (rectangularize 53 76 V4PRRData).getD 28 [] := by
  apply padOne_mulRow_eq_of_coefficients 76 RData V4JData 28
    ((rectangularize 53 76 V4PRRData).getD 28 [])
  · decide
  · have hTargetSupport : (V4PRRData.getD 28 []).length ≤ 76 := by
      decide
    rw [getD_rectangularize 53 76 V4PRRData 28 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRRRow28_coefficients

private theorem v4PRRRow29_coefficients (j : ℕ) (hj : j < 76) :
    mulCoeffTwo RData V4JData 29 j =
      ((rectangularize 53 76 V4PRRData).getD 29 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRRRow29_spec :
    padOne 76 (mulRow RData V4JData 29) =
      (rectangularize 53 76 V4PRRData).getD 29 [] := by
  apply padOne_mulRow_eq_of_coefficients 76 RData V4JData 29
    ((rectangularize 53 76 V4PRRData).getD 29 [])
  · decide
  · have hTargetSupport : (V4PRRData.getD 29 []).length ≤ 76 := by
      decide
    rw [getD_rectangularize 53 76 V4PRRData 29 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRRRow29_coefficients

private theorem v4PRRRow30_coefficients (j : ℕ) (hj : j < 76) :
    mulCoeffTwo RData V4JData 30 j =
      ((rectangularize 53 76 V4PRRData).getD 30 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRRRow30_spec :
    padOne 76 (mulRow RData V4JData 30) =
      (rectangularize 53 76 V4PRRData).getD 30 [] := by
  apply padOne_mulRow_eq_of_coefficients 76 RData V4JData 30
    ((rectangularize 53 76 V4PRRData).getD 30 [])
  · decide
  · have hTargetSupport : (V4PRRData.getD 30 []).length ≤ 76 := by
      decide
    rw [getD_rectangularize 53 76 V4PRRData 30 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRRRow30_coefficients

private theorem v4PRRRow31_coefficients (j : ℕ) (hj : j < 76) :
    mulCoeffTwo RData V4JData 31 j =
      ((rectangularize 53 76 V4PRRData).getD 31 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRRRow31_spec :
    padOne 76 (mulRow RData V4JData 31) =
      (rectangularize 53 76 V4PRRData).getD 31 [] := by
  apply padOne_mulRow_eq_of_coefficients 76 RData V4JData 31
    ((rectangularize 53 76 V4PRRData).getD 31 [])
  · decide
  · have hTargetSupport : (V4PRRData.getD 31 []).length ≤ 76 := by
      decide
    rw [getD_rectangularize 53 76 V4PRRData 31 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRRRow31_coefficients

private theorem v4PRRRow32_coefficients (j : ℕ) (hj : j < 76) :
    mulCoeffTwo RData V4JData 32 j =
      ((rectangularize 53 76 V4PRRData).getD 32 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRRRow32_spec :
    padOne 76 (mulRow RData V4JData 32) =
      (rectangularize 53 76 V4PRRData).getD 32 [] := by
  apply padOne_mulRow_eq_of_coefficients 76 RData V4JData 32
    ((rectangularize 53 76 V4PRRData).getD 32 [])
  · decide
  · have hTargetSupport : (V4PRRData.getD 32 []).length ≤ 76 := by
      decide
    rw [getD_rectangularize 53 76 V4PRRData 32 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRRRow32_coefficients

private theorem v4PRRRow33_coefficients (j : ℕ) (hj : j < 76) :
    mulCoeffTwo RData V4JData 33 j =
      ((rectangularize 53 76 V4PRRData).getD 33 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRRRow33_spec :
    padOne 76 (mulRow RData V4JData 33) =
      (rectangularize 53 76 V4PRRData).getD 33 [] := by
  apply padOne_mulRow_eq_of_coefficients 76 RData V4JData 33
    ((rectangularize 53 76 V4PRRData).getD 33 [])
  · decide
  · have hTargetSupport : (V4PRRData.getD 33 []).length ≤ 76 := by
      decide
    rw [getD_rectangularize 53 76 V4PRRData 33 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRRRow33_coefficients

private theorem v4PRRRow34_coefficients (j : ℕ) (hj : j < 76) :
    mulCoeffTwo RData V4JData 34 j =
      ((rectangularize 53 76 V4PRRData).getD 34 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRRRow34_spec :
    padOne 76 (mulRow RData V4JData 34) =
      (rectangularize 53 76 V4PRRData).getD 34 [] := by
  apply padOne_mulRow_eq_of_coefficients 76 RData V4JData 34
    ((rectangularize 53 76 V4PRRData).getD 34 [])
  · decide
  · have hTargetSupport : (V4PRRData.getD 34 []).length ≤ 76 := by
      decide
    rw [getD_rectangularize 53 76 V4PRRData 34 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRRRow34_coefficients

private theorem v4PRRRow35_coefficients (j : ℕ) (hj : j < 76) :
    mulCoeffTwo RData V4JData 35 j =
      ((rectangularize 53 76 V4PRRData).getD 35 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRRRow35_spec :
    padOne 76 (mulRow RData V4JData 35) =
      (rectangularize 53 76 V4PRRData).getD 35 [] := by
  apply padOne_mulRow_eq_of_coefficients 76 RData V4JData 35
    ((rectangularize 53 76 V4PRRData).getD 35 [])
  · decide
  · have hTargetSupport : (V4PRRData.getD 35 []).length ≤ 76 := by
      decide
    rw [getD_rectangularize 53 76 V4PRRData 35 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRRRow35_coefficients

private theorem v4PRRRow36_spec :
    padOne 76 (mulRow RData V4JData 36) =
      (rectangularize 53 76 V4PRRData).getD 36 [] := by
  decide

private theorem v4PRRRow37_spec :
    padOne 76 (mulRow RData V4JData 37) =
      (rectangularize 53 76 V4PRRData).getD 37 [] := by
  decide

private theorem v4PRRRow38_spec :
    padOne 76 (mulRow RData V4JData 38) =
      (rectangularize 53 76 V4PRRData).getD 38 [] := by
  decide

private theorem v4PRRRow39_spec :
    padOne 76 (mulRow RData V4JData 39) =
      (rectangularize 53 76 V4PRRData).getD 39 [] := by
  decide

private theorem v4PRRRow40_spec :
    padOne 76 (mulRow RData V4JData 40) =
      (rectangularize 53 76 V4PRRData).getD 40 [] := by
  decide

private theorem v4PRRRow41_spec :
    padOne 76 (mulRow RData V4JData 41) =
      (rectangularize 53 76 V4PRRData).getD 41 [] := by
  decide

private theorem v4PRRRow42_spec :
    padOne 76 (mulRow RData V4JData 42) =
      (rectangularize 53 76 V4PRRData).getD 42 [] := by
  decide

private theorem v4PRRRow43_spec :
    padOne 76 (mulRow RData V4JData 43) =
      (rectangularize 53 76 V4PRRData).getD 43 [] := by
  decide

private theorem v4PRRRow44_spec :
    padOne 76 (mulRow RData V4JData 44) =
      (rectangularize 53 76 V4PRRData).getD 44 [] := by
  decide

private theorem v4PRRRow45_spec :
    padOne 76 (mulRow RData V4JData 45) =
      (rectangularize 53 76 V4PRRData).getD 45 [] := by
  decide

private theorem v4PRRRow46_spec :
    padOne 76 (mulRow RData V4JData 46) =
      (rectangularize 53 76 V4PRRData).getD 46 [] := by
  decide

private theorem v4PRRRow47_spec :
    padOne 76 (mulRow RData V4JData 47) =
      (rectangularize 53 76 V4PRRData).getD 47 [] := by
  decide

private theorem v4PRRRow48_spec :
    padOne 76 (mulRow RData V4JData 48) =
      (rectangularize 53 76 V4PRRData).getD 48 [] := by
  decide

private theorem v4PRRRow49_spec :
    padOne 76 (mulRow RData V4JData 49) =
      (rectangularize 53 76 V4PRRData).getD 49 [] := by
  decide

private theorem v4PRRRow50_spec :
    padOne 76 (mulRow RData V4JData 50) =
      (rectangularize 53 76 V4PRRData).getD 50 [] := by
  decide

private theorem v4PRRRow51_spec :
    padOne 76 (mulRow RData V4JData 51) =
      (rectangularize 53 76 V4PRRData).getD 51 [] := by
  decide

private theorem v4PRRRow52_spec :
    padOne 76 (mulRow RData V4JData 52) =
      (rectangularize 53 76 V4PRRData).getD 52 [] := by
  decide

private theorem v4PRRRows_spec (n : ℕ) (hn : n < 53) :
    padOne 76 (mulRow RData V4JData n) =
      (rectangularize 53 76 V4PRRData).getD n [] := by
  have hCases :
    n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨
    n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨
    n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨
    n = 15 ∨ n = 16 ∨ n = 17 ∨ n = 18 ∨ n = 19 ∨
    n = 20 ∨ n = 21 ∨ n = 22 ∨ n = 23 ∨ n = 24 ∨
    n = 25 ∨ n = 26 ∨ n = 27 ∨ n = 28 ∨ n = 29 ∨
    n = 30 ∨ n = 31 ∨ n = 32 ∨ n = 33 ∨ n = 34 ∨
    n = 35 ∨ n = 36 ∨ n = 37 ∨ n = 38 ∨ n = 39 ∨
    n = 40 ∨ n = 41 ∨ n = 42 ∨ n = 43 ∨ n = 44 ∨
    n = 45 ∨ n = 46 ∨ n = 47 ∨ n = 48 ∨ n = 49 ∨
    n = 50 ∨ n = 51 ∨ n = 52 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · exact v4PRRRow0_spec
  · exact v4PRRRow1_spec
  · exact v4PRRRow2_spec
  · exact v4PRRRow3_spec
  · exact v4PRRRow4_spec
  · exact v4PRRRow5_spec
  · exact v4PRRRow6_spec
  · exact v4PRRRow7_spec
  · exact v4PRRRow8_spec
  · exact v4PRRRow9_spec
  · exact v4PRRRow10_spec
  · exact v4PRRRow11_spec
  · exact v4PRRRow12_spec
  · exact v4PRRRow13_spec
  · exact v4PRRRow14_spec
  · exact v4PRRRow15_spec
  · exact v4PRRRow16_spec
  · exact v4PRRRow17_spec
  · exact v4PRRRow18_spec
  · exact v4PRRRow19_spec
  · exact v4PRRRow20_spec
  · exact v4PRRRow21_spec
  · exact v4PRRRow22_spec
  · exact v4PRRRow23_spec
  · exact v4PRRRow24_spec
  · exact v4PRRRow25_spec
  · exact v4PRRRow26_spec
  · exact v4PRRRow27_spec
  · exact v4PRRRow28_spec
  · exact v4PRRRow29_spec
  · exact v4PRRRow30_spec
  · exact v4PRRRow31_spec
  · exact v4PRRRow32_spec
  · exact v4PRRRow33_spec
  · exact v4PRRRow34_spec
  · exact v4PRRRow35_spec
  · exact v4PRRRow36_spec
  · exact v4PRRRow37_spec
  · exact v4PRRRow38_spec
  · exact v4PRRRow39_spec
  · exact v4PRRRow40_spec
  · exact v4PRRRow41_spec
  · exact v4PRRRow42_spec
  · exact v4PRRRow43_spec
  · exact v4PRRRow44_spec
  · exact v4PRRRow45_spec
  · exact v4PRRRow46_spec
  · exact v4PRRRow47_spec
  · exact v4PRRRow48_spec
  · exact v4PRRRow49_spec
  · exact v4PRRRow50_spec
  · exact v4PRRRow51_spec
  · exact v4PRRRow52_spec

private theorem v4PRRLeft_length :
    (rectangularize 53 76 (Two.mul RData V4JData)).length = 53 := by
  decide

private theorem v4PRRRight_length :
    (rectangularize 53 76 V4PRRData).length = 53 := by
  decide

-- Exact bidegree bound (52, 75); no row or column is discarded.
private theorem v4PRRData_spec :
    rectangularize 53 76 (Two.mul RData V4JData) =
      rectangularize 53 76 V4PRRData := by
  apply List.ext_getElem (v4PRRLeft_length.trans v4PRRRight_length.symm)
  intro n hn _
  rw [List.getElem_eq_getD [], List.getElem_eq_getD []]
  rw [v4PRRLeft_length] at hn
  rw [getD_rectangularize 53 76 (Two.mul RData V4JData) n hn,
    ← mulRow_eq_getD]
  exact v4PRRRows_spec n hn

private theorem v4PRSRow0_spec :
    padOne 77 (mulRow SData V4PRRData 0) =
      (rectangularize 53 77 V4PRSData).getD 0 [] := by
  decide

private theorem v4PRSRow1_spec :
    padOne 77 (mulRow SData V4PRRData 1) =
      (rectangularize 53 77 V4PRSData).getD 1 [] := by
  decide

private theorem v4PRSRow2_spec :
    padOne 77 (mulRow SData V4PRRData 2) =
      (rectangularize 53 77 V4PRSData).getD 2 [] := by
  decide

private theorem v4PRSRow3_spec :
    padOne 77 (mulRow SData V4PRRData 3) =
      (rectangularize 53 77 V4PRSData).getD 3 [] := by
  decide

private theorem v4PRSRow4_spec :
    padOne 77 (mulRow SData V4PRRData 4) =
      (rectangularize 53 77 V4PRSData).getD 4 [] := by
  decide

private theorem v4PRSRow5_spec :
    padOne 77 (mulRow SData V4PRRData 5) =
      (rectangularize 53 77 V4PRSData).getD 5 [] := by
  decide

private theorem v4PRSRow6_spec :
    padOne 77 (mulRow SData V4PRRData 6) =
      (rectangularize 53 77 V4PRSData).getD 6 [] := by
  decide

private theorem v4PRSRow7_spec :
    padOne 77 (mulRow SData V4PRRData 7) =
      (rectangularize 53 77 V4PRSData).getD 7 [] := by
  decide

private theorem v4PRSRow8_spec :
    padOne 77 (mulRow SData V4PRRData 8) =
      (rectangularize 53 77 V4PRSData).getD 8 [] := by
  decide

private theorem v4PRSRow9_spec :
    padOne 77 (mulRow SData V4PRRData 9) =
      (rectangularize 53 77 V4PRSData).getD 9 [] := by
  decide

private theorem v4PRSRow10_spec :
    padOne 77 (mulRow SData V4PRRData 10) =
      (rectangularize 53 77 V4PRSData).getD 10 [] := by
  decide

private theorem v4PRSRow11_spec :
    padOne 77 (mulRow SData V4PRRData 11) =
      (rectangularize 53 77 V4PRSData).getD 11 [] := by
  decide

private theorem v4PRSRow12_spec :
    padOne 77 (mulRow SData V4PRRData 12) =
      (rectangularize 53 77 V4PRSData).getD 12 [] := by
  decide

private theorem v4PRSRow13_spec :
    padOne 77 (mulRow SData V4PRRData 13) =
      (rectangularize 53 77 V4PRSData).getD 13 [] := by
  decide

private theorem v4PRSRow14_spec :
    padOne 77 (mulRow SData V4PRRData 14) =
      (rectangularize 53 77 V4PRSData).getD 14 [] := by
  decide

private theorem v4PRSRow15_spec :
    padOne 77 (mulRow SData V4PRRData 15) =
      (rectangularize 53 77 V4PRSData).getD 15 [] := by
  decide

private theorem v4PRSRow16_spec :
    padOne 77 (mulRow SData V4PRRData 16) =
      (rectangularize 53 77 V4PRSData).getD 16 [] := by
  decide

private theorem v4PRSRow17_coefficients (j : ℕ) (hj : j < 77) :
    mulCoeffTwo SData V4PRRData 17 j =
      ((rectangularize 53 77 V4PRSData).getD 17 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRSRow17_spec :
    padOne 77 (mulRow SData V4PRRData 17) =
      (rectangularize 53 77 V4PRSData).getD 17 [] := by
  apply padOne_mulRow_eq_of_coefficients 77 SData V4PRRData 17
    ((rectangularize 53 77 V4PRSData).getD 17 [])
  · decide
  · have hTargetSupport : (V4PRSData.getD 17 []).length ≤ 77 := by
      decide
    rw [getD_rectangularize 53 77 V4PRSData 17 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRSRow17_coefficients

private theorem v4PRSRow18_coefficients (j : ℕ) (hj : j < 77) :
    mulCoeffTwo SData V4PRRData 18 j =
      ((rectangularize 53 77 V4PRSData).getD 18 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRSRow18_spec :
    padOne 77 (mulRow SData V4PRRData 18) =
      (rectangularize 53 77 V4PRSData).getD 18 [] := by
  apply padOne_mulRow_eq_of_coefficients 77 SData V4PRRData 18
    ((rectangularize 53 77 V4PRSData).getD 18 [])
  · decide
  · have hTargetSupport : (V4PRSData.getD 18 []).length ≤ 77 := by
      decide
    rw [getD_rectangularize 53 77 V4PRSData 18 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRSRow18_coefficients

private theorem v4PRSRow19_coefficients (j : ℕ) (hj : j < 77) :
    mulCoeffTwo SData V4PRRData 19 j =
      ((rectangularize 53 77 V4PRSData).getD 19 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRSRow19_spec :
    padOne 77 (mulRow SData V4PRRData 19) =
      (rectangularize 53 77 V4PRSData).getD 19 [] := by
  apply padOne_mulRow_eq_of_coefficients 77 SData V4PRRData 19
    ((rectangularize 53 77 V4PRSData).getD 19 [])
  · decide
  · have hTargetSupport : (V4PRSData.getD 19 []).length ≤ 77 := by
      decide
    rw [getD_rectangularize 53 77 V4PRSData 19 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRSRow19_coefficients

private theorem v4PRSRow20_coefficients (j : ℕ) (hj : j < 77) :
    mulCoeffTwo SData V4PRRData 20 j =
      ((rectangularize 53 77 V4PRSData).getD 20 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRSRow20_spec :
    padOne 77 (mulRow SData V4PRRData 20) =
      (rectangularize 53 77 V4PRSData).getD 20 [] := by
  apply padOne_mulRow_eq_of_coefficients 77 SData V4PRRData 20
    ((rectangularize 53 77 V4PRSData).getD 20 [])
  · decide
  · have hTargetSupport : (V4PRSData.getD 20 []).length ≤ 77 := by
      decide
    rw [getD_rectangularize 53 77 V4PRSData 20 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRSRow20_coefficients

private theorem v4PRSRow21_coefficients (j : ℕ) (hj : j < 77) :
    mulCoeffTwo SData V4PRRData 21 j =
      ((rectangularize 53 77 V4PRSData).getD 21 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRSRow21_spec :
    padOne 77 (mulRow SData V4PRRData 21) =
      (rectangularize 53 77 V4PRSData).getD 21 [] := by
  apply padOne_mulRow_eq_of_coefficients 77 SData V4PRRData 21
    ((rectangularize 53 77 V4PRSData).getD 21 [])
  · decide
  · have hTargetSupport : (V4PRSData.getD 21 []).length ≤ 77 := by
      decide
    rw [getD_rectangularize 53 77 V4PRSData 21 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRSRow21_coefficients

private theorem v4PRSRow22_coefficients (j : ℕ) (hj : j < 77) :
    mulCoeffTwo SData V4PRRData 22 j =
      ((rectangularize 53 77 V4PRSData).getD 22 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRSRow22_spec :
    padOne 77 (mulRow SData V4PRRData 22) =
      (rectangularize 53 77 V4PRSData).getD 22 [] := by
  apply padOne_mulRow_eq_of_coefficients 77 SData V4PRRData 22
    ((rectangularize 53 77 V4PRSData).getD 22 [])
  · decide
  · have hTargetSupport : (V4PRSData.getD 22 []).length ≤ 77 := by
      decide
    rw [getD_rectangularize 53 77 V4PRSData 22 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRSRow22_coefficients

private theorem v4PRSRow23_coefficients (j : ℕ) (hj : j < 77) :
    mulCoeffTwo SData V4PRRData 23 j =
      ((rectangularize 53 77 V4PRSData).getD 23 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRSRow23_spec :
    padOne 77 (mulRow SData V4PRRData 23) =
      (rectangularize 53 77 V4PRSData).getD 23 [] := by
  apply padOne_mulRow_eq_of_coefficients 77 SData V4PRRData 23
    ((rectangularize 53 77 V4PRSData).getD 23 [])
  · decide
  · have hTargetSupport : (V4PRSData.getD 23 []).length ≤ 77 := by
      decide
    rw [getD_rectangularize 53 77 V4PRSData 23 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRSRow23_coefficients

private theorem v4PRSRow24_coefficients (j : ℕ) (hj : j < 77) :
    mulCoeffTwo SData V4PRRData 24 j =
      ((rectangularize 53 77 V4PRSData).getD 24 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRSRow24_spec :
    padOne 77 (mulRow SData V4PRRData 24) =
      (rectangularize 53 77 V4PRSData).getD 24 [] := by
  apply padOne_mulRow_eq_of_coefficients 77 SData V4PRRData 24
    ((rectangularize 53 77 V4PRSData).getD 24 [])
  · decide
  · have hTargetSupport : (V4PRSData.getD 24 []).length ≤ 77 := by
      decide
    rw [getD_rectangularize 53 77 V4PRSData 24 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRSRow24_coefficients

private theorem v4PRSRow25_coefficients (j : ℕ) (hj : j < 77) :
    mulCoeffTwo SData V4PRRData 25 j =
      ((rectangularize 53 77 V4PRSData).getD 25 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRSRow25_spec :
    padOne 77 (mulRow SData V4PRRData 25) =
      (rectangularize 53 77 V4PRSData).getD 25 [] := by
  apply padOne_mulRow_eq_of_coefficients 77 SData V4PRRData 25
    ((rectangularize 53 77 V4PRSData).getD 25 [])
  · decide
  · have hTargetSupport : (V4PRSData.getD 25 []).length ≤ 77 := by
      decide
    rw [getD_rectangularize 53 77 V4PRSData 25 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRSRow25_coefficients

private theorem v4PRSRow26_coefficients (j : ℕ) (hj : j < 77) :
    mulCoeffTwo SData V4PRRData 26 j =
      ((rectangularize 53 77 V4PRSData).getD 26 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRSRow26_spec :
    padOne 77 (mulRow SData V4PRRData 26) =
      (rectangularize 53 77 V4PRSData).getD 26 [] := by
  apply padOne_mulRow_eq_of_coefficients 77 SData V4PRRData 26
    ((rectangularize 53 77 V4PRSData).getD 26 [])
  · decide
  · have hTargetSupport : (V4PRSData.getD 26 []).length ≤ 77 := by
      decide
    rw [getD_rectangularize 53 77 V4PRSData 26 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRSRow26_coefficients

private theorem v4PRSRow27_coefficients (j : ℕ) (hj : j < 77) :
    mulCoeffTwo SData V4PRRData 27 j =
      ((rectangularize 53 77 V4PRSData).getD 27 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRSRow27_spec :
    padOne 77 (mulRow SData V4PRRData 27) =
      (rectangularize 53 77 V4PRSData).getD 27 [] := by
  apply padOne_mulRow_eq_of_coefficients 77 SData V4PRRData 27
    ((rectangularize 53 77 V4PRSData).getD 27 [])
  · decide
  · have hTargetSupport : (V4PRSData.getD 27 []).length ≤ 77 := by
      decide
    rw [getD_rectangularize 53 77 V4PRSData 27 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRSRow27_coefficients

private theorem v4PRSRow28_coefficients (j : ℕ) (hj : j < 77) :
    mulCoeffTwo SData V4PRRData 28 j =
      ((rectangularize 53 77 V4PRSData).getD 28 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRSRow28_spec :
    padOne 77 (mulRow SData V4PRRData 28) =
      (rectangularize 53 77 V4PRSData).getD 28 [] := by
  apply padOne_mulRow_eq_of_coefficients 77 SData V4PRRData 28
    ((rectangularize 53 77 V4PRSData).getD 28 [])
  · decide
  · have hTargetSupport : (V4PRSData.getD 28 []).length ≤ 77 := by
      decide
    rw [getD_rectangularize 53 77 V4PRSData 28 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRSRow28_coefficients

private theorem v4PRSRow29_coefficients (j : ℕ) (hj : j < 77) :
    mulCoeffTwo SData V4PRRData 29 j =
      ((rectangularize 53 77 V4PRSData).getD 29 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRSRow29_spec :
    padOne 77 (mulRow SData V4PRRData 29) =
      (rectangularize 53 77 V4PRSData).getD 29 [] := by
  apply padOne_mulRow_eq_of_coefficients 77 SData V4PRRData 29
    ((rectangularize 53 77 V4PRSData).getD 29 [])
  · decide
  · have hTargetSupport : (V4PRSData.getD 29 []).length ≤ 77 := by
      decide
    rw [getD_rectangularize 53 77 V4PRSData 29 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRSRow29_coefficients

private theorem v4PRSRow30_coefficients (j : ℕ) (hj : j < 77) :
    mulCoeffTwo SData V4PRRData 30 j =
      ((rectangularize 53 77 V4PRSData).getD 30 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRSRow30_spec :
    padOne 77 (mulRow SData V4PRRData 30) =
      (rectangularize 53 77 V4PRSData).getD 30 [] := by
  apply padOne_mulRow_eq_of_coefficients 77 SData V4PRRData 30
    ((rectangularize 53 77 V4PRSData).getD 30 [])
  · decide
  · have hTargetSupport : (V4PRSData.getD 30 []).length ≤ 77 := by
      decide
    rw [getD_rectangularize 53 77 V4PRSData 30 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRSRow30_coefficients

private theorem v4PRSRow31_coefficients (j : ℕ) (hj : j < 77) :
    mulCoeffTwo SData V4PRRData 31 j =
      ((rectangularize 53 77 V4PRSData).getD 31 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRSRow31_spec :
    padOne 77 (mulRow SData V4PRRData 31) =
      (rectangularize 53 77 V4PRSData).getD 31 [] := by
  apply padOne_mulRow_eq_of_coefficients 77 SData V4PRRData 31
    ((rectangularize 53 77 V4PRSData).getD 31 [])
  · decide
  · have hTargetSupport : (V4PRSData.getD 31 []).length ≤ 77 := by
      decide
    rw [getD_rectangularize 53 77 V4PRSData 31 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRSRow31_coefficients

private theorem v4PRSRow32_coefficients (j : ℕ) (hj : j < 77) :
    mulCoeffTwo SData V4PRRData 32 j =
      ((rectangularize 53 77 V4PRSData).getD 32 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRSRow32_spec :
    padOne 77 (mulRow SData V4PRRData 32) =
      (rectangularize 53 77 V4PRSData).getD 32 [] := by
  apply padOne_mulRow_eq_of_coefficients 77 SData V4PRRData 32
    ((rectangularize 53 77 V4PRSData).getD 32 [])
  · decide
  · have hTargetSupport : (V4PRSData.getD 32 []).length ≤ 77 := by
      decide
    rw [getD_rectangularize 53 77 V4PRSData 32 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRSRow32_coefficients

private theorem v4PRSRow33_coefficients (j : ℕ) (hj : j < 77) :
    mulCoeffTwo SData V4PRRData 33 j =
      ((rectangularize 53 77 V4PRSData).getD 33 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRSRow33_spec :
    padOne 77 (mulRow SData V4PRRData 33) =
      (rectangularize 53 77 V4PRSData).getD 33 [] := by
  apply padOne_mulRow_eq_of_coefficients 77 SData V4PRRData 33
    ((rectangularize 53 77 V4PRSData).getD 33 [])
  · decide
  · have hTargetSupport : (V4PRSData.getD 33 []).length ≤ 77 := by
      decide
    rw [getD_rectangularize 53 77 V4PRSData 33 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRSRow33_coefficients

private theorem v4PRSRow34_coefficients (j : ℕ) (hj : j < 77) :
    mulCoeffTwo SData V4PRRData 34 j =
      ((rectangularize 53 77 V4PRSData).getD 34 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRSRow34_spec :
    padOne 77 (mulRow SData V4PRRData 34) =
      (rectangularize 53 77 V4PRSData).getD 34 [] := by
  apply padOne_mulRow_eq_of_coefficients 77 SData V4PRRData 34
    ((rectangularize 53 77 V4PRSData).getD 34 [])
  · decide
  · have hTargetSupport : (V4PRSData.getD 34 []).length ≤ 77 := by
      decide
    rw [getD_rectangularize 53 77 V4PRSData 34 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRSRow34_coefficients

private theorem v4PRSRow35_coefficients (j : ℕ) (hj : j < 77) :
    mulCoeffTwo SData V4PRRData 35 j =
      ((rectangularize 53 77 V4PRSData).getD 35 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRSRow35_spec :
    padOne 77 (mulRow SData V4PRRData 35) =
      (rectangularize 53 77 V4PRSData).getD 35 [] := by
  apply padOne_mulRow_eq_of_coefficients 77 SData V4PRRData 35
    ((rectangularize 53 77 V4PRSData).getD 35 [])
  · decide
  · have hTargetSupport : (V4PRSData.getD 35 []).length ≤ 77 := by
      decide
    rw [getD_rectangularize 53 77 V4PRSData 35 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRSRow35_coefficients

private theorem v4PRSRow36_coefficients (j : ℕ) (hj : j < 77) :
    mulCoeffTwo SData V4PRRData 36 j =
      ((rectangularize 53 77 V4PRSData).getD 36 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRSRow36_spec :
    padOne 77 (mulRow SData V4PRRData 36) =
      (rectangularize 53 77 V4PRSData).getD 36 [] := by
  apply padOne_mulRow_eq_of_coefficients 77 SData V4PRRData 36
    ((rectangularize 53 77 V4PRSData).getD 36 [])
  · decide
  · have hTargetSupport : (V4PRSData.getD 36 []).length ≤ 77 := by
      decide
    rw [getD_rectangularize 53 77 V4PRSData 36 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRSRow36_coefficients

private theorem v4PRSRow37_spec :
    padOne 77 (mulRow SData V4PRRData 37) =
      (rectangularize 53 77 V4PRSData).getD 37 [] := by
  decide

private theorem v4PRSRow38_spec :
    padOne 77 (mulRow SData V4PRRData 38) =
      (rectangularize 53 77 V4PRSData).getD 38 [] := by
  decide

private theorem v4PRSRow39_spec :
    padOne 77 (mulRow SData V4PRRData 39) =
      (rectangularize 53 77 V4PRSData).getD 39 [] := by
  decide

private theorem v4PRSRow40_spec :
    padOne 77 (mulRow SData V4PRRData 40) =
      (rectangularize 53 77 V4PRSData).getD 40 [] := by
  decide

private theorem v4PRSRow41_spec :
    padOne 77 (mulRow SData V4PRRData 41) =
      (rectangularize 53 77 V4PRSData).getD 41 [] := by
  decide

private theorem v4PRSRow42_spec :
    padOne 77 (mulRow SData V4PRRData 42) =
      (rectangularize 53 77 V4PRSData).getD 42 [] := by
  decide

private theorem v4PRSRow43_spec :
    padOne 77 (mulRow SData V4PRRData 43) =
      (rectangularize 53 77 V4PRSData).getD 43 [] := by
  decide

private theorem v4PRSRow44_spec :
    padOne 77 (mulRow SData V4PRRData 44) =
      (rectangularize 53 77 V4PRSData).getD 44 [] := by
  decide

private theorem v4PRSRow45_spec :
    padOne 77 (mulRow SData V4PRRData 45) =
      (rectangularize 53 77 V4PRSData).getD 45 [] := by
  decide

private theorem v4PRSRow46_spec :
    padOne 77 (mulRow SData V4PRRData 46) =
      (rectangularize 53 77 V4PRSData).getD 46 [] := by
  decide

private theorem v4PRSRow47_spec :
    padOne 77 (mulRow SData V4PRRData 47) =
      (rectangularize 53 77 V4PRSData).getD 47 [] := by
  decide

private theorem v4PRSRow48_spec :
    padOne 77 (mulRow SData V4PRRData 48) =
      (rectangularize 53 77 V4PRSData).getD 48 [] := by
  decide

private theorem v4PRSRow49_spec :
    padOne 77 (mulRow SData V4PRRData 49) =
      (rectangularize 53 77 V4PRSData).getD 49 [] := by
  decide

private theorem v4PRSRow50_spec :
    padOne 77 (mulRow SData V4PRRData 50) =
      (rectangularize 53 77 V4PRSData).getD 50 [] := by
  decide

private theorem v4PRSRow51_spec :
    padOne 77 (mulRow SData V4PRRData 51) =
      (rectangularize 53 77 V4PRSData).getD 51 [] := by
  decide

private theorem v4PRSRow52_spec :
    padOne 77 (mulRow SData V4PRRData 52) =
      (rectangularize 53 77 V4PRSData).getD 52 [] := by
  decide

private theorem v4PRSRows_spec (n : ℕ) (hn : n < 53) :
    padOne 77 (mulRow SData V4PRRData n) =
      (rectangularize 53 77 V4PRSData).getD n [] := by
  have hCases :
    n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨
    n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨
    n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨
    n = 15 ∨ n = 16 ∨ n = 17 ∨ n = 18 ∨ n = 19 ∨
    n = 20 ∨ n = 21 ∨ n = 22 ∨ n = 23 ∨ n = 24 ∨
    n = 25 ∨ n = 26 ∨ n = 27 ∨ n = 28 ∨ n = 29 ∨
    n = 30 ∨ n = 31 ∨ n = 32 ∨ n = 33 ∨ n = 34 ∨
    n = 35 ∨ n = 36 ∨ n = 37 ∨ n = 38 ∨ n = 39 ∨
    n = 40 ∨ n = 41 ∨ n = 42 ∨ n = 43 ∨ n = 44 ∨
    n = 45 ∨ n = 46 ∨ n = 47 ∨ n = 48 ∨ n = 49 ∨
    n = 50 ∨ n = 51 ∨ n = 52 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · exact v4PRSRow0_spec
  · exact v4PRSRow1_spec
  · exact v4PRSRow2_spec
  · exact v4PRSRow3_spec
  · exact v4PRSRow4_spec
  · exact v4PRSRow5_spec
  · exact v4PRSRow6_spec
  · exact v4PRSRow7_spec
  · exact v4PRSRow8_spec
  · exact v4PRSRow9_spec
  · exact v4PRSRow10_spec
  · exact v4PRSRow11_spec
  · exact v4PRSRow12_spec
  · exact v4PRSRow13_spec
  · exact v4PRSRow14_spec
  · exact v4PRSRow15_spec
  · exact v4PRSRow16_spec
  · exact v4PRSRow17_spec
  · exact v4PRSRow18_spec
  · exact v4PRSRow19_spec
  · exact v4PRSRow20_spec
  · exact v4PRSRow21_spec
  · exact v4PRSRow22_spec
  · exact v4PRSRow23_spec
  · exact v4PRSRow24_spec
  · exact v4PRSRow25_spec
  · exact v4PRSRow26_spec
  · exact v4PRSRow27_spec
  · exact v4PRSRow28_spec
  · exact v4PRSRow29_spec
  · exact v4PRSRow30_spec
  · exact v4PRSRow31_spec
  · exact v4PRSRow32_spec
  · exact v4PRSRow33_spec
  · exact v4PRSRow34_spec
  · exact v4PRSRow35_spec
  · exact v4PRSRow36_spec
  · exact v4PRSRow37_spec
  · exact v4PRSRow38_spec
  · exact v4PRSRow39_spec
  · exact v4PRSRow40_spec
  · exact v4PRSRow41_spec
  · exact v4PRSRow42_spec
  · exact v4PRSRow43_spec
  · exact v4PRSRow44_spec
  · exact v4PRSRow45_spec
  · exact v4PRSRow46_spec
  · exact v4PRSRow47_spec
  · exact v4PRSRow48_spec
  · exact v4PRSRow49_spec
  · exact v4PRSRow50_spec
  · exact v4PRSRow51_spec
  · exact v4PRSRow52_spec

private theorem v4PRSLeft_length :
    (rectangularize 53 77 (Two.mul SData V4PRRData)).length = 53 := by
  decide

private theorem v4PRSRight_length :
    (rectangularize 53 77 V4PRSData).length = 53 := by
  decide

-- Exact bidegree bound (52, 76); no row or column is discarded.
private theorem v4PRSData_spec :
    rectangularize 53 77 (Two.mul SData V4PRRData) =
      rectangularize 53 77 V4PRSData := by
  apply List.ext_getElem (v4PRSLeft_length.trans v4PRSRight_length.symm)
  intro n hn _
  rw [List.getElem_eq_getD [], List.getElem_eq_getD []]
  rw [v4PRSLeft_length] at hn
  rw [getD_rectangularize 53 77 (Two.mul SData V4PRRData) n hn,
    ← mulRow_eq_getD]
  exact v4PRSRows_spec n hn

private theorem v4PRB1Row0_spec :
    padOne 78 (mulRow BData V4PRSData 0) =
      (rectangularize 53 78 V4PRB1Data).getD 0 [] := by
  decide

private theorem v4PRB1Row1_spec :
    padOne 78 (mulRow BData V4PRSData 1) =
      (rectangularize 53 78 V4PRB1Data).getD 1 [] := by
  decide

private theorem v4PRB1Row2_spec :
    padOne 78 (mulRow BData V4PRSData 2) =
      (rectangularize 53 78 V4PRB1Data).getD 2 [] := by
  decide

private theorem v4PRB1Row3_spec :
    padOne 78 (mulRow BData V4PRSData 3) =
      (rectangularize 53 78 V4PRB1Data).getD 3 [] := by
  decide

private theorem v4PRB1Row4_spec :
    padOne 78 (mulRow BData V4PRSData 4) =
      (rectangularize 53 78 V4PRB1Data).getD 4 [] := by
  decide

private theorem v4PRB1Row5_spec :
    padOne 78 (mulRow BData V4PRSData 5) =
      (rectangularize 53 78 V4PRB1Data).getD 5 [] := by
  decide

private theorem v4PRB1Row6_spec :
    padOne 78 (mulRow BData V4PRSData 6) =
      (rectangularize 53 78 V4PRB1Data).getD 6 [] := by
  decide

private theorem v4PRB1Row7_spec :
    padOne 78 (mulRow BData V4PRSData 7) =
      (rectangularize 53 78 V4PRB1Data).getD 7 [] := by
  decide

private theorem v4PRB1Row8_spec :
    padOne 78 (mulRow BData V4PRSData 8) =
      (rectangularize 53 78 V4PRB1Data).getD 8 [] := by
  decide

private theorem v4PRB1Row9_spec :
    padOne 78 (mulRow BData V4PRSData 9) =
      (rectangularize 53 78 V4PRB1Data).getD 9 [] := by
  decide

private theorem v4PRB1Row10_spec :
    padOne 78 (mulRow BData V4PRSData 10) =
      (rectangularize 53 78 V4PRB1Data).getD 10 [] := by
  decide

private theorem v4PRB1Row11_spec :
    padOne 78 (mulRow BData V4PRSData 11) =
      (rectangularize 53 78 V4PRB1Data).getD 11 [] := by
  decide

private theorem v4PRB1Row12_spec :
    padOne 78 (mulRow BData V4PRSData 12) =
      (rectangularize 53 78 V4PRB1Data).getD 12 [] := by
  decide

private theorem v4PRB1Row13_spec :
    padOne 78 (mulRow BData V4PRSData 13) =
      (rectangularize 53 78 V4PRB1Data).getD 13 [] := by
  decide

private theorem v4PRB1Row14_spec :
    padOne 78 (mulRow BData V4PRSData 14) =
      (rectangularize 53 78 V4PRB1Data).getD 14 [] := by
  decide

private theorem v4PRB1Row15_spec :
    padOne 78 (mulRow BData V4PRSData 15) =
      (rectangularize 53 78 V4PRB1Data).getD 15 [] := by
  decide

private theorem v4PRB1Row16_coefficients (j : ℕ) (hj : j < 78) :
    mulCoeffTwo BData V4PRSData 16 j =
      ((rectangularize 53 78 V4PRB1Data).getD 16 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB1Row16_spec :
    padOne 78 (mulRow BData V4PRSData 16) =
      (rectangularize 53 78 V4PRB1Data).getD 16 [] := by
  apply padOne_mulRow_eq_of_coefficients 78 BData V4PRSData 16
    ((rectangularize 53 78 V4PRB1Data).getD 16 [])
  · decide
  · have hTargetSupport : (V4PRB1Data.getD 16 []).length ≤ 78 := by
      decide
    rw [getD_rectangularize 53 78 V4PRB1Data 16 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB1Row16_coefficients

private theorem v4PRB1Row17_coefficients (j : ℕ) (hj : j < 78) :
    mulCoeffTwo BData V4PRSData 17 j =
      ((rectangularize 53 78 V4PRB1Data).getD 17 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB1Row17_spec :
    padOne 78 (mulRow BData V4PRSData 17) =
      (rectangularize 53 78 V4PRB1Data).getD 17 [] := by
  apply padOne_mulRow_eq_of_coefficients 78 BData V4PRSData 17
    ((rectangularize 53 78 V4PRB1Data).getD 17 [])
  · decide
  · have hTargetSupport : (V4PRB1Data.getD 17 []).length ≤ 78 := by
      decide
    rw [getD_rectangularize 53 78 V4PRB1Data 17 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB1Row17_coefficients

private theorem v4PRB1Row18_coefficients (j : ℕ) (hj : j < 78) :
    mulCoeffTwo BData V4PRSData 18 j =
      ((rectangularize 53 78 V4PRB1Data).getD 18 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB1Row18_spec :
    padOne 78 (mulRow BData V4PRSData 18) =
      (rectangularize 53 78 V4PRB1Data).getD 18 [] := by
  apply padOne_mulRow_eq_of_coefficients 78 BData V4PRSData 18
    ((rectangularize 53 78 V4PRB1Data).getD 18 [])
  · decide
  · have hTargetSupport : (V4PRB1Data.getD 18 []).length ≤ 78 := by
      decide
    rw [getD_rectangularize 53 78 V4PRB1Data 18 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB1Row18_coefficients

private theorem v4PRB1Row19_coefficients (j : ℕ) (hj : j < 78) :
    mulCoeffTwo BData V4PRSData 19 j =
      ((rectangularize 53 78 V4PRB1Data).getD 19 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB1Row19_spec :
    padOne 78 (mulRow BData V4PRSData 19) =
      (rectangularize 53 78 V4PRB1Data).getD 19 [] := by
  apply padOne_mulRow_eq_of_coefficients 78 BData V4PRSData 19
    ((rectangularize 53 78 V4PRB1Data).getD 19 [])
  · decide
  · have hTargetSupport : (V4PRB1Data.getD 19 []).length ≤ 78 := by
      decide
    rw [getD_rectangularize 53 78 V4PRB1Data 19 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB1Row19_coefficients

private theorem v4PRB1Row20_coefficients (j : ℕ) (hj : j < 78) :
    mulCoeffTwo BData V4PRSData 20 j =
      ((rectangularize 53 78 V4PRB1Data).getD 20 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB1Row20_spec :
    padOne 78 (mulRow BData V4PRSData 20) =
      (rectangularize 53 78 V4PRB1Data).getD 20 [] := by
  apply padOne_mulRow_eq_of_coefficients 78 BData V4PRSData 20
    ((rectangularize 53 78 V4PRB1Data).getD 20 [])
  · decide
  · have hTargetSupport : (V4PRB1Data.getD 20 []).length ≤ 78 := by
      decide
    rw [getD_rectangularize 53 78 V4PRB1Data 20 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB1Row20_coefficients

private theorem v4PRB1Row21_coefficients (j : ℕ) (hj : j < 78) :
    mulCoeffTwo BData V4PRSData 21 j =
      ((rectangularize 53 78 V4PRB1Data).getD 21 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB1Row21_spec :
    padOne 78 (mulRow BData V4PRSData 21) =
      (rectangularize 53 78 V4PRB1Data).getD 21 [] := by
  apply padOne_mulRow_eq_of_coefficients 78 BData V4PRSData 21
    ((rectangularize 53 78 V4PRB1Data).getD 21 [])
  · decide
  · have hTargetSupport : (V4PRB1Data.getD 21 []).length ≤ 78 := by
      decide
    rw [getD_rectangularize 53 78 V4PRB1Data 21 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB1Row21_coefficients

private theorem v4PRB1Row22_coefficients (j : ℕ) (hj : j < 78) :
    mulCoeffTwo BData V4PRSData 22 j =
      ((rectangularize 53 78 V4PRB1Data).getD 22 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB1Row22_spec :
    padOne 78 (mulRow BData V4PRSData 22) =
      (rectangularize 53 78 V4PRB1Data).getD 22 [] := by
  apply padOne_mulRow_eq_of_coefficients 78 BData V4PRSData 22
    ((rectangularize 53 78 V4PRB1Data).getD 22 [])
  · decide
  · have hTargetSupport : (V4PRB1Data.getD 22 []).length ≤ 78 := by
      decide
    rw [getD_rectangularize 53 78 V4PRB1Data 22 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB1Row22_coefficients

private theorem v4PRB1Row23_coefficients (j : ℕ) (hj : j < 78) :
    mulCoeffTwo BData V4PRSData 23 j =
      ((rectangularize 53 78 V4PRB1Data).getD 23 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB1Row23_spec :
    padOne 78 (mulRow BData V4PRSData 23) =
      (rectangularize 53 78 V4PRB1Data).getD 23 [] := by
  apply padOne_mulRow_eq_of_coefficients 78 BData V4PRSData 23
    ((rectangularize 53 78 V4PRB1Data).getD 23 [])
  · decide
  · have hTargetSupport : (V4PRB1Data.getD 23 []).length ≤ 78 := by
      decide
    rw [getD_rectangularize 53 78 V4PRB1Data 23 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB1Row23_coefficients

private theorem v4PRB1Row24_coefficients (j : ℕ) (hj : j < 78) :
    mulCoeffTwo BData V4PRSData 24 j =
      ((rectangularize 53 78 V4PRB1Data).getD 24 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB1Row24_spec :
    padOne 78 (mulRow BData V4PRSData 24) =
      (rectangularize 53 78 V4PRB1Data).getD 24 [] := by
  apply padOne_mulRow_eq_of_coefficients 78 BData V4PRSData 24
    ((rectangularize 53 78 V4PRB1Data).getD 24 [])
  · decide
  · have hTargetSupport : (V4PRB1Data.getD 24 []).length ≤ 78 := by
      decide
    rw [getD_rectangularize 53 78 V4PRB1Data 24 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB1Row24_coefficients

private theorem v4PRB1Row25_coefficients (j : ℕ) (hj : j < 78) :
    mulCoeffTwo BData V4PRSData 25 j =
      ((rectangularize 53 78 V4PRB1Data).getD 25 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB1Row25_spec :
    padOne 78 (mulRow BData V4PRSData 25) =
      (rectangularize 53 78 V4PRB1Data).getD 25 [] := by
  apply padOne_mulRow_eq_of_coefficients 78 BData V4PRSData 25
    ((rectangularize 53 78 V4PRB1Data).getD 25 [])
  · decide
  · have hTargetSupport : (V4PRB1Data.getD 25 []).length ≤ 78 := by
      decide
    rw [getD_rectangularize 53 78 V4PRB1Data 25 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB1Row25_coefficients

private theorem v4PRB1Row26_coefficients (j : ℕ) (hj : j < 78) :
    mulCoeffTwo BData V4PRSData 26 j =
      ((rectangularize 53 78 V4PRB1Data).getD 26 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB1Row26_spec :
    padOne 78 (mulRow BData V4PRSData 26) =
      (rectangularize 53 78 V4PRB1Data).getD 26 [] := by
  apply padOne_mulRow_eq_of_coefficients 78 BData V4PRSData 26
    ((rectangularize 53 78 V4PRB1Data).getD 26 [])
  · decide
  · have hTargetSupport : (V4PRB1Data.getD 26 []).length ≤ 78 := by
      decide
    rw [getD_rectangularize 53 78 V4PRB1Data 26 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB1Row26_coefficients

private theorem v4PRB1Row27_coefficients (j : ℕ) (hj : j < 78) :
    mulCoeffTwo BData V4PRSData 27 j =
      ((rectangularize 53 78 V4PRB1Data).getD 27 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB1Row27_spec :
    padOne 78 (mulRow BData V4PRSData 27) =
      (rectangularize 53 78 V4PRB1Data).getD 27 [] := by
  apply padOne_mulRow_eq_of_coefficients 78 BData V4PRSData 27
    ((rectangularize 53 78 V4PRB1Data).getD 27 [])
  · decide
  · have hTargetSupport : (V4PRB1Data.getD 27 []).length ≤ 78 := by
      decide
    rw [getD_rectangularize 53 78 V4PRB1Data 27 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB1Row27_coefficients

private theorem v4PRB1Row28_coefficients (j : ℕ) (hj : j < 78) :
    mulCoeffTwo BData V4PRSData 28 j =
      ((rectangularize 53 78 V4PRB1Data).getD 28 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB1Row28_spec :
    padOne 78 (mulRow BData V4PRSData 28) =
      (rectangularize 53 78 V4PRB1Data).getD 28 [] := by
  apply padOne_mulRow_eq_of_coefficients 78 BData V4PRSData 28
    ((rectangularize 53 78 V4PRB1Data).getD 28 [])
  · decide
  · have hTargetSupport : (V4PRB1Data.getD 28 []).length ≤ 78 := by
      decide
    rw [getD_rectangularize 53 78 V4PRB1Data 28 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB1Row28_coefficients

private theorem v4PRB1Row29_coefficients (j : ℕ) (hj : j < 78) :
    mulCoeffTwo BData V4PRSData 29 j =
      ((rectangularize 53 78 V4PRB1Data).getD 29 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB1Row29_spec :
    padOne 78 (mulRow BData V4PRSData 29) =
      (rectangularize 53 78 V4PRB1Data).getD 29 [] := by
  apply padOne_mulRow_eq_of_coefficients 78 BData V4PRSData 29
    ((rectangularize 53 78 V4PRB1Data).getD 29 [])
  · decide
  · have hTargetSupport : (V4PRB1Data.getD 29 []).length ≤ 78 := by
      decide
    rw [getD_rectangularize 53 78 V4PRB1Data 29 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB1Row29_coefficients

private theorem v4PRB1Row30_coefficients (j : ℕ) (hj : j < 78) :
    mulCoeffTwo BData V4PRSData 30 j =
      ((rectangularize 53 78 V4PRB1Data).getD 30 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB1Row30_spec :
    padOne 78 (mulRow BData V4PRSData 30) =
      (rectangularize 53 78 V4PRB1Data).getD 30 [] := by
  apply padOne_mulRow_eq_of_coefficients 78 BData V4PRSData 30
    ((rectangularize 53 78 V4PRB1Data).getD 30 [])
  · decide
  · have hTargetSupport : (V4PRB1Data.getD 30 []).length ≤ 78 := by
      decide
    rw [getD_rectangularize 53 78 V4PRB1Data 30 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB1Row30_coefficients

private theorem v4PRB1Row31_coefficients (j : ℕ) (hj : j < 78) :
    mulCoeffTwo BData V4PRSData 31 j =
      ((rectangularize 53 78 V4PRB1Data).getD 31 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB1Row31_spec :
    padOne 78 (mulRow BData V4PRSData 31) =
      (rectangularize 53 78 V4PRB1Data).getD 31 [] := by
  apply padOne_mulRow_eq_of_coefficients 78 BData V4PRSData 31
    ((rectangularize 53 78 V4PRB1Data).getD 31 [])
  · decide
  · have hTargetSupport : (V4PRB1Data.getD 31 []).length ≤ 78 := by
      decide
    rw [getD_rectangularize 53 78 V4PRB1Data 31 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB1Row31_coefficients

private theorem v4PRB1Row32_coefficients (j : ℕ) (hj : j < 78) :
    mulCoeffTwo BData V4PRSData 32 j =
      ((rectangularize 53 78 V4PRB1Data).getD 32 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB1Row32_spec :
    padOne 78 (mulRow BData V4PRSData 32) =
      (rectangularize 53 78 V4PRB1Data).getD 32 [] := by
  apply padOne_mulRow_eq_of_coefficients 78 BData V4PRSData 32
    ((rectangularize 53 78 V4PRB1Data).getD 32 [])
  · decide
  · have hTargetSupport : (V4PRB1Data.getD 32 []).length ≤ 78 := by
      decide
    rw [getD_rectangularize 53 78 V4PRB1Data 32 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB1Row32_coefficients

private theorem v4PRB1Row33_coefficients (j : ℕ) (hj : j < 78) :
    mulCoeffTwo BData V4PRSData 33 j =
      ((rectangularize 53 78 V4PRB1Data).getD 33 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB1Row33_spec :
    padOne 78 (mulRow BData V4PRSData 33) =
      (rectangularize 53 78 V4PRB1Data).getD 33 [] := by
  apply padOne_mulRow_eq_of_coefficients 78 BData V4PRSData 33
    ((rectangularize 53 78 V4PRB1Data).getD 33 [])
  · decide
  · have hTargetSupport : (V4PRB1Data.getD 33 []).length ≤ 78 := by
      decide
    rw [getD_rectangularize 53 78 V4PRB1Data 33 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB1Row33_coefficients

private theorem v4PRB1Row34_coefficients (j : ℕ) (hj : j < 78) :
    mulCoeffTwo BData V4PRSData 34 j =
      ((rectangularize 53 78 V4PRB1Data).getD 34 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB1Row34_spec :
    padOne 78 (mulRow BData V4PRSData 34) =
      (rectangularize 53 78 V4PRB1Data).getD 34 [] := by
  apply padOne_mulRow_eq_of_coefficients 78 BData V4PRSData 34
    ((rectangularize 53 78 V4PRB1Data).getD 34 [])
  · decide
  · have hTargetSupport : (V4PRB1Data.getD 34 []).length ≤ 78 := by
      decide
    rw [getD_rectangularize 53 78 V4PRB1Data 34 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB1Row34_coefficients

private theorem v4PRB1Row35_coefficients (j : ℕ) (hj : j < 78) :
    mulCoeffTwo BData V4PRSData 35 j =
      ((rectangularize 53 78 V4PRB1Data).getD 35 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB1Row35_spec :
    padOne 78 (mulRow BData V4PRSData 35) =
      (rectangularize 53 78 V4PRB1Data).getD 35 [] := by
  apply padOne_mulRow_eq_of_coefficients 78 BData V4PRSData 35
    ((rectangularize 53 78 V4PRB1Data).getD 35 [])
  · decide
  · have hTargetSupport : (V4PRB1Data.getD 35 []).length ≤ 78 := by
      decide
    rw [getD_rectangularize 53 78 V4PRB1Data 35 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB1Row35_coefficients

private theorem v4PRB1Row36_coefficients (j : ℕ) (hj : j < 78) :
    mulCoeffTwo BData V4PRSData 36 j =
      ((rectangularize 53 78 V4PRB1Data).getD 36 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB1Row36_spec :
    padOne 78 (mulRow BData V4PRSData 36) =
      (rectangularize 53 78 V4PRB1Data).getD 36 [] := by
  apply padOne_mulRow_eq_of_coefficients 78 BData V4PRSData 36
    ((rectangularize 53 78 V4PRB1Data).getD 36 [])
  · decide
  · have hTargetSupport : (V4PRB1Data.getD 36 []).length ≤ 78 := by
      decide
    rw [getD_rectangularize 53 78 V4PRB1Data 36 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB1Row36_coefficients

private theorem v4PRB1Row37_coefficients (j : ℕ) (hj : j < 78) :
    mulCoeffTwo BData V4PRSData 37 j =
      ((rectangularize 53 78 V4PRB1Data).getD 37 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB1Row37_spec :
    padOne 78 (mulRow BData V4PRSData 37) =
      (rectangularize 53 78 V4PRB1Data).getD 37 [] := by
  apply padOne_mulRow_eq_of_coefficients 78 BData V4PRSData 37
    ((rectangularize 53 78 V4PRB1Data).getD 37 [])
  · decide
  · have hTargetSupport : (V4PRB1Data.getD 37 []).length ≤ 78 := by
      decide
    rw [getD_rectangularize 53 78 V4PRB1Data 37 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB1Row37_coefficients

private theorem v4PRB1Row38_spec :
    padOne 78 (mulRow BData V4PRSData 38) =
      (rectangularize 53 78 V4PRB1Data).getD 38 [] := by
  decide

private theorem v4PRB1Row39_spec :
    padOne 78 (mulRow BData V4PRSData 39) =
      (rectangularize 53 78 V4PRB1Data).getD 39 [] := by
  decide

private theorem v4PRB1Row40_spec :
    padOne 78 (mulRow BData V4PRSData 40) =
      (rectangularize 53 78 V4PRB1Data).getD 40 [] := by
  decide

private theorem v4PRB1Row41_spec :
    padOne 78 (mulRow BData V4PRSData 41) =
      (rectangularize 53 78 V4PRB1Data).getD 41 [] := by
  decide

private theorem v4PRB1Row42_spec :
    padOne 78 (mulRow BData V4PRSData 42) =
      (rectangularize 53 78 V4PRB1Data).getD 42 [] := by
  decide

private theorem v4PRB1Row43_spec :
    padOne 78 (mulRow BData V4PRSData 43) =
      (rectangularize 53 78 V4PRB1Data).getD 43 [] := by
  decide

private theorem v4PRB1Row44_spec :
    padOne 78 (mulRow BData V4PRSData 44) =
      (rectangularize 53 78 V4PRB1Data).getD 44 [] := by
  decide

private theorem v4PRB1Row45_spec :
    padOne 78 (mulRow BData V4PRSData 45) =
      (rectangularize 53 78 V4PRB1Data).getD 45 [] := by
  decide

private theorem v4PRB1Row46_spec :
    padOne 78 (mulRow BData V4PRSData 46) =
      (rectangularize 53 78 V4PRB1Data).getD 46 [] := by
  decide

private theorem v4PRB1Row47_spec :
    padOne 78 (mulRow BData V4PRSData 47) =
      (rectangularize 53 78 V4PRB1Data).getD 47 [] := by
  decide

private theorem v4PRB1Row48_spec :
    padOne 78 (mulRow BData V4PRSData 48) =
      (rectangularize 53 78 V4PRB1Data).getD 48 [] := by
  decide

private theorem v4PRB1Row49_spec :
    padOne 78 (mulRow BData V4PRSData 49) =
      (rectangularize 53 78 V4PRB1Data).getD 49 [] := by
  decide

private theorem v4PRB1Row50_spec :
    padOne 78 (mulRow BData V4PRSData 50) =
      (rectangularize 53 78 V4PRB1Data).getD 50 [] := by
  decide

private theorem v4PRB1Row51_spec :
    padOne 78 (mulRow BData V4PRSData 51) =
      (rectangularize 53 78 V4PRB1Data).getD 51 [] := by
  decide

private theorem v4PRB1Row52_spec :
    padOne 78 (mulRow BData V4PRSData 52) =
      (rectangularize 53 78 V4PRB1Data).getD 52 [] := by
  decide

private theorem v4PRB1Rows_spec (n : ℕ) (hn : n < 53) :
    padOne 78 (mulRow BData V4PRSData n) =
      (rectangularize 53 78 V4PRB1Data).getD n [] := by
  have hCases :
    n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨
    n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨
    n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨
    n = 15 ∨ n = 16 ∨ n = 17 ∨ n = 18 ∨ n = 19 ∨
    n = 20 ∨ n = 21 ∨ n = 22 ∨ n = 23 ∨ n = 24 ∨
    n = 25 ∨ n = 26 ∨ n = 27 ∨ n = 28 ∨ n = 29 ∨
    n = 30 ∨ n = 31 ∨ n = 32 ∨ n = 33 ∨ n = 34 ∨
    n = 35 ∨ n = 36 ∨ n = 37 ∨ n = 38 ∨ n = 39 ∨
    n = 40 ∨ n = 41 ∨ n = 42 ∨ n = 43 ∨ n = 44 ∨
    n = 45 ∨ n = 46 ∨ n = 47 ∨ n = 48 ∨ n = 49 ∨
    n = 50 ∨ n = 51 ∨ n = 52 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · exact v4PRB1Row0_spec
  · exact v4PRB1Row1_spec
  · exact v4PRB1Row2_spec
  · exact v4PRB1Row3_spec
  · exact v4PRB1Row4_spec
  · exact v4PRB1Row5_spec
  · exact v4PRB1Row6_spec
  · exact v4PRB1Row7_spec
  · exact v4PRB1Row8_spec
  · exact v4PRB1Row9_spec
  · exact v4PRB1Row10_spec
  · exact v4PRB1Row11_spec
  · exact v4PRB1Row12_spec
  · exact v4PRB1Row13_spec
  · exact v4PRB1Row14_spec
  · exact v4PRB1Row15_spec
  · exact v4PRB1Row16_spec
  · exact v4PRB1Row17_spec
  · exact v4PRB1Row18_spec
  · exact v4PRB1Row19_spec
  · exact v4PRB1Row20_spec
  · exact v4PRB1Row21_spec
  · exact v4PRB1Row22_spec
  · exact v4PRB1Row23_spec
  · exact v4PRB1Row24_spec
  · exact v4PRB1Row25_spec
  · exact v4PRB1Row26_spec
  · exact v4PRB1Row27_spec
  · exact v4PRB1Row28_spec
  · exact v4PRB1Row29_spec
  · exact v4PRB1Row30_spec
  · exact v4PRB1Row31_spec
  · exact v4PRB1Row32_spec
  · exact v4PRB1Row33_spec
  · exact v4PRB1Row34_spec
  · exact v4PRB1Row35_spec
  · exact v4PRB1Row36_spec
  · exact v4PRB1Row37_spec
  · exact v4PRB1Row38_spec
  · exact v4PRB1Row39_spec
  · exact v4PRB1Row40_spec
  · exact v4PRB1Row41_spec
  · exact v4PRB1Row42_spec
  · exact v4PRB1Row43_spec
  · exact v4PRB1Row44_spec
  · exact v4PRB1Row45_spec
  · exact v4PRB1Row46_spec
  · exact v4PRB1Row47_spec
  · exact v4PRB1Row48_spec
  · exact v4PRB1Row49_spec
  · exact v4PRB1Row50_spec
  · exact v4PRB1Row51_spec
  · exact v4PRB1Row52_spec

private theorem v4PRB1Left_length :
    (rectangularize 53 78 (Two.mul BData V4PRSData)).length = 53 := by
  decide

private theorem v4PRB1Right_length :
    (rectangularize 53 78 V4PRB1Data).length = 53 := by
  decide

-- Exact bidegree bound (52, 77); no row or column is discarded.
private theorem v4PRB1Data_spec :
    rectangularize 53 78 (Two.mul BData V4PRSData) =
      rectangularize 53 78 V4PRB1Data := by
  apply List.ext_getElem (v4PRB1Left_length.trans v4PRB1Right_length.symm)
  intro n hn _
  rw [List.getElem_eq_getD [], List.getElem_eq_getD []]
  rw [v4PRB1Left_length] at hn
  rw [getD_rectangularize 53 78 (Two.mul BData V4PRSData) n hn,
    ← mulRow_eq_getD]
  exact v4PRB1Rows_spec n hn

private theorem v4PRB2Row0_spec :
    padOne 79 (mulRow BData V4PRB1Data 0) =
      (rectangularize 53 79 V4PRB2Data).getD 0 [] := by
  decide

private theorem v4PRB2Row1_spec :
    padOne 79 (mulRow BData V4PRB1Data 1) =
      (rectangularize 53 79 V4PRB2Data).getD 1 [] := by
  decide

private theorem v4PRB2Row2_spec :
    padOne 79 (mulRow BData V4PRB1Data 2) =
      (rectangularize 53 79 V4PRB2Data).getD 2 [] := by
  decide

private theorem v4PRB2Row3_spec :
    padOne 79 (mulRow BData V4PRB1Data 3) =
      (rectangularize 53 79 V4PRB2Data).getD 3 [] := by
  decide

private theorem v4PRB2Row4_spec :
    padOne 79 (mulRow BData V4PRB1Data 4) =
      (rectangularize 53 79 V4PRB2Data).getD 4 [] := by
  decide

private theorem v4PRB2Row5_spec :
    padOne 79 (mulRow BData V4PRB1Data 5) =
      (rectangularize 53 79 V4PRB2Data).getD 5 [] := by
  decide

private theorem v4PRB2Row6_spec :
    padOne 79 (mulRow BData V4PRB1Data 6) =
      (rectangularize 53 79 V4PRB2Data).getD 6 [] := by
  decide

private theorem v4PRB2Row7_spec :
    padOne 79 (mulRow BData V4PRB1Data 7) =
      (rectangularize 53 79 V4PRB2Data).getD 7 [] := by
  decide

private theorem v4PRB2Row8_spec :
    padOne 79 (mulRow BData V4PRB1Data 8) =
      (rectangularize 53 79 V4PRB2Data).getD 8 [] := by
  decide

private theorem v4PRB2Row9_spec :
    padOne 79 (mulRow BData V4PRB1Data 9) =
      (rectangularize 53 79 V4PRB2Data).getD 9 [] := by
  decide

private theorem v4PRB2Row10_spec :
    padOne 79 (mulRow BData V4PRB1Data 10) =
      (rectangularize 53 79 V4PRB2Data).getD 10 [] := by
  decide

private theorem v4PRB2Row11_spec :
    padOne 79 (mulRow BData V4PRB1Data 11) =
      (rectangularize 53 79 V4PRB2Data).getD 11 [] := by
  decide

private theorem v4PRB2Row12_spec :
    padOne 79 (mulRow BData V4PRB1Data 12) =
      (rectangularize 53 79 V4PRB2Data).getD 12 [] := by
  decide

private theorem v4PRB2Row13_spec :
    padOne 79 (mulRow BData V4PRB1Data 13) =
      (rectangularize 53 79 V4PRB2Data).getD 13 [] := by
  decide

private theorem v4PRB2Row14_spec :
    padOne 79 (mulRow BData V4PRB1Data 14) =
      (rectangularize 53 79 V4PRB2Data).getD 14 [] := by
  decide

private theorem v4PRB2Row15_coefficients (j : ℕ) (hj : j < 79) :
    mulCoeffTwo BData V4PRB1Data 15 j =
      ((rectangularize 53 79 V4PRB2Data).getD 15 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB2Row15_spec :
    padOne 79 (mulRow BData V4PRB1Data 15) =
      (rectangularize 53 79 V4PRB2Data).getD 15 [] := by
  apply padOne_mulRow_eq_of_coefficients 79 BData V4PRB1Data 15
    ((rectangularize 53 79 V4PRB2Data).getD 15 [])
  · decide
  · have hTargetSupport : (V4PRB2Data.getD 15 []).length ≤ 79 := by
      decide
    rw [getD_rectangularize 53 79 V4PRB2Data 15 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB2Row15_coefficients

private theorem v4PRB2Row16_coefficients (j : ℕ) (hj : j < 79) :
    mulCoeffTwo BData V4PRB1Data 16 j =
      ((rectangularize 53 79 V4PRB2Data).getD 16 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB2Row16_spec :
    padOne 79 (mulRow BData V4PRB1Data 16) =
      (rectangularize 53 79 V4PRB2Data).getD 16 [] := by
  apply padOne_mulRow_eq_of_coefficients 79 BData V4PRB1Data 16
    ((rectangularize 53 79 V4PRB2Data).getD 16 [])
  · decide
  · have hTargetSupport : (V4PRB2Data.getD 16 []).length ≤ 79 := by
      decide
    rw [getD_rectangularize 53 79 V4PRB2Data 16 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB2Row16_coefficients

private theorem v4PRB2Row17_coefficients (j : ℕ) (hj : j < 79) :
    mulCoeffTwo BData V4PRB1Data 17 j =
      ((rectangularize 53 79 V4PRB2Data).getD 17 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB2Row17_spec :
    padOne 79 (mulRow BData V4PRB1Data 17) =
      (rectangularize 53 79 V4PRB2Data).getD 17 [] := by
  apply padOne_mulRow_eq_of_coefficients 79 BData V4PRB1Data 17
    ((rectangularize 53 79 V4PRB2Data).getD 17 [])
  · decide
  · have hTargetSupport : (V4PRB2Data.getD 17 []).length ≤ 79 := by
      decide
    rw [getD_rectangularize 53 79 V4PRB2Data 17 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB2Row17_coefficients

private theorem v4PRB2Row18_coefficients (j : ℕ) (hj : j < 79) :
    mulCoeffTwo BData V4PRB1Data 18 j =
      ((rectangularize 53 79 V4PRB2Data).getD 18 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB2Row18_spec :
    padOne 79 (mulRow BData V4PRB1Data 18) =
      (rectangularize 53 79 V4PRB2Data).getD 18 [] := by
  apply padOne_mulRow_eq_of_coefficients 79 BData V4PRB1Data 18
    ((rectangularize 53 79 V4PRB2Data).getD 18 [])
  · decide
  · have hTargetSupport : (V4PRB2Data.getD 18 []).length ≤ 79 := by
      decide
    rw [getD_rectangularize 53 79 V4PRB2Data 18 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB2Row18_coefficients

private theorem v4PRB2Row19_coefficients (j : ℕ) (hj : j < 79) :
    mulCoeffTwo BData V4PRB1Data 19 j =
      ((rectangularize 53 79 V4PRB2Data).getD 19 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB2Row19_spec :
    padOne 79 (mulRow BData V4PRB1Data 19) =
      (rectangularize 53 79 V4PRB2Data).getD 19 [] := by
  apply padOne_mulRow_eq_of_coefficients 79 BData V4PRB1Data 19
    ((rectangularize 53 79 V4PRB2Data).getD 19 [])
  · decide
  · have hTargetSupport : (V4PRB2Data.getD 19 []).length ≤ 79 := by
      decide
    rw [getD_rectangularize 53 79 V4PRB2Data 19 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB2Row19_coefficients

private theorem v4PRB2Row20_coefficients (j : ℕ) (hj : j < 79) :
    mulCoeffTwo BData V4PRB1Data 20 j =
      ((rectangularize 53 79 V4PRB2Data).getD 20 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB2Row20_spec :
    padOne 79 (mulRow BData V4PRB1Data 20) =
      (rectangularize 53 79 V4PRB2Data).getD 20 [] := by
  apply padOne_mulRow_eq_of_coefficients 79 BData V4PRB1Data 20
    ((rectangularize 53 79 V4PRB2Data).getD 20 [])
  · decide
  · have hTargetSupport : (V4PRB2Data.getD 20 []).length ≤ 79 := by
      decide
    rw [getD_rectangularize 53 79 V4PRB2Data 20 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB2Row20_coefficients

private theorem v4PRB2Row21_coefficients (j : ℕ) (hj : j < 79) :
    mulCoeffTwo BData V4PRB1Data 21 j =
      ((rectangularize 53 79 V4PRB2Data).getD 21 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB2Row21_spec :
    padOne 79 (mulRow BData V4PRB1Data 21) =
      (rectangularize 53 79 V4PRB2Data).getD 21 [] := by
  apply padOne_mulRow_eq_of_coefficients 79 BData V4PRB1Data 21
    ((rectangularize 53 79 V4PRB2Data).getD 21 [])
  · decide
  · have hTargetSupport : (V4PRB2Data.getD 21 []).length ≤ 79 := by
      decide
    rw [getD_rectangularize 53 79 V4PRB2Data 21 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB2Row21_coefficients

private theorem v4PRB2Row22_coefficients (j : ℕ) (hj : j < 79) :
    mulCoeffTwo BData V4PRB1Data 22 j =
      ((rectangularize 53 79 V4PRB2Data).getD 22 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB2Row22_spec :
    padOne 79 (mulRow BData V4PRB1Data 22) =
      (rectangularize 53 79 V4PRB2Data).getD 22 [] := by
  apply padOne_mulRow_eq_of_coefficients 79 BData V4PRB1Data 22
    ((rectangularize 53 79 V4PRB2Data).getD 22 [])
  · decide
  · have hTargetSupport : (V4PRB2Data.getD 22 []).length ≤ 79 := by
      decide
    rw [getD_rectangularize 53 79 V4PRB2Data 22 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB2Row22_coefficients

private theorem v4PRB2Row23_coefficients (j : ℕ) (hj : j < 79) :
    mulCoeffTwo BData V4PRB1Data 23 j =
      ((rectangularize 53 79 V4PRB2Data).getD 23 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB2Row23_spec :
    padOne 79 (mulRow BData V4PRB1Data 23) =
      (rectangularize 53 79 V4PRB2Data).getD 23 [] := by
  apply padOne_mulRow_eq_of_coefficients 79 BData V4PRB1Data 23
    ((rectangularize 53 79 V4PRB2Data).getD 23 [])
  · decide
  · have hTargetSupport : (V4PRB2Data.getD 23 []).length ≤ 79 := by
      decide
    rw [getD_rectangularize 53 79 V4PRB2Data 23 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB2Row23_coefficients

private theorem v4PRB2Row24_coefficients (j : ℕ) (hj : j < 79) :
    mulCoeffTwo BData V4PRB1Data 24 j =
      ((rectangularize 53 79 V4PRB2Data).getD 24 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB2Row24_spec :
    padOne 79 (mulRow BData V4PRB1Data 24) =
      (rectangularize 53 79 V4PRB2Data).getD 24 [] := by
  apply padOne_mulRow_eq_of_coefficients 79 BData V4PRB1Data 24
    ((rectangularize 53 79 V4PRB2Data).getD 24 [])
  · decide
  · have hTargetSupport : (V4PRB2Data.getD 24 []).length ≤ 79 := by
      decide
    rw [getD_rectangularize 53 79 V4PRB2Data 24 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB2Row24_coefficients

private theorem v4PRB2Row25_coefficients (j : ℕ) (hj : j < 79) :
    mulCoeffTwo BData V4PRB1Data 25 j =
      ((rectangularize 53 79 V4PRB2Data).getD 25 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB2Row25_spec :
    padOne 79 (mulRow BData V4PRB1Data 25) =
      (rectangularize 53 79 V4PRB2Data).getD 25 [] := by
  apply padOne_mulRow_eq_of_coefficients 79 BData V4PRB1Data 25
    ((rectangularize 53 79 V4PRB2Data).getD 25 [])
  · decide
  · have hTargetSupport : (V4PRB2Data.getD 25 []).length ≤ 79 := by
      decide
    rw [getD_rectangularize 53 79 V4PRB2Data 25 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB2Row25_coefficients

private theorem v4PRB2Row26_coefficients (j : ℕ) (hj : j < 79) :
    mulCoeffTwo BData V4PRB1Data 26 j =
      ((rectangularize 53 79 V4PRB2Data).getD 26 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB2Row26_spec :
    padOne 79 (mulRow BData V4PRB1Data 26) =
      (rectangularize 53 79 V4PRB2Data).getD 26 [] := by
  apply padOne_mulRow_eq_of_coefficients 79 BData V4PRB1Data 26
    ((rectangularize 53 79 V4PRB2Data).getD 26 [])
  · decide
  · have hTargetSupport : (V4PRB2Data.getD 26 []).length ≤ 79 := by
      decide
    rw [getD_rectangularize 53 79 V4PRB2Data 26 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB2Row26_coefficients

private theorem v4PRB2Row27_coefficients (j : ℕ) (hj : j < 79) :
    mulCoeffTwo BData V4PRB1Data 27 j =
      ((rectangularize 53 79 V4PRB2Data).getD 27 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB2Row27_spec :
    padOne 79 (mulRow BData V4PRB1Data 27) =
      (rectangularize 53 79 V4PRB2Data).getD 27 [] := by
  apply padOne_mulRow_eq_of_coefficients 79 BData V4PRB1Data 27
    ((rectangularize 53 79 V4PRB2Data).getD 27 [])
  · decide
  · have hTargetSupport : (V4PRB2Data.getD 27 []).length ≤ 79 := by
      decide
    rw [getD_rectangularize 53 79 V4PRB2Data 27 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB2Row27_coefficients

private theorem v4PRB2Row28_coefficients (j : ℕ) (hj : j < 79) :
    mulCoeffTwo BData V4PRB1Data 28 j =
      ((rectangularize 53 79 V4PRB2Data).getD 28 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB2Row28_spec :
    padOne 79 (mulRow BData V4PRB1Data 28) =
      (rectangularize 53 79 V4PRB2Data).getD 28 [] := by
  apply padOne_mulRow_eq_of_coefficients 79 BData V4PRB1Data 28
    ((rectangularize 53 79 V4PRB2Data).getD 28 [])
  · decide
  · have hTargetSupport : (V4PRB2Data.getD 28 []).length ≤ 79 := by
      decide
    rw [getD_rectangularize 53 79 V4PRB2Data 28 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB2Row28_coefficients

private theorem v4PRB2Row29_coefficients (j : ℕ) (hj : j < 79) :
    mulCoeffTwo BData V4PRB1Data 29 j =
      ((rectangularize 53 79 V4PRB2Data).getD 29 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB2Row29_spec :
    padOne 79 (mulRow BData V4PRB1Data 29) =
      (rectangularize 53 79 V4PRB2Data).getD 29 [] := by
  apply padOne_mulRow_eq_of_coefficients 79 BData V4PRB1Data 29
    ((rectangularize 53 79 V4PRB2Data).getD 29 [])
  · decide
  · have hTargetSupport : (V4PRB2Data.getD 29 []).length ≤ 79 := by
      decide
    rw [getD_rectangularize 53 79 V4PRB2Data 29 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB2Row29_coefficients

private theorem v4PRB2Row30_coefficients (j : ℕ) (hj : j < 79) :
    mulCoeffTwo BData V4PRB1Data 30 j =
      ((rectangularize 53 79 V4PRB2Data).getD 30 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB2Row30_spec :
    padOne 79 (mulRow BData V4PRB1Data 30) =
      (rectangularize 53 79 V4PRB2Data).getD 30 [] := by
  apply padOne_mulRow_eq_of_coefficients 79 BData V4PRB1Data 30
    ((rectangularize 53 79 V4PRB2Data).getD 30 [])
  · decide
  · have hTargetSupport : (V4PRB2Data.getD 30 []).length ≤ 79 := by
      decide
    rw [getD_rectangularize 53 79 V4PRB2Data 30 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB2Row30_coefficients

private theorem v4PRB2Row31_coefficients (j : ℕ) (hj : j < 79) :
    mulCoeffTwo BData V4PRB1Data 31 j =
      ((rectangularize 53 79 V4PRB2Data).getD 31 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB2Row31_spec :
    padOne 79 (mulRow BData V4PRB1Data 31) =
      (rectangularize 53 79 V4PRB2Data).getD 31 [] := by
  apply padOne_mulRow_eq_of_coefficients 79 BData V4PRB1Data 31
    ((rectangularize 53 79 V4PRB2Data).getD 31 [])
  · decide
  · have hTargetSupport : (V4PRB2Data.getD 31 []).length ≤ 79 := by
      decide
    rw [getD_rectangularize 53 79 V4PRB2Data 31 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB2Row31_coefficients

private theorem v4PRB2Row32_coefficients (j : ℕ) (hj : j < 79) :
    mulCoeffTwo BData V4PRB1Data 32 j =
      ((rectangularize 53 79 V4PRB2Data).getD 32 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB2Row32_spec :
    padOne 79 (mulRow BData V4PRB1Data 32) =
      (rectangularize 53 79 V4PRB2Data).getD 32 [] := by
  apply padOne_mulRow_eq_of_coefficients 79 BData V4PRB1Data 32
    ((rectangularize 53 79 V4PRB2Data).getD 32 [])
  · decide
  · have hTargetSupport : (V4PRB2Data.getD 32 []).length ≤ 79 := by
      decide
    rw [getD_rectangularize 53 79 V4PRB2Data 32 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB2Row32_coefficients

private theorem v4PRB2Row33_coefficients (j : ℕ) (hj : j < 79) :
    mulCoeffTwo BData V4PRB1Data 33 j =
      ((rectangularize 53 79 V4PRB2Data).getD 33 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB2Row33_spec :
    padOne 79 (mulRow BData V4PRB1Data 33) =
      (rectangularize 53 79 V4PRB2Data).getD 33 [] := by
  apply padOne_mulRow_eq_of_coefficients 79 BData V4PRB1Data 33
    ((rectangularize 53 79 V4PRB2Data).getD 33 [])
  · decide
  · have hTargetSupport : (V4PRB2Data.getD 33 []).length ≤ 79 := by
      decide
    rw [getD_rectangularize 53 79 V4PRB2Data 33 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB2Row33_coefficients

private theorem v4PRB2Row34_coefficients (j : ℕ) (hj : j < 79) :
    mulCoeffTwo BData V4PRB1Data 34 j =
      ((rectangularize 53 79 V4PRB2Data).getD 34 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB2Row34_spec :
    padOne 79 (mulRow BData V4PRB1Data 34) =
      (rectangularize 53 79 V4PRB2Data).getD 34 [] := by
  apply padOne_mulRow_eq_of_coefficients 79 BData V4PRB1Data 34
    ((rectangularize 53 79 V4PRB2Data).getD 34 [])
  · decide
  · have hTargetSupport : (V4PRB2Data.getD 34 []).length ≤ 79 := by
      decide
    rw [getD_rectangularize 53 79 V4PRB2Data 34 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB2Row34_coefficients

private theorem v4PRB2Row35_coefficients (j : ℕ) (hj : j < 79) :
    mulCoeffTwo BData V4PRB1Data 35 j =
      ((rectangularize 53 79 V4PRB2Data).getD 35 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB2Row35_spec :
    padOne 79 (mulRow BData V4PRB1Data 35) =
      (rectangularize 53 79 V4PRB2Data).getD 35 [] := by
  apply padOne_mulRow_eq_of_coefficients 79 BData V4PRB1Data 35
    ((rectangularize 53 79 V4PRB2Data).getD 35 [])
  · decide
  · have hTargetSupport : (V4PRB2Data.getD 35 []).length ≤ 79 := by
      decide
    rw [getD_rectangularize 53 79 V4PRB2Data 35 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB2Row35_coefficients

private theorem v4PRB2Row36_coefficients (j : ℕ) (hj : j < 79) :
    mulCoeffTwo BData V4PRB1Data 36 j =
      ((rectangularize 53 79 V4PRB2Data).getD 36 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB2Row36_spec :
    padOne 79 (mulRow BData V4PRB1Data 36) =
      (rectangularize 53 79 V4PRB2Data).getD 36 [] := by
  apply padOne_mulRow_eq_of_coefficients 79 BData V4PRB1Data 36
    ((rectangularize 53 79 V4PRB2Data).getD 36 [])
  · decide
  · have hTargetSupport : (V4PRB2Data.getD 36 []).length ≤ 79 := by
      decide
    rw [getD_rectangularize 53 79 V4PRB2Data 36 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB2Row36_coefficients

private theorem v4PRB2Row37_coefficients (j : ℕ) (hj : j < 79) :
    mulCoeffTwo BData V4PRB1Data 37 j =
      ((rectangularize 53 79 V4PRB2Data).getD 37 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB2Row37_spec :
    padOne 79 (mulRow BData V4PRB1Data 37) =
      (rectangularize 53 79 V4PRB2Data).getD 37 [] := by
  apply padOne_mulRow_eq_of_coefficients 79 BData V4PRB1Data 37
    ((rectangularize 53 79 V4PRB2Data).getD 37 [])
  · decide
  · have hTargetSupport : (V4PRB2Data.getD 37 []).length ≤ 79 := by
      decide
    rw [getD_rectangularize 53 79 V4PRB2Data 37 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB2Row37_coefficients

private theorem v4PRB2Row38_coefficients (j : ℕ) (hj : j < 79) :
    mulCoeffTwo BData V4PRB1Data 38 j =
      ((rectangularize 53 79 V4PRB2Data).getD 38 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB2Row38_spec :
    padOne 79 (mulRow BData V4PRB1Data 38) =
      (rectangularize 53 79 V4PRB2Data).getD 38 [] := by
  apply padOne_mulRow_eq_of_coefficients 79 BData V4PRB1Data 38
    ((rectangularize 53 79 V4PRB2Data).getD 38 [])
  · decide
  · have hTargetSupport : (V4PRB2Data.getD 38 []).length ≤ 79 := by
      decide
    rw [getD_rectangularize 53 79 V4PRB2Data 38 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB2Row38_coefficients

private theorem v4PRB2Row39_spec :
    padOne 79 (mulRow BData V4PRB1Data 39) =
      (rectangularize 53 79 V4PRB2Data).getD 39 [] := by
  decide

private theorem v4PRB2Row40_spec :
    padOne 79 (mulRow BData V4PRB1Data 40) =
      (rectangularize 53 79 V4PRB2Data).getD 40 [] := by
  decide

private theorem v4PRB2Row41_spec :
    padOne 79 (mulRow BData V4PRB1Data 41) =
      (rectangularize 53 79 V4PRB2Data).getD 41 [] := by
  decide

private theorem v4PRB2Row42_spec :
    padOne 79 (mulRow BData V4PRB1Data 42) =
      (rectangularize 53 79 V4PRB2Data).getD 42 [] := by
  decide

private theorem v4PRB2Row43_spec :
    padOne 79 (mulRow BData V4PRB1Data 43) =
      (rectangularize 53 79 V4PRB2Data).getD 43 [] := by
  decide

private theorem v4PRB2Row44_spec :
    padOne 79 (mulRow BData V4PRB1Data 44) =
      (rectangularize 53 79 V4PRB2Data).getD 44 [] := by
  decide

private theorem v4PRB2Row45_spec :
    padOne 79 (mulRow BData V4PRB1Data 45) =
      (rectangularize 53 79 V4PRB2Data).getD 45 [] := by
  decide

private theorem v4PRB2Row46_spec :
    padOne 79 (mulRow BData V4PRB1Data 46) =
      (rectangularize 53 79 V4PRB2Data).getD 46 [] := by
  decide

private theorem v4PRB2Row47_spec :
    padOne 79 (mulRow BData V4PRB1Data 47) =
      (rectangularize 53 79 V4PRB2Data).getD 47 [] := by
  decide

private theorem v4PRB2Row48_spec :
    padOne 79 (mulRow BData V4PRB1Data 48) =
      (rectangularize 53 79 V4PRB2Data).getD 48 [] := by
  decide

private theorem v4PRB2Row49_spec :
    padOne 79 (mulRow BData V4PRB1Data 49) =
      (rectangularize 53 79 V4PRB2Data).getD 49 [] := by
  decide

private theorem v4PRB2Row50_spec :
    padOne 79 (mulRow BData V4PRB1Data 50) =
      (rectangularize 53 79 V4PRB2Data).getD 50 [] := by
  decide

private theorem v4PRB2Row51_spec :
    padOne 79 (mulRow BData V4PRB1Data 51) =
      (rectangularize 53 79 V4PRB2Data).getD 51 [] := by
  decide

private theorem v4PRB2Row52_spec :
    padOne 79 (mulRow BData V4PRB1Data 52) =
      (rectangularize 53 79 V4PRB2Data).getD 52 [] := by
  decide

private theorem v4PRB2Rows_spec (n : ℕ) (hn : n < 53) :
    padOne 79 (mulRow BData V4PRB1Data n) =
      (rectangularize 53 79 V4PRB2Data).getD n [] := by
  have hCases :
    n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨
    n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨
    n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨
    n = 15 ∨ n = 16 ∨ n = 17 ∨ n = 18 ∨ n = 19 ∨
    n = 20 ∨ n = 21 ∨ n = 22 ∨ n = 23 ∨ n = 24 ∨
    n = 25 ∨ n = 26 ∨ n = 27 ∨ n = 28 ∨ n = 29 ∨
    n = 30 ∨ n = 31 ∨ n = 32 ∨ n = 33 ∨ n = 34 ∨
    n = 35 ∨ n = 36 ∨ n = 37 ∨ n = 38 ∨ n = 39 ∨
    n = 40 ∨ n = 41 ∨ n = 42 ∨ n = 43 ∨ n = 44 ∨
    n = 45 ∨ n = 46 ∨ n = 47 ∨ n = 48 ∨ n = 49 ∨
    n = 50 ∨ n = 51 ∨ n = 52 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · exact v4PRB2Row0_spec
  · exact v4PRB2Row1_spec
  · exact v4PRB2Row2_spec
  · exact v4PRB2Row3_spec
  · exact v4PRB2Row4_spec
  · exact v4PRB2Row5_spec
  · exact v4PRB2Row6_spec
  · exact v4PRB2Row7_spec
  · exact v4PRB2Row8_spec
  · exact v4PRB2Row9_spec
  · exact v4PRB2Row10_spec
  · exact v4PRB2Row11_spec
  · exact v4PRB2Row12_spec
  · exact v4PRB2Row13_spec
  · exact v4PRB2Row14_spec
  · exact v4PRB2Row15_spec
  · exact v4PRB2Row16_spec
  · exact v4PRB2Row17_spec
  · exact v4PRB2Row18_spec
  · exact v4PRB2Row19_spec
  · exact v4PRB2Row20_spec
  · exact v4PRB2Row21_spec
  · exact v4PRB2Row22_spec
  · exact v4PRB2Row23_spec
  · exact v4PRB2Row24_spec
  · exact v4PRB2Row25_spec
  · exact v4PRB2Row26_spec
  · exact v4PRB2Row27_spec
  · exact v4PRB2Row28_spec
  · exact v4PRB2Row29_spec
  · exact v4PRB2Row30_spec
  · exact v4PRB2Row31_spec
  · exact v4PRB2Row32_spec
  · exact v4PRB2Row33_spec
  · exact v4PRB2Row34_spec
  · exact v4PRB2Row35_spec
  · exact v4PRB2Row36_spec
  · exact v4PRB2Row37_spec
  · exact v4PRB2Row38_spec
  · exact v4PRB2Row39_spec
  · exact v4PRB2Row40_spec
  · exact v4PRB2Row41_spec
  · exact v4PRB2Row42_spec
  · exact v4PRB2Row43_spec
  · exact v4PRB2Row44_spec
  · exact v4PRB2Row45_spec
  · exact v4PRB2Row46_spec
  · exact v4PRB2Row47_spec
  · exact v4PRB2Row48_spec
  · exact v4PRB2Row49_spec
  · exact v4PRB2Row50_spec
  · exact v4PRB2Row51_spec
  · exact v4PRB2Row52_spec

private theorem v4PRB2Left_length :
    (rectangularize 53 79 (Two.mul BData V4PRB1Data)).length = 53 := by
  decide

private theorem v4PRB2Right_length :
    (rectangularize 53 79 V4PRB2Data).length = 53 := by
  decide

-- Exact bidegree bound (52, 78); no row or column is discarded.
private theorem v4PRB2Data_spec :
    rectangularize 53 79 (Two.mul BData V4PRB1Data) =
      rectangularize 53 79 V4PRB2Data := by
  apply List.ext_getElem (v4PRB2Left_length.trans v4PRB2Right_length.symm)
  intro n hn _
  rw [List.getElem_eq_getD [], List.getElem_eq_getD []]
  rw [v4PRB2Left_length] at hn
  rw [getD_rectangularize 53 79 (Two.mul BData V4PRB1Data) n hn,
    ← mulRow_eq_getD]
  exact v4PRB2Rows_spec n hn

private theorem v4PRB3Row0_spec :
    padOne 80 (mulRow BData V4PRB2Data 0) =
      (rectangularize 53 80 V4PRB3Data).getD 0 [] := by
  decide

private theorem v4PRB3Row1_spec :
    padOne 80 (mulRow BData V4PRB2Data 1) =
      (rectangularize 53 80 V4PRB3Data).getD 1 [] := by
  decide

private theorem v4PRB3Row2_spec :
    padOne 80 (mulRow BData V4PRB2Data 2) =
      (rectangularize 53 80 V4PRB3Data).getD 2 [] := by
  decide

private theorem v4PRB3Row3_spec :
    padOne 80 (mulRow BData V4PRB2Data 3) =
      (rectangularize 53 80 V4PRB3Data).getD 3 [] := by
  decide

private theorem v4PRB3Row4_spec :
    padOne 80 (mulRow BData V4PRB2Data 4) =
      (rectangularize 53 80 V4PRB3Data).getD 4 [] := by
  decide

private theorem v4PRB3Row5_spec :
    padOne 80 (mulRow BData V4PRB2Data 5) =
      (rectangularize 53 80 V4PRB3Data).getD 5 [] := by
  decide

private theorem v4PRB3Row6_spec :
    padOne 80 (mulRow BData V4PRB2Data 6) =
      (rectangularize 53 80 V4PRB3Data).getD 6 [] := by
  decide

private theorem v4PRB3Row7_spec :
    padOne 80 (mulRow BData V4PRB2Data 7) =
      (rectangularize 53 80 V4PRB3Data).getD 7 [] := by
  decide

private theorem v4PRB3Row8_spec :
    padOne 80 (mulRow BData V4PRB2Data 8) =
      (rectangularize 53 80 V4PRB3Data).getD 8 [] := by
  decide

private theorem v4PRB3Row9_spec :
    padOne 80 (mulRow BData V4PRB2Data 9) =
      (rectangularize 53 80 V4PRB3Data).getD 9 [] := by
  decide

private theorem v4PRB3Row10_spec :
    padOne 80 (mulRow BData V4PRB2Data 10) =
      (rectangularize 53 80 V4PRB3Data).getD 10 [] := by
  decide

private theorem v4PRB3Row11_spec :
    padOne 80 (mulRow BData V4PRB2Data 11) =
      (rectangularize 53 80 V4PRB3Data).getD 11 [] := by
  decide

private theorem v4PRB3Row12_spec :
    padOne 80 (mulRow BData V4PRB2Data 12) =
      (rectangularize 53 80 V4PRB3Data).getD 12 [] := by
  decide

private theorem v4PRB3Row13_spec :
    padOne 80 (mulRow BData V4PRB2Data 13) =
      (rectangularize 53 80 V4PRB3Data).getD 13 [] := by
  decide

private theorem v4PRB3Row14_coefficients (j : ℕ) (hj : j < 80) :
    mulCoeffTwo BData V4PRB2Data 14 j =
      ((rectangularize 53 80 V4PRB3Data).getD 14 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB3Row14_spec :
    padOne 80 (mulRow BData V4PRB2Data 14) =
      (rectangularize 53 80 V4PRB3Data).getD 14 [] := by
  apply padOne_mulRow_eq_of_coefficients 80 BData V4PRB2Data 14
    ((rectangularize 53 80 V4PRB3Data).getD 14 [])
  · decide
  · have hTargetSupport : (V4PRB3Data.getD 14 []).length ≤ 80 := by
      decide
    rw [getD_rectangularize 53 80 V4PRB3Data 14 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB3Row14_coefficients

private theorem v4PRB3Row15_coefficients (j : ℕ) (hj : j < 80) :
    mulCoeffTwo BData V4PRB2Data 15 j =
      ((rectangularize 53 80 V4PRB3Data).getD 15 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB3Row15_spec :
    padOne 80 (mulRow BData V4PRB2Data 15) =
      (rectangularize 53 80 V4PRB3Data).getD 15 [] := by
  apply padOne_mulRow_eq_of_coefficients 80 BData V4PRB2Data 15
    ((rectangularize 53 80 V4PRB3Data).getD 15 [])
  · decide
  · have hTargetSupport : (V4PRB3Data.getD 15 []).length ≤ 80 := by
      decide
    rw [getD_rectangularize 53 80 V4PRB3Data 15 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB3Row15_coefficients

private theorem v4PRB3Row16_coefficients (j : ℕ) (hj : j < 80) :
    mulCoeffTwo BData V4PRB2Data 16 j =
      ((rectangularize 53 80 V4PRB3Data).getD 16 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB3Row16_spec :
    padOne 80 (mulRow BData V4PRB2Data 16) =
      (rectangularize 53 80 V4PRB3Data).getD 16 [] := by
  apply padOne_mulRow_eq_of_coefficients 80 BData V4PRB2Data 16
    ((rectangularize 53 80 V4PRB3Data).getD 16 [])
  · decide
  · have hTargetSupport : (V4PRB3Data.getD 16 []).length ≤ 80 := by
      decide
    rw [getD_rectangularize 53 80 V4PRB3Data 16 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB3Row16_coefficients

private theorem v4PRB3Row17_coefficients (j : ℕ) (hj : j < 80) :
    mulCoeffTwo BData V4PRB2Data 17 j =
      ((rectangularize 53 80 V4PRB3Data).getD 17 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB3Row17_spec :
    padOne 80 (mulRow BData V4PRB2Data 17) =
      (rectangularize 53 80 V4PRB3Data).getD 17 [] := by
  apply padOne_mulRow_eq_of_coefficients 80 BData V4PRB2Data 17
    ((rectangularize 53 80 V4PRB3Data).getD 17 [])
  · decide
  · have hTargetSupport : (V4PRB3Data.getD 17 []).length ≤ 80 := by
      decide
    rw [getD_rectangularize 53 80 V4PRB3Data 17 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB3Row17_coefficients

private theorem v4PRB3Row18_coefficients (j : ℕ) (hj : j < 80) :
    mulCoeffTwo BData V4PRB2Data 18 j =
      ((rectangularize 53 80 V4PRB3Data).getD 18 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB3Row18_spec :
    padOne 80 (mulRow BData V4PRB2Data 18) =
      (rectangularize 53 80 V4PRB3Data).getD 18 [] := by
  apply padOne_mulRow_eq_of_coefficients 80 BData V4PRB2Data 18
    ((rectangularize 53 80 V4PRB3Data).getD 18 [])
  · decide
  · have hTargetSupport : (V4PRB3Data.getD 18 []).length ≤ 80 := by
      decide
    rw [getD_rectangularize 53 80 V4PRB3Data 18 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB3Row18_coefficients

private theorem v4PRB3Row19_coefficients (j : ℕ) (hj : j < 80) :
    mulCoeffTwo BData V4PRB2Data 19 j =
      ((rectangularize 53 80 V4PRB3Data).getD 19 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB3Row19_spec :
    padOne 80 (mulRow BData V4PRB2Data 19) =
      (rectangularize 53 80 V4PRB3Data).getD 19 [] := by
  apply padOne_mulRow_eq_of_coefficients 80 BData V4PRB2Data 19
    ((rectangularize 53 80 V4PRB3Data).getD 19 [])
  · decide
  · have hTargetSupport : (V4PRB3Data.getD 19 []).length ≤ 80 := by
      decide
    rw [getD_rectangularize 53 80 V4PRB3Data 19 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB3Row19_coefficients

private theorem v4PRB3Row20_coefficients (j : ℕ) (hj : j < 80) :
    mulCoeffTwo BData V4PRB2Data 20 j =
      ((rectangularize 53 80 V4PRB3Data).getD 20 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB3Row20_spec :
    padOne 80 (mulRow BData V4PRB2Data 20) =
      (rectangularize 53 80 V4PRB3Data).getD 20 [] := by
  apply padOne_mulRow_eq_of_coefficients 80 BData V4PRB2Data 20
    ((rectangularize 53 80 V4PRB3Data).getD 20 [])
  · decide
  · have hTargetSupport : (V4PRB3Data.getD 20 []).length ≤ 80 := by
      decide
    rw [getD_rectangularize 53 80 V4PRB3Data 20 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB3Row20_coefficients

private theorem v4PRB3Row21_coefficients (j : ℕ) (hj : j < 80) :
    mulCoeffTwo BData V4PRB2Data 21 j =
      ((rectangularize 53 80 V4PRB3Data).getD 21 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB3Row21_spec :
    padOne 80 (mulRow BData V4PRB2Data 21) =
      (rectangularize 53 80 V4PRB3Data).getD 21 [] := by
  apply padOne_mulRow_eq_of_coefficients 80 BData V4PRB2Data 21
    ((rectangularize 53 80 V4PRB3Data).getD 21 [])
  · decide
  · have hTargetSupport : (V4PRB3Data.getD 21 []).length ≤ 80 := by
      decide
    rw [getD_rectangularize 53 80 V4PRB3Data 21 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB3Row21_coefficients

private theorem v4PRB3Row22_coefficients (j : ℕ) (hj : j < 80) :
    mulCoeffTwo BData V4PRB2Data 22 j =
      ((rectangularize 53 80 V4PRB3Data).getD 22 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB3Row22_spec :
    padOne 80 (mulRow BData V4PRB2Data 22) =
      (rectangularize 53 80 V4PRB3Data).getD 22 [] := by
  apply padOne_mulRow_eq_of_coefficients 80 BData V4PRB2Data 22
    ((rectangularize 53 80 V4PRB3Data).getD 22 [])
  · decide
  · have hTargetSupport : (V4PRB3Data.getD 22 []).length ≤ 80 := by
      decide
    rw [getD_rectangularize 53 80 V4PRB3Data 22 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB3Row22_coefficients

private theorem v4PRB3Row23_coefficients (j : ℕ) (hj : j < 80) :
    mulCoeffTwo BData V4PRB2Data 23 j =
      ((rectangularize 53 80 V4PRB3Data).getD 23 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB3Row23_spec :
    padOne 80 (mulRow BData V4PRB2Data 23) =
      (rectangularize 53 80 V4PRB3Data).getD 23 [] := by
  apply padOne_mulRow_eq_of_coefficients 80 BData V4PRB2Data 23
    ((rectangularize 53 80 V4PRB3Data).getD 23 [])
  · decide
  · have hTargetSupport : (V4PRB3Data.getD 23 []).length ≤ 80 := by
      decide
    rw [getD_rectangularize 53 80 V4PRB3Data 23 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB3Row23_coefficients

private theorem v4PRB3Row24_coefficients (j : ℕ) (hj : j < 80) :
    mulCoeffTwo BData V4PRB2Data 24 j =
      ((rectangularize 53 80 V4PRB3Data).getD 24 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB3Row24_spec :
    padOne 80 (mulRow BData V4PRB2Data 24) =
      (rectangularize 53 80 V4PRB3Data).getD 24 [] := by
  apply padOne_mulRow_eq_of_coefficients 80 BData V4PRB2Data 24
    ((rectangularize 53 80 V4PRB3Data).getD 24 [])
  · decide
  · have hTargetSupport : (V4PRB3Data.getD 24 []).length ≤ 80 := by
      decide
    rw [getD_rectangularize 53 80 V4PRB3Data 24 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB3Row24_coefficients

private theorem v4PRB3Row25_coefficients (j : ℕ) (hj : j < 80) :
    mulCoeffTwo BData V4PRB2Data 25 j =
      ((rectangularize 53 80 V4PRB3Data).getD 25 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB3Row25_spec :
    padOne 80 (mulRow BData V4PRB2Data 25) =
      (rectangularize 53 80 V4PRB3Data).getD 25 [] := by
  apply padOne_mulRow_eq_of_coefficients 80 BData V4PRB2Data 25
    ((rectangularize 53 80 V4PRB3Data).getD 25 [])
  · decide
  · have hTargetSupport : (V4PRB3Data.getD 25 []).length ≤ 80 := by
      decide
    rw [getD_rectangularize 53 80 V4PRB3Data 25 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB3Row25_coefficients

private theorem v4PRB3Row26_coefficients (j : ℕ) (hj : j < 80) :
    mulCoeffTwo BData V4PRB2Data 26 j =
      ((rectangularize 53 80 V4PRB3Data).getD 26 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB3Row26_spec :
    padOne 80 (mulRow BData V4PRB2Data 26) =
      (rectangularize 53 80 V4PRB3Data).getD 26 [] := by
  apply padOne_mulRow_eq_of_coefficients 80 BData V4PRB2Data 26
    ((rectangularize 53 80 V4PRB3Data).getD 26 [])
  · decide
  · have hTargetSupport : (V4PRB3Data.getD 26 []).length ≤ 80 := by
      decide
    rw [getD_rectangularize 53 80 V4PRB3Data 26 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB3Row26_coefficients

private theorem v4PRB3Row27_coefficients (j : ℕ) (hj : j < 80) :
    mulCoeffTwo BData V4PRB2Data 27 j =
      ((rectangularize 53 80 V4PRB3Data).getD 27 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB3Row27_spec :
    padOne 80 (mulRow BData V4PRB2Data 27) =
      (rectangularize 53 80 V4PRB3Data).getD 27 [] := by
  apply padOne_mulRow_eq_of_coefficients 80 BData V4PRB2Data 27
    ((rectangularize 53 80 V4PRB3Data).getD 27 [])
  · decide
  · have hTargetSupport : (V4PRB3Data.getD 27 []).length ≤ 80 := by
      decide
    rw [getD_rectangularize 53 80 V4PRB3Data 27 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB3Row27_coefficients

private theorem v4PRB3Row28_coefficients (j : ℕ) (hj : j < 80) :
    mulCoeffTwo BData V4PRB2Data 28 j =
      ((rectangularize 53 80 V4PRB3Data).getD 28 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB3Row28_spec :
    padOne 80 (mulRow BData V4PRB2Data 28) =
      (rectangularize 53 80 V4PRB3Data).getD 28 [] := by
  apply padOne_mulRow_eq_of_coefficients 80 BData V4PRB2Data 28
    ((rectangularize 53 80 V4PRB3Data).getD 28 [])
  · decide
  · have hTargetSupport : (V4PRB3Data.getD 28 []).length ≤ 80 := by
      decide
    rw [getD_rectangularize 53 80 V4PRB3Data 28 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB3Row28_coefficients

private theorem v4PRB3Row29_coefficients (j : ℕ) (hj : j < 80) :
    mulCoeffTwo BData V4PRB2Data 29 j =
      ((rectangularize 53 80 V4PRB3Data).getD 29 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB3Row29_spec :
    padOne 80 (mulRow BData V4PRB2Data 29) =
      (rectangularize 53 80 V4PRB3Data).getD 29 [] := by
  apply padOne_mulRow_eq_of_coefficients 80 BData V4PRB2Data 29
    ((rectangularize 53 80 V4PRB3Data).getD 29 [])
  · decide
  · have hTargetSupport : (V4PRB3Data.getD 29 []).length ≤ 80 := by
      decide
    rw [getD_rectangularize 53 80 V4PRB3Data 29 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB3Row29_coefficients

private theorem v4PRB3Row30_coefficients (j : ℕ) (hj : j < 80) :
    mulCoeffTwo BData V4PRB2Data 30 j =
      ((rectangularize 53 80 V4PRB3Data).getD 30 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB3Row30_spec :
    padOne 80 (mulRow BData V4PRB2Data 30) =
      (rectangularize 53 80 V4PRB3Data).getD 30 [] := by
  apply padOne_mulRow_eq_of_coefficients 80 BData V4PRB2Data 30
    ((rectangularize 53 80 V4PRB3Data).getD 30 [])
  · decide
  · have hTargetSupport : (V4PRB3Data.getD 30 []).length ≤ 80 := by
      decide
    rw [getD_rectangularize 53 80 V4PRB3Data 30 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB3Row30_coefficients

private theorem v4PRB3Row31_coefficients (j : ℕ) (hj : j < 80) :
    mulCoeffTwo BData V4PRB2Data 31 j =
      ((rectangularize 53 80 V4PRB3Data).getD 31 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB3Row31_spec :
    padOne 80 (mulRow BData V4PRB2Data 31) =
      (rectangularize 53 80 V4PRB3Data).getD 31 [] := by
  apply padOne_mulRow_eq_of_coefficients 80 BData V4PRB2Data 31
    ((rectangularize 53 80 V4PRB3Data).getD 31 [])
  · decide
  · have hTargetSupport : (V4PRB3Data.getD 31 []).length ≤ 80 := by
      decide
    rw [getD_rectangularize 53 80 V4PRB3Data 31 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB3Row31_coefficients

private theorem v4PRB3Row32_coefficients (j : ℕ) (hj : j < 80) :
    mulCoeffTwo BData V4PRB2Data 32 j =
      ((rectangularize 53 80 V4PRB3Data).getD 32 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB3Row32_spec :
    padOne 80 (mulRow BData V4PRB2Data 32) =
      (rectangularize 53 80 V4PRB3Data).getD 32 [] := by
  apply padOne_mulRow_eq_of_coefficients 80 BData V4PRB2Data 32
    ((rectangularize 53 80 V4PRB3Data).getD 32 [])
  · decide
  · have hTargetSupport : (V4PRB3Data.getD 32 []).length ≤ 80 := by
      decide
    rw [getD_rectangularize 53 80 V4PRB3Data 32 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB3Row32_coefficients

private theorem v4PRB3Row33_coefficients (j : ℕ) (hj : j < 80) :
    mulCoeffTwo BData V4PRB2Data 33 j =
      ((rectangularize 53 80 V4PRB3Data).getD 33 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB3Row33_spec :
    padOne 80 (mulRow BData V4PRB2Data 33) =
      (rectangularize 53 80 V4PRB3Data).getD 33 [] := by
  apply padOne_mulRow_eq_of_coefficients 80 BData V4PRB2Data 33
    ((rectangularize 53 80 V4PRB3Data).getD 33 [])
  · decide
  · have hTargetSupport : (V4PRB3Data.getD 33 []).length ≤ 80 := by
      decide
    rw [getD_rectangularize 53 80 V4PRB3Data 33 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB3Row33_coefficients

private theorem v4PRB3Row34_coefficients (j : ℕ) (hj : j < 80) :
    mulCoeffTwo BData V4PRB2Data 34 j =
      ((rectangularize 53 80 V4PRB3Data).getD 34 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB3Row34_spec :
    padOne 80 (mulRow BData V4PRB2Data 34) =
      (rectangularize 53 80 V4PRB3Data).getD 34 [] := by
  apply padOne_mulRow_eq_of_coefficients 80 BData V4PRB2Data 34
    ((rectangularize 53 80 V4PRB3Data).getD 34 [])
  · decide
  · have hTargetSupport : (V4PRB3Data.getD 34 []).length ≤ 80 := by
      decide
    rw [getD_rectangularize 53 80 V4PRB3Data 34 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB3Row34_coefficients

private theorem v4PRB3Row35_coefficients (j : ℕ) (hj : j < 80) :
    mulCoeffTwo BData V4PRB2Data 35 j =
      ((rectangularize 53 80 V4PRB3Data).getD 35 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB3Row35_spec :
    padOne 80 (mulRow BData V4PRB2Data 35) =
      (rectangularize 53 80 V4PRB3Data).getD 35 [] := by
  apply padOne_mulRow_eq_of_coefficients 80 BData V4PRB2Data 35
    ((rectangularize 53 80 V4PRB3Data).getD 35 [])
  · decide
  · have hTargetSupport : (V4PRB3Data.getD 35 []).length ≤ 80 := by
      decide
    rw [getD_rectangularize 53 80 V4PRB3Data 35 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB3Row35_coefficients

private theorem v4PRB3Row36_coefficients (j : ℕ) (hj : j < 80) :
    mulCoeffTwo BData V4PRB2Data 36 j =
      ((rectangularize 53 80 V4PRB3Data).getD 36 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB3Row36_spec :
    padOne 80 (mulRow BData V4PRB2Data 36) =
      (rectangularize 53 80 V4PRB3Data).getD 36 [] := by
  apply padOne_mulRow_eq_of_coefficients 80 BData V4PRB2Data 36
    ((rectangularize 53 80 V4PRB3Data).getD 36 [])
  · decide
  · have hTargetSupport : (V4PRB3Data.getD 36 []).length ≤ 80 := by
      decide
    rw [getD_rectangularize 53 80 V4PRB3Data 36 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB3Row36_coefficients

private theorem v4PRB3Row37_coefficients (j : ℕ) (hj : j < 80) :
    mulCoeffTwo BData V4PRB2Data 37 j =
      ((rectangularize 53 80 V4PRB3Data).getD 37 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB3Row37_spec :
    padOne 80 (mulRow BData V4PRB2Data 37) =
      (rectangularize 53 80 V4PRB3Data).getD 37 [] := by
  apply padOne_mulRow_eq_of_coefficients 80 BData V4PRB2Data 37
    ((rectangularize 53 80 V4PRB3Data).getD 37 [])
  · decide
  · have hTargetSupport : (V4PRB3Data.getD 37 []).length ≤ 80 := by
      decide
    rw [getD_rectangularize 53 80 V4PRB3Data 37 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB3Row37_coefficients

private theorem v4PRB3Row38_coefficients (j : ℕ) (hj : j < 80) :
    mulCoeffTwo BData V4PRB2Data 38 j =
      ((rectangularize 53 80 V4PRB3Data).getD 38 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRB3Row38_spec :
    padOne 80 (mulRow BData V4PRB2Data 38) =
      (rectangularize 53 80 V4PRB3Data).getD 38 [] := by
  apply padOne_mulRow_eq_of_coefficients 80 BData V4PRB2Data 38
    ((rectangularize 53 80 V4PRB3Data).getD 38 [])
  · decide
  · have hTargetSupport : (V4PRB3Data.getD 38 []).length ≤ 80 := by
      decide
    rw [getD_rectangularize 53 80 V4PRB3Data 38 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRB3Row38_coefficients

private theorem v4PRB3Row39_spec :
    padOne 80 (mulRow BData V4PRB2Data 39) =
      (rectangularize 53 80 V4PRB3Data).getD 39 [] := by
  decide

private theorem v4PRB3Row40_spec :
    padOne 80 (mulRow BData V4PRB2Data 40) =
      (rectangularize 53 80 V4PRB3Data).getD 40 [] := by
  decide

private theorem v4PRB3Row41_spec :
    padOne 80 (mulRow BData V4PRB2Data 41) =
      (rectangularize 53 80 V4PRB3Data).getD 41 [] := by
  decide

private theorem v4PRB3Row42_spec :
    padOne 80 (mulRow BData V4PRB2Data 42) =
      (rectangularize 53 80 V4PRB3Data).getD 42 [] := by
  decide

private theorem v4PRB3Row43_spec :
    padOne 80 (mulRow BData V4PRB2Data 43) =
      (rectangularize 53 80 V4PRB3Data).getD 43 [] := by
  decide

private theorem v4PRB3Row44_spec :
    padOne 80 (mulRow BData V4PRB2Data 44) =
      (rectangularize 53 80 V4PRB3Data).getD 44 [] := by
  decide

private theorem v4PRB3Row45_spec :
    padOne 80 (mulRow BData V4PRB2Data 45) =
      (rectangularize 53 80 V4PRB3Data).getD 45 [] := by
  decide

private theorem v4PRB3Row46_spec :
    padOne 80 (mulRow BData V4PRB2Data 46) =
      (rectangularize 53 80 V4PRB3Data).getD 46 [] := by
  decide

private theorem v4PRB3Row47_spec :
    padOne 80 (mulRow BData V4PRB2Data 47) =
      (rectangularize 53 80 V4PRB3Data).getD 47 [] := by
  decide

private theorem v4PRB3Row48_spec :
    padOne 80 (mulRow BData V4PRB2Data 48) =
      (rectangularize 53 80 V4PRB3Data).getD 48 [] := by
  decide

private theorem v4PRB3Row49_spec :
    padOne 80 (mulRow BData V4PRB2Data 49) =
      (rectangularize 53 80 V4PRB3Data).getD 49 [] := by
  decide

private theorem v4PRB3Row50_spec :
    padOne 80 (mulRow BData V4PRB2Data 50) =
      (rectangularize 53 80 V4PRB3Data).getD 50 [] := by
  decide

private theorem v4PRB3Row51_spec :
    padOne 80 (mulRow BData V4PRB2Data 51) =
      (rectangularize 53 80 V4PRB3Data).getD 51 [] := by
  decide

private theorem v4PRB3Row52_spec :
    padOne 80 (mulRow BData V4PRB2Data 52) =
      (rectangularize 53 80 V4PRB3Data).getD 52 [] := by
  decide

private theorem v4PRB3Rows_spec (n : ℕ) (hn : n < 53) :
    padOne 80 (mulRow BData V4PRB2Data n) =
      (rectangularize 53 80 V4PRB3Data).getD n [] := by
  have hCases :
    n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨
    n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨
    n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨
    n = 15 ∨ n = 16 ∨ n = 17 ∨ n = 18 ∨ n = 19 ∨
    n = 20 ∨ n = 21 ∨ n = 22 ∨ n = 23 ∨ n = 24 ∨
    n = 25 ∨ n = 26 ∨ n = 27 ∨ n = 28 ∨ n = 29 ∨
    n = 30 ∨ n = 31 ∨ n = 32 ∨ n = 33 ∨ n = 34 ∨
    n = 35 ∨ n = 36 ∨ n = 37 ∨ n = 38 ∨ n = 39 ∨
    n = 40 ∨ n = 41 ∨ n = 42 ∨ n = 43 ∨ n = 44 ∨
    n = 45 ∨ n = 46 ∨ n = 47 ∨ n = 48 ∨ n = 49 ∨
    n = 50 ∨ n = 51 ∨ n = 52 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · exact v4PRB3Row0_spec
  · exact v4PRB3Row1_spec
  · exact v4PRB3Row2_spec
  · exact v4PRB3Row3_spec
  · exact v4PRB3Row4_spec
  · exact v4PRB3Row5_spec
  · exact v4PRB3Row6_spec
  · exact v4PRB3Row7_spec
  · exact v4PRB3Row8_spec
  · exact v4PRB3Row9_spec
  · exact v4PRB3Row10_spec
  · exact v4PRB3Row11_spec
  · exact v4PRB3Row12_spec
  · exact v4PRB3Row13_spec
  · exact v4PRB3Row14_spec
  · exact v4PRB3Row15_spec
  · exact v4PRB3Row16_spec
  · exact v4PRB3Row17_spec
  · exact v4PRB3Row18_spec
  · exact v4PRB3Row19_spec
  · exact v4PRB3Row20_spec
  · exact v4PRB3Row21_spec
  · exact v4PRB3Row22_spec
  · exact v4PRB3Row23_spec
  · exact v4PRB3Row24_spec
  · exact v4PRB3Row25_spec
  · exact v4PRB3Row26_spec
  · exact v4PRB3Row27_spec
  · exact v4PRB3Row28_spec
  · exact v4PRB3Row29_spec
  · exact v4PRB3Row30_spec
  · exact v4PRB3Row31_spec
  · exact v4PRB3Row32_spec
  · exact v4PRB3Row33_spec
  · exact v4PRB3Row34_spec
  · exact v4PRB3Row35_spec
  · exact v4PRB3Row36_spec
  · exact v4PRB3Row37_spec
  · exact v4PRB3Row38_spec
  · exact v4PRB3Row39_spec
  · exact v4PRB3Row40_spec
  · exact v4PRB3Row41_spec
  · exact v4PRB3Row42_spec
  · exact v4PRB3Row43_spec
  · exact v4PRB3Row44_spec
  · exact v4PRB3Row45_spec
  · exact v4PRB3Row46_spec
  · exact v4PRB3Row47_spec
  · exact v4PRB3Row48_spec
  · exact v4PRB3Row49_spec
  · exact v4PRB3Row50_spec
  · exact v4PRB3Row51_spec
  · exact v4PRB3Row52_spec

private theorem v4PRB3Left_length :
    (rectangularize 53 80 (Two.mul BData V4PRB2Data)).length = 53 := by
  decide

private theorem v4PRB3Right_length :
    (rectangularize 53 80 V4PRB3Data).length = 53 := by
  decide

-- Exact bidegree bound (52, 79); no row or column is discarded.
private theorem v4PRB3Data_spec :
    rectangularize 53 80 (Two.mul BData V4PRB2Data) =
      rectangularize 53 80 V4PRB3Data := by
  apply List.ext_getElem (v4PRB3Left_length.trans v4PRB3Right_length.symm)
  intro n hn _
  rw [List.getElem_eq_getD [], List.getElem_eq_getD []]
  rw [v4PRB3Left_length] at hn
  rw [getD_rectangularize 53 80 (Two.mul BData V4PRB2Data) n hn,
    ← mulRow_eq_getD]
  exact v4PRB3Rows_spec n hn

private theorem v4PRGRow0_spec :
    padOne 82 (mulRow GData V4PRB3Data 0) =
      (rectangularize 54 82 V4PRGData).getD 0 [] := by
  decide

private theorem v4PRGRow1_spec :
    padOne 82 (mulRow GData V4PRB3Data 1) =
      (rectangularize 54 82 V4PRGData).getD 1 [] := by
  decide

private theorem v4PRGRow2_spec :
    padOne 82 (mulRow GData V4PRB3Data 2) =
      (rectangularize 54 82 V4PRGData).getD 2 [] := by
  decide

private theorem v4PRGRow3_spec :
    padOne 82 (mulRow GData V4PRB3Data 3) =
      (rectangularize 54 82 V4PRGData).getD 3 [] := by
  decide

private theorem v4PRGRow4_spec :
    padOne 82 (mulRow GData V4PRB3Data 4) =
      (rectangularize 54 82 V4PRGData).getD 4 [] := by
  decide

private theorem v4PRGRow5_spec :
    padOne 82 (mulRow GData V4PRB3Data 5) =
      (rectangularize 54 82 V4PRGData).getD 5 [] := by
  decide

private theorem v4PRGRow6_spec :
    padOne 82 (mulRow GData V4PRB3Data 6) =
      (rectangularize 54 82 V4PRGData).getD 6 [] := by
  decide

private theorem v4PRGRow7_spec :
    padOne 82 (mulRow GData V4PRB3Data 7) =
      (rectangularize 54 82 V4PRGData).getD 7 [] := by
  decide

private theorem v4PRGRow8_spec :
    padOne 82 (mulRow GData V4PRB3Data 8) =
      (rectangularize 54 82 V4PRGData).getD 8 [] := by
  decide

private theorem v4PRGRow9_spec :
    padOne 82 (mulRow GData V4PRB3Data 9) =
      (rectangularize 54 82 V4PRGData).getD 9 [] := by
  decide

private theorem v4PRGRow10_spec :
    padOne 82 (mulRow GData V4PRB3Data 10) =
      (rectangularize 54 82 V4PRGData).getD 10 [] := by
  decide

private theorem v4PRGRow11_spec :
    padOne 82 (mulRow GData V4PRB3Data 11) =
      (rectangularize 54 82 V4PRGData).getD 11 [] := by
  decide

private theorem v4PRGRow12_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo GData V4PRB3Data 12 j =
      ((rectangularize 54 82 V4PRGData).getD 12 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRGRow12_spec :
    padOne 82 (mulRow GData V4PRB3Data 12) =
      (rectangularize 54 82 V4PRGData).getD 12 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 GData V4PRB3Data 12
    ((rectangularize 54 82 V4PRGData).getD 12 [])
  · decide
  · have hTargetSupport : (V4PRGData.getD 12 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 54 82 V4PRGData 12 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRGRow12_coefficients

private theorem v4PRGRow13_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo GData V4PRB3Data 13 j =
      ((rectangularize 54 82 V4PRGData).getD 13 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRGRow13_spec :
    padOne 82 (mulRow GData V4PRB3Data 13) =
      (rectangularize 54 82 V4PRGData).getD 13 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 GData V4PRB3Data 13
    ((rectangularize 54 82 V4PRGData).getD 13 [])
  · decide
  · have hTargetSupport : (V4PRGData.getD 13 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 54 82 V4PRGData 13 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRGRow13_coefficients

private theorem v4PRGRow14_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo GData V4PRB3Data 14 j =
      ((rectangularize 54 82 V4PRGData).getD 14 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRGRow14_spec :
    padOne 82 (mulRow GData V4PRB3Data 14) =
      (rectangularize 54 82 V4PRGData).getD 14 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 GData V4PRB3Data 14
    ((rectangularize 54 82 V4PRGData).getD 14 [])
  · decide
  · have hTargetSupport : (V4PRGData.getD 14 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 54 82 V4PRGData 14 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRGRow14_coefficients

private theorem v4PRGRow15_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo GData V4PRB3Data 15 j =
      ((rectangularize 54 82 V4PRGData).getD 15 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRGRow15_spec :
    padOne 82 (mulRow GData V4PRB3Data 15) =
      (rectangularize 54 82 V4PRGData).getD 15 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 GData V4PRB3Data 15
    ((rectangularize 54 82 V4PRGData).getD 15 [])
  · decide
  · have hTargetSupport : (V4PRGData.getD 15 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 54 82 V4PRGData 15 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRGRow15_coefficients

private theorem v4PRGRow16_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo GData V4PRB3Data 16 j =
      ((rectangularize 54 82 V4PRGData).getD 16 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRGRow16_spec :
    padOne 82 (mulRow GData V4PRB3Data 16) =
      (rectangularize 54 82 V4PRGData).getD 16 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 GData V4PRB3Data 16
    ((rectangularize 54 82 V4PRGData).getD 16 [])
  · decide
  · have hTargetSupport : (V4PRGData.getD 16 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 54 82 V4PRGData 16 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRGRow16_coefficients

private theorem v4PRGRow17_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo GData V4PRB3Data 17 j =
      ((rectangularize 54 82 V4PRGData).getD 17 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRGRow17_spec :
    padOne 82 (mulRow GData V4PRB3Data 17) =
      (rectangularize 54 82 V4PRGData).getD 17 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 GData V4PRB3Data 17
    ((rectangularize 54 82 V4PRGData).getD 17 [])
  · decide
  · have hTargetSupport : (V4PRGData.getD 17 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 54 82 V4PRGData 17 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRGRow17_coefficients

private theorem v4PRGRow18_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo GData V4PRB3Data 18 j =
      ((rectangularize 54 82 V4PRGData).getD 18 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRGRow18_spec :
    padOne 82 (mulRow GData V4PRB3Data 18) =
      (rectangularize 54 82 V4PRGData).getD 18 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 GData V4PRB3Data 18
    ((rectangularize 54 82 V4PRGData).getD 18 [])
  · decide
  · have hTargetSupport : (V4PRGData.getD 18 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 54 82 V4PRGData 18 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRGRow18_coefficients

private theorem v4PRGRow19_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo GData V4PRB3Data 19 j =
      ((rectangularize 54 82 V4PRGData).getD 19 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRGRow19_spec :
    padOne 82 (mulRow GData V4PRB3Data 19) =
      (rectangularize 54 82 V4PRGData).getD 19 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 GData V4PRB3Data 19
    ((rectangularize 54 82 V4PRGData).getD 19 [])
  · decide
  · have hTargetSupport : (V4PRGData.getD 19 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 54 82 V4PRGData 19 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRGRow19_coefficients

private theorem v4PRGRow20_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo GData V4PRB3Data 20 j =
      ((rectangularize 54 82 V4PRGData).getD 20 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRGRow20_spec :
    padOne 82 (mulRow GData V4PRB3Data 20) =
      (rectangularize 54 82 V4PRGData).getD 20 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 GData V4PRB3Data 20
    ((rectangularize 54 82 V4PRGData).getD 20 [])
  · decide
  · have hTargetSupport : (V4PRGData.getD 20 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 54 82 V4PRGData 20 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRGRow20_coefficients

private theorem v4PRGRow21_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo GData V4PRB3Data 21 j =
      ((rectangularize 54 82 V4PRGData).getD 21 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRGRow21_spec :
    padOne 82 (mulRow GData V4PRB3Data 21) =
      (rectangularize 54 82 V4PRGData).getD 21 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 GData V4PRB3Data 21
    ((rectangularize 54 82 V4PRGData).getD 21 [])
  · decide
  · have hTargetSupport : (V4PRGData.getD 21 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 54 82 V4PRGData 21 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRGRow21_coefficients

private theorem v4PRGRow22_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo GData V4PRB3Data 22 j =
      ((rectangularize 54 82 V4PRGData).getD 22 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRGRow22_spec :
    padOne 82 (mulRow GData V4PRB3Data 22) =
      (rectangularize 54 82 V4PRGData).getD 22 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 GData V4PRB3Data 22
    ((rectangularize 54 82 V4PRGData).getD 22 [])
  · decide
  · have hTargetSupport : (V4PRGData.getD 22 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 54 82 V4PRGData 22 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRGRow22_coefficients

private theorem v4PRGRow23_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo GData V4PRB3Data 23 j =
      ((rectangularize 54 82 V4PRGData).getD 23 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRGRow23_spec :
    padOne 82 (mulRow GData V4PRB3Data 23) =
      (rectangularize 54 82 V4PRGData).getD 23 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 GData V4PRB3Data 23
    ((rectangularize 54 82 V4PRGData).getD 23 [])
  · decide
  · have hTargetSupport : (V4PRGData.getD 23 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 54 82 V4PRGData 23 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRGRow23_coefficients

private theorem v4PRGRow24_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo GData V4PRB3Data 24 j =
      ((rectangularize 54 82 V4PRGData).getD 24 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRGRow24_spec :
    padOne 82 (mulRow GData V4PRB3Data 24) =
      (rectangularize 54 82 V4PRGData).getD 24 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 GData V4PRB3Data 24
    ((rectangularize 54 82 V4PRGData).getD 24 [])
  · decide
  · have hTargetSupport : (V4PRGData.getD 24 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 54 82 V4PRGData 24 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRGRow24_coefficients

private theorem v4PRGRow25_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo GData V4PRB3Data 25 j =
      ((rectangularize 54 82 V4PRGData).getD 25 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRGRow25_spec :
    padOne 82 (mulRow GData V4PRB3Data 25) =
      (rectangularize 54 82 V4PRGData).getD 25 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 GData V4PRB3Data 25
    ((rectangularize 54 82 V4PRGData).getD 25 [])
  · decide
  · have hTargetSupport : (V4PRGData.getD 25 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 54 82 V4PRGData 25 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRGRow25_coefficients

private theorem v4PRGRow26_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo GData V4PRB3Data 26 j =
      ((rectangularize 54 82 V4PRGData).getD 26 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRGRow26_spec :
    padOne 82 (mulRow GData V4PRB3Data 26) =
      (rectangularize 54 82 V4PRGData).getD 26 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 GData V4PRB3Data 26
    ((rectangularize 54 82 V4PRGData).getD 26 [])
  · decide
  · have hTargetSupport : (V4PRGData.getD 26 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 54 82 V4PRGData 26 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRGRow26_coefficients

private theorem v4PRGRow27_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo GData V4PRB3Data 27 j =
      ((rectangularize 54 82 V4PRGData).getD 27 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRGRow27_spec :
    padOne 82 (mulRow GData V4PRB3Data 27) =
      (rectangularize 54 82 V4PRGData).getD 27 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 GData V4PRB3Data 27
    ((rectangularize 54 82 V4PRGData).getD 27 [])
  · decide
  · have hTargetSupport : (V4PRGData.getD 27 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 54 82 V4PRGData 27 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRGRow27_coefficients

private theorem v4PRGRow28_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo GData V4PRB3Data 28 j =
      ((rectangularize 54 82 V4PRGData).getD 28 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRGRow28_spec :
    padOne 82 (mulRow GData V4PRB3Data 28) =
      (rectangularize 54 82 V4PRGData).getD 28 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 GData V4PRB3Data 28
    ((rectangularize 54 82 V4PRGData).getD 28 [])
  · decide
  · have hTargetSupport : (V4PRGData.getD 28 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 54 82 V4PRGData 28 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRGRow28_coefficients

private theorem v4PRGRow29_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo GData V4PRB3Data 29 j =
      ((rectangularize 54 82 V4PRGData).getD 29 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRGRow29_spec :
    padOne 82 (mulRow GData V4PRB3Data 29) =
      (rectangularize 54 82 V4PRGData).getD 29 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 GData V4PRB3Data 29
    ((rectangularize 54 82 V4PRGData).getD 29 [])
  · decide
  · have hTargetSupport : (V4PRGData.getD 29 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 54 82 V4PRGData 29 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRGRow29_coefficients

private theorem v4PRGRow30_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo GData V4PRB3Data 30 j =
      ((rectangularize 54 82 V4PRGData).getD 30 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRGRow30_spec :
    padOne 82 (mulRow GData V4PRB3Data 30) =
      (rectangularize 54 82 V4PRGData).getD 30 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 GData V4PRB3Data 30
    ((rectangularize 54 82 V4PRGData).getD 30 [])
  · decide
  · have hTargetSupport : (V4PRGData.getD 30 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 54 82 V4PRGData 30 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRGRow30_coefficients

private theorem v4PRGRow31_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo GData V4PRB3Data 31 j =
      ((rectangularize 54 82 V4PRGData).getD 31 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRGRow31_spec :
    padOne 82 (mulRow GData V4PRB3Data 31) =
      (rectangularize 54 82 V4PRGData).getD 31 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 GData V4PRB3Data 31
    ((rectangularize 54 82 V4PRGData).getD 31 [])
  · decide
  · have hTargetSupport : (V4PRGData.getD 31 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 54 82 V4PRGData 31 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRGRow31_coefficients

private theorem v4PRGRow32_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo GData V4PRB3Data 32 j =
      ((rectangularize 54 82 V4PRGData).getD 32 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRGRow32_spec :
    padOne 82 (mulRow GData V4PRB3Data 32) =
      (rectangularize 54 82 V4PRGData).getD 32 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 GData V4PRB3Data 32
    ((rectangularize 54 82 V4PRGData).getD 32 [])
  · decide
  · have hTargetSupport : (V4PRGData.getD 32 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 54 82 V4PRGData 32 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRGRow32_coefficients

private theorem v4PRGRow33_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo GData V4PRB3Data 33 j =
      ((rectangularize 54 82 V4PRGData).getD 33 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRGRow33_spec :
    padOne 82 (mulRow GData V4PRB3Data 33) =
      (rectangularize 54 82 V4PRGData).getD 33 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 GData V4PRB3Data 33
    ((rectangularize 54 82 V4PRGData).getD 33 [])
  · decide
  · have hTargetSupport : (V4PRGData.getD 33 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 54 82 V4PRGData 33 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRGRow33_coefficients

private theorem v4PRGRow34_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo GData V4PRB3Data 34 j =
      ((rectangularize 54 82 V4PRGData).getD 34 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRGRow34_spec :
    padOne 82 (mulRow GData V4PRB3Data 34) =
      (rectangularize 54 82 V4PRGData).getD 34 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 GData V4PRB3Data 34
    ((rectangularize 54 82 V4PRGData).getD 34 [])
  · decide
  · have hTargetSupport : (V4PRGData.getD 34 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 54 82 V4PRGData 34 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRGRow34_coefficients

private theorem v4PRGRow35_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo GData V4PRB3Data 35 j =
      ((rectangularize 54 82 V4PRGData).getD 35 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRGRow35_spec :
    padOne 82 (mulRow GData V4PRB3Data 35) =
      (rectangularize 54 82 V4PRGData).getD 35 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 GData V4PRB3Data 35
    ((rectangularize 54 82 V4PRGData).getD 35 [])
  · decide
  · have hTargetSupport : (V4PRGData.getD 35 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 54 82 V4PRGData 35 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRGRow35_coefficients

private theorem v4PRGRow36_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo GData V4PRB3Data 36 j =
      ((rectangularize 54 82 V4PRGData).getD 36 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRGRow36_spec :
    padOne 82 (mulRow GData V4PRB3Data 36) =
      (rectangularize 54 82 V4PRGData).getD 36 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 GData V4PRB3Data 36
    ((rectangularize 54 82 V4PRGData).getD 36 [])
  · decide
  · have hTargetSupport : (V4PRGData.getD 36 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 54 82 V4PRGData 36 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRGRow36_coefficients

private theorem v4PRGRow37_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo GData V4PRB3Data 37 j =
      ((rectangularize 54 82 V4PRGData).getD 37 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRGRow37_spec :
    padOne 82 (mulRow GData V4PRB3Data 37) =
      (rectangularize 54 82 V4PRGData).getD 37 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 GData V4PRB3Data 37
    ((rectangularize 54 82 V4PRGData).getD 37 [])
  · decide
  · have hTargetSupport : (V4PRGData.getD 37 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 54 82 V4PRGData 37 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRGRow37_coefficients

private theorem v4PRGRow38_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo GData V4PRB3Data 38 j =
      ((rectangularize 54 82 V4PRGData).getD 38 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRGRow38_spec :
    padOne 82 (mulRow GData V4PRB3Data 38) =
      (rectangularize 54 82 V4PRGData).getD 38 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 GData V4PRB3Data 38
    ((rectangularize 54 82 V4PRGData).getD 38 [])
  · decide
  · have hTargetSupport : (V4PRGData.getD 38 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 54 82 V4PRGData 38 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRGRow38_coefficients

private theorem v4PRGRow39_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo GData V4PRB3Data 39 j =
      ((rectangularize 54 82 V4PRGData).getD 39 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRGRow39_spec :
    padOne 82 (mulRow GData V4PRB3Data 39) =
      (rectangularize 54 82 V4PRGData).getD 39 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 GData V4PRB3Data 39
    ((rectangularize 54 82 V4PRGData).getD 39 [])
  · decide
  · have hTargetSupport : (V4PRGData.getD 39 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 54 82 V4PRGData 39 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRGRow39_coefficients

private theorem v4PRGRow40_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo GData V4PRB3Data 40 j =
      ((rectangularize 54 82 V4PRGData).getD 40 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRGRow40_spec :
    padOne 82 (mulRow GData V4PRB3Data 40) =
      (rectangularize 54 82 V4PRGData).getD 40 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 GData V4PRB3Data 40
    ((rectangularize 54 82 V4PRGData).getD 40 [])
  · decide
  · have hTargetSupport : (V4PRGData.getD 40 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 54 82 V4PRGData 40 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRGRow40_coefficients

private theorem v4PRGRow41_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo GData V4PRB3Data 41 j =
      ((rectangularize 54 82 V4PRGData).getD 41 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRGRow41_spec :
    padOne 82 (mulRow GData V4PRB3Data 41) =
      (rectangularize 54 82 V4PRGData).getD 41 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 GData V4PRB3Data 41
    ((rectangularize 54 82 V4PRGData).getD 41 [])
  · decide
  · have hTargetSupport : (V4PRGData.getD 41 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 54 82 V4PRGData 41 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRGRow41_coefficients

private theorem v4PRGRow42_spec :
    padOne 82 (mulRow GData V4PRB3Data 42) =
      (rectangularize 54 82 V4PRGData).getD 42 [] := by
  decide

private theorem v4PRGRow43_spec :
    padOne 82 (mulRow GData V4PRB3Data 43) =
      (rectangularize 54 82 V4PRGData).getD 43 [] := by
  decide

private theorem v4PRGRow44_spec :
    padOne 82 (mulRow GData V4PRB3Data 44) =
      (rectangularize 54 82 V4PRGData).getD 44 [] := by
  decide

private theorem v4PRGRow45_spec :
    padOne 82 (mulRow GData V4PRB3Data 45) =
      (rectangularize 54 82 V4PRGData).getD 45 [] := by
  decide

private theorem v4PRGRow46_spec :
    padOne 82 (mulRow GData V4PRB3Data 46) =
      (rectangularize 54 82 V4PRGData).getD 46 [] := by
  decide

private theorem v4PRGRow47_spec :
    padOne 82 (mulRow GData V4PRB3Data 47) =
      (rectangularize 54 82 V4PRGData).getD 47 [] := by
  decide

private theorem v4PRGRow48_spec :
    padOne 82 (mulRow GData V4PRB3Data 48) =
      (rectangularize 54 82 V4PRGData).getD 48 [] := by
  decide

private theorem v4PRGRow49_spec :
    padOne 82 (mulRow GData V4PRB3Data 49) =
      (rectangularize 54 82 V4PRGData).getD 49 [] := by
  decide

private theorem v4PRGRow50_spec :
    padOne 82 (mulRow GData V4PRB3Data 50) =
      (rectangularize 54 82 V4PRGData).getD 50 [] := by
  decide

private theorem v4PRGRow51_spec :
    padOne 82 (mulRow GData V4PRB3Data 51) =
      (rectangularize 54 82 V4PRGData).getD 51 [] := by
  decide

private theorem v4PRGRow52_spec :
    padOne 82 (mulRow GData V4PRB3Data 52) =
      (rectangularize 54 82 V4PRGData).getD 52 [] := by
  decide

private theorem v4PRGRow53_spec :
    padOne 82 (mulRow GData V4PRB3Data 53) =
      (rectangularize 54 82 V4PRGData).getD 53 [] := by
  decide

private theorem v4PRGRows_spec (n : ℕ) (hn : n < 54) :
    padOne 82 (mulRow GData V4PRB3Data n) =
      (rectangularize 54 82 V4PRGData).getD n [] := by
  have hCases :
    n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨
    n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨
    n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨
    n = 15 ∨ n = 16 ∨ n = 17 ∨ n = 18 ∨ n = 19 ∨
    n = 20 ∨ n = 21 ∨ n = 22 ∨ n = 23 ∨ n = 24 ∨
    n = 25 ∨ n = 26 ∨ n = 27 ∨ n = 28 ∨ n = 29 ∨
    n = 30 ∨ n = 31 ∨ n = 32 ∨ n = 33 ∨ n = 34 ∨
    n = 35 ∨ n = 36 ∨ n = 37 ∨ n = 38 ∨ n = 39 ∨
    n = 40 ∨ n = 41 ∨ n = 42 ∨ n = 43 ∨ n = 44 ∨
    n = 45 ∨ n = 46 ∨ n = 47 ∨ n = 48 ∨ n = 49 ∨
    n = 50 ∨ n = 51 ∨ n = 52 ∨ n = 53 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact v4PRGRow0_spec
  · exact v4PRGRow1_spec
  · exact v4PRGRow2_spec
  · exact v4PRGRow3_spec
  · exact v4PRGRow4_spec
  · exact v4PRGRow5_spec
  · exact v4PRGRow6_spec
  · exact v4PRGRow7_spec
  · exact v4PRGRow8_spec
  · exact v4PRGRow9_spec
  · exact v4PRGRow10_spec
  · exact v4PRGRow11_spec
  · exact v4PRGRow12_spec
  · exact v4PRGRow13_spec
  · exact v4PRGRow14_spec
  · exact v4PRGRow15_spec
  · exact v4PRGRow16_spec
  · exact v4PRGRow17_spec
  · exact v4PRGRow18_spec
  · exact v4PRGRow19_spec
  · exact v4PRGRow20_spec
  · exact v4PRGRow21_spec
  · exact v4PRGRow22_spec
  · exact v4PRGRow23_spec
  · exact v4PRGRow24_spec
  · exact v4PRGRow25_spec
  · exact v4PRGRow26_spec
  · exact v4PRGRow27_spec
  · exact v4PRGRow28_spec
  · exact v4PRGRow29_spec
  · exact v4PRGRow30_spec
  · exact v4PRGRow31_spec
  · exact v4PRGRow32_spec
  · exact v4PRGRow33_spec
  · exact v4PRGRow34_spec
  · exact v4PRGRow35_spec
  · exact v4PRGRow36_spec
  · exact v4PRGRow37_spec
  · exact v4PRGRow38_spec
  · exact v4PRGRow39_spec
  · exact v4PRGRow40_spec
  · exact v4PRGRow41_spec
  · exact v4PRGRow42_spec
  · exact v4PRGRow43_spec
  · exact v4PRGRow44_spec
  · exact v4PRGRow45_spec
  · exact v4PRGRow46_spec
  · exact v4PRGRow47_spec
  · exact v4PRGRow48_spec
  · exact v4PRGRow49_spec
  · exact v4PRGRow50_spec
  · exact v4PRGRow51_spec
  · exact v4PRGRow52_spec
  · exact v4PRGRow53_spec

private theorem v4PRGLeft_length :
    (rectangularize 54 82 (Two.mul GData V4PRB3Data)).length = 54 := by
  decide

private theorem v4PRGRight_length :
    (rectangularize 54 82 V4PRGData).length = 54 := by
  decide

-- Exact bidegree bound (53, 81); no row or column is discarded.
private theorem v4PRGData_spec :
    rectangularize 54 82 (Two.mul GData V4PRB3Data) =
      rectangularize 54 82 V4PRGData := by
  apply List.ext_getElem (v4PRGLeft_length.trans v4PRGRight_length.symm)
  intro n hn _
  rw [List.getElem_eq_getD [], List.getElem_eq_getD []]
  rw [v4PRGLeft_length] at hn
  rw [getD_rectangularize 54 82 (Two.mul GData V4PRB3Data) n hn,
    ← mulRow_eq_getD]
  exact v4PRGRows_spec n hn

private theorem v4PRE1Row0_spec :
    padOne 84 (mulRow EData V4PRGData 0) =
      (rectangularize 56 84 V4PRE1Data).getD 0 [] := by
  decide

private theorem v4PRE1Row1_spec :
    padOne 84 (mulRow EData V4PRGData 1) =
      (rectangularize 56 84 V4PRE1Data).getD 1 [] := by
  decide

private theorem v4PRE1Row2_spec :
    padOne 84 (mulRow EData V4PRGData 2) =
      (rectangularize 56 84 V4PRE1Data).getD 2 [] := by
  decide

private theorem v4PRE1Row3_spec :
    padOne 84 (mulRow EData V4PRGData 3) =
      (rectangularize 56 84 V4PRE1Data).getD 3 [] := by
  decide

private theorem v4PRE1Row4_spec :
    padOne 84 (mulRow EData V4PRGData 4) =
      (rectangularize 56 84 V4PRE1Data).getD 4 [] := by
  decide

private theorem v4PRE1Row5_spec :
    padOne 84 (mulRow EData V4PRGData 5) =
      (rectangularize 56 84 V4PRE1Data).getD 5 [] := by
  decide

private theorem v4PRE1Row6_spec :
    padOne 84 (mulRow EData V4PRGData 6) =
      (rectangularize 56 84 V4PRE1Data).getD 6 [] := by
  decide

private theorem v4PRE1Row7_spec :
    padOne 84 (mulRow EData V4PRGData 7) =
      (rectangularize 56 84 V4PRE1Data).getD 7 [] := by
  decide

private theorem v4PRE1Row8_spec :
    padOne 84 (mulRow EData V4PRGData 8) =
      (rectangularize 56 84 V4PRE1Data).getD 8 [] := by
  decide

private theorem v4PRE1Row9_spec :
    padOne 84 (mulRow EData V4PRGData 9) =
      (rectangularize 56 84 V4PRE1Data).getD 9 [] := by
  decide

private theorem v4PRE1Row10_coefficients (j : ℕ) (hj : j < 84) :
    mulCoeffTwo EData V4PRGData 10 j =
      ((rectangularize 56 84 V4PRE1Data).getD 10 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE1Row10_spec :
    padOne 84 (mulRow EData V4PRGData 10) =
      (rectangularize 56 84 V4PRE1Data).getD 10 [] := by
  apply padOne_mulRow_eq_of_coefficients 84 EData V4PRGData 10
    ((rectangularize 56 84 V4PRE1Data).getD 10 [])
  · decide
  · have hTargetSupport : (V4PRE1Data.getD 10 []).length ≤ 84 := by
      decide
    rw [getD_rectangularize 56 84 V4PRE1Data 10 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE1Row10_coefficients

private theorem v4PRE1Row11_coefficients (j : ℕ) (hj : j < 84) :
    mulCoeffTwo EData V4PRGData 11 j =
      ((rectangularize 56 84 V4PRE1Data).getD 11 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE1Row11_spec :
    padOne 84 (mulRow EData V4PRGData 11) =
      (rectangularize 56 84 V4PRE1Data).getD 11 [] := by
  apply padOne_mulRow_eq_of_coefficients 84 EData V4PRGData 11
    ((rectangularize 56 84 V4PRE1Data).getD 11 [])
  · decide
  · have hTargetSupport : (V4PRE1Data.getD 11 []).length ≤ 84 := by
      decide
    rw [getD_rectangularize 56 84 V4PRE1Data 11 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE1Row11_coefficients

private theorem v4PRE1Row12_coefficients (j : ℕ) (hj : j < 84) :
    mulCoeffTwo EData V4PRGData 12 j =
      ((rectangularize 56 84 V4PRE1Data).getD 12 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE1Row12_spec :
    padOne 84 (mulRow EData V4PRGData 12) =
      (rectangularize 56 84 V4PRE1Data).getD 12 [] := by
  apply padOne_mulRow_eq_of_coefficients 84 EData V4PRGData 12
    ((rectangularize 56 84 V4PRE1Data).getD 12 [])
  · decide
  · have hTargetSupport : (V4PRE1Data.getD 12 []).length ≤ 84 := by
      decide
    rw [getD_rectangularize 56 84 V4PRE1Data 12 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE1Row12_coefficients

private theorem v4PRE1Row13_coefficients (j : ℕ) (hj : j < 84) :
    mulCoeffTwo EData V4PRGData 13 j =
      ((rectangularize 56 84 V4PRE1Data).getD 13 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE1Row13_spec :
    padOne 84 (mulRow EData V4PRGData 13) =
      (rectangularize 56 84 V4PRE1Data).getD 13 [] := by
  apply padOne_mulRow_eq_of_coefficients 84 EData V4PRGData 13
    ((rectangularize 56 84 V4PRE1Data).getD 13 [])
  · decide
  · have hTargetSupport : (V4PRE1Data.getD 13 []).length ≤ 84 := by
      decide
    rw [getD_rectangularize 56 84 V4PRE1Data 13 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE1Row13_coefficients

private theorem v4PRE1Row14_coefficients (j : ℕ) (hj : j < 84) :
    mulCoeffTwo EData V4PRGData 14 j =
      ((rectangularize 56 84 V4PRE1Data).getD 14 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE1Row14_spec :
    padOne 84 (mulRow EData V4PRGData 14) =
      (rectangularize 56 84 V4PRE1Data).getD 14 [] := by
  apply padOne_mulRow_eq_of_coefficients 84 EData V4PRGData 14
    ((rectangularize 56 84 V4PRE1Data).getD 14 [])
  · decide
  · have hTargetSupport : (V4PRE1Data.getD 14 []).length ≤ 84 := by
      decide
    rw [getD_rectangularize 56 84 V4PRE1Data 14 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE1Row14_coefficients

private theorem v4PRE1Row15_coefficients (j : ℕ) (hj : j < 84) :
    mulCoeffTwo EData V4PRGData 15 j =
      ((rectangularize 56 84 V4PRE1Data).getD 15 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE1Row15_spec :
    padOne 84 (mulRow EData V4PRGData 15) =
      (rectangularize 56 84 V4PRE1Data).getD 15 [] := by
  apply padOne_mulRow_eq_of_coefficients 84 EData V4PRGData 15
    ((rectangularize 56 84 V4PRE1Data).getD 15 [])
  · decide
  · have hTargetSupport : (V4PRE1Data.getD 15 []).length ≤ 84 := by
      decide
    rw [getD_rectangularize 56 84 V4PRE1Data 15 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE1Row15_coefficients

private theorem v4PRE1Row16_coefficients (j : ℕ) (hj : j < 84) :
    mulCoeffTwo EData V4PRGData 16 j =
      ((rectangularize 56 84 V4PRE1Data).getD 16 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE1Row16_spec :
    padOne 84 (mulRow EData V4PRGData 16) =
      (rectangularize 56 84 V4PRE1Data).getD 16 [] := by
  apply padOne_mulRow_eq_of_coefficients 84 EData V4PRGData 16
    ((rectangularize 56 84 V4PRE1Data).getD 16 [])
  · decide
  · have hTargetSupport : (V4PRE1Data.getD 16 []).length ≤ 84 := by
      decide
    rw [getD_rectangularize 56 84 V4PRE1Data 16 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE1Row16_coefficients

private theorem v4PRE1Row17_coefficients (j : ℕ) (hj : j < 84) :
    mulCoeffTwo EData V4PRGData 17 j =
      ((rectangularize 56 84 V4PRE1Data).getD 17 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE1Row17_spec :
    padOne 84 (mulRow EData V4PRGData 17) =
      (rectangularize 56 84 V4PRE1Data).getD 17 [] := by
  apply padOne_mulRow_eq_of_coefficients 84 EData V4PRGData 17
    ((rectangularize 56 84 V4PRE1Data).getD 17 [])
  · decide
  · have hTargetSupport : (V4PRE1Data.getD 17 []).length ≤ 84 := by
      decide
    rw [getD_rectangularize 56 84 V4PRE1Data 17 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE1Row17_coefficients

private theorem v4PRE1Row18_coefficients (j : ℕ) (hj : j < 84) :
    mulCoeffTwo EData V4PRGData 18 j =
      ((rectangularize 56 84 V4PRE1Data).getD 18 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE1Row18_spec :
    padOne 84 (mulRow EData V4PRGData 18) =
      (rectangularize 56 84 V4PRE1Data).getD 18 [] := by
  apply padOne_mulRow_eq_of_coefficients 84 EData V4PRGData 18
    ((rectangularize 56 84 V4PRE1Data).getD 18 [])
  · decide
  · have hTargetSupport : (V4PRE1Data.getD 18 []).length ≤ 84 := by
      decide
    rw [getD_rectangularize 56 84 V4PRE1Data 18 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE1Row18_coefficients

private theorem v4PRE1Row19_coefficients (j : ℕ) (hj : j < 84) :
    mulCoeffTwo EData V4PRGData 19 j =
      ((rectangularize 56 84 V4PRE1Data).getD 19 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE1Row19_spec :
    padOne 84 (mulRow EData V4PRGData 19) =
      (rectangularize 56 84 V4PRE1Data).getD 19 [] := by
  apply padOne_mulRow_eq_of_coefficients 84 EData V4PRGData 19
    ((rectangularize 56 84 V4PRE1Data).getD 19 [])
  · decide
  · have hTargetSupport : (V4PRE1Data.getD 19 []).length ≤ 84 := by
      decide
    rw [getD_rectangularize 56 84 V4PRE1Data 19 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE1Row19_coefficients

private theorem v4PRE1Row20_coefficients (j : ℕ) (hj : j < 84) :
    mulCoeffTwo EData V4PRGData 20 j =
      ((rectangularize 56 84 V4PRE1Data).getD 20 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE1Row20_spec :
    padOne 84 (mulRow EData V4PRGData 20) =
      (rectangularize 56 84 V4PRE1Data).getD 20 [] := by
  apply padOne_mulRow_eq_of_coefficients 84 EData V4PRGData 20
    ((rectangularize 56 84 V4PRE1Data).getD 20 [])
  · decide
  · have hTargetSupport : (V4PRE1Data.getD 20 []).length ≤ 84 := by
      decide
    rw [getD_rectangularize 56 84 V4PRE1Data 20 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE1Row20_coefficients

private theorem v4PRE1Row21_coefficients (j : ℕ) (hj : j < 84) :
    mulCoeffTwo EData V4PRGData 21 j =
      ((rectangularize 56 84 V4PRE1Data).getD 21 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE1Row21_spec :
    padOne 84 (mulRow EData V4PRGData 21) =
      (rectangularize 56 84 V4PRE1Data).getD 21 [] := by
  apply padOne_mulRow_eq_of_coefficients 84 EData V4PRGData 21
    ((rectangularize 56 84 V4PRE1Data).getD 21 [])
  · decide
  · have hTargetSupport : (V4PRE1Data.getD 21 []).length ≤ 84 := by
      decide
    rw [getD_rectangularize 56 84 V4PRE1Data 21 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE1Row21_coefficients

private theorem v4PRE1Row22_coefficients (j : ℕ) (hj : j < 84) :
    mulCoeffTwo EData V4PRGData 22 j =
      ((rectangularize 56 84 V4PRE1Data).getD 22 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE1Row22_spec :
    padOne 84 (mulRow EData V4PRGData 22) =
      (rectangularize 56 84 V4PRE1Data).getD 22 [] := by
  apply padOne_mulRow_eq_of_coefficients 84 EData V4PRGData 22
    ((rectangularize 56 84 V4PRE1Data).getD 22 [])
  · decide
  · have hTargetSupport : (V4PRE1Data.getD 22 []).length ≤ 84 := by
      decide
    rw [getD_rectangularize 56 84 V4PRE1Data 22 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE1Row22_coefficients

private theorem v4PRE1Row23_coefficients (j : ℕ) (hj : j < 84) :
    mulCoeffTwo EData V4PRGData 23 j =
      ((rectangularize 56 84 V4PRE1Data).getD 23 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE1Row23_spec :
    padOne 84 (mulRow EData V4PRGData 23) =
      (rectangularize 56 84 V4PRE1Data).getD 23 [] := by
  apply padOne_mulRow_eq_of_coefficients 84 EData V4PRGData 23
    ((rectangularize 56 84 V4PRE1Data).getD 23 [])
  · decide
  · have hTargetSupport : (V4PRE1Data.getD 23 []).length ≤ 84 := by
      decide
    rw [getD_rectangularize 56 84 V4PRE1Data 23 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE1Row23_coefficients

private theorem v4PRE1Row24_coefficients (j : ℕ) (hj : j < 84) :
    mulCoeffTwo EData V4PRGData 24 j =
      ((rectangularize 56 84 V4PRE1Data).getD 24 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE1Row24_spec :
    padOne 84 (mulRow EData V4PRGData 24) =
      (rectangularize 56 84 V4PRE1Data).getD 24 [] := by
  apply padOne_mulRow_eq_of_coefficients 84 EData V4PRGData 24
    ((rectangularize 56 84 V4PRE1Data).getD 24 [])
  · decide
  · have hTargetSupport : (V4PRE1Data.getD 24 []).length ≤ 84 := by
      decide
    rw [getD_rectangularize 56 84 V4PRE1Data 24 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE1Row24_coefficients

private theorem v4PRE1Row25_coefficients (j : ℕ) (hj : j < 84) :
    mulCoeffTwo EData V4PRGData 25 j =
      ((rectangularize 56 84 V4PRE1Data).getD 25 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE1Row25_spec :
    padOne 84 (mulRow EData V4PRGData 25) =
      (rectangularize 56 84 V4PRE1Data).getD 25 [] := by
  apply padOne_mulRow_eq_of_coefficients 84 EData V4PRGData 25
    ((rectangularize 56 84 V4PRE1Data).getD 25 [])
  · decide
  · have hTargetSupport : (V4PRE1Data.getD 25 []).length ≤ 84 := by
      decide
    rw [getD_rectangularize 56 84 V4PRE1Data 25 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE1Row25_coefficients

private theorem v4PRE1Row26_coefficients (j : ℕ) (hj : j < 84) :
    mulCoeffTwo EData V4PRGData 26 j =
      ((rectangularize 56 84 V4PRE1Data).getD 26 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE1Row26_spec :
    padOne 84 (mulRow EData V4PRGData 26) =
      (rectangularize 56 84 V4PRE1Data).getD 26 [] := by
  apply padOne_mulRow_eq_of_coefficients 84 EData V4PRGData 26
    ((rectangularize 56 84 V4PRE1Data).getD 26 [])
  · decide
  · have hTargetSupport : (V4PRE1Data.getD 26 []).length ≤ 84 := by
      decide
    rw [getD_rectangularize 56 84 V4PRE1Data 26 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE1Row26_coefficients

private theorem v4PRE1Row27_coefficients (j : ℕ) (hj : j < 84) :
    mulCoeffTwo EData V4PRGData 27 j =
      ((rectangularize 56 84 V4PRE1Data).getD 27 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE1Row27_spec :
    padOne 84 (mulRow EData V4PRGData 27) =
      (rectangularize 56 84 V4PRE1Data).getD 27 [] := by
  apply padOne_mulRow_eq_of_coefficients 84 EData V4PRGData 27
    ((rectangularize 56 84 V4PRE1Data).getD 27 [])
  · decide
  · have hTargetSupport : (V4PRE1Data.getD 27 []).length ≤ 84 := by
      decide
    rw [getD_rectangularize 56 84 V4PRE1Data 27 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE1Row27_coefficients

private theorem v4PRE1Row28_coefficients (j : ℕ) (hj : j < 84) :
    mulCoeffTwo EData V4PRGData 28 j =
      ((rectangularize 56 84 V4PRE1Data).getD 28 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE1Row28_spec :
    padOne 84 (mulRow EData V4PRGData 28) =
      (rectangularize 56 84 V4PRE1Data).getD 28 [] := by
  apply padOne_mulRow_eq_of_coefficients 84 EData V4PRGData 28
    ((rectangularize 56 84 V4PRE1Data).getD 28 [])
  · decide
  · have hTargetSupport : (V4PRE1Data.getD 28 []).length ≤ 84 := by
      decide
    rw [getD_rectangularize 56 84 V4PRE1Data 28 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE1Row28_coefficients

private theorem v4PRE1Row29_coefficients (j : ℕ) (hj : j < 84) :
    mulCoeffTwo EData V4PRGData 29 j =
      ((rectangularize 56 84 V4PRE1Data).getD 29 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE1Row29_spec :
    padOne 84 (mulRow EData V4PRGData 29) =
      (rectangularize 56 84 V4PRE1Data).getD 29 [] := by
  apply padOne_mulRow_eq_of_coefficients 84 EData V4PRGData 29
    ((rectangularize 56 84 V4PRE1Data).getD 29 [])
  · decide
  · have hTargetSupport : (V4PRE1Data.getD 29 []).length ≤ 84 := by
      decide
    rw [getD_rectangularize 56 84 V4PRE1Data 29 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE1Row29_coefficients

private theorem v4PRE1Row30_coefficients (j : ℕ) (hj : j < 84) :
    mulCoeffTwo EData V4PRGData 30 j =
      ((rectangularize 56 84 V4PRE1Data).getD 30 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE1Row30_spec :
    padOne 84 (mulRow EData V4PRGData 30) =
      (rectangularize 56 84 V4PRE1Data).getD 30 [] := by
  apply padOne_mulRow_eq_of_coefficients 84 EData V4PRGData 30
    ((rectangularize 56 84 V4PRE1Data).getD 30 [])
  · decide
  · have hTargetSupport : (V4PRE1Data.getD 30 []).length ≤ 84 := by
      decide
    rw [getD_rectangularize 56 84 V4PRE1Data 30 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE1Row30_coefficients

private theorem v4PRE1Row31_coefficients (j : ℕ) (hj : j < 84) :
    mulCoeffTwo EData V4PRGData 31 j =
      ((rectangularize 56 84 V4PRE1Data).getD 31 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE1Row31_spec :
    padOne 84 (mulRow EData V4PRGData 31) =
      (rectangularize 56 84 V4PRE1Data).getD 31 [] := by
  apply padOne_mulRow_eq_of_coefficients 84 EData V4PRGData 31
    ((rectangularize 56 84 V4PRE1Data).getD 31 [])
  · decide
  · have hTargetSupport : (V4PRE1Data.getD 31 []).length ≤ 84 := by
      decide
    rw [getD_rectangularize 56 84 V4PRE1Data 31 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE1Row31_coefficients

private theorem v4PRE1Row32_coefficients (j : ℕ) (hj : j < 84) :
    mulCoeffTwo EData V4PRGData 32 j =
      ((rectangularize 56 84 V4PRE1Data).getD 32 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE1Row32_spec :
    padOne 84 (mulRow EData V4PRGData 32) =
      (rectangularize 56 84 V4PRE1Data).getD 32 [] := by
  apply padOne_mulRow_eq_of_coefficients 84 EData V4PRGData 32
    ((rectangularize 56 84 V4PRE1Data).getD 32 [])
  · decide
  · have hTargetSupport : (V4PRE1Data.getD 32 []).length ≤ 84 := by
      decide
    rw [getD_rectangularize 56 84 V4PRE1Data 32 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE1Row32_coefficients

private theorem v4PRE1Row33_coefficients (j : ℕ) (hj : j < 84) :
    mulCoeffTwo EData V4PRGData 33 j =
      ((rectangularize 56 84 V4PRE1Data).getD 33 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE1Row33_spec :
    padOne 84 (mulRow EData V4PRGData 33) =
      (rectangularize 56 84 V4PRE1Data).getD 33 [] := by
  apply padOne_mulRow_eq_of_coefficients 84 EData V4PRGData 33
    ((rectangularize 56 84 V4PRE1Data).getD 33 [])
  · decide
  · have hTargetSupport : (V4PRE1Data.getD 33 []).length ≤ 84 := by
      decide
    rw [getD_rectangularize 56 84 V4PRE1Data 33 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE1Row33_coefficients

private theorem v4PRE1Row34_coefficients (j : ℕ) (hj : j < 84) :
    mulCoeffTwo EData V4PRGData 34 j =
      ((rectangularize 56 84 V4PRE1Data).getD 34 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE1Row34_spec :
    padOne 84 (mulRow EData V4PRGData 34) =
      (rectangularize 56 84 V4PRE1Data).getD 34 [] := by
  apply padOne_mulRow_eq_of_coefficients 84 EData V4PRGData 34
    ((rectangularize 56 84 V4PRE1Data).getD 34 [])
  · decide
  · have hTargetSupport : (V4PRE1Data.getD 34 []).length ≤ 84 := by
      decide
    rw [getD_rectangularize 56 84 V4PRE1Data 34 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE1Row34_coefficients

private theorem v4PRE1Row35_coefficients (j : ℕ) (hj : j < 84) :
    mulCoeffTwo EData V4PRGData 35 j =
      ((rectangularize 56 84 V4PRE1Data).getD 35 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE1Row35_spec :
    padOne 84 (mulRow EData V4PRGData 35) =
      (rectangularize 56 84 V4PRE1Data).getD 35 [] := by
  apply padOne_mulRow_eq_of_coefficients 84 EData V4PRGData 35
    ((rectangularize 56 84 V4PRE1Data).getD 35 [])
  · decide
  · have hTargetSupport : (V4PRE1Data.getD 35 []).length ≤ 84 := by
      decide
    rw [getD_rectangularize 56 84 V4PRE1Data 35 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE1Row35_coefficients

private theorem v4PRE1Row36_coefficients (j : ℕ) (hj : j < 84) :
    mulCoeffTwo EData V4PRGData 36 j =
      ((rectangularize 56 84 V4PRE1Data).getD 36 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE1Row36_spec :
    padOne 84 (mulRow EData V4PRGData 36) =
      (rectangularize 56 84 V4PRE1Data).getD 36 [] := by
  apply padOne_mulRow_eq_of_coefficients 84 EData V4PRGData 36
    ((rectangularize 56 84 V4PRE1Data).getD 36 [])
  · decide
  · have hTargetSupport : (V4PRE1Data.getD 36 []).length ≤ 84 := by
      decide
    rw [getD_rectangularize 56 84 V4PRE1Data 36 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE1Row36_coefficients

private theorem v4PRE1Row37_coefficients (j : ℕ) (hj : j < 84) :
    mulCoeffTwo EData V4PRGData 37 j =
      ((rectangularize 56 84 V4PRE1Data).getD 37 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE1Row37_spec :
    padOne 84 (mulRow EData V4PRGData 37) =
      (rectangularize 56 84 V4PRE1Data).getD 37 [] := by
  apply padOne_mulRow_eq_of_coefficients 84 EData V4PRGData 37
    ((rectangularize 56 84 V4PRE1Data).getD 37 [])
  · decide
  · have hTargetSupport : (V4PRE1Data.getD 37 []).length ≤ 84 := by
      decide
    rw [getD_rectangularize 56 84 V4PRE1Data 37 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE1Row37_coefficients

private theorem v4PRE1Row38_coefficients (j : ℕ) (hj : j < 84) :
    mulCoeffTwo EData V4PRGData 38 j =
      ((rectangularize 56 84 V4PRE1Data).getD 38 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE1Row38_spec :
    padOne 84 (mulRow EData V4PRGData 38) =
      (rectangularize 56 84 V4PRE1Data).getD 38 [] := by
  apply padOne_mulRow_eq_of_coefficients 84 EData V4PRGData 38
    ((rectangularize 56 84 V4PRE1Data).getD 38 [])
  · decide
  · have hTargetSupport : (V4PRE1Data.getD 38 []).length ≤ 84 := by
      decide
    rw [getD_rectangularize 56 84 V4PRE1Data 38 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE1Row38_coefficients

private theorem v4PRE1Row39_coefficients (j : ℕ) (hj : j < 84) :
    mulCoeffTwo EData V4PRGData 39 j =
      ((rectangularize 56 84 V4PRE1Data).getD 39 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE1Row39_spec :
    padOne 84 (mulRow EData V4PRGData 39) =
      (rectangularize 56 84 V4PRE1Data).getD 39 [] := by
  apply padOne_mulRow_eq_of_coefficients 84 EData V4PRGData 39
    ((rectangularize 56 84 V4PRE1Data).getD 39 [])
  · decide
  · have hTargetSupport : (V4PRE1Data.getD 39 []).length ≤ 84 := by
      decide
    rw [getD_rectangularize 56 84 V4PRE1Data 39 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE1Row39_coefficients

private theorem v4PRE1Row40_coefficients (j : ℕ) (hj : j < 84) :
    mulCoeffTwo EData V4PRGData 40 j =
      ((rectangularize 56 84 V4PRE1Data).getD 40 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE1Row40_spec :
    padOne 84 (mulRow EData V4PRGData 40) =
      (rectangularize 56 84 V4PRE1Data).getD 40 [] := by
  apply padOne_mulRow_eq_of_coefficients 84 EData V4PRGData 40
    ((rectangularize 56 84 V4PRE1Data).getD 40 [])
  · decide
  · have hTargetSupport : (V4PRE1Data.getD 40 []).length ≤ 84 := by
      decide
    rw [getD_rectangularize 56 84 V4PRE1Data 40 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE1Row40_coefficients

private theorem v4PRE1Row41_coefficients (j : ℕ) (hj : j < 84) :
    mulCoeffTwo EData V4PRGData 41 j =
      ((rectangularize 56 84 V4PRE1Data).getD 41 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE1Row41_spec :
    padOne 84 (mulRow EData V4PRGData 41) =
      (rectangularize 56 84 V4PRE1Data).getD 41 [] := by
  apply padOne_mulRow_eq_of_coefficients 84 EData V4PRGData 41
    ((rectangularize 56 84 V4PRE1Data).getD 41 [])
  · decide
  · have hTargetSupport : (V4PRE1Data.getD 41 []).length ≤ 84 := by
      decide
    rw [getD_rectangularize 56 84 V4PRE1Data 41 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE1Row41_coefficients

private theorem v4PRE1Row42_coefficients (j : ℕ) (hj : j < 84) :
    mulCoeffTwo EData V4PRGData 42 j =
      ((rectangularize 56 84 V4PRE1Data).getD 42 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE1Row42_spec :
    padOne 84 (mulRow EData V4PRGData 42) =
      (rectangularize 56 84 V4PRE1Data).getD 42 [] := by
  apply padOne_mulRow_eq_of_coefficients 84 EData V4PRGData 42
    ((rectangularize 56 84 V4PRE1Data).getD 42 [])
  · decide
  · have hTargetSupport : (V4PRE1Data.getD 42 []).length ≤ 84 := by
      decide
    rw [getD_rectangularize 56 84 V4PRE1Data 42 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE1Row42_coefficients

private theorem v4PRE1Row43_coefficients (j : ℕ) (hj : j < 84) :
    mulCoeffTwo EData V4PRGData 43 j =
      ((rectangularize 56 84 V4PRE1Data).getD 43 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE1Row43_spec :
    padOne 84 (mulRow EData V4PRGData 43) =
      (rectangularize 56 84 V4PRE1Data).getD 43 [] := by
  apply padOne_mulRow_eq_of_coefficients 84 EData V4PRGData 43
    ((rectangularize 56 84 V4PRE1Data).getD 43 [])
  · decide
  · have hTargetSupport : (V4PRE1Data.getD 43 []).length ≤ 84 := by
      decide
    rw [getD_rectangularize 56 84 V4PRE1Data 43 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE1Row43_coefficients

private theorem v4PRE1Row44_coefficients (j : ℕ) (hj : j < 84) :
    mulCoeffTwo EData V4PRGData 44 j =
      ((rectangularize 56 84 V4PRE1Data).getD 44 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE1Row44_spec :
    padOne 84 (mulRow EData V4PRGData 44) =
      (rectangularize 56 84 V4PRE1Data).getD 44 [] := by
  apply padOne_mulRow_eq_of_coefficients 84 EData V4PRGData 44
    ((rectangularize 56 84 V4PRE1Data).getD 44 [])
  · decide
  · have hTargetSupport : (V4PRE1Data.getD 44 []).length ≤ 84 := by
      decide
    rw [getD_rectangularize 56 84 V4PRE1Data 44 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE1Row44_coefficients

private theorem v4PRE1Row45_spec :
    padOne 84 (mulRow EData V4PRGData 45) =
      (rectangularize 56 84 V4PRE1Data).getD 45 [] := by
  decide

private theorem v4PRE1Row46_spec :
    padOne 84 (mulRow EData V4PRGData 46) =
      (rectangularize 56 84 V4PRE1Data).getD 46 [] := by
  decide

private theorem v4PRE1Row47_spec :
    padOne 84 (mulRow EData V4PRGData 47) =
      (rectangularize 56 84 V4PRE1Data).getD 47 [] := by
  decide

private theorem v4PRE1Row48_spec :
    padOne 84 (mulRow EData V4PRGData 48) =
      (rectangularize 56 84 V4PRE1Data).getD 48 [] := by
  decide

private theorem v4PRE1Row49_spec :
    padOne 84 (mulRow EData V4PRGData 49) =
      (rectangularize 56 84 V4PRE1Data).getD 49 [] := by
  decide

private theorem v4PRE1Row50_spec :
    padOne 84 (mulRow EData V4PRGData 50) =
      (rectangularize 56 84 V4PRE1Data).getD 50 [] := by
  decide

private theorem v4PRE1Row51_spec :
    padOne 84 (mulRow EData V4PRGData 51) =
      (rectangularize 56 84 V4PRE1Data).getD 51 [] := by
  decide

private theorem v4PRE1Row52_spec :
    padOne 84 (mulRow EData V4PRGData 52) =
      (rectangularize 56 84 V4PRE1Data).getD 52 [] := by
  decide

private theorem v4PRE1Row53_spec :
    padOne 84 (mulRow EData V4PRGData 53) =
      (rectangularize 56 84 V4PRE1Data).getD 53 [] := by
  decide

private theorem v4PRE1Row54_spec :
    padOne 84 (mulRow EData V4PRGData 54) =
      (rectangularize 56 84 V4PRE1Data).getD 54 [] := by
  decide

private theorem v4PRE1Row55_spec :
    padOne 84 (mulRow EData V4PRGData 55) =
      (rectangularize 56 84 V4PRE1Data).getD 55 [] := by
  decide

private theorem v4PRE1Rows_spec (n : ℕ) (hn : n < 56) :
    padOne 84 (mulRow EData V4PRGData n) =
      (rectangularize 56 84 V4PRE1Data).getD n [] := by
  have hCases :
    n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨
    n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨
    n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨
    n = 15 ∨ n = 16 ∨ n = 17 ∨ n = 18 ∨ n = 19 ∨
    n = 20 ∨ n = 21 ∨ n = 22 ∨ n = 23 ∨ n = 24 ∨
    n = 25 ∨ n = 26 ∨ n = 27 ∨ n = 28 ∨ n = 29 ∨
    n = 30 ∨ n = 31 ∨ n = 32 ∨ n = 33 ∨ n = 34 ∨
    n = 35 ∨ n = 36 ∨ n = 37 ∨ n = 38 ∨ n = 39 ∨
    n = 40 ∨ n = 41 ∨ n = 42 ∨ n = 43 ∨ n = 44 ∨
    n = 45 ∨ n = 46 ∨ n = 47 ∨ n = 48 ∨ n = 49 ∨
    n = 50 ∨ n = 51 ∨ n = 52 ∨ n = 53 ∨ n = 54 ∨
    n = 55 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact v4PRE1Row0_spec
  · exact v4PRE1Row1_spec
  · exact v4PRE1Row2_spec
  · exact v4PRE1Row3_spec
  · exact v4PRE1Row4_spec
  · exact v4PRE1Row5_spec
  · exact v4PRE1Row6_spec
  · exact v4PRE1Row7_spec
  · exact v4PRE1Row8_spec
  · exact v4PRE1Row9_spec
  · exact v4PRE1Row10_spec
  · exact v4PRE1Row11_spec
  · exact v4PRE1Row12_spec
  · exact v4PRE1Row13_spec
  · exact v4PRE1Row14_spec
  · exact v4PRE1Row15_spec
  · exact v4PRE1Row16_spec
  · exact v4PRE1Row17_spec
  · exact v4PRE1Row18_spec
  · exact v4PRE1Row19_spec
  · exact v4PRE1Row20_spec
  · exact v4PRE1Row21_spec
  · exact v4PRE1Row22_spec
  · exact v4PRE1Row23_spec
  · exact v4PRE1Row24_spec
  · exact v4PRE1Row25_spec
  · exact v4PRE1Row26_spec
  · exact v4PRE1Row27_spec
  · exact v4PRE1Row28_spec
  · exact v4PRE1Row29_spec
  · exact v4PRE1Row30_spec
  · exact v4PRE1Row31_spec
  · exact v4PRE1Row32_spec
  · exact v4PRE1Row33_spec
  · exact v4PRE1Row34_spec
  · exact v4PRE1Row35_spec
  · exact v4PRE1Row36_spec
  · exact v4PRE1Row37_spec
  · exact v4PRE1Row38_spec
  · exact v4PRE1Row39_spec
  · exact v4PRE1Row40_spec
  · exact v4PRE1Row41_spec
  · exact v4PRE1Row42_spec
  · exact v4PRE1Row43_spec
  · exact v4PRE1Row44_spec
  · exact v4PRE1Row45_spec
  · exact v4PRE1Row46_spec
  · exact v4PRE1Row47_spec
  · exact v4PRE1Row48_spec
  · exact v4PRE1Row49_spec
  · exact v4PRE1Row50_spec
  · exact v4PRE1Row51_spec
  · exact v4PRE1Row52_spec
  · exact v4PRE1Row53_spec
  · exact v4PRE1Row54_spec
  · exact v4PRE1Row55_spec

private theorem v4PRE1Left_length :
    (rectangularize 56 84 (Two.mul EData V4PRGData)).length = 56 := by
  decide

private theorem v4PRE1Right_length :
    (rectangularize 56 84 V4PRE1Data).length = 56 := by
  decide

-- Exact bidegree bound (55, 83); no row or column is discarded.
private theorem v4PRE1Data_spec :
    rectangularize 56 84 (Two.mul EData V4PRGData) =
      rectangularize 56 84 V4PRE1Data := by
  apply List.ext_getElem (v4PRE1Left_length.trans v4PRE1Right_length.symm)
  intro n hn _
  rw [List.getElem_eq_getD [], List.getElem_eq_getD []]
  rw [v4PRE1Left_length] at hn
  rw [getD_rectangularize 56 84 (Two.mul EData V4PRGData) n hn,
    ← mulRow_eq_getD]
  exact v4PRE1Rows_spec n hn

private theorem v4PRE2Row0_spec :
    padOne 86 (mulRow EData V4PRE1Data 0) =
      (rectangularize 58 86 V4PRE2Data).getD 0 [] := by
  decide

private theorem v4PRE2Row1_spec :
    padOne 86 (mulRow EData V4PRE1Data 1) =
      (rectangularize 58 86 V4PRE2Data).getD 1 [] := by
  decide

private theorem v4PRE2Row2_spec :
    padOne 86 (mulRow EData V4PRE1Data 2) =
      (rectangularize 58 86 V4PRE2Data).getD 2 [] := by
  decide

private theorem v4PRE2Row3_spec :
    padOne 86 (mulRow EData V4PRE1Data 3) =
      (rectangularize 58 86 V4PRE2Data).getD 3 [] := by
  decide

private theorem v4PRE2Row4_spec :
    padOne 86 (mulRow EData V4PRE1Data 4) =
      (rectangularize 58 86 V4PRE2Data).getD 4 [] := by
  decide

private theorem v4PRE2Row5_spec :
    padOne 86 (mulRow EData V4PRE1Data 5) =
      (rectangularize 58 86 V4PRE2Data).getD 5 [] := by
  decide

private theorem v4PRE2Row6_spec :
    padOne 86 (mulRow EData V4PRE1Data 6) =
      (rectangularize 58 86 V4PRE2Data).getD 6 [] := by
  decide

private theorem v4PRE2Row7_spec :
    padOne 86 (mulRow EData V4PRE1Data 7) =
      (rectangularize 58 86 V4PRE2Data).getD 7 [] := by
  decide

private theorem v4PRE2Row8_coefficients (j : ℕ) (hj : j < 86) :
    mulCoeffTwo EData V4PRE1Data 8 j =
      ((rectangularize 58 86 V4PRE2Data).getD 8 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE2Row8_spec :
    padOne 86 (mulRow EData V4PRE1Data 8) =
      (rectangularize 58 86 V4PRE2Data).getD 8 [] := by
  apply padOne_mulRow_eq_of_coefficients 86 EData V4PRE1Data 8
    ((rectangularize 58 86 V4PRE2Data).getD 8 [])
  · decide
  · have hTargetSupport : (V4PRE2Data.getD 8 []).length ≤ 86 := by
      decide
    rw [getD_rectangularize 58 86 V4PRE2Data 8 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE2Row8_coefficients

private theorem v4PRE2Row9_coefficients (j : ℕ) (hj : j < 86) :
    mulCoeffTwo EData V4PRE1Data 9 j =
      ((rectangularize 58 86 V4PRE2Data).getD 9 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE2Row9_spec :
    padOne 86 (mulRow EData V4PRE1Data 9) =
      (rectangularize 58 86 V4PRE2Data).getD 9 [] := by
  apply padOne_mulRow_eq_of_coefficients 86 EData V4PRE1Data 9
    ((rectangularize 58 86 V4PRE2Data).getD 9 [])
  · decide
  · have hTargetSupport : (V4PRE2Data.getD 9 []).length ≤ 86 := by
      decide
    rw [getD_rectangularize 58 86 V4PRE2Data 9 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE2Row9_coefficients

private theorem v4PRE2Row10_coefficients (j : ℕ) (hj : j < 86) :
    mulCoeffTwo EData V4PRE1Data 10 j =
      ((rectangularize 58 86 V4PRE2Data).getD 10 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE2Row10_spec :
    padOne 86 (mulRow EData V4PRE1Data 10) =
      (rectangularize 58 86 V4PRE2Data).getD 10 [] := by
  apply padOne_mulRow_eq_of_coefficients 86 EData V4PRE1Data 10
    ((rectangularize 58 86 V4PRE2Data).getD 10 [])
  · decide
  · have hTargetSupport : (V4PRE2Data.getD 10 []).length ≤ 86 := by
      decide
    rw [getD_rectangularize 58 86 V4PRE2Data 10 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE2Row10_coefficients

private theorem v4PRE2Row11_coefficients (j : ℕ) (hj : j < 86) :
    mulCoeffTwo EData V4PRE1Data 11 j =
      ((rectangularize 58 86 V4PRE2Data).getD 11 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE2Row11_spec :
    padOne 86 (mulRow EData V4PRE1Data 11) =
      (rectangularize 58 86 V4PRE2Data).getD 11 [] := by
  apply padOne_mulRow_eq_of_coefficients 86 EData V4PRE1Data 11
    ((rectangularize 58 86 V4PRE2Data).getD 11 [])
  · decide
  · have hTargetSupport : (V4PRE2Data.getD 11 []).length ≤ 86 := by
      decide
    rw [getD_rectangularize 58 86 V4PRE2Data 11 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE2Row11_coefficients

private theorem v4PRE2Row12_coefficients (j : ℕ) (hj : j < 86) :
    mulCoeffTwo EData V4PRE1Data 12 j =
      ((rectangularize 58 86 V4PRE2Data).getD 12 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE2Row12_spec :
    padOne 86 (mulRow EData V4PRE1Data 12) =
      (rectangularize 58 86 V4PRE2Data).getD 12 [] := by
  apply padOne_mulRow_eq_of_coefficients 86 EData V4PRE1Data 12
    ((rectangularize 58 86 V4PRE2Data).getD 12 [])
  · decide
  · have hTargetSupport : (V4PRE2Data.getD 12 []).length ≤ 86 := by
      decide
    rw [getD_rectangularize 58 86 V4PRE2Data 12 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE2Row12_coefficients

private theorem v4PRE2Row13_coefficients (j : ℕ) (hj : j < 86) :
    mulCoeffTwo EData V4PRE1Data 13 j =
      ((rectangularize 58 86 V4PRE2Data).getD 13 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE2Row13_spec :
    padOne 86 (mulRow EData V4PRE1Data 13) =
      (rectangularize 58 86 V4PRE2Data).getD 13 [] := by
  apply padOne_mulRow_eq_of_coefficients 86 EData V4PRE1Data 13
    ((rectangularize 58 86 V4PRE2Data).getD 13 [])
  · decide
  · have hTargetSupport : (V4PRE2Data.getD 13 []).length ≤ 86 := by
      decide
    rw [getD_rectangularize 58 86 V4PRE2Data 13 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE2Row13_coefficients

private theorem v4PRE2Row14_coefficients (j : ℕ) (hj : j < 86) :
    mulCoeffTwo EData V4PRE1Data 14 j =
      ((rectangularize 58 86 V4PRE2Data).getD 14 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE2Row14_spec :
    padOne 86 (mulRow EData V4PRE1Data 14) =
      (rectangularize 58 86 V4PRE2Data).getD 14 [] := by
  apply padOne_mulRow_eq_of_coefficients 86 EData V4PRE1Data 14
    ((rectangularize 58 86 V4PRE2Data).getD 14 [])
  · decide
  · have hTargetSupport : (V4PRE2Data.getD 14 []).length ≤ 86 := by
      decide
    rw [getD_rectangularize 58 86 V4PRE2Data 14 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE2Row14_coefficients

private theorem v4PRE2Row15_coefficients (j : ℕ) (hj : j < 86) :
    mulCoeffTwo EData V4PRE1Data 15 j =
      ((rectangularize 58 86 V4PRE2Data).getD 15 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE2Row15_spec :
    padOne 86 (mulRow EData V4PRE1Data 15) =
      (rectangularize 58 86 V4PRE2Data).getD 15 [] := by
  apply padOne_mulRow_eq_of_coefficients 86 EData V4PRE1Data 15
    ((rectangularize 58 86 V4PRE2Data).getD 15 [])
  · decide
  · have hTargetSupport : (V4PRE2Data.getD 15 []).length ≤ 86 := by
      decide
    rw [getD_rectangularize 58 86 V4PRE2Data 15 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE2Row15_coefficients

private theorem v4PRE2Row16_coefficients (j : ℕ) (hj : j < 86) :
    mulCoeffTwo EData V4PRE1Data 16 j =
      ((rectangularize 58 86 V4PRE2Data).getD 16 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE2Row16_spec :
    padOne 86 (mulRow EData V4PRE1Data 16) =
      (rectangularize 58 86 V4PRE2Data).getD 16 [] := by
  apply padOne_mulRow_eq_of_coefficients 86 EData V4PRE1Data 16
    ((rectangularize 58 86 V4PRE2Data).getD 16 [])
  · decide
  · have hTargetSupport : (V4PRE2Data.getD 16 []).length ≤ 86 := by
      decide
    rw [getD_rectangularize 58 86 V4PRE2Data 16 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE2Row16_coefficients

private theorem v4PRE2Row17_coefficients (j : ℕ) (hj : j < 86) :
    mulCoeffTwo EData V4PRE1Data 17 j =
      ((rectangularize 58 86 V4PRE2Data).getD 17 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE2Row17_spec :
    padOne 86 (mulRow EData V4PRE1Data 17) =
      (rectangularize 58 86 V4PRE2Data).getD 17 [] := by
  apply padOne_mulRow_eq_of_coefficients 86 EData V4PRE1Data 17
    ((rectangularize 58 86 V4PRE2Data).getD 17 [])
  · decide
  · have hTargetSupport : (V4PRE2Data.getD 17 []).length ≤ 86 := by
      decide
    rw [getD_rectangularize 58 86 V4PRE2Data 17 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE2Row17_coefficients

private theorem v4PRE2Row18_coefficients (j : ℕ) (hj : j < 86) :
    mulCoeffTwo EData V4PRE1Data 18 j =
      ((rectangularize 58 86 V4PRE2Data).getD 18 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE2Row18_spec :
    padOne 86 (mulRow EData V4PRE1Data 18) =
      (rectangularize 58 86 V4PRE2Data).getD 18 [] := by
  apply padOne_mulRow_eq_of_coefficients 86 EData V4PRE1Data 18
    ((rectangularize 58 86 V4PRE2Data).getD 18 [])
  · decide
  · have hTargetSupport : (V4PRE2Data.getD 18 []).length ≤ 86 := by
      decide
    rw [getD_rectangularize 58 86 V4PRE2Data 18 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE2Row18_coefficients

private theorem v4PRE2Row19_coefficients (j : ℕ) (hj : j < 86) :
    mulCoeffTwo EData V4PRE1Data 19 j =
      ((rectangularize 58 86 V4PRE2Data).getD 19 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE2Row19_spec :
    padOne 86 (mulRow EData V4PRE1Data 19) =
      (rectangularize 58 86 V4PRE2Data).getD 19 [] := by
  apply padOne_mulRow_eq_of_coefficients 86 EData V4PRE1Data 19
    ((rectangularize 58 86 V4PRE2Data).getD 19 [])
  · decide
  · have hTargetSupport : (V4PRE2Data.getD 19 []).length ≤ 86 := by
      decide
    rw [getD_rectangularize 58 86 V4PRE2Data 19 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE2Row19_coefficients

private theorem v4PRE2Row20_coefficients (j : ℕ) (hj : j < 86) :
    mulCoeffTwo EData V4PRE1Data 20 j =
      ((rectangularize 58 86 V4PRE2Data).getD 20 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE2Row20_spec :
    padOne 86 (mulRow EData V4PRE1Data 20) =
      (rectangularize 58 86 V4PRE2Data).getD 20 [] := by
  apply padOne_mulRow_eq_of_coefficients 86 EData V4PRE1Data 20
    ((rectangularize 58 86 V4PRE2Data).getD 20 [])
  · decide
  · have hTargetSupport : (V4PRE2Data.getD 20 []).length ≤ 86 := by
      decide
    rw [getD_rectangularize 58 86 V4PRE2Data 20 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE2Row20_coefficients

private theorem v4PRE2Row21_coefficients (j : ℕ) (hj : j < 86) :
    mulCoeffTwo EData V4PRE1Data 21 j =
      ((rectangularize 58 86 V4PRE2Data).getD 21 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE2Row21_spec :
    padOne 86 (mulRow EData V4PRE1Data 21) =
      (rectangularize 58 86 V4PRE2Data).getD 21 [] := by
  apply padOne_mulRow_eq_of_coefficients 86 EData V4PRE1Data 21
    ((rectangularize 58 86 V4PRE2Data).getD 21 [])
  · decide
  · have hTargetSupport : (V4PRE2Data.getD 21 []).length ≤ 86 := by
      decide
    rw [getD_rectangularize 58 86 V4PRE2Data 21 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE2Row21_coefficients

private theorem v4PRE2Row22_coefficients (j : ℕ) (hj : j < 86) :
    mulCoeffTwo EData V4PRE1Data 22 j =
      ((rectangularize 58 86 V4PRE2Data).getD 22 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE2Row22_spec :
    padOne 86 (mulRow EData V4PRE1Data 22) =
      (rectangularize 58 86 V4PRE2Data).getD 22 [] := by
  apply padOne_mulRow_eq_of_coefficients 86 EData V4PRE1Data 22
    ((rectangularize 58 86 V4PRE2Data).getD 22 [])
  · decide
  · have hTargetSupport : (V4PRE2Data.getD 22 []).length ≤ 86 := by
      decide
    rw [getD_rectangularize 58 86 V4PRE2Data 22 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE2Row22_coefficients

private theorem v4PRE2Row23_coefficients (j : ℕ) (hj : j < 86) :
    mulCoeffTwo EData V4PRE1Data 23 j =
      ((rectangularize 58 86 V4PRE2Data).getD 23 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE2Row23_spec :
    padOne 86 (mulRow EData V4PRE1Data 23) =
      (rectangularize 58 86 V4PRE2Data).getD 23 [] := by
  apply padOne_mulRow_eq_of_coefficients 86 EData V4PRE1Data 23
    ((rectangularize 58 86 V4PRE2Data).getD 23 [])
  · decide
  · have hTargetSupport : (V4PRE2Data.getD 23 []).length ≤ 86 := by
      decide
    rw [getD_rectangularize 58 86 V4PRE2Data 23 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE2Row23_coefficients

private theorem v4PRE2Row24_coefficients (j : ℕ) (hj : j < 86) :
    mulCoeffTwo EData V4PRE1Data 24 j =
      ((rectangularize 58 86 V4PRE2Data).getD 24 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE2Row24_spec :
    padOne 86 (mulRow EData V4PRE1Data 24) =
      (rectangularize 58 86 V4PRE2Data).getD 24 [] := by
  apply padOne_mulRow_eq_of_coefficients 86 EData V4PRE1Data 24
    ((rectangularize 58 86 V4PRE2Data).getD 24 [])
  · decide
  · have hTargetSupport : (V4PRE2Data.getD 24 []).length ≤ 86 := by
      decide
    rw [getD_rectangularize 58 86 V4PRE2Data 24 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE2Row24_coefficients

private theorem v4PRE2Row25_coefficients (j : ℕ) (hj : j < 86) :
    mulCoeffTwo EData V4PRE1Data 25 j =
      ((rectangularize 58 86 V4PRE2Data).getD 25 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE2Row25_spec :
    padOne 86 (mulRow EData V4PRE1Data 25) =
      (rectangularize 58 86 V4PRE2Data).getD 25 [] := by
  apply padOne_mulRow_eq_of_coefficients 86 EData V4PRE1Data 25
    ((rectangularize 58 86 V4PRE2Data).getD 25 [])
  · decide
  · have hTargetSupport : (V4PRE2Data.getD 25 []).length ≤ 86 := by
      decide
    rw [getD_rectangularize 58 86 V4PRE2Data 25 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE2Row25_coefficients

private theorem v4PRE2Row26_coefficients (j : ℕ) (hj : j < 86) :
    mulCoeffTwo EData V4PRE1Data 26 j =
      ((rectangularize 58 86 V4PRE2Data).getD 26 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE2Row26_spec :
    padOne 86 (mulRow EData V4PRE1Data 26) =
      (rectangularize 58 86 V4PRE2Data).getD 26 [] := by
  apply padOne_mulRow_eq_of_coefficients 86 EData V4PRE1Data 26
    ((rectangularize 58 86 V4PRE2Data).getD 26 [])
  · decide
  · have hTargetSupport : (V4PRE2Data.getD 26 []).length ≤ 86 := by
      decide
    rw [getD_rectangularize 58 86 V4PRE2Data 26 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE2Row26_coefficients

private theorem v4PRE2Row27_coefficients (j : ℕ) (hj : j < 86) :
    mulCoeffTwo EData V4PRE1Data 27 j =
      ((rectangularize 58 86 V4PRE2Data).getD 27 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE2Row27_spec :
    padOne 86 (mulRow EData V4PRE1Data 27) =
      (rectangularize 58 86 V4PRE2Data).getD 27 [] := by
  apply padOne_mulRow_eq_of_coefficients 86 EData V4PRE1Data 27
    ((rectangularize 58 86 V4PRE2Data).getD 27 [])
  · decide
  · have hTargetSupport : (V4PRE2Data.getD 27 []).length ≤ 86 := by
      decide
    rw [getD_rectangularize 58 86 V4PRE2Data 27 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE2Row27_coefficients

private theorem v4PRE2Row28_coefficients (j : ℕ) (hj : j < 86) :
    mulCoeffTwo EData V4PRE1Data 28 j =
      ((rectangularize 58 86 V4PRE2Data).getD 28 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE2Row28_spec :
    padOne 86 (mulRow EData V4PRE1Data 28) =
      (rectangularize 58 86 V4PRE2Data).getD 28 [] := by
  apply padOne_mulRow_eq_of_coefficients 86 EData V4PRE1Data 28
    ((rectangularize 58 86 V4PRE2Data).getD 28 [])
  · decide
  · have hTargetSupport : (V4PRE2Data.getD 28 []).length ≤ 86 := by
      decide
    rw [getD_rectangularize 58 86 V4PRE2Data 28 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE2Row28_coefficients

private theorem v4PRE2Row29_coefficients (j : ℕ) (hj : j < 86) :
    mulCoeffTwo EData V4PRE1Data 29 j =
      ((rectangularize 58 86 V4PRE2Data).getD 29 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE2Row29_spec :
    padOne 86 (mulRow EData V4PRE1Data 29) =
      (rectangularize 58 86 V4PRE2Data).getD 29 [] := by
  apply padOne_mulRow_eq_of_coefficients 86 EData V4PRE1Data 29
    ((rectangularize 58 86 V4PRE2Data).getD 29 [])
  · decide
  · have hTargetSupport : (V4PRE2Data.getD 29 []).length ≤ 86 := by
      decide
    rw [getD_rectangularize 58 86 V4PRE2Data 29 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE2Row29_coefficients

private theorem v4PRE2Row30_coefficients (j : ℕ) (hj : j < 86) :
    mulCoeffTwo EData V4PRE1Data 30 j =
      ((rectangularize 58 86 V4PRE2Data).getD 30 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE2Row30_spec :
    padOne 86 (mulRow EData V4PRE1Data 30) =
      (rectangularize 58 86 V4PRE2Data).getD 30 [] := by
  apply padOne_mulRow_eq_of_coefficients 86 EData V4PRE1Data 30
    ((rectangularize 58 86 V4PRE2Data).getD 30 [])
  · decide
  · have hTargetSupport : (V4PRE2Data.getD 30 []).length ≤ 86 := by
      decide
    rw [getD_rectangularize 58 86 V4PRE2Data 30 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE2Row30_coefficients

private theorem v4PRE2Row31_coefficients (j : ℕ) (hj : j < 86) :
    mulCoeffTwo EData V4PRE1Data 31 j =
      ((rectangularize 58 86 V4PRE2Data).getD 31 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE2Row31_spec :
    padOne 86 (mulRow EData V4PRE1Data 31) =
      (rectangularize 58 86 V4PRE2Data).getD 31 [] := by
  apply padOne_mulRow_eq_of_coefficients 86 EData V4PRE1Data 31
    ((rectangularize 58 86 V4PRE2Data).getD 31 [])
  · decide
  · have hTargetSupport : (V4PRE2Data.getD 31 []).length ≤ 86 := by
      decide
    rw [getD_rectangularize 58 86 V4PRE2Data 31 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE2Row31_coefficients

private theorem v4PRE2Row32_coefficients (j : ℕ) (hj : j < 86) :
    mulCoeffTwo EData V4PRE1Data 32 j =
      ((rectangularize 58 86 V4PRE2Data).getD 32 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE2Row32_spec :
    padOne 86 (mulRow EData V4PRE1Data 32) =
      (rectangularize 58 86 V4PRE2Data).getD 32 [] := by
  apply padOne_mulRow_eq_of_coefficients 86 EData V4PRE1Data 32
    ((rectangularize 58 86 V4PRE2Data).getD 32 [])
  · decide
  · have hTargetSupport : (V4PRE2Data.getD 32 []).length ≤ 86 := by
      decide
    rw [getD_rectangularize 58 86 V4PRE2Data 32 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE2Row32_coefficients

private theorem v4PRE2Row33_coefficients (j : ℕ) (hj : j < 86) :
    mulCoeffTwo EData V4PRE1Data 33 j =
      ((rectangularize 58 86 V4PRE2Data).getD 33 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE2Row33_spec :
    padOne 86 (mulRow EData V4PRE1Data 33) =
      (rectangularize 58 86 V4PRE2Data).getD 33 [] := by
  apply padOne_mulRow_eq_of_coefficients 86 EData V4PRE1Data 33
    ((rectangularize 58 86 V4PRE2Data).getD 33 [])
  · decide
  · have hTargetSupport : (V4PRE2Data.getD 33 []).length ≤ 86 := by
      decide
    rw [getD_rectangularize 58 86 V4PRE2Data 33 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE2Row33_coefficients

private theorem v4PRE2Row34_coefficients (j : ℕ) (hj : j < 86) :
    mulCoeffTwo EData V4PRE1Data 34 j =
      ((rectangularize 58 86 V4PRE2Data).getD 34 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE2Row34_spec :
    padOne 86 (mulRow EData V4PRE1Data 34) =
      (rectangularize 58 86 V4PRE2Data).getD 34 [] := by
  apply padOne_mulRow_eq_of_coefficients 86 EData V4PRE1Data 34
    ((rectangularize 58 86 V4PRE2Data).getD 34 [])
  · decide
  · have hTargetSupport : (V4PRE2Data.getD 34 []).length ≤ 86 := by
      decide
    rw [getD_rectangularize 58 86 V4PRE2Data 34 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE2Row34_coefficients

private theorem v4PRE2Row35_coefficients (j : ℕ) (hj : j < 86) :
    mulCoeffTwo EData V4PRE1Data 35 j =
      ((rectangularize 58 86 V4PRE2Data).getD 35 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE2Row35_spec :
    padOne 86 (mulRow EData V4PRE1Data 35) =
      (rectangularize 58 86 V4PRE2Data).getD 35 [] := by
  apply padOne_mulRow_eq_of_coefficients 86 EData V4PRE1Data 35
    ((rectangularize 58 86 V4PRE2Data).getD 35 [])
  · decide
  · have hTargetSupport : (V4PRE2Data.getD 35 []).length ≤ 86 := by
      decide
    rw [getD_rectangularize 58 86 V4PRE2Data 35 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE2Row35_coefficients

private theorem v4PRE2Row36_coefficients (j : ℕ) (hj : j < 86) :
    mulCoeffTwo EData V4PRE1Data 36 j =
      ((rectangularize 58 86 V4PRE2Data).getD 36 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE2Row36_spec :
    padOne 86 (mulRow EData V4PRE1Data 36) =
      (rectangularize 58 86 V4PRE2Data).getD 36 [] := by
  apply padOne_mulRow_eq_of_coefficients 86 EData V4PRE1Data 36
    ((rectangularize 58 86 V4PRE2Data).getD 36 [])
  · decide
  · have hTargetSupport : (V4PRE2Data.getD 36 []).length ≤ 86 := by
      decide
    rw [getD_rectangularize 58 86 V4PRE2Data 36 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE2Row36_coefficients

private theorem v4PRE2Row37_coefficients (j : ℕ) (hj : j < 86) :
    mulCoeffTwo EData V4PRE1Data 37 j =
      ((rectangularize 58 86 V4PRE2Data).getD 37 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE2Row37_spec :
    padOne 86 (mulRow EData V4PRE1Data 37) =
      (rectangularize 58 86 V4PRE2Data).getD 37 [] := by
  apply padOne_mulRow_eq_of_coefficients 86 EData V4PRE1Data 37
    ((rectangularize 58 86 V4PRE2Data).getD 37 [])
  · decide
  · have hTargetSupport : (V4PRE2Data.getD 37 []).length ≤ 86 := by
      decide
    rw [getD_rectangularize 58 86 V4PRE2Data 37 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE2Row37_coefficients

private theorem v4PRE2Row38_coefficients (j : ℕ) (hj : j < 86) :
    mulCoeffTwo EData V4PRE1Data 38 j =
      ((rectangularize 58 86 V4PRE2Data).getD 38 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE2Row38_spec :
    padOne 86 (mulRow EData V4PRE1Data 38) =
      (rectangularize 58 86 V4PRE2Data).getD 38 [] := by
  apply padOne_mulRow_eq_of_coefficients 86 EData V4PRE1Data 38
    ((rectangularize 58 86 V4PRE2Data).getD 38 [])
  · decide
  · have hTargetSupport : (V4PRE2Data.getD 38 []).length ≤ 86 := by
      decide
    rw [getD_rectangularize 58 86 V4PRE2Data 38 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE2Row38_coefficients

private theorem v4PRE2Row39_coefficients (j : ℕ) (hj : j < 86) :
    mulCoeffTwo EData V4PRE1Data 39 j =
      ((rectangularize 58 86 V4PRE2Data).getD 39 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE2Row39_spec :
    padOne 86 (mulRow EData V4PRE1Data 39) =
      (rectangularize 58 86 V4PRE2Data).getD 39 [] := by
  apply padOne_mulRow_eq_of_coefficients 86 EData V4PRE1Data 39
    ((rectangularize 58 86 V4PRE2Data).getD 39 [])
  · decide
  · have hTargetSupport : (V4PRE2Data.getD 39 []).length ≤ 86 := by
      decide
    rw [getD_rectangularize 58 86 V4PRE2Data 39 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE2Row39_coefficients

private theorem v4PRE2Row40_coefficients (j : ℕ) (hj : j < 86) :
    mulCoeffTwo EData V4PRE1Data 40 j =
      ((rectangularize 58 86 V4PRE2Data).getD 40 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE2Row40_spec :
    padOne 86 (mulRow EData V4PRE1Data 40) =
      (rectangularize 58 86 V4PRE2Data).getD 40 [] := by
  apply padOne_mulRow_eq_of_coefficients 86 EData V4PRE1Data 40
    ((rectangularize 58 86 V4PRE2Data).getD 40 [])
  · decide
  · have hTargetSupport : (V4PRE2Data.getD 40 []).length ≤ 86 := by
      decide
    rw [getD_rectangularize 58 86 V4PRE2Data 40 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE2Row40_coefficients

private theorem v4PRE2Row41_coefficients (j : ℕ) (hj : j < 86) :
    mulCoeffTwo EData V4PRE1Data 41 j =
      ((rectangularize 58 86 V4PRE2Data).getD 41 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE2Row41_spec :
    padOne 86 (mulRow EData V4PRE1Data 41) =
      (rectangularize 58 86 V4PRE2Data).getD 41 [] := by
  apply padOne_mulRow_eq_of_coefficients 86 EData V4PRE1Data 41
    ((rectangularize 58 86 V4PRE2Data).getD 41 [])
  · decide
  · have hTargetSupport : (V4PRE2Data.getD 41 []).length ≤ 86 := by
      decide
    rw [getD_rectangularize 58 86 V4PRE2Data 41 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE2Row41_coefficients

private theorem v4PRE2Row42_coefficients (j : ℕ) (hj : j < 86) :
    mulCoeffTwo EData V4PRE1Data 42 j =
      ((rectangularize 58 86 V4PRE2Data).getD 42 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE2Row42_spec :
    padOne 86 (mulRow EData V4PRE1Data 42) =
      (rectangularize 58 86 V4PRE2Data).getD 42 [] := by
  apply padOne_mulRow_eq_of_coefficients 86 EData V4PRE1Data 42
    ((rectangularize 58 86 V4PRE2Data).getD 42 [])
  · decide
  · have hTargetSupport : (V4PRE2Data.getD 42 []).length ≤ 86 := by
      decide
    rw [getD_rectangularize 58 86 V4PRE2Data 42 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE2Row42_coefficients

private theorem v4PRE2Row43_coefficients (j : ℕ) (hj : j < 86) :
    mulCoeffTwo EData V4PRE1Data 43 j =
      ((rectangularize 58 86 V4PRE2Data).getD 43 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE2Row43_spec :
    padOne 86 (mulRow EData V4PRE1Data 43) =
      (rectangularize 58 86 V4PRE2Data).getD 43 [] := by
  apply padOne_mulRow_eq_of_coefficients 86 EData V4PRE1Data 43
    ((rectangularize 58 86 V4PRE2Data).getD 43 [])
  · decide
  · have hTargetSupport : (V4PRE2Data.getD 43 []).length ≤ 86 := by
      decide
    rw [getD_rectangularize 58 86 V4PRE2Data 43 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE2Row43_coefficients

private theorem v4PRE2Row44_coefficients (j : ℕ) (hj : j < 86) :
    mulCoeffTwo EData V4PRE1Data 44 j =
      ((rectangularize 58 86 V4PRE2Data).getD 44 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE2Row44_spec :
    padOne 86 (mulRow EData V4PRE1Data 44) =
      (rectangularize 58 86 V4PRE2Data).getD 44 [] := by
  apply padOne_mulRow_eq_of_coefficients 86 EData V4PRE1Data 44
    ((rectangularize 58 86 V4PRE2Data).getD 44 [])
  · decide
  · have hTargetSupport : (V4PRE2Data.getD 44 []).length ≤ 86 := by
      decide
    rw [getD_rectangularize 58 86 V4PRE2Data 44 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE2Row44_coefficients

private theorem v4PRE2Row45_coefficients (j : ℕ) (hj : j < 86) :
    mulCoeffTwo EData V4PRE1Data 45 j =
      ((rectangularize 58 86 V4PRE2Data).getD 45 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE2Row45_spec :
    padOne 86 (mulRow EData V4PRE1Data 45) =
      (rectangularize 58 86 V4PRE2Data).getD 45 [] := by
  apply padOne_mulRow_eq_of_coefficients 86 EData V4PRE1Data 45
    ((rectangularize 58 86 V4PRE2Data).getD 45 [])
  · decide
  · have hTargetSupport : (V4PRE2Data.getD 45 []).length ≤ 86 := by
      decide
    rw [getD_rectangularize 58 86 V4PRE2Data 45 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE2Row45_coefficients

private theorem v4PRE2Row46_coefficients (j : ℕ) (hj : j < 86) :
    mulCoeffTwo EData V4PRE1Data 46 j =
      ((rectangularize 58 86 V4PRE2Data).getD 46 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE2Row46_spec :
    padOne 86 (mulRow EData V4PRE1Data 46) =
      (rectangularize 58 86 V4PRE2Data).getD 46 [] := by
  apply padOne_mulRow_eq_of_coefficients 86 EData V4PRE1Data 46
    ((rectangularize 58 86 V4PRE2Data).getD 46 [])
  · decide
  · have hTargetSupport : (V4PRE2Data.getD 46 []).length ≤ 86 := by
      decide
    rw [getD_rectangularize 58 86 V4PRE2Data 46 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE2Row46_coefficients

private theorem v4PRE2Row47_spec :
    padOne 86 (mulRow EData V4PRE1Data 47) =
      (rectangularize 58 86 V4PRE2Data).getD 47 [] := by
  decide

private theorem v4PRE2Row48_spec :
    padOne 86 (mulRow EData V4PRE1Data 48) =
      (rectangularize 58 86 V4PRE2Data).getD 48 [] := by
  decide

private theorem v4PRE2Row49_spec :
    padOne 86 (mulRow EData V4PRE1Data 49) =
      (rectangularize 58 86 V4PRE2Data).getD 49 [] := by
  decide

private theorem v4PRE2Row50_spec :
    padOne 86 (mulRow EData V4PRE1Data 50) =
      (rectangularize 58 86 V4PRE2Data).getD 50 [] := by
  decide

private theorem v4PRE2Row51_spec :
    padOne 86 (mulRow EData V4PRE1Data 51) =
      (rectangularize 58 86 V4PRE2Data).getD 51 [] := by
  decide

private theorem v4PRE2Row52_spec :
    padOne 86 (mulRow EData V4PRE1Data 52) =
      (rectangularize 58 86 V4PRE2Data).getD 52 [] := by
  decide

private theorem v4PRE2Row53_spec :
    padOne 86 (mulRow EData V4PRE1Data 53) =
      (rectangularize 58 86 V4PRE2Data).getD 53 [] := by
  decide

private theorem v4PRE2Row54_spec :
    padOne 86 (mulRow EData V4PRE1Data 54) =
      (rectangularize 58 86 V4PRE2Data).getD 54 [] := by
  decide

private theorem v4PRE2Row55_spec :
    padOne 86 (mulRow EData V4PRE1Data 55) =
      (rectangularize 58 86 V4PRE2Data).getD 55 [] := by
  decide

private theorem v4PRE2Row56_spec :
    padOne 86 (mulRow EData V4PRE1Data 56) =
      (rectangularize 58 86 V4PRE2Data).getD 56 [] := by
  decide

private theorem v4PRE2Row57_spec :
    padOne 86 (mulRow EData V4PRE1Data 57) =
      (rectangularize 58 86 V4PRE2Data).getD 57 [] := by
  decide

private theorem v4PRE2Rows_spec (n : ℕ) (hn : n < 58) :
    padOne 86 (mulRow EData V4PRE1Data n) =
      (rectangularize 58 86 V4PRE2Data).getD n [] := by
  have hCases :
    n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨
    n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨
    n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨
    n = 15 ∨ n = 16 ∨ n = 17 ∨ n = 18 ∨ n = 19 ∨
    n = 20 ∨ n = 21 ∨ n = 22 ∨ n = 23 ∨ n = 24 ∨
    n = 25 ∨ n = 26 ∨ n = 27 ∨ n = 28 ∨ n = 29 ∨
    n = 30 ∨ n = 31 ∨ n = 32 ∨ n = 33 ∨ n = 34 ∨
    n = 35 ∨ n = 36 ∨ n = 37 ∨ n = 38 ∨ n = 39 ∨
    n = 40 ∨ n = 41 ∨ n = 42 ∨ n = 43 ∨ n = 44 ∨
    n = 45 ∨ n = 46 ∨ n = 47 ∨ n = 48 ∨ n = 49 ∨
    n = 50 ∨ n = 51 ∨ n = 52 ∨ n = 53 ∨ n = 54 ∨
    n = 55 ∨ n = 56 ∨ n = 57 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4PRE2Row0_spec
  · exact v4PRE2Row1_spec
  · exact v4PRE2Row2_spec
  · exact v4PRE2Row3_spec
  · exact v4PRE2Row4_spec
  · exact v4PRE2Row5_spec
  · exact v4PRE2Row6_spec
  · exact v4PRE2Row7_spec
  · exact v4PRE2Row8_spec
  · exact v4PRE2Row9_spec
  · exact v4PRE2Row10_spec
  · exact v4PRE2Row11_spec
  · exact v4PRE2Row12_spec
  · exact v4PRE2Row13_spec
  · exact v4PRE2Row14_spec
  · exact v4PRE2Row15_spec
  · exact v4PRE2Row16_spec
  · exact v4PRE2Row17_spec
  · exact v4PRE2Row18_spec
  · exact v4PRE2Row19_spec
  · exact v4PRE2Row20_spec
  · exact v4PRE2Row21_spec
  · exact v4PRE2Row22_spec
  · exact v4PRE2Row23_spec
  · exact v4PRE2Row24_spec
  · exact v4PRE2Row25_spec
  · exact v4PRE2Row26_spec
  · exact v4PRE2Row27_spec
  · exact v4PRE2Row28_spec
  · exact v4PRE2Row29_spec
  · exact v4PRE2Row30_spec
  · exact v4PRE2Row31_spec
  · exact v4PRE2Row32_spec
  · exact v4PRE2Row33_spec
  · exact v4PRE2Row34_spec
  · exact v4PRE2Row35_spec
  · exact v4PRE2Row36_spec
  · exact v4PRE2Row37_spec
  · exact v4PRE2Row38_spec
  · exact v4PRE2Row39_spec
  · exact v4PRE2Row40_spec
  · exact v4PRE2Row41_spec
  · exact v4PRE2Row42_spec
  · exact v4PRE2Row43_spec
  · exact v4PRE2Row44_spec
  · exact v4PRE2Row45_spec
  · exact v4PRE2Row46_spec
  · exact v4PRE2Row47_spec
  · exact v4PRE2Row48_spec
  · exact v4PRE2Row49_spec
  · exact v4PRE2Row50_spec
  · exact v4PRE2Row51_spec
  · exact v4PRE2Row52_spec
  · exact v4PRE2Row53_spec
  · exact v4PRE2Row54_spec
  · exact v4PRE2Row55_spec
  · exact v4PRE2Row56_spec
  · exact v4PRE2Row57_spec

private theorem v4PRE2Left_length :
    (rectangularize 58 86 (Two.mul EData V4PRE1Data)).length = 58 := by
  decide

private theorem v4PRE2Right_length :
    (rectangularize 58 86 V4PRE2Data).length = 58 := by
  decide

-- Exact bidegree bound (57, 85); no row or column is discarded.
private theorem v4PRE2Data_spec :
    rectangularize 58 86 (Two.mul EData V4PRE1Data) =
      rectangularize 58 86 V4PRE2Data := by
  apply List.ext_getElem (v4PRE2Left_length.trans v4PRE2Right_length.symm)
  intro n hn _
  rw [List.getElem_eq_getD [], List.getElem_eq_getD []]
  rw [v4PRE2Left_length] at hn
  rw [getD_rectangularize 58 86 (Two.mul EData V4PRE1Data) n hn,
    ← mulRow_eq_getD]
  exact v4PRE2Rows_spec n hn

private theorem v4PRE3Row0_spec :
    padOne 88 (mulRow EData V4PRE2Data 0) =
      (rectangularize 60 88 V4PRE3Data).getD 0 [] := by
  decide

private theorem v4PRE3Row1_spec :
    padOne 88 (mulRow EData V4PRE2Data 1) =
      (rectangularize 60 88 V4PRE3Data).getD 1 [] := by
  decide

private theorem v4PRE3Row2_spec :
    padOne 88 (mulRow EData V4PRE2Data 2) =
      (rectangularize 60 88 V4PRE3Data).getD 2 [] := by
  decide

private theorem v4PRE3Row3_spec :
    padOne 88 (mulRow EData V4PRE2Data 3) =
      (rectangularize 60 88 V4PRE3Data).getD 3 [] := by
  decide

private theorem v4PRE3Row4_spec :
    padOne 88 (mulRow EData V4PRE2Data 4) =
      (rectangularize 60 88 V4PRE3Data).getD 4 [] := by
  decide

private theorem v4PRE3Row5_spec :
    padOne 88 (mulRow EData V4PRE2Data 5) =
      (rectangularize 60 88 V4PRE3Data).getD 5 [] := by
  decide

private theorem v4PRE3Row6_coefficients (j : ℕ) (hj : j < 88) :
    mulCoeffTwo EData V4PRE2Data 6 j =
      ((rectangularize 60 88 V4PRE3Data).getD 6 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE3Row6_spec :
    padOne 88 (mulRow EData V4PRE2Data 6) =
      (rectangularize 60 88 V4PRE3Data).getD 6 [] := by
  apply padOne_mulRow_eq_of_coefficients 88 EData V4PRE2Data 6
    ((rectangularize 60 88 V4PRE3Data).getD 6 [])
  · decide
  · have hTargetSupport : (V4PRE3Data.getD 6 []).length ≤ 88 := by
      decide
    rw [getD_rectangularize 60 88 V4PRE3Data 6 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE3Row6_coefficients

private theorem v4PRE3Row7_coefficients (j : ℕ) (hj : j < 88) :
    mulCoeffTwo EData V4PRE2Data 7 j =
      ((rectangularize 60 88 V4PRE3Data).getD 7 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE3Row7_spec :
    padOne 88 (mulRow EData V4PRE2Data 7) =
      (rectangularize 60 88 V4PRE3Data).getD 7 [] := by
  apply padOne_mulRow_eq_of_coefficients 88 EData V4PRE2Data 7
    ((rectangularize 60 88 V4PRE3Data).getD 7 [])
  · decide
  · have hTargetSupport : (V4PRE3Data.getD 7 []).length ≤ 88 := by
      decide
    rw [getD_rectangularize 60 88 V4PRE3Data 7 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE3Row7_coefficients

private theorem v4PRE3Row8_coefficients (j : ℕ) (hj : j < 88) :
    mulCoeffTwo EData V4PRE2Data 8 j =
      ((rectangularize 60 88 V4PRE3Data).getD 8 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE3Row8_spec :
    padOne 88 (mulRow EData V4PRE2Data 8) =
      (rectangularize 60 88 V4PRE3Data).getD 8 [] := by
  apply padOne_mulRow_eq_of_coefficients 88 EData V4PRE2Data 8
    ((rectangularize 60 88 V4PRE3Data).getD 8 [])
  · decide
  · have hTargetSupport : (V4PRE3Data.getD 8 []).length ≤ 88 := by
      decide
    rw [getD_rectangularize 60 88 V4PRE3Data 8 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE3Row8_coefficients

private theorem v4PRE3Row9_coefficients (j : ℕ) (hj : j < 88) :
    mulCoeffTwo EData V4PRE2Data 9 j =
      ((rectangularize 60 88 V4PRE3Data).getD 9 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE3Row9_spec :
    padOne 88 (mulRow EData V4PRE2Data 9) =
      (rectangularize 60 88 V4PRE3Data).getD 9 [] := by
  apply padOne_mulRow_eq_of_coefficients 88 EData V4PRE2Data 9
    ((rectangularize 60 88 V4PRE3Data).getD 9 [])
  · decide
  · have hTargetSupport : (V4PRE3Data.getD 9 []).length ≤ 88 := by
      decide
    rw [getD_rectangularize 60 88 V4PRE3Data 9 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE3Row9_coefficients

private theorem v4PRE3Row10_coefficients (j : ℕ) (hj : j < 88) :
    mulCoeffTwo EData V4PRE2Data 10 j =
      ((rectangularize 60 88 V4PRE3Data).getD 10 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE3Row10_spec :
    padOne 88 (mulRow EData V4PRE2Data 10) =
      (rectangularize 60 88 V4PRE3Data).getD 10 [] := by
  apply padOne_mulRow_eq_of_coefficients 88 EData V4PRE2Data 10
    ((rectangularize 60 88 V4PRE3Data).getD 10 [])
  · decide
  · have hTargetSupport : (V4PRE3Data.getD 10 []).length ≤ 88 := by
      decide
    rw [getD_rectangularize 60 88 V4PRE3Data 10 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE3Row10_coefficients

private theorem v4PRE3Row11_coefficients (j : ℕ) (hj : j < 88) :
    mulCoeffTwo EData V4PRE2Data 11 j =
      ((rectangularize 60 88 V4PRE3Data).getD 11 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE3Row11_spec :
    padOne 88 (mulRow EData V4PRE2Data 11) =
      (rectangularize 60 88 V4PRE3Data).getD 11 [] := by
  apply padOne_mulRow_eq_of_coefficients 88 EData V4PRE2Data 11
    ((rectangularize 60 88 V4PRE3Data).getD 11 [])
  · decide
  · have hTargetSupport : (V4PRE3Data.getD 11 []).length ≤ 88 := by
      decide
    rw [getD_rectangularize 60 88 V4PRE3Data 11 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE3Row11_coefficients

private theorem v4PRE3Row12_coefficients (j : ℕ) (hj : j < 88) :
    mulCoeffTwo EData V4PRE2Data 12 j =
      ((rectangularize 60 88 V4PRE3Data).getD 12 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE3Row12_spec :
    padOne 88 (mulRow EData V4PRE2Data 12) =
      (rectangularize 60 88 V4PRE3Data).getD 12 [] := by
  apply padOne_mulRow_eq_of_coefficients 88 EData V4PRE2Data 12
    ((rectangularize 60 88 V4PRE3Data).getD 12 [])
  · decide
  · have hTargetSupport : (V4PRE3Data.getD 12 []).length ≤ 88 := by
      decide
    rw [getD_rectangularize 60 88 V4PRE3Data 12 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE3Row12_coefficients

private theorem v4PRE3Row13_coefficients (j : ℕ) (hj : j < 88) :
    mulCoeffTwo EData V4PRE2Data 13 j =
      ((rectangularize 60 88 V4PRE3Data).getD 13 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE3Row13_spec :
    padOne 88 (mulRow EData V4PRE2Data 13) =
      (rectangularize 60 88 V4PRE3Data).getD 13 [] := by
  apply padOne_mulRow_eq_of_coefficients 88 EData V4PRE2Data 13
    ((rectangularize 60 88 V4PRE3Data).getD 13 [])
  · decide
  · have hTargetSupport : (V4PRE3Data.getD 13 []).length ≤ 88 := by
      decide
    rw [getD_rectangularize 60 88 V4PRE3Data 13 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE3Row13_coefficients

private theorem v4PRE3Row14_coefficients (j : ℕ) (hj : j < 88) :
    mulCoeffTwo EData V4PRE2Data 14 j =
      ((rectangularize 60 88 V4PRE3Data).getD 14 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE3Row14_spec :
    padOne 88 (mulRow EData V4PRE2Data 14) =
      (rectangularize 60 88 V4PRE3Data).getD 14 [] := by
  apply padOne_mulRow_eq_of_coefficients 88 EData V4PRE2Data 14
    ((rectangularize 60 88 V4PRE3Data).getD 14 [])
  · decide
  · have hTargetSupport : (V4PRE3Data.getD 14 []).length ≤ 88 := by
      decide
    rw [getD_rectangularize 60 88 V4PRE3Data 14 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE3Row14_coefficients

private theorem v4PRE3Row15_coefficients (j : ℕ) (hj : j < 88) :
    mulCoeffTwo EData V4PRE2Data 15 j =
      ((rectangularize 60 88 V4PRE3Data).getD 15 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE3Row15_spec :
    padOne 88 (mulRow EData V4PRE2Data 15) =
      (rectangularize 60 88 V4PRE3Data).getD 15 [] := by
  apply padOne_mulRow_eq_of_coefficients 88 EData V4PRE2Data 15
    ((rectangularize 60 88 V4PRE3Data).getD 15 [])
  · decide
  · have hTargetSupport : (V4PRE3Data.getD 15 []).length ≤ 88 := by
      decide
    rw [getD_rectangularize 60 88 V4PRE3Data 15 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE3Row15_coefficients

private theorem v4PRE3Row16_coefficients (j : ℕ) (hj : j < 88) :
    mulCoeffTwo EData V4PRE2Data 16 j =
      ((rectangularize 60 88 V4PRE3Data).getD 16 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE3Row16_spec :
    padOne 88 (mulRow EData V4PRE2Data 16) =
      (rectangularize 60 88 V4PRE3Data).getD 16 [] := by
  apply padOne_mulRow_eq_of_coefficients 88 EData V4PRE2Data 16
    ((rectangularize 60 88 V4PRE3Data).getD 16 [])
  · decide
  · have hTargetSupport : (V4PRE3Data.getD 16 []).length ≤ 88 := by
      decide
    rw [getD_rectangularize 60 88 V4PRE3Data 16 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE3Row16_coefficients

private theorem v4PRE3Row17_coefficients (j : ℕ) (hj : j < 88) :
    mulCoeffTwo EData V4PRE2Data 17 j =
      ((rectangularize 60 88 V4PRE3Data).getD 17 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE3Row17_spec :
    padOne 88 (mulRow EData V4PRE2Data 17) =
      (rectangularize 60 88 V4PRE3Data).getD 17 [] := by
  apply padOne_mulRow_eq_of_coefficients 88 EData V4PRE2Data 17
    ((rectangularize 60 88 V4PRE3Data).getD 17 [])
  · decide
  · have hTargetSupport : (V4PRE3Data.getD 17 []).length ≤ 88 := by
      decide
    rw [getD_rectangularize 60 88 V4PRE3Data 17 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE3Row17_coefficients

private theorem v4PRE3Row18_coefficients (j : ℕ) (hj : j < 88) :
    mulCoeffTwo EData V4PRE2Data 18 j =
      ((rectangularize 60 88 V4PRE3Data).getD 18 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE3Row18_spec :
    padOne 88 (mulRow EData V4PRE2Data 18) =
      (rectangularize 60 88 V4PRE3Data).getD 18 [] := by
  apply padOne_mulRow_eq_of_coefficients 88 EData V4PRE2Data 18
    ((rectangularize 60 88 V4PRE3Data).getD 18 [])
  · decide
  · have hTargetSupport : (V4PRE3Data.getD 18 []).length ≤ 88 := by
      decide
    rw [getD_rectangularize 60 88 V4PRE3Data 18 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE3Row18_coefficients

private theorem v4PRE3Row19_coefficients (j : ℕ) (hj : j < 88) :
    mulCoeffTwo EData V4PRE2Data 19 j =
      ((rectangularize 60 88 V4PRE3Data).getD 19 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE3Row19_spec :
    padOne 88 (mulRow EData V4PRE2Data 19) =
      (rectangularize 60 88 V4PRE3Data).getD 19 [] := by
  apply padOne_mulRow_eq_of_coefficients 88 EData V4PRE2Data 19
    ((rectangularize 60 88 V4PRE3Data).getD 19 [])
  · decide
  · have hTargetSupport : (V4PRE3Data.getD 19 []).length ≤ 88 := by
      decide
    rw [getD_rectangularize 60 88 V4PRE3Data 19 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE3Row19_coefficients

private theorem v4PRE3Row20_coefficients (j : ℕ) (hj : j < 88) :
    mulCoeffTwo EData V4PRE2Data 20 j =
      ((rectangularize 60 88 V4PRE3Data).getD 20 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE3Row20_spec :
    padOne 88 (mulRow EData V4PRE2Data 20) =
      (rectangularize 60 88 V4PRE3Data).getD 20 [] := by
  apply padOne_mulRow_eq_of_coefficients 88 EData V4PRE2Data 20
    ((rectangularize 60 88 V4PRE3Data).getD 20 [])
  · decide
  · have hTargetSupport : (V4PRE3Data.getD 20 []).length ≤ 88 := by
      decide
    rw [getD_rectangularize 60 88 V4PRE3Data 20 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE3Row20_coefficients

private theorem v4PRE3Row21_coefficients (j : ℕ) (hj : j < 88) :
    mulCoeffTwo EData V4PRE2Data 21 j =
      ((rectangularize 60 88 V4PRE3Data).getD 21 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE3Row21_spec :
    padOne 88 (mulRow EData V4PRE2Data 21) =
      (rectangularize 60 88 V4PRE3Data).getD 21 [] := by
  apply padOne_mulRow_eq_of_coefficients 88 EData V4PRE2Data 21
    ((rectangularize 60 88 V4PRE3Data).getD 21 [])
  · decide
  · have hTargetSupport : (V4PRE3Data.getD 21 []).length ≤ 88 := by
      decide
    rw [getD_rectangularize 60 88 V4PRE3Data 21 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE3Row21_coefficients

private theorem v4PRE3Row22_coefficients (j : ℕ) (hj : j < 88) :
    mulCoeffTwo EData V4PRE2Data 22 j =
      ((rectangularize 60 88 V4PRE3Data).getD 22 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE3Row22_spec :
    padOne 88 (mulRow EData V4PRE2Data 22) =
      (rectangularize 60 88 V4PRE3Data).getD 22 [] := by
  apply padOne_mulRow_eq_of_coefficients 88 EData V4PRE2Data 22
    ((rectangularize 60 88 V4PRE3Data).getD 22 [])
  · decide
  · have hTargetSupport : (V4PRE3Data.getD 22 []).length ≤ 88 := by
      decide
    rw [getD_rectangularize 60 88 V4PRE3Data 22 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE3Row22_coefficients

private theorem v4PRE3Row23_coefficients (j : ℕ) (hj : j < 88) :
    mulCoeffTwo EData V4PRE2Data 23 j =
      ((rectangularize 60 88 V4PRE3Data).getD 23 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE3Row23_spec :
    padOne 88 (mulRow EData V4PRE2Data 23) =
      (rectangularize 60 88 V4PRE3Data).getD 23 [] := by
  apply padOne_mulRow_eq_of_coefficients 88 EData V4PRE2Data 23
    ((rectangularize 60 88 V4PRE3Data).getD 23 [])
  · decide
  · have hTargetSupport : (V4PRE3Data.getD 23 []).length ≤ 88 := by
      decide
    rw [getD_rectangularize 60 88 V4PRE3Data 23 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE3Row23_coefficients

private theorem v4PRE3Row24_coefficients (j : ℕ) (hj : j < 88) :
    mulCoeffTwo EData V4PRE2Data 24 j =
      ((rectangularize 60 88 V4PRE3Data).getD 24 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE3Row24_spec :
    padOne 88 (mulRow EData V4PRE2Data 24) =
      (rectangularize 60 88 V4PRE3Data).getD 24 [] := by
  apply padOne_mulRow_eq_of_coefficients 88 EData V4PRE2Data 24
    ((rectangularize 60 88 V4PRE3Data).getD 24 [])
  · decide
  · have hTargetSupport : (V4PRE3Data.getD 24 []).length ≤ 88 := by
      decide
    rw [getD_rectangularize 60 88 V4PRE3Data 24 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE3Row24_coefficients

private theorem v4PRE3Row25_coefficients (j : ℕ) (hj : j < 88) :
    mulCoeffTwo EData V4PRE2Data 25 j =
      ((rectangularize 60 88 V4PRE3Data).getD 25 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE3Row25_spec :
    padOne 88 (mulRow EData V4PRE2Data 25) =
      (rectangularize 60 88 V4PRE3Data).getD 25 [] := by
  apply padOne_mulRow_eq_of_coefficients 88 EData V4PRE2Data 25
    ((rectangularize 60 88 V4PRE3Data).getD 25 [])
  · decide
  · have hTargetSupport : (V4PRE3Data.getD 25 []).length ≤ 88 := by
      decide
    rw [getD_rectangularize 60 88 V4PRE3Data 25 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE3Row25_coefficients

private theorem v4PRE3Row26_coefficients (j : ℕ) (hj : j < 88) :
    mulCoeffTwo EData V4PRE2Data 26 j =
      ((rectangularize 60 88 V4PRE3Data).getD 26 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE3Row26_spec :
    padOne 88 (mulRow EData V4PRE2Data 26) =
      (rectangularize 60 88 V4PRE3Data).getD 26 [] := by
  apply padOne_mulRow_eq_of_coefficients 88 EData V4PRE2Data 26
    ((rectangularize 60 88 V4PRE3Data).getD 26 [])
  · decide
  · have hTargetSupport : (V4PRE3Data.getD 26 []).length ≤ 88 := by
      decide
    rw [getD_rectangularize 60 88 V4PRE3Data 26 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE3Row26_coefficients

private theorem v4PRE3Row27_coefficients (j : ℕ) (hj : j < 88) :
    mulCoeffTwo EData V4PRE2Data 27 j =
      ((rectangularize 60 88 V4PRE3Data).getD 27 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE3Row27_spec :
    padOne 88 (mulRow EData V4PRE2Data 27) =
      (rectangularize 60 88 V4PRE3Data).getD 27 [] := by
  apply padOne_mulRow_eq_of_coefficients 88 EData V4PRE2Data 27
    ((rectangularize 60 88 V4PRE3Data).getD 27 [])
  · decide
  · have hTargetSupport : (V4PRE3Data.getD 27 []).length ≤ 88 := by
      decide
    rw [getD_rectangularize 60 88 V4PRE3Data 27 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE3Row27_coefficients

private theorem v4PRE3Row28_coefficients (j : ℕ) (hj : j < 88) :
    mulCoeffTwo EData V4PRE2Data 28 j =
      ((rectangularize 60 88 V4PRE3Data).getD 28 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE3Row28_spec :
    padOne 88 (mulRow EData V4PRE2Data 28) =
      (rectangularize 60 88 V4PRE3Data).getD 28 [] := by
  apply padOne_mulRow_eq_of_coefficients 88 EData V4PRE2Data 28
    ((rectangularize 60 88 V4PRE3Data).getD 28 [])
  · decide
  · have hTargetSupport : (V4PRE3Data.getD 28 []).length ≤ 88 := by
      decide
    rw [getD_rectangularize 60 88 V4PRE3Data 28 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE3Row28_coefficients

private theorem v4PRE3Row29_coefficients (j : ℕ) (hj : j < 88) :
    mulCoeffTwo EData V4PRE2Data 29 j =
      ((rectangularize 60 88 V4PRE3Data).getD 29 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE3Row29_spec :
    padOne 88 (mulRow EData V4PRE2Data 29) =
      (rectangularize 60 88 V4PRE3Data).getD 29 [] := by
  apply padOne_mulRow_eq_of_coefficients 88 EData V4PRE2Data 29
    ((rectangularize 60 88 V4PRE3Data).getD 29 [])
  · decide
  · have hTargetSupport : (V4PRE3Data.getD 29 []).length ≤ 88 := by
      decide
    rw [getD_rectangularize 60 88 V4PRE3Data 29 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE3Row29_coefficients

private theorem v4PRE3Row30_coefficients (j : ℕ) (hj : j < 88) :
    mulCoeffTwo EData V4PRE2Data 30 j =
      ((rectangularize 60 88 V4PRE3Data).getD 30 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE3Row30_spec :
    padOne 88 (mulRow EData V4PRE2Data 30) =
      (rectangularize 60 88 V4PRE3Data).getD 30 [] := by
  apply padOne_mulRow_eq_of_coefficients 88 EData V4PRE2Data 30
    ((rectangularize 60 88 V4PRE3Data).getD 30 [])
  · decide
  · have hTargetSupport : (V4PRE3Data.getD 30 []).length ≤ 88 := by
      decide
    rw [getD_rectangularize 60 88 V4PRE3Data 30 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE3Row30_coefficients

private theorem v4PRE3Row31_coefficients (j : ℕ) (hj : j < 88) :
    mulCoeffTwo EData V4PRE2Data 31 j =
      ((rectangularize 60 88 V4PRE3Data).getD 31 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE3Row31_spec :
    padOne 88 (mulRow EData V4PRE2Data 31) =
      (rectangularize 60 88 V4PRE3Data).getD 31 [] := by
  apply padOne_mulRow_eq_of_coefficients 88 EData V4PRE2Data 31
    ((rectangularize 60 88 V4PRE3Data).getD 31 [])
  · decide
  · have hTargetSupport : (V4PRE3Data.getD 31 []).length ≤ 88 := by
      decide
    rw [getD_rectangularize 60 88 V4PRE3Data 31 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE3Row31_coefficients

private theorem v4PRE3Row32_coefficients (j : ℕ) (hj : j < 88) :
    mulCoeffTwo EData V4PRE2Data 32 j =
      ((rectangularize 60 88 V4PRE3Data).getD 32 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE3Row32_spec :
    padOne 88 (mulRow EData V4PRE2Data 32) =
      (rectangularize 60 88 V4PRE3Data).getD 32 [] := by
  apply padOne_mulRow_eq_of_coefficients 88 EData V4PRE2Data 32
    ((rectangularize 60 88 V4PRE3Data).getD 32 [])
  · decide
  · have hTargetSupport : (V4PRE3Data.getD 32 []).length ≤ 88 := by
      decide
    rw [getD_rectangularize 60 88 V4PRE3Data 32 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE3Row32_coefficients

private theorem v4PRE3Row33_coefficients (j : ℕ) (hj : j < 88) :
    mulCoeffTwo EData V4PRE2Data 33 j =
      ((rectangularize 60 88 V4PRE3Data).getD 33 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE3Row33_spec :
    padOne 88 (mulRow EData V4PRE2Data 33) =
      (rectangularize 60 88 V4PRE3Data).getD 33 [] := by
  apply padOne_mulRow_eq_of_coefficients 88 EData V4PRE2Data 33
    ((rectangularize 60 88 V4PRE3Data).getD 33 [])
  · decide
  · have hTargetSupport : (V4PRE3Data.getD 33 []).length ≤ 88 := by
      decide
    rw [getD_rectangularize 60 88 V4PRE3Data 33 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE3Row33_coefficients

private theorem v4PRE3Row34_coefficients (j : ℕ) (hj : j < 88) :
    mulCoeffTwo EData V4PRE2Data 34 j =
      ((rectangularize 60 88 V4PRE3Data).getD 34 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE3Row34_spec :
    padOne 88 (mulRow EData V4PRE2Data 34) =
      (rectangularize 60 88 V4PRE3Data).getD 34 [] := by
  apply padOne_mulRow_eq_of_coefficients 88 EData V4PRE2Data 34
    ((rectangularize 60 88 V4PRE3Data).getD 34 [])
  · decide
  · have hTargetSupport : (V4PRE3Data.getD 34 []).length ≤ 88 := by
      decide
    rw [getD_rectangularize 60 88 V4PRE3Data 34 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE3Row34_coefficients

private theorem v4PRE3Row35_coefficients (j : ℕ) (hj : j < 88) :
    mulCoeffTwo EData V4PRE2Data 35 j =
      ((rectangularize 60 88 V4PRE3Data).getD 35 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE3Row35_spec :
    padOne 88 (mulRow EData V4PRE2Data 35) =
      (rectangularize 60 88 V4PRE3Data).getD 35 [] := by
  apply padOne_mulRow_eq_of_coefficients 88 EData V4PRE2Data 35
    ((rectangularize 60 88 V4PRE3Data).getD 35 [])
  · decide
  · have hTargetSupport : (V4PRE3Data.getD 35 []).length ≤ 88 := by
      decide
    rw [getD_rectangularize 60 88 V4PRE3Data 35 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE3Row35_coefficients

private theorem v4PRE3Row36_coefficients (j : ℕ) (hj : j < 88) :
    mulCoeffTwo EData V4PRE2Data 36 j =
      ((rectangularize 60 88 V4PRE3Data).getD 36 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE3Row36_spec :
    padOne 88 (mulRow EData V4PRE2Data 36) =
      (rectangularize 60 88 V4PRE3Data).getD 36 [] := by
  apply padOne_mulRow_eq_of_coefficients 88 EData V4PRE2Data 36
    ((rectangularize 60 88 V4PRE3Data).getD 36 [])
  · decide
  · have hTargetSupport : (V4PRE3Data.getD 36 []).length ≤ 88 := by
      decide
    rw [getD_rectangularize 60 88 V4PRE3Data 36 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE3Row36_coefficients

private theorem v4PRE3Row37_coefficients (j : ℕ) (hj : j < 88) :
    mulCoeffTwo EData V4PRE2Data 37 j =
      ((rectangularize 60 88 V4PRE3Data).getD 37 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE3Row37_spec :
    padOne 88 (mulRow EData V4PRE2Data 37) =
      (rectangularize 60 88 V4PRE3Data).getD 37 [] := by
  apply padOne_mulRow_eq_of_coefficients 88 EData V4PRE2Data 37
    ((rectangularize 60 88 V4PRE3Data).getD 37 [])
  · decide
  · have hTargetSupport : (V4PRE3Data.getD 37 []).length ≤ 88 := by
      decide
    rw [getD_rectangularize 60 88 V4PRE3Data 37 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE3Row37_coefficients

private theorem v4PRE3Row38_coefficients (j : ℕ) (hj : j < 88) :
    mulCoeffTwo EData V4PRE2Data 38 j =
      ((rectangularize 60 88 V4PRE3Data).getD 38 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE3Row38_spec :
    padOne 88 (mulRow EData V4PRE2Data 38) =
      (rectangularize 60 88 V4PRE3Data).getD 38 [] := by
  apply padOne_mulRow_eq_of_coefficients 88 EData V4PRE2Data 38
    ((rectangularize 60 88 V4PRE3Data).getD 38 [])
  · decide
  · have hTargetSupport : (V4PRE3Data.getD 38 []).length ≤ 88 := by
      decide
    rw [getD_rectangularize 60 88 V4PRE3Data 38 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE3Row38_coefficients

private theorem v4PRE3Row39_coefficients (j : ℕ) (hj : j < 88) :
    mulCoeffTwo EData V4PRE2Data 39 j =
      ((rectangularize 60 88 V4PRE3Data).getD 39 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE3Row39_spec :
    padOne 88 (mulRow EData V4PRE2Data 39) =
      (rectangularize 60 88 V4PRE3Data).getD 39 [] := by
  apply padOne_mulRow_eq_of_coefficients 88 EData V4PRE2Data 39
    ((rectangularize 60 88 V4PRE3Data).getD 39 [])
  · decide
  · have hTargetSupport : (V4PRE3Data.getD 39 []).length ≤ 88 := by
      decide
    rw [getD_rectangularize 60 88 V4PRE3Data 39 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE3Row39_coefficients

private theorem v4PRE3Row40_coefficients (j : ℕ) (hj : j < 88) :
    mulCoeffTwo EData V4PRE2Data 40 j =
      ((rectangularize 60 88 V4PRE3Data).getD 40 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE3Row40_spec :
    padOne 88 (mulRow EData V4PRE2Data 40) =
      (rectangularize 60 88 V4PRE3Data).getD 40 [] := by
  apply padOne_mulRow_eq_of_coefficients 88 EData V4PRE2Data 40
    ((rectangularize 60 88 V4PRE3Data).getD 40 [])
  · decide
  · have hTargetSupport : (V4PRE3Data.getD 40 []).length ≤ 88 := by
      decide
    rw [getD_rectangularize 60 88 V4PRE3Data 40 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE3Row40_coefficients

private theorem v4PRE3Row41_coefficients (j : ℕ) (hj : j < 88) :
    mulCoeffTwo EData V4PRE2Data 41 j =
      ((rectangularize 60 88 V4PRE3Data).getD 41 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE3Row41_spec :
    padOne 88 (mulRow EData V4PRE2Data 41) =
      (rectangularize 60 88 V4PRE3Data).getD 41 [] := by
  apply padOne_mulRow_eq_of_coefficients 88 EData V4PRE2Data 41
    ((rectangularize 60 88 V4PRE3Data).getD 41 [])
  · decide
  · have hTargetSupport : (V4PRE3Data.getD 41 []).length ≤ 88 := by
      decide
    rw [getD_rectangularize 60 88 V4PRE3Data 41 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE3Row41_coefficients

private theorem v4PRE3Row42_coefficients (j : ℕ) (hj : j < 88) :
    mulCoeffTwo EData V4PRE2Data 42 j =
      ((rectangularize 60 88 V4PRE3Data).getD 42 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE3Row42_spec :
    padOne 88 (mulRow EData V4PRE2Data 42) =
      (rectangularize 60 88 V4PRE3Data).getD 42 [] := by
  apply padOne_mulRow_eq_of_coefficients 88 EData V4PRE2Data 42
    ((rectangularize 60 88 V4PRE3Data).getD 42 [])
  · decide
  · have hTargetSupport : (V4PRE3Data.getD 42 []).length ≤ 88 := by
      decide
    rw [getD_rectangularize 60 88 V4PRE3Data 42 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE3Row42_coefficients

private theorem v4PRE3Row43_coefficients (j : ℕ) (hj : j < 88) :
    mulCoeffTwo EData V4PRE2Data 43 j =
      ((rectangularize 60 88 V4PRE3Data).getD 43 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE3Row43_spec :
    padOne 88 (mulRow EData V4PRE2Data 43) =
      (rectangularize 60 88 V4PRE3Data).getD 43 [] := by
  apply padOne_mulRow_eq_of_coefficients 88 EData V4PRE2Data 43
    ((rectangularize 60 88 V4PRE3Data).getD 43 [])
  · decide
  · have hTargetSupport : (V4PRE3Data.getD 43 []).length ≤ 88 := by
      decide
    rw [getD_rectangularize 60 88 V4PRE3Data 43 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE3Row43_coefficients

private theorem v4PRE3Row44_coefficients (j : ℕ) (hj : j < 88) :
    mulCoeffTwo EData V4PRE2Data 44 j =
      ((rectangularize 60 88 V4PRE3Data).getD 44 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE3Row44_spec :
    padOne 88 (mulRow EData V4PRE2Data 44) =
      (rectangularize 60 88 V4PRE3Data).getD 44 [] := by
  apply padOne_mulRow_eq_of_coefficients 88 EData V4PRE2Data 44
    ((rectangularize 60 88 V4PRE3Data).getD 44 [])
  · decide
  · have hTargetSupport : (V4PRE3Data.getD 44 []).length ≤ 88 := by
      decide
    rw [getD_rectangularize 60 88 V4PRE3Data 44 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE3Row44_coefficients

private theorem v4PRE3Row45_coefficients (j : ℕ) (hj : j < 88) :
    mulCoeffTwo EData V4PRE2Data 45 j =
      ((rectangularize 60 88 V4PRE3Data).getD 45 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE3Row45_spec :
    padOne 88 (mulRow EData V4PRE2Data 45) =
      (rectangularize 60 88 V4PRE3Data).getD 45 [] := by
  apply padOne_mulRow_eq_of_coefficients 88 EData V4PRE2Data 45
    ((rectangularize 60 88 V4PRE3Data).getD 45 [])
  · decide
  · have hTargetSupport : (V4PRE3Data.getD 45 []).length ≤ 88 := by
      decide
    rw [getD_rectangularize 60 88 V4PRE3Data 45 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE3Row45_coefficients

private theorem v4PRE3Row46_coefficients (j : ℕ) (hj : j < 88) :
    mulCoeffTwo EData V4PRE2Data 46 j =
      ((rectangularize 60 88 V4PRE3Data).getD 46 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE3Row46_spec :
    padOne 88 (mulRow EData V4PRE2Data 46) =
      (rectangularize 60 88 V4PRE3Data).getD 46 [] := by
  apply padOne_mulRow_eq_of_coefficients 88 EData V4PRE2Data 46
    ((rectangularize 60 88 V4PRE3Data).getD 46 [])
  · decide
  · have hTargetSupport : (V4PRE3Data.getD 46 []).length ≤ 88 := by
      decide
    rw [getD_rectangularize 60 88 V4PRE3Data 46 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE3Row46_coefficients

private theorem v4PRE3Row47_coefficients (j : ℕ) (hj : j < 88) :
    mulCoeffTwo EData V4PRE2Data 47 j =
      ((rectangularize 60 88 V4PRE3Data).getD 47 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE3Row47_spec :
    padOne 88 (mulRow EData V4PRE2Data 47) =
      (rectangularize 60 88 V4PRE3Data).getD 47 [] := by
  apply padOne_mulRow_eq_of_coefficients 88 EData V4PRE2Data 47
    ((rectangularize 60 88 V4PRE3Data).getD 47 [])
  · decide
  · have hTargetSupport : (V4PRE3Data.getD 47 []).length ≤ 88 := by
      decide
    rw [getD_rectangularize 60 88 V4PRE3Data 47 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE3Row47_coefficients

private theorem v4PRE3Row48_coefficients (j : ℕ) (hj : j < 88) :
    mulCoeffTwo EData V4PRE2Data 48 j =
      ((rectangularize 60 88 V4PRE3Data).getD 48 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE3Row48_spec :
    padOne 88 (mulRow EData V4PRE2Data 48) =
      (rectangularize 60 88 V4PRE3Data).getD 48 [] := by
  apply padOne_mulRow_eq_of_coefficients 88 EData V4PRE2Data 48
    ((rectangularize 60 88 V4PRE3Data).getD 48 [])
  · decide
  · have hTargetSupport : (V4PRE3Data.getD 48 []).length ≤ 88 := by
      decide
    rw [getD_rectangularize 60 88 V4PRE3Data 48 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE3Row48_coefficients

private theorem v4PRE3Row49_coefficients (j : ℕ) (hj : j < 88) :
    mulCoeffTwo EData V4PRE2Data 49 j =
      ((rectangularize 60 88 V4PRE3Data).getD 49 []).getD j 0 := by
  interval_cases j <;> decide

private theorem v4PRE3Row49_spec :
    padOne 88 (mulRow EData V4PRE2Data 49) =
      (rectangularize 60 88 V4PRE3Data).getD 49 [] := by
  apply padOne_mulRow_eq_of_coefficients 88 EData V4PRE2Data 49
    ((rectangularize 60 88 V4PRE3Data).getD 49 [])
  · decide
  · have hTargetSupport : (V4PRE3Data.getD 49 []).length ≤ 88 := by
      decide
    rw [getD_rectangularize 60 88 V4PRE3Data 49 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PRE3Row49_coefficients

private theorem v4PRE3Row50_spec :
    padOne 88 (mulRow EData V4PRE2Data 50) =
      (rectangularize 60 88 V4PRE3Data).getD 50 [] := by
  decide

private theorem v4PRE3Row51_spec :
    padOne 88 (mulRow EData V4PRE2Data 51) =
      (rectangularize 60 88 V4PRE3Data).getD 51 [] := by
  decide

private theorem v4PRE3Row52_spec :
    padOne 88 (mulRow EData V4PRE2Data 52) =
      (rectangularize 60 88 V4PRE3Data).getD 52 [] := by
  decide

private theorem v4PRE3Row53_spec :
    padOne 88 (mulRow EData V4PRE2Data 53) =
      (rectangularize 60 88 V4PRE3Data).getD 53 [] := by
  decide

private theorem v4PRE3Row54_spec :
    padOne 88 (mulRow EData V4PRE2Data 54) =
      (rectangularize 60 88 V4PRE3Data).getD 54 [] := by
  decide

private theorem v4PRE3Row55_spec :
    padOne 88 (mulRow EData V4PRE2Data 55) =
      (rectangularize 60 88 V4PRE3Data).getD 55 [] := by
  decide

private theorem v4PRE3Row56_spec :
    padOne 88 (mulRow EData V4PRE2Data 56) =
      (rectangularize 60 88 V4PRE3Data).getD 56 [] := by
  decide

private theorem v4PRE3Row57_spec :
    padOne 88 (mulRow EData V4PRE2Data 57) =
      (rectangularize 60 88 V4PRE3Data).getD 57 [] := by
  decide

private theorem v4PRE3Row58_spec :
    padOne 88 (mulRow EData V4PRE2Data 58) =
      (rectangularize 60 88 V4PRE3Data).getD 58 [] := by
  decide

private theorem v4PRE3Row59_spec :
    padOne 88 (mulRow EData V4PRE2Data 59) =
      (rectangularize 60 88 V4PRE3Data).getD 59 [] := by
  decide

private theorem v4PRE3Rows_spec (n : ℕ) (hn : n < 60) :
    padOne 88 (mulRow EData V4PRE2Data n) =
      (rectangularize 60 88 V4PRE3Data).getD n [] := by
  have hCases :
    n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨
    n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨
    n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨
    n = 15 ∨ n = 16 ∨ n = 17 ∨ n = 18 ∨ n = 19 ∨
    n = 20 ∨ n = 21 ∨ n = 22 ∨ n = 23 ∨ n = 24 ∨
    n = 25 ∨ n = 26 ∨ n = 27 ∨ n = 28 ∨ n = 29 ∨
    n = 30 ∨ n = 31 ∨ n = 32 ∨ n = 33 ∨ n = 34 ∨
    n = 35 ∨ n = 36 ∨ n = 37 ∨ n = 38 ∨ n = 39 ∨
    n = 40 ∨ n = 41 ∨ n = 42 ∨ n = 43 ∨ n = 44 ∨
    n = 45 ∨ n = 46 ∨ n = 47 ∨ n = 48 ∨ n = 49 ∨
    n = 50 ∨ n = 51 ∨ n = 52 ∨ n = 53 ∨ n = 54 ∨
    n = 55 ∨ n = 56 ∨ n = 57 ∨ n = 58 ∨ n = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact v4PRE3Row0_spec
  · exact v4PRE3Row1_spec
  · exact v4PRE3Row2_spec
  · exact v4PRE3Row3_spec
  · exact v4PRE3Row4_spec
  · exact v4PRE3Row5_spec
  · exact v4PRE3Row6_spec
  · exact v4PRE3Row7_spec
  · exact v4PRE3Row8_spec
  · exact v4PRE3Row9_spec
  · exact v4PRE3Row10_spec
  · exact v4PRE3Row11_spec
  · exact v4PRE3Row12_spec
  · exact v4PRE3Row13_spec
  · exact v4PRE3Row14_spec
  · exact v4PRE3Row15_spec
  · exact v4PRE3Row16_spec
  · exact v4PRE3Row17_spec
  · exact v4PRE3Row18_spec
  · exact v4PRE3Row19_spec
  · exact v4PRE3Row20_spec
  · exact v4PRE3Row21_spec
  · exact v4PRE3Row22_spec
  · exact v4PRE3Row23_spec
  · exact v4PRE3Row24_spec
  · exact v4PRE3Row25_spec
  · exact v4PRE3Row26_spec
  · exact v4PRE3Row27_spec
  · exact v4PRE3Row28_spec
  · exact v4PRE3Row29_spec
  · exact v4PRE3Row30_spec
  · exact v4PRE3Row31_spec
  · exact v4PRE3Row32_spec
  · exact v4PRE3Row33_spec
  · exact v4PRE3Row34_spec
  · exact v4PRE3Row35_spec
  · exact v4PRE3Row36_spec
  · exact v4PRE3Row37_spec
  · exact v4PRE3Row38_spec
  · exact v4PRE3Row39_spec
  · exact v4PRE3Row40_spec
  · exact v4PRE3Row41_spec
  · exact v4PRE3Row42_spec
  · exact v4PRE3Row43_spec
  · exact v4PRE3Row44_spec
  · exact v4PRE3Row45_spec
  · exact v4PRE3Row46_spec
  · exact v4PRE3Row47_spec
  · exact v4PRE3Row48_spec
  · exact v4PRE3Row49_spec
  · exact v4PRE3Row50_spec
  · exact v4PRE3Row51_spec
  · exact v4PRE3Row52_spec
  · exact v4PRE3Row53_spec
  · exact v4PRE3Row54_spec
  · exact v4PRE3Row55_spec
  · exact v4PRE3Row56_spec
  · exact v4PRE3Row57_spec
  · exact v4PRE3Row58_spec
  · exact v4PRE3Row59_spec

private theorem v4PRE3Left_length :
    (rectangularize 60 88 (Two.mul EData V4PRE2Data)).length = 60 := by
  decide

private theorem v4PRE3Right_length :
    (rectangularize 60 88 V4PRE3Data).length = 60 := by
  decide

-- Exact bidegree bound (59, 87); no row or column is discarded.
private theorem v4PRE3Data_spec :
    rectangularize 60 88 (Two.mul EData V4PRE2Data) =
      rectangularize 60 88 V4PRE3Data := by
  apply List.ext_getElem (v4PRE3Left_length.trans v4PRE3Right_length.symm)
  intro n hn _
  rw [List.getElem_eq_getD [], List.getElem_eq_getD []]
  rw [v4PRE3Left_length] at hn
  rw [getD_rectangularize 60 88 (Two.mul EData V4PRE2Data) n hn,
    ← mulRow_eq_getD]
  exact v4PRE3Rows_spec n hn

/-- Evaluation of the checked `r * s * B^3 * G * E^3` branch of `P9`. -/
theorem eval_v4PRightData (r s : ℚ) :
    Two.eval V4PRE3Data r s =
      OrderTwentyFiveRelationZeroCertificate.Internal.E r s ^ 3 *
        OrderTwentyFiveRawOrbitFactorCertificate.G r s *
          OrderTwentyFiveRelationZeroCertificate.Internal.B r s ^ 3 *
            s * r * Two.eval V4JData r s := by
  have hR := congrArg (fun p => Two.eval p r s) v4PRRData_spec
  have hS := congrArg (fun p => Two.eval p r s) v4PRSData_spec
  have hB1 := congrArg (fun p => Two.eval p r s) v4PRB1Data_spec
  have hB2 := congrArg (fun p => Two.eval p r s) v4PRB2Data_spec
  have hB3 := congrArg (fun p => Two.eval p r s) v4PRB3Data_spec
  have hG := congrArg (fun p => Two.eval p r s) v4PRGData_spec
  have hE1 := congrArg (fun p => Two.eval p r s) v4PRE1Data_spec
  have hE2 := congrArg (fun p => Two.eval p r s) v4PRE2Data_spec
  have hE3 := congrArg (fun p => Two.eval p r s) v4PRE3Data_spec
  simp only [eval_rectangularize, Two.eval_mul] at hR hS hB1 hB2 hB3
  simp only [eval_rectangularize, Two.eval_mul] at hG hE1 hE2 hE3
  calc
    Two.eval V4PRE3Data r s =
        Two.eval EData r s * Two.eval V4PRE2Data r s := hE3.symm
    _ = Two.eval EData r s *
        (Two.eval EData r s * Two.eval V4PRE1Data r s) := by rw [← hE2]
    _ = Two.eval EData r s *
        (Two.eval EData r s *
          (Two.eval EData r s * Two.eval V4PRGData r s)) := by rw [← hE1]
    _ = Two.eval EData r s *
        (Two.eval EData r s *
          (Two.eval EData r s *
            (Two.eval GData r s * Two.eval V4PRB3Data r s))) := by rw [← hG]
    _ = Two.eval EData r s *
        (Two.eval EData r s *
          (Two.eval EData r s *
            (Two.eval GData r s *
              (Two.eval BData r s * Two.eval V4PRB2Data r s)))) := by rw [← hB3]
    _ = Two.eval EData r s *
        (Two.eval EData r s *
          (Two.eval EData r s *
            (Two.eval GData r s *
              (Two.eval BData r s *
                (Two.eval BData r s * Two.eval V4PRB1Data r s))))) := by rw [← hB2]
    _ = Two.eval EData r s ^ 3 * Two.eval GData r s *
        Two.eval BData r s ^ 3 * Two.eval SData r s *
          Two.eval RData r s * Two.eval V4JData r s := by
      rw [← hB1, ← hS, ← hR]
      ring
    _ = OrderTwentyFiveRelationZeroCertificate.Internal.E r s ^ 3 *
        OrderTwentyFiveRawOrbitFactorCertificate.G r s *
          OrderTwentyFiveRelationZeroCertificate.Internal.B r s ^ 3 *
            s * r * Two.eval V4JData r s := by
      rw [eval_EData, eval_GData, eval_BData, eval_SData, eval_RData]

end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
