/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialVFourCoreCertificate
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialVFourPLeftData

/-!
# Checked left branch of the canonical P9 factor in raw V fourth power

Each staged dense multiplication is checked row by row within its exact
rectangle, including every possible outer and inner tail.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveRelationZeroCertificate.Dense
open OrderTwentyFiveDensePolynomialRectangular
open OrderTwentyFiveDensePolynomialRowCertificate

private theorem v4PLD1Row0_spec :
    padOne 79 (mulRow DData V4JData 0) =
      (rectangularize 54 79 V4PLD1Data).getD 0 [] := by
  decide

private theorem v4PLD1Row1_spec :
    padOne 79 (mulRow DData V4JData 1) =
      (rectangularize 54 79 V4PLD1Data).getD 1 [] := by
  decide

private theorem v4PLD1Row2_spec :
    padOne 79 (mulRow DData V4JData 2) =
      (rectangularize 54 79 V4PLD1Data).getD 2 [] := by
  decide

private theorem v4PLD1Row3_spec :
    padOne 79 (mulRow DData V4JData 3) =
      (rectangularize 54 79 V4PLD1Data).getD 3 [] := by
  decide

private theorem v4PLD1Row4_spec :
    padOne 79 (mulRow DData V4JData 4) =
      (rectangularize 54 79 V4PLD1Data).getD 4 [] := by
  decide

private theorem v4PLD1Row5_spec :
    padOne 79 (mulRow DData V4JData 5) =
      (rectangularize 54 79 V4PLD1Data).getD 5 [] := by
  decide

private theorem v4PLD1Row6_spec :
    padOne 79 (mulRow DData V4JData 6) =
      (rectangularize 54 79 V4PLD1Data).getD 6 [] := by
  decide

private theorem v4PLD1Row7_spec :
    padOne 79 (mulRow DData V4JData 7) =
      (rectangularize 54 79 V4PLD1Data).getD 7 [] := by
  decide

private theorem v4PLD1Row8_spec :
    padOne 79 (mulRow DData V4JData 8) =
      (rectangularize 54 79 V4PLD1Data).getD 8 [] := by
  decide

private theorem v4PLD1Row9_spec :
    padOne 79 (mulRow DData V4JData 9) =
      (rectangularize 54 79 V4PLD1Data).getD 9 [] := by
  decide

private theorem v4PLD1Row10_spec :
    padOne 79 (mulRow DData V4JData 10) =
      (rectangularize 54 79 V4PLD1Data).getD 10 [] := by
  decide

private theorem v4PLD1Row11_spec :
    padOne 79 (mulRow DData V4JData 11) =
      (rectangularize 54 79 V4PLD1Data).getD 11 [] := by
  decide

private theorem v4PLD1Row12_spec :
    padOne 79 (mulRow DData V4JData 12) =
      (rectangularize 54 79 V4PLD1Data).getD 12 [] := by
  decide

private theorem v4PLD1Row13_spec :
    padOne 79 (mulRow DData V4JData 13) =
      (rectangularize 54 79 V4PLD1Data).getD 13 [] := by
  decide

private theorem v4PLD1Row14_spec :
    padOne 79 (mulRow DData V4JData 14) =
      (rectangularize 54 79 V4PLD1Data).getD 14 [] := by
  decide

private theorem v4PLD1Row15Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4JData 15 j =
      ((rectangularize 54 79 V4PLD1Data).getD 15 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row15Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4JData 15 j =
      ((rectangularize 54 79 V4PLD1Data).getD 15 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row15Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4JData 15 j =
      ((rectangularize 54 79 V4PLD1Data).getD 15 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row15Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4JData 15 j =
      ((rectangularize 54 79 V4PLD1Data).getD 15 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row15Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4JData 15 j =
      ((rectangularize 54 79 V4PLD1Data).getD 15 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row15Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4JData 15 j =
      ((rectangularize 54 79 V4PLD1Data).getD 15 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row15Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4JData 15 j =
      ((rectangularize 54 79 V4PLD1Data).getD 15 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row15Coeffs70To78_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 79) :
    mulCoeffTwo DData V4JData 15 j =
      ((rectangularize 54 79 V4PLD1Data).getD 15 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLD1Row15_coefficients (j : ℕ) (hj : j < 79) :
    mulCoeffTwo DData V4JData 15 j =
      ((rectangularize 54 79 V4PLD1Data).getD 15 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD1Row15Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD1Row15Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD1Row15Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD1Row15Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD1Row15Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD1Row15Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD1Row15Coeffs60To69_spec j (by omega) h70
  exact v4PLD1Row15Coeffs70To78_spec j (by omega) hj

private theorem v4PLD1Row15_spec :
    padOne 79 (mulRow DData V4JData 15) =
      (rectangularize 54 79 V4PLD1Data).getD 15 [] := by
  apply padOne_mulRow_eq_of_coefficients 79 DData V4JData 15
    ((rectangularize 54 79 V4PLD1Data).getD 15 [])
  · decide
  · have hTargetSupport : (V4PLD1Data.getD 15 []).length ≤ 79 := by
      decide
    rw [getD_rectangularize 54 79 V4PLD1Data 15 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD1Row15_coefficients

private theorem v4PLD1Row16Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4JData 16 j =
      ((rectangularize 54 79 V4PLD1Data).getD 16 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row16Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4JData 16 j =
      ((rectangularize 54 79 V4PLD1Data).getD 16 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row16Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4JData 16 j =
      ((rectangularize 54 79 V4PLD1Data).getD 16 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row16Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4JData 16 j =
      ((rectangularize 54 79 V4PLD1Data).getD 16 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row16Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4JData 16 j =
      ((rectangularize 54 79 V4PLD1Data).getD 16 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row16Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4JData 16 j =
      ((rectangularize 54 79 V4PLD1Data).getD 16 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row16Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4JData 16 j =
      ((rectangularize 54 79 V4PLD1Data).getD 16 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row16Coeffs70To78_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 79) :
    mulCoeffTwo DData V4JData 16 j =
      ((rectangularize 54 79 V4PLD1Data).getD 16 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLD1Row16_coefficients (j : ℕ) (hj : j < 79) :
    mulCoeffTwo DData V4JData 16 j =
      ((rectangularize 54 79 V4PLD1Data).getD 16 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD1Row16Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD1Row16Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD1Row16Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD1Row16Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD1Row16Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD1Row16Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD1Row16Coeffs60To69_spec j (by omega) h70
  exact v4PLD1Row16Coeffs70To78_spec j (by omega) hj

private theorem v4PLD1Row16_spec :
    padOne 79 (mulRow DData V4JData 16) =
      (rectangularize 54 79 V4PLD1Data).getD 16 [] := by
  apply padOne_mulRow_eq_of_coefficients 79 DData V4JData 16
    ((rectangularize 54 79 V4PLD1Data).getD 16 [])
  · decide
  · have hTargetSupport : (V4PLD1Data.getD 16 []).length ≤ 79 := by
      decide
    rw [getD_rectangularize 54 79 V4PLD1Data 16 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD1Row16_coefficients

private theorem v4PLD1Row17Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4JData 17 j =
      ((rectangularize 54 79 V4PLD1Data).getD 17 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row17Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4JData 17 j =
      ((rectangularize 54 79 V4PLD1Data).getD 17 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row17Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4JData 17 j =
      ((rectangularize 54 79 V4PLD1Data).getD 17 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row17Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4JData 17 j =
      ((rectangularize 54 79 V4PLD1Data).getD 17 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row17Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4JData 17 j =
      ((rectangularize 54 79 V4PLD1Data).getD 17 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row17Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4JData 17 j =
      ((rectangularize 54 79 V4PLD1Data).getD 17 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row17Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4JData 17 j =
      ((rectangularize 54 79 V4PLD1Data).getD 17 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row17Coeffs70To78_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 79) :
    mulCoeffTwo DData V4JData 17 j =
      ((rectangularize 54 79 V4PLD1Data).getD 17 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLD1Row17_coefficients (j : ℕ) (hj : j < 79) :
    mulCoeffTwo DData V4JData 17 j =
      ((rectangularize 54 79 V4PLD1Data).getD 17 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD1Row17Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD1Row17Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD1Row17Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD1Row17Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD1Row17Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD1Row17Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD1Row17Coeffs60To69_spec j (by omega) h70
  exact v4PLD1Row17Coeffs70To78_spec j (by omega) hj

private theorem v4PLD1Row17_spec :
    padOne 79 (mulRow DData V4JData 17) =
      (rectangularize 54 79 V4PLD1Data).getD 17 [] := by
  apply padOne_mulRow_eq_of_coefficients 79 DData V4JData 17
    ((rectangularize 54 79 V4PLD1Data).getD 17 [])
  · decide
  · have hTargetSupport : (V4PLD1Data.getD 17 []).length ≤ 79 := by
      decide
    rw [getD_rectangularize 54 79 V4PLD1Data 17 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD1Row17_coefficients

private theorem v4PLD1Row18Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4JData 18 j =
      ((rectangularize 54 79 V4PLD1Data).getD 18 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row18Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4JData 18 j =
      ((rectangularize 54 79 V4PLD1Data).getD 18 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row18Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4JData 18 j =
      ((rectangularize 54 79 V4PLD1Data).getD 18 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row18Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4JData 18 j =
      ((rectangularize 54 79 V4PLD1Data).getD 18 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row18Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4JData 18 j =
      ((rectangularize 54 79 V4PLD1Data).getD 18 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row18Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4JData 18 j =
      ((rectangularize 54 79 V4PLD1Data).getD 18 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row18Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4JData 18 j =
      ((rectangularize 54 79 V4PLD1Data).getD 18 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row18Coeffs70To78_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 79) :
    mulCoeffTwo DData V4JData 18 j =
      ((rectangularize 54 79 V4PLD1Data).getD 18 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLD1Row18_coefficients (j : ℕ) (hj : j < 79) :
    mulCoeffTwo DData V4JData 18 j =
      ((rectangularize 54 79 V4PLD1Data).getD 18 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD1Row18Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD1Row18Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD1Row18Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD1Row18Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD1Row18Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD1Row18Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD1Row18Coeffs60To69_spec j (by omega) h70
  exact v4PLD1Row18Coeffs70To78_spec j (by omega) hj

private theorem v4PLD1Row18_spec :
    padOne 79 (mulRow DData V4JData 18) =
      (rectangularize 54 79 V4PLD1Data).getD 18 [] := by
  apply padOne_mulRow_eq_of_coefficients 79 DData V4JData 18
    ((rectangularize 54 79 V4PLD1Data).getD 18 [])
  · decide
  · have hTargetSupport : (V4PLD1Data.getD 18 []).length ≤ 79 := by
      decide
    rw [getD_rectangularize 54 79 V4PLD1Data 18 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD1Row18_coefficients

private theorem v4PLD1Row19Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4JData 19 j =
      ((rectangularize 54 79 V4PLD1Data).getD 19 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row19Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4JData 19 j =
      ((rectangularize 54 79 V4PLD1Data).getD 19 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row19Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4JData 19 j =
      ((rectangularize 54 79 V4PLD1Data).getD 19 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row19Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4JData 19 j =
      ((rectangularize 54 79 V4PLD1Data).getD 19 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row19Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4JData 19 j =
      ((rectangularize 54 79 V4PLD1Data).getD 19 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row19Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4JData 19 j =
      ((rectangularize 54 79 V4PLD1Data).getD 19 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row19Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4JData 19 j =
      ((rectangularize 54 79 V4PLD1Data).getD 19 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row19Coeffs70To78_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 79) :
    mulCoeffTwo DData V4JData 19 j =
      ((rectangularize 54 79 V4PLD1Data).getD 19 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLD1Row19_coefficients (j : ℕ) (hj : j < 79) :
    mulCoeffTwo DData V4JData 19 j =
      ((rectangularize 54 79 V4PLD1Data).getD 19 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD1Row19Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD1Row19Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD1Row19Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD1Row19Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD1Row19Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD1Row19Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD1Row19Coeffs60To69_spec j (by omega) h70
  exact v4PLD1Row19Coeffs70To78_spec j (by omega) hj

private theorem v4PLD1Row19_spec :
    padOne 79 (mulRow DData V4JData 19) =
      (rectangularize 54 79 V4PLD1Data).getD 19 [] := by
  apply padOne_mulRow_eq_of_coefficients 79 DData V4JData 19
    ((rectangularize 54 79 V4PLD1Data).getD 19 [])
  · decide
  · have hTargetSupport : (V4PLD1Data.getD 19 []).length ≤ 79 := by
      decide
    rw [getD_rectangularize 54 79 V4PLD1Data 19 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD1Row19_coefficients

private theorem v4PLD1Row20Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4JData 20 j =
      ((rectangularize 54 79 V4PLD1Data).getD 20 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row20Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4JData 20 j =
      ((rectangularize 54 79 V4PLD1Data).getD 20 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row20Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4JData 20 j =
      ((rectangularize 54 79 V4PLD1Data).getD 20 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row20Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4JData 20 j =
      ((rectangularize 54 79 V4PLD1Data).getD 20 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row20Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4JData 20 j =
      ((rectangularize 54 79 V4PLD1Data).getD 20 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row20Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4JData 20 j =
      ((rectangularize 54 79 V4PLD1Data).getD 20 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row20Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4JData 20 j =
      ((rectangularize 54 79 V4PLD1Data).getD 20 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row20Coeffs70To78_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 79) :
    mulCoeffTwo DData V4JData 20 j =
      ((rectangularize 54 79 V4PLD1Data).getD 20 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLD1Row20_coefficients (j : ℕ) (hj : j < 79) :
    mulCoeffTwo DData V4JData 20 j =
      ((rectangularize 54 79 V4PLD1Data).getD 20 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD1Row20Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD1Row20Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD1Row20Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD1Row20Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD1Row20Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD1Row20Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD1Row20Coeffs60To69_spec j (by omega) h70
  exact v4PLD1Row20Coeffs70To78_spec j (by omega) hj

private theorem v4PLD1Row20_spec :
    padOne 79 (mulRow DData V4JData 20) =
      (rectangularize 54 79 V4PLD1Data).getD 20 [] := by
  apply padOne_mulRow_eq_of_coefficients 79 DData V4JData 20
    ((rectangularize 54 79 V4PLD1Data).getD 20 [])
  · decide
  · have hTargetSupport : (V4PLD1Data.getD 20 []).length ≤ 79 := by
      decide
    rw [getD_rectangularize 54 79 V4PLD1Data 20 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD1Row20_coefficients

private theorem v4PLD1Row21Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4JData 21 j =
      ((rectangularize 54 79 V4PLD1Data).getD 21 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row21Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4JData 21 j =
      ((rectangularize 54 79 V4PLD1Data).getD 21 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row21Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4JData 21 j =
      ((rectangularize 54 79 V4PLD1Data).getD 21 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row21Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4JData 21 j =
      ((rectangularize 54 79 V4PLD1Data).getD 21 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row21Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4JData 21 j =
      ((rectangularize 54 79 V4PLD1Data).getD 21 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row21Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4JData 21 j =
      ((rectangularize 54 79 V4PLD1Data).getD 21 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row21Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4JData 21 j =
      ((rectangularize 54 79 V4PLD1Data).getD 21 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row21Coeffs70To78_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 79) :
    mulCoeffTwo DData V4JData 21 j =
      ((rectangularize 54 79 V4PLD1Data).getD 21 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLD1Row21_coefficients (j : ℕ) (hj : j < 79) :
    mulCoeffTwo DData V4JData 21 j =
      ((rectangularize 54 79 V4PLD1Data).getD 21 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD1Row21Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD1Row21Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD1Row21Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD1Row21Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD1Row21Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD1Row21Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD1Row21Coeffs60To69_spec j (by omega) h70
  exact v4PLD1Row21Coeffs70To78_spec j (by omega) hj

private theorem v4PLD1Row21_spec :
    padOne 79 (mulRow DData V4JData 21) =
      (rectangularize 54 79 V4PLD1Data).getD 21 [] := by
  apply padOne_mulRow_eq_of_coefficients 79 DData V4JData 21
    ((rectangularize 54 79 V4PLD1Data).getD 21 [])
  · decide
  · have hTargetSupport : (V4PLD1Data.getD 21 []).length ≤ 79 := by
      decide
    rw [getD_rectangularize 54 79 V4PLD1Data 21 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD1Row21_coefficients

private theorem v4PLD1Row22Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4JData 22 j =
      ((rectangularize 54 79 V4PLD1Data).getD 22 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row22Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4JData 22 j =
      ((rectangularize 54 79 V4PLD1Data).getD 22 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row22Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4JData 22 j =
      ((rectangularize 54 79 V4PLD1Data).getD 22 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row22Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4JData 22 j =
      ((rectangularize 54 79 V4PLD1Data).getD 22 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row22Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4JData 22 j =
      ((rectangularize 54 79 V4PLD1Data).getD 22 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row22Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4JData 22 j =
      ((rectangularize 54 79 V4PLD1Data).getD 22 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row22Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4JData 22 j =
      ((rectangularize 54 79 V4PLD1Data).getD 22 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row22Coeffs70To78_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 79) :
    mulCoeffTwo DData V4JData 22 j =
      ((rectangularize 54 79 V4PLD1Data).getD 22 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLD1Row22_coefficients (j : ℕ) (hj : j < 79) :
    mulCoeffTwo DData V4JData 22 j =
      ((rectangularize 54 79 V4PLD1Data).getD 22 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD1Row22Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD1Row22Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD1Row22Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD1Row22Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD1Row22Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD1Row22Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD1Row22Coeffs60To69_spec j (by omega) h70
  exact v4PLD1Row22Coeffs70To78_spec j (by omega) hj

private theorem v4PLD1Row22_spec :
    padOne 79 (mulRow DData V4JData 22) =
      (rectangularize 54 79 V4PLD1Data).getD 22 [] := by
  apply padOne_mulRow_eq_of_coefficients 79 DData V4JData 22
    ((rectangularize 54 79 V4PLD1Data).getD 22 [])
  · decide
  · have hTargetSupport : (V4PLD1Data.getD 22 []).length ≤ 79 := by
      decide
    rw [getD_rectangularize 54 79 V4PLD1Data 22 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD1Row22_coefficients

private theorem v4PLD1Row23Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4JData 23 j =
      ((rectangularize 54 79 V4PLD1Data).getD 23 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row23Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4JData 23 j =
      ((rectangularize 54 79 V4PLD1Data).getD 23 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row23Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4JData 23 j =
      ((rectangularize 54 79 V4PLD1Data).getD 23 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row23Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4JData 23 j =
      ((rectangularize 54 79 V4PLD1Data).getD 23 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row23Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4JData 23 j =
      ((rectangularize 54 79 V4PLD1Data).getD 23 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row23Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4JData 23 j =
      ((rectangularize 54 79 V4PLD1Data).getD 23 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row23Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4JData 23 j =
      ((rectangularize 54 79 V4PLD1Data).getD 23 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row23Coeffs70To78_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 79) :
    mulCoeffTwo DData V4JData 23 j =
      ((rectangularize 54 79 V4PLD1Data).getD 23 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLD1Row23_coefficients (j : ℕ) (hj : j < 79) :
    mulCoeffTwo DData V4JData 23 j =
      ((rectangularize 54 79 V4PLD1Data).getD 23 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD1Row23Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD1Row23Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD1Row23Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD1Row23Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD1Row23Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD1Row23Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD1Row23Coeffs60To69_spec j (by omega) h70
  exact v4PLD1Row23Coeffs70To78_spec j (by omega) hj

private theorem v4PLD1Row23_spec :
    padOne 79 (mulRow DData V4JData 23) =
      (rectangularize 54 79 V4PLD1Data).getD 23 [] := by
  apply padOne_mulRow_eq_of_coefficients 79 DData V4JData 23
    ((rectangularize 54 79 V4PLD1Data).getD 23 [])
  · decide
  · have hTargetSupport : (V4PLD1Data.getD 23 []).length ≤ 79 := by
      decide
    rw [getD_rectangularize 54 79 V4PLD1Data 23 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD1Row23_coefficients

private theorem v4PLD1Row24Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4JData 24 j =
      ((rectangularize 54 79 V4PLD1Data).getD 24 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row24Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4JData 24 j =
      ((rectangularize 54 79 V4PLD1Data).getD 24 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row24Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4JData 24 j =
      ((rectangularize 54 79 V4PLD1Data).getD 24 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row24Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4JData 24 j =
      ((rectangularize 54 79 V4PLD1Data).getD 24 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row24Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4JData 24 j =
      ((rectangularize 54 79 V4PLD1Data).getD 24 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row24Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4JData 24 j =
      ((rectangularize 54 79 V4PLD1Data).getD 24 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row24Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4JData 24 j =
      ((rectangularize 54 79 V4PLD1Data).getD 24 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row24Coeffs70To78_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 79) :
    mulCoeffTwo DData V4JData 24 j =
      ((rectangularize 54 79 V4PLD1Data).getD 24 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLD1Row24_coefficients (j : ℕ) (hj : j < 79) :
    mulCoeffTwo DData V4JData 24 j =
      ((rectangularize 54 79 V4PLD1Data).getD 24 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD1Row24Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD1Row24Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD1Row24Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD1Row24Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD1Row24Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD1Row24Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD1Row24Coeffs60To69_spec j (by omega) h70
  exact v4PLD1Row24Coeffs70To78_spec j (by omega) hj

private theorem v4PLD1Row24_spec :
    padOne 79 (mulRow DData V4JData 24) =
      (rectangularize 54 79 V4PLD1Data).getD 24 [] := by
  apply padOne_mulRow_eq_of_coefficients 79 DData V4JData 24
    ((rectangularize 54 79 V4PLD1Data).getD 24 [])
  · decide
  · have hTargetSupport : (V4PLD1Data.getD 24 []).length ≤ 79 := by
      decide
    rw [getD_rectangularize 54 79 V4PLD1Data 24 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD1Row24_coefficients

private theorem v4PLD1Row25Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4JData 25 j =
      ((rectangularize 54 79 V4PLD1Data).getD 25 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row25Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4JData 25 j =
      ((rectangularize 54 79 V4PLD1Data).getD 25 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row25Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4JData 25 j =
      ((rectangularize 54 79 V4PLD1Data).getD 25 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row25Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4JData 25 j =
      ((rectangularize 54 79 V4PLD1Data).getD 25 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row25Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4JData 25 j =
      ((rectangularize 54 79 V4PLD1Data).getD 25 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row25Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4JData 25 j =
      ((rectangularize 54 79 V4PLD1Data).getD 25 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row25Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4JData 25 j =
      ((rectangularize 54 79 V4PLD1Data).getD 25 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row25Coeffs70To78_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 79) :
    mulCoeffTwo DData V4JData 25 j =
      ((rectangularize 54 79 V4PLD1Data).getD 25 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLD1Row25_coefficients (j : ℕ) (hj : j < 79) :
    mulCoeffTwo DData V4JData 25 j =
      ((rectangularize 54 79 V4PLD1Data).getD 25 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD1Row25Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD1Row25Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD1Row25Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD1Row25Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD1Row25Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD1Row25Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD1Row25Coeffs60To69_spec j (by omega) h70
  exact v4PLD1Row25Coeffs70To78_spec j (by omega) hj

private theorem v4PLD1Row25_spec :
    padOne 79 (mulRow DData V4JData 25) =
      (rectangularize 54 79 V4PLD1Data).getD 25 [] := by
  apply padOne_mulRow_eq_of_coefficients 79 DData V4JData 25
    ((rectangularize 54 79 V4PLD1Data).getD 25 [])
  · decide
  · have hTargetSupport : (V4PLD1Data.getD 25 []).length ≤ 79 := by
      decide
    rw [getD_rectangularize 54 79 V4PLD1Data 25 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD1Row25_coefficients

private theorem v4PLD1Row26Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4JData 26 j =
      ((rectangularize 54 79 V4PLD1Data).getD 26 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row26Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4JData 26 j =
      ((rectangularize 54 79 V4PLD1Data).getD 26 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row26Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4JData 26 j =
      ((rectangularize 54 79 V4PLD1Data).getD 26 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row26Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4JData 26 j =
      ((rectangularize 54 79 V4PLD1Data).getD 26 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row26Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4JData 26 j =
      ((rectangularize 54 79 V4PLD1Data).getD 26 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row26Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4JData 26 j =
      ((rectangularize 54 79 V4PLD1Data).getD 26 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row26Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4JData 26 j =
      ((rectangularize 54 79 V4PLD1Data).getD 26 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row26Coeffs70To78_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 79) :
    mulCoeffTwo DData V4JData 26 j =
      ((rectangularize 54 79 V4PLD1Data).getD 26 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLD1Row26_coefficients (j : ℕ) (hj : j < 79) :
    mulCoeffTwo DData V4JData 26 j =
      ((rectangularize 54 79 V4PLD1Data).getD 26 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD1Row26Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD1Row26Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD1Row26Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD1Row26Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD1Row26Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD1Row26Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD1Row26Coeffs60To69_spec j (by omega) h70
  exact v4PLD1Row26Coeffs70To78_spec j (by omega) hj

private theorem v4PLD1Row26_spec :
    padOne 79 (mulRow DData V4JData 26) =
      (rectangularize 54 79 V4PLD1Data).getD 26 [] := by
  apply padOne_mulRow_eq_of_coefficients 79 DData V4JData 26
    ((rectangularize 54 79 V4PLD1Data).getD 26 [])
  · decide
  · have hTargetSupport : (V4PLD1Data.getD 26 []).length ≤ 79 := by
      decide
    rw [getD_rectangularize 54 79 V4PLD1Data 26 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD1Row26_coefficients

private theorem v4PLD1Row27Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4JData 27 j =
      ((rectangularize 54 79 V4PLD1Data).getD 27 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row27Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4JData 27 j =
      ((rectangularize 54 79 V4PLD1Data).getD 27 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row27Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4JData 27 j =
      ((rectangularize 54 79 V4PLD1Data).getD 27 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row27Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4JData 27 j =
      ((rectangularize 54 79 V4PLD1Data).getD 27 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row27Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4JData 27 j =
      ((rectangularize 54 79 V4PLD1Data).getD 27 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row27Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4JData 27 j =
      ((rectangularize 54 79 V4PLD1Data).getD 27 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row27Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4JData 27 j =
      ((rectangularize 54 79 V4PLD1Data).getD 27 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row27Coeffs70To78_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 79) :
    mulCoeffTwo DData V4JData 27 j =
      ((rectangularize 54 79 V4PLD1Data).getD 27 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLD1Row27_coefficients (j : ℕ) (hj : j < 79) :
    mulCoeffTwo DData V4JData 27 j =
      ((rectangularize 54 79 V4PLD1Data).getD 27 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD1Row27Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD1Row27Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD1Row27Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD1Row27Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD1Row27Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD1Row27Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD1Row27Coeffs60To69_spec j (by omega) h70
  exact v4PLD1Row27Coeffs70To78_spec j (by omega) hj

private theorem v4PLD1Row27_spec :
    padOne 79 (mulRow DData V4JData 27) =
      (rectangularize 54 79 V4PLD1Data).getD 27 [] := by
  apply padOne_mulRow_eq_of_coefficients 79 DData V4JData 27
    ((rectangularize 54 79 V4PLD1Data).getD 27 [])
  · decide
  · have hTargetSupport : (V4PLD1Data.getD 27 []).length ≤ 79 := by
      decide
    rw [getD_rectangularize 54 79 V4PLD1Data 27 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD1Row27_coefficients

private theorem v4PLD1Row28Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4JData 28 j =
      ((rectangularize 54 79 V4PLD1Data).getD 28 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row28Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4JData 28 j =
      ((rectangularize 54 79 V4PLD1Data).getD 28 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row28Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4JData 28 j =
      ((rectangularize 54 79 V4PLD1Data).getD 28 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row28Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4JData 28 j =
      ((rectangularize 54 79 V4PLD1Data).getD 28 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row28Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4JData 28 j =
      ((rectangularize 54 79 V4PLD1Data).getD 28 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row28Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4JData 28 j =
      ((rectangularize 54 79 V4PLD1Data).getD 28 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row28Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4JData 28 j =
      ((rectangularize 54 79 V4PLD1Data).getD 28 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row28Coeffs70To78_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 79) :
    mulCoeffTwo DData V4JData 28 j =
      ((rectangularize 54 79 V4PLD1Data).getD 28 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLD1Row28_coefficients (j : ℕ) (hj : j < 79) :
    mulCoeffTwo DData V4JData 28 j =
      ((rectangularize 54 79 V4PLD1Data).getD 28 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD1Row28Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD1Row28Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD1Row28Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD1Row28Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD1Row28Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD1Row28Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD1Row28Coeffs60To69_spec j (by omega) h70
  exact v4PLD1Row28Coeffs70To78_spec j (by omega) hj

private theorem v4PLD1Row28_spec :
    padOne 79 (mulRow DData V4JData 28) =
      (rectangularize 54 79 V4PLD1Data).getD 28 [] := by
  apply padOne_mulRow_eq_of_coefficients 79 DData V4JData 28
    ((rectangularize 54 79 V4PLD1Data).getD 28 [])
  · decide
  · have hTargetSupport : (V4PLD1Data.getD 28 []).length ≤ 79 := by
      decide
    rw [getD_rectangularize 54 79 V4PLD1Data 28 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD1Row28_coefficients

private theorem v4PLD1Row29Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4JData 29 j =
      ((rectangularize 54 79 V4PLD1Data).getD 29 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row29Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4JData 29 j =
      ((rectangularize 54 79 V4PLD1Data).getD 29 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row29Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4JData 29 j =
      ((rectangularize 54 79 V4PLD1Data).getD 29 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row29Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4JData 29 j =
      ((rectangularize 54 79 V4PLD1Data).getD 29 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row29Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4JData 29 j =
      ((rectangularize 54 79 V4PLD1Data).getD 29 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row29Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4JData 29 j =
      ((rectangularize 54 79 V4PLD1Data).getD 29 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row29Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4JData 29 j =
      ((rectangularize 54 79 V4PLD1Data).getD 29 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row29Coeffs70To78_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 79) :
    mulCoeffTwo DData V4JData 29 j =
      ((rectangularize 54 79 V4PLD1Data).getD 29 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLD1Row29_coefficients (j : ℕ) (hj : j < 79) :
    mulCoeffTwo DData V4JData 29 j =
      ((rectangularize 54 79 V4PLD1Data).getD 29 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD1Row29Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD1Row29Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD1Row29Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD1Row29Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD1Row29Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD1Row29Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD1Row29Coeffs60To69_spec j (by omega) h70
  exact v4PLD1Row29Coeffs70To78_spec j (by omega) hj

private theorem v4PLD1Row29_spec :
    padOne 79 (mulRow DData V4JData 29) =
      (rectangularize 54 79 V4PLD1Data).getD 29 [] := by
  apply padOne_mulRow_eq_of_coefficients 79 DData V4JData 29
    ((rectangularize 54 79 V4PLD1Data).getD 29 [])
  · decide
  · have hTargetSupport : (V4PLD1Data.getD 29 []).length ≤ 79 := by
      decide
    rw [getD_rectangularize 54 79 V4PLD1Data 29 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD1Row29_coefficients

private theorem v4PLD1Row30Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4JData 30 j =
      ((rectangularize 54 79 V4PLD1Data).getD 30 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row30Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4JData 30 j =
      ((rectangularize 54 79 V4PLD1Data).getD 30 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row30Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4JData 30 j =
      ((rectangularize 54 79 V4PLD1Data).getD 30 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row30Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4JData 30 j =
      ((rectangularize 54 79 V4PLD1Data).getD 30 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row30Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4JData 30 j =
      ((rectangularize 54 79 V4PLD1Data).getD 30 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row30Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4JData 30 j =
      ((rectangularize 54 79 V4PLD1Data).getD 30 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row30Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4JData 30 j =
      ((rectangularize 54 79 V4PLD1Data).getD 30 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row30Coeffs70To78_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 79) :
    mulCoeffTwo DData V4JData 30 j =
      ((rectangularize 54 79 V4PLD1Data).getD 30 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLD1Row30_coefficients (j : ℕ) (hj : j < 79) :
    mulCoeffTwo DData V4JData 30 j =
      ((rectangularize 54 79 V4PLD1Data).getD 30 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD1Row30Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD1Row30Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD1Row30Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD1Row30Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD1Row30Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD1Row30Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD1Row30Coeffs60To69_spec j (by omega) h70
  exact v4PLD1Row30Coeffs70To78_spec j (by omega) hj

private theorem v4PLD1Row30_spec :
    padOne 79 (mulRow DData V4JData 30) =
      (rectangularize 54 79 V4PLD1Data).getD 30 [] := by
  apply padOne_mulRow_eq_of_coefficients 79 DData V4JData 30
    ((rectangularize 54 79 V4PLD1Data).getD 30 [])
  · decide
  · have hTargetSupport : (V4PLD1Data.getD 30 []).length ≤ 79 := by
      decide
    rw [getD_rectangularize 54 79 V4PLD1Data 30 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD1Row30_coefficients

private theorem v4PLD1Row31Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4JData 31 j =
      ((rectangularize 54 79 V4PLD1Data).getD 31 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row31Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4JData 31 j =
      ((rectangularize 54 79 V4PLD1Data).getD 31 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row31Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4JData 31 j =
      ((rectangularize 54 79 V4PLD1Data).getD 31 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row31Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4JData 31 j =
      ((rectangularize 54 79 V4PLD1Data).getD 31 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row31Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4JData 31 j =
      ((rectangularize 54 79 V4PLD1Data).getD 31 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row31Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4JData 31 j =
      ((rectangularize 54 79 V4PLD1Data).getD 31 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row31Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4JData 31 j =
      ((rectangularize 54 79 V4PLD1Data).getD 31 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row31Coeffs70To78_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 79) :
    mulCoeffTwo DData V4JData 31 j =
      ((rectangularize 54 79 V4PLD1Data).getD 31 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLD1Row31_coefficients (j : ℕ) (hj : j < 79) :
    mulCoeffTwo DData V4JData 31 j =
      ((rectangularize 54 79 V4PLD1Data).getD 31 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD1Row31Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD1Row31Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD1Row31Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD1Row31Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD1Row31Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD1Row31Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD1Row31Coeffs60To69_spec j (by omega) h70
  exact v4PLD1Row31Coeffs70To78_spec j (by omega) hj

private theorem v4PLD1Row31_spec :
    padOne 79 (mulRow DData V4JData 31) =
      (rectangularize 54 79 V4PLD1Data).getD 31 [] := by
  apply padOne_mulRow_eq_of_coefficients 79 DData V4JData 31
    ((rectangularize 54 79 V4PLD1Data).getD 31 [])
  · decide
  · have hTargetSupport : (V4PLD1Data.getD 31 []).length ≤ 79 := by
      decide
    rw [getD_rectangularize 54 79 V4PLD1Data 31 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD1Row31_coefficients

private theorem v4PLD1Row32Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4JData 32 j =
      ((rectangularize 54 79 V4PLD1Data).getD 32 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row32Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4JData 32 j =
      ((rectangularize 54 79 V4PLD1Data).getD 32 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row32Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4JData 32 j =
      ((rectangularize 54 79 V4PLD1Data).getD 32 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row32Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4JData 32 j =
      ((rectangularize 54 79 V4PLD1Data).getD 32 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row32Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4JData 32 j =
      ((rectangularize 54 79 V4PLD1Data).getD 32 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row32Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4JData 32 j =
      ((rectangularize 54 79 V4PLD1Data).getD 32 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row32Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4JData 32 j =
      ((rectangularize 54 79 V4PLD1Data).getD 32 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row32Coeffs70To78_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 79) :
    mulCoeffTwo DData V4JData 32 j =
      ((rectangularize 54 79 V4PLD1Data).getD 32 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLD1Row32_coefficients (j : ℕ) (hj : j < 79) :
    mulCoeffTwo DData V4JData 32 j =
      ((rectangularize 54 79 V4PLD1Data).getD 32 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD1Row32Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD1Row32Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD1Row32Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD1Row32Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD1Row32Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD1Row32Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD1Row32Coeffs60To69_spec j (by omega) h70
  exact v4PLD1Row32Coeffs70To78_spec j (by omega) hj

private theorem v4PLD1Row32_spec :
    padOne 79 (mulRow DData V4JData 32) =
      (rectangularize 54 79 V4PLD1Data).getD 32 [] := by
  apply padOne_mulRow_eq_of_coefficients 79 DData V4JData 32
    ((rectangularize 54 79 V4PLD1Data).getD 32 [])
  · decide
  · have hTargetSupport : (V4PLD1Data.getD 32 []).length ≤ 79 := by
      decide
    rw [getD_rectangularize 54 79 V4PLD1Data 32 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD1Row32_coefficients

private theorem v4PLD1Row33Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4JData 33 j =
      ((rectangularize 54 79 V4PLD1Data).getD 33 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row33Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4JData 33 j =
      ((rectangularize 54 79 V4PLD1Data).getD 33 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row33Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4JData 33 j =
      ((rectangularize 54 79 V4PLD1Data).getD 33 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row33Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4JData 33 j =
      ((rectangularize 54 79 V4PLD1Data).getD 33 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row33Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4JData 33 j =
      ((rectangularize 54 79 V4PLD1Data).getD 33 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row33Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4JData 33 j =
      ((rectangularize 54 79 V4PLD1Data).getD 33 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row33Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4JData 33 j =
      ((rectangularize 54 79 V4PLD1Data).getD 33 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row33Coeffs70To78_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 79) :
    mulCoeffTwo DData V4JData 33 j =
      ((rectangularize 54 79 V4PLD1Data).getD 33 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLD1Row33_coefficients (j : ℕ) (hj : j < 79) :
    mulCoeffTwo DData V4JData 33 j =
      ((rectangularize 54 79 V4PLD1Data).getD 33 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD1Row33Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD1Row33Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD1Row33Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD1Row33Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD1Row33Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD1Row33Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD1Row33Coeffs60To69_spec j (by omega) h70
  exact v4PLD1Row33Coeffs70To78_spec j (by omega) hj

private theorem v4PLD1Row33_spec :
    padOne 79 (mulRow DData V4JData 33) =
      (rectangularize 54 79 V4PLD1Data).getD 33 [] := by
  apply padOne_mulRow_eq_of_coefficients 79 DData V4JData 33
    ((rectangularize 54 79 V4PLD1Data).getD 33 [])
  · decide
  · have hTargetSupport : (V4PLD1Data.getD 33 []).length ≤ 79 := by
      decide
    rw [getD_rectangularize 54 79 V4PLD1Data 33 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD1Row33_coefficients

private theorem v4PLD1Row34Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4JData 34 j =
      ((rectangularize 54 79 V4PLD1Data).getD 34 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row34Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4JData 34 j =
      ((rectangularize 54 79 V4PLD1Data).getD 34 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row34Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4JData 34 j =
      ((rectangularize 54 79 V4PLD1Data).getD 34 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row34Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4JData 34 j =
      ((rectangularize 54 79 V4PLD1Data).getD 34 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row34Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4JData 34 j =
      ((rectangularize 54 79 V4PLD1Data).getD 34 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row34Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4JData 34 j =
      ((rectangularize 54 79 V4PLD1Data).getD 34 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row34Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4JData 34 j =
      ((rectangularize 54 79 V4PLD1Data).getD 34 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row34Coeffs70To78_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 79) :
    mulCoeffTwo DData V4JData 34 j =
      ((rectangularize 54 79 V4PLD1Data).getD 34 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLD1Row34_coefficients (j : ℕ) (hj : j < 79) :
    mulCoeffTwo DData V4JData 34 j =
      ((rectangularize 54 79 V4PLD1Data).getD 34 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD1Row34Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD1Row34Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD1Row34Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD1Row34Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD1Row34Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD1Row34Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD1Row34Coeffs60To69_spec j (by omega) h70
  exact v4PLD1Row34Coeffs70To78_spec j (by omega) hj

private theorem v4PLD1Row34_spec :
    padOne 79 (mulRow DData V4JData 34) =
      (rectangularize 54 79 V4PLD1Data).getD 34 [] := by
  apply padOne_mulRow_eq_of_coefficients 79 DData V4JData 34
    ((rectangularize 54 79 V4PLD1Data).getD 34 [])
  · decide
  · have hTargetSupport : (V4PLD1Data.getD 34 []).length ≤ 79 := by
      decide
    rw [getD_rectangularize 54 79 V4PLD1Data 34 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD1Row34_coefficients

private theorem v4PLD1Row35Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4JData 35 j =
      ((rectangularize 54 79 V4PLD1Data).getD 35 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row35Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4JData 35 j =
      ((rectangularize 54 79 V4PLD1Data).getD 35 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row35Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4JData 35 j =
      ((rectangularize 54 79 V4PLD1Data).getD 35 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row35Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4JData 35 j =
      ((rectangularize 54 79 V4PLD1Data).getD 35 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row35Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4JData 35 j =
      ((rectangularize 54 79 V4PLD1Data).getD 35 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row35Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4JData 35 j =
      ((rectangularize 54 79 V4PLD1Data).getD 35 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row35Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4JData 35 j =
      ((rectangularize 54 79 V4PLD1Data).getD 35 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row35Coeffs70To78_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 79) :
    mulCoeffTwo DData V4JData 35 j =
      ((rectangularize 54 79 V4PLD1Data).getD 35 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLD1Row35_coefficients (j : ℕ) (hj : j < 79) :
    mulCoeffTwo DData V4JData 35 j =
      ((rectangularize 54 79 V4PLD1Data).getD 35 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD1Row35Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD1Row35Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD1Row35Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD1Row35Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD1Row35Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD1Row35Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD1Row35Coeffs60To69_spec j (by omega) h70
  exact v4PLD1Row35Coeffs70To78_spec j (by omega) hj

private theorem v4PLD1Row35_spec :
    padOne 79 (mulRow DData V4JData 35) =
      (rectangularize 54 79 V4PLD1Data).getD 35 [] := by
  apply padOne_mulRow_eq_of_coefficients 79 DData V4JData 35
    ((rectangularize 54 79 V4PLD1Data).getD 35 [])
  · decide
  · have hTargetSupport : (V4PLD1Data.getD 35 []).length ≤ 79 := by
      decide
    rw [getD_rectangularize 54 79 V4PLD1Data 35 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD1Row35_coefficients

private theorem v4PLD1Row36Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4JData 36 j =
      ((rectangularize 54 79 V4PLD1Data).getD 36 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row36Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4JData 36 j =
      ((rectangularize 54 79 V4PLD1Data).getD 36 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row36Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4JData 36 j =
      ((rectangularize 54 79 V4PLD1Data).getD 36 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row36Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4JData 36 j =
      ((rectangularize 54 79 V4PLD1Data).getD 36 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row36Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4JData 36 j =
      ((rectangularize 54 79 V4PLD1Data).getD 36 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row36Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4JData 36 j =
      ((rectangularize 54 79 V4PLD1Data).getD 36 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row36Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4JData 36 j =
      ((rectangularize 54 79 V4PLD1Data).getD 36 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row36Coeffs70To78_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 79) :
    mulCoeffTwo DData V4JData 36 j =
      ((rectangularize 54 79 V4PLD1Data).getD 36 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLD1Row36_coefficients (j : ℕ) (hj : j < 79) :
    mulCoeffTwo DData V4JData 36 j =
      ((rectangularize 54 79 V4PLD1Data).getD 36 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD1Row36Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD1Row36Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD1Row36Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD1Row36Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD1Row36Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD1Row36Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD1Row36Coeffs60To69_spec j (by omega) h70
  exact v4PLD1Row36Coeffs70To78_spec j (by omega) hj

private theorem v4PLD1Row36_spec :
    padOne 79 (mulRow DData V4JData 36) =
      (rectangularize 54 79 V4PLD1Data).getD 36 [] := by
  apply padOne_mulRow_eq_of_coefficients 79 DData V4JData 36
    ((rectangularize 54 79 V4PLD1Data).getD 36 [])
  · decide
  · have hTargetSupport : (V4PLD1Data.getD 36 []).length ≤ 79 := by
      decide
    rw [getD_rectangularize 54 79 V4PLD1Data 36 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD1Row36_coefficients

private theorem v4PLD1Row37Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4JData 37 j =
      ((rectangularize 54 79 V4PLD1Data).getD 37 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row37Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4JData 37 j =
      ((rectangularize 54 79 V4PLD1Data).getD 37 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row37Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4JData 37 j =
      ((rectangularize 54 79 V4PLD1Data).getD 37 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row37Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4JData 37 j =
      ((rectangularize 54 79 V4PLD1Data).getD 37 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row37Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4JData 37 j =
      ((rectangularize 54 79 V4PLD1Data).getD 37 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row37Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4JData 37 j =
      ((rectangularize 54 79 V4PLD1Data).getD 37 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row37Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4JData 37 j =
      ((rectangularize 54 79 V4PLD1Data).getD 37 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row37Coeffs70To78_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 79) :
    mulCoeffTwo DData V4JData 37 j =
      ((rectangularize 54 79 V4PLD1Data).getD 37 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLD1Row37_coefficients (j : ℕ) (hj : j < 79) :
    mulCoeffTwo DData V4JData 37 j =
      ((rectangularize 54 79 V4PLD1Data).getD 37 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD1Row37Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD1Row37Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD1Row37Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD1Row37Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD1Row37Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD1Row37Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD1Row37Coeffs60To69_spec j (by omega) h70
  exact v4PLD1Row37Coeffs70To78_spec j (by omega) hj

private theorem v4PLD1Row37_spec :
    padOne 79 (mulRow DData V4JData 37) =
      (rectangularize 54 79 V4PLD1Data).getD 37 [] := by
  apply padOne_mulRow_eq_of_coefficients 79 DData V4JData 37
    ((rectangularize 54 79 V4PLD1Data).getD 37 [])
  · decide
  · have hTargetSupport : (V4PLD1Data.getD 37 []).length ≤ 79 := by
      decide
    rw [getD_rectangularize 54 79 V4PLD1Data 37 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD1Row37_coefficients

private theorem v4PLD1Row38Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4JData 38 j =
      ((rectangularize 54 79 V4PLD1Data).getD 38 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row38Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4JData 38 j =
      ((rectangularize 54 79 V4PLD1Data).getD 38 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row38Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4JData 38 j =
      ((rectangularize 54 79 V4PLD1Data).getD 38 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row38Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4JData 38 j =
      ((rectangularize 54 79 V4PLD1Data).getD 38 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row38Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4JData 38 j =
      ((rectangularize 54 79 V4PLD1Data).getD 38 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row38Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4JData 38 j =
      ((rectangularize 54 79 V4PLD1Data).getD 38 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row38Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4JData 38 j =
      ((rectangularize 54 79 V4PLD1Data).getD 38 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD1Row38Coeffs70To78_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 79) :
    mulCoeffTwo DData V4JData 38 j =
      ((rectangularize 54 79 V4PLD1Data).getD 38 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLD1Row38_coefficients (j : ℕ) (hj : j < 79) :
    mulCoeffTwo DData V4JData 38 j =
      ((rectangularize 54 79 V4PLD1Data).getD 38 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD1Row38Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD1Row38Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD1Row38Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD1Row38Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD1Row38Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD1Row38Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD1Row38Coeffs60To69_spec j (by omega) h70
  exact v4PLD1Row38Coeffs70To78_spec j (by omega) hj

private theorem v4PLD1Row38_spec :
    padOne 79 (mulRow DData V4JData 38) =
      (rectangularize 54 79 V4PLD1Data).getD 38 [] := by
  apply padOne_mulRow_eq_of_coefficients 79 DData V4JData 38
    ((rectangularize 54 79 V4PLD1Data).getD 38 [])
  · decide
  · have hTargetSupport : (V4PLD1Data.getD 38 []).length ≤ 79 := by
      decide
    rw [getD_rectangularize 54 79 V4PLD1Data 38 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD1Row38_coefficients

private theorem v4PLD1Row39_spec :
    padOne 79 (mulRow DData V4JData 39) =
      (rectangularize 54 79 V4PLD1Data).getD 39 [] := by
  decide

private theorem v4PLD1Row40_spec :
    padOne 79 (mulRow DData V4JData 40) =
      (rectangularize 54 79 V4PLD1Data).getD 40 [] := by
  decide

private theorem v4PLD1Row41_spec :
    padOne 79 (mulRow DData V4JData 41) =
      (rectangularize 54 79 V4PLD1Data).getD 41 [] := by
  decide

private theorem v4PLD1Row42_spec :
    padOne 79 (mulRow DData V4JData 42) =
      (rectangularize 54 79 V4PLD1Data).getD 42 [] := by
  decide

private theorem v4PLD1Row43_spec :
    padOne 79 (mulRow DData V4JData 43) =
      (rectangularize 54 79 V4PLD1Data).getD 43 [] := by
  decide

private theorem v4PLD1Row44_spec :
    padOne 79 (mulRow DData V4JData 44) =
      (rectangularize 54 79 V4PLD1Data).getD 44 [] := by
  decide

private theorem v4PLD1Row45_spec :
    padOne 79 (mulRow DData V4JData 45) =
      (rectangularize 54 79 V4PLD1Data).getD 45 [] := by
  decide

private theorem v4PLD1Row46_spec :
    padOne 79 (mulRow DData V4JData 46) =
      (rectangularize 54 79 V4PLD1Data).getD 46 [] := by
  decide

private theorem v4PLD1Row47_spec :
    padOne 79 (mulRow DData V4JData 47) =
      (rectangularize 54 79 V4PLD1Data).getD 47 [] := by
  decide

private theorem v4PLD1Row48_spec :
    padOne 79 (mulRow DData V4JData 48) =
      (rectangularize 54 79 V4PLD1Data).getD 48 [] := by
  decide

private theorem v4PLD1Row49_spec :
    padOne 79 (mulRow DData V4JData 49) =
      (rectangularize 54 79 V4PLD1Data).getD 49 [] := by
  decide

private theorem v4PLD1Row50_spec :
    padOne 79 (mulRow DData V4JData 50) =
      (rectangularize 54 79 V4PLD1Data).getD 50 [] := by
  decide

private theorem v4PLD1Row51_spec :
    padOne 79 (mulRow DData V4JData 51) =
      (rectangularize 54 79 V4PLD1Data).getD 51 [] := by
  decide

private theorem v4PLD1Row52_spec :
    padOne 79 (mulRow DData V4JData 52) =
      (rectangularize 54 79 V4PLD1Data).getD 52 [] := by
  decide

private theorem v4PLD1Row53_spec :
    padOne 79 (mulRow DData V4JData 53) =
      (rectangularize 54 79 V4PLD1Data).getD 53 [] := by
  decide

private theorem v4PLD1Rows_spec (n : ℕ) (hn : n < 54) :
    padOne 79 (mulRow DData V4JData n) =
      (rectangularize 54 79 V4PLD1Data).getD n [] := by
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
  · exact v4PLD1Row0_spec
  · exact v4PLD1Row1_spec
  · exact v4PLD1Row2_spec
  · exact v4PLD1Row3_spec
  · exact v4PLD1Row4_spec
  · exact v4PLD1Row5_spec
  · exact v4PLD1Row6_spec
  · exact v4PLD1Row7_spec
  · exact v4PLD1Row8_spec
  · exact v4PLD1Row9_spec
  · exact v4PLD1Row10_spec
  · exact v4PLD1Row11_spec
  · exact v4PLD1Row12_spec
  · exact v4PLD1Row13_spec
  · exact v4PLD1Row14_spec
  · exact v4PLD1Row15_spec
  · exact v4PLD1Row16_spec
  · exact v4PLD1Row17_spec
  · exact v4PLD1Row18_spec
  · exact v4PLD1Row19_spec
  · exact v4PLD1Row20_spec
  · exact v4PLD1Row21_spec
  · exact v4PLD1Row22_spec
  · exact v4PLD1Row23_spec
  · exact v4PLD1Row24_spec
  · exact v4PLD1Row25_spec
  · exact v4PLD1Row26_spec
  · exact v4PLD1Row27_spec
  · exact v4PLD1Row28_spec
  · exact v4PLD1Row29_spec
  · exact v4PLD1Row30_spec
  · exact v4PLD1Row31_spec
  · exact v4PLD1Row32_spec
  · exact v4PLD1Row33_spec
  · exact v4PLD1Row34_spec
  · exact v4PLD1Row35_spec
  · exact v4PLD1Row36_spec
  · exact v4PLD1Row37_spec
  · exact v4PLD1Row38_spec
  · exact v4PLD1Row39_spec
  · exact v4PLD1Row40_spec
  · exact v4PLD1Row41_spec
  · exact v4PLD1Row42_spec
  · exact v4PLD1Row43_spec
  · exact v4PLD1Row44_spec
  · exact v4PLD1Row45_spec
  · exact v4PLD1Row46_spec
  · exact v4PLD1Row47_spec
  · exact v4PLD1Row48_spec
  · exact v4PLD1Row49_spec
  · exact v4PLD1Row50_spec
  · exact v4PLD1Row51_spec
  · exact v4PLD1Row52_spec
  · exact v4PLD1Row53_spec

private theorem v4PLD1Left_length :
    (rectangularize 54 79 (Two.mul DData V4JData)).length = 54 := by
  decide

private theorem v4PLD1Right_length :
    (rectangularize 54 79 V4PLD1Data).length = 54 := by
  decide

-- Exact bidegree bound (53, 78); no row or column is discarded.
private theorem v4PLD1Data_spec :
    rectangularize 54 79 (Two.mul DData V4JData) =
      rectangularize 54 79 V4PLD1Data := by
  apply List.ext_getElem (v4PLD1Left_length.trans v4PLD1Right_length.symm)
  intro n hn _
  rw [List.getElem_eq_getD [], List.getElem_eq_getD []]
  rw [v4PLD1Left_length] at hn
  rw [getD_rectangularize 54 79 (Two.mul DData V4JData) n hn,
    ← mulRow_eq_getD]
  exact v4PLD1Rows_spec n hn

private theorem v4PLD2Row0_spec :
    padOne 82 (mulRow DData V4PLD1Data 0) =
      (rectangularize 56 82 V4PLD2Data).getD 0 [] := by
  decide

private theorem v4PLD2Row1_spec :
    padOne 82 (mulRow DData V4PLD1Data 1) =
      (rectangularize 56 82 V4PLD2Data).getD 1 [] := by
  decide

private theorem v4PLD2Row2_spec :
    padOne 82 (mulRow DData V4PLD1Data 2) =
      (rectangularize 56 82 V4PLD2Data).getD 2 [] := by
  decide

private theorem v4PLD2Row3_spec :
    padOne 82 (mulRow DData V4PLD1Data 3) =
      (rectangularize 56 82 V4PLD2Data).getD 3 [] := by
  decide

private theorem v4PLD2Row4_spec :
    padOne 82 (mulRow DData V4PLD1Data 4) =
      (rectangularize 56 82 V4PLD2Data).getD 4 [] := by
  decide

private theorem v4PLD2Row5_spec :
    padOne 82 (mulRow DData V4PLD1Data 5) =
      (rectangularize 56 82 V4PLD2Data).getD 5 [] := by
  decide

private theorem v4PLD2Row6_spec :
    padOne 82 (mulRow DData V4PLD1Data 6) =
      (rectangularize 56 82 V4PLD2Data).getD 6 [] := by
  decide

private theorem v4PLD2Row7_spec :
    padOne 82 (mulRow DData V4PLD1Data 7) =
      (rectangularize 56 82 V4PLD2Data).getD 7 [] := by
  decide

private theorem v4PLD2Row8_spec :
    padOne 82 (mulRow DData V4PLD1Data 8) =
      (rectangularize 56 82 V4PLD2Data).getD 8 [] := by
  decide

private theorem v4PLD2Row9_spec :
    padOne 82 (mulRow DData V4PLD1Data 9) =
      (rectangularize 56 82 V4PLD2Data).getD 9 [] := by
  decide

private theorem v4PLD2Row10_spec :
    padOne 82 (mulRow DData V4PLD1Data 10) =
      (rectangularize 56 82 V4PLD2Data).getD 10 [] := by
  decide

private theorem v4PLD2Row11_spec :
    padOne 82 (mulRow DData V4PLD1Data 11) =
      (rectangularize 56 82 V4PLD2Data).getD 11 [] := by
  decide

private theorem v4PLD2Row12_spec :
    padOne 82 (mulRow DData V4PLD1Data 12) =
      (rectangularize 56 82 V4PLD2Data).getD 12 [] := by
  decide

private theorem v4PLD2Row13Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD1Data 13 j =
      ((rectangularize 56 82 V4PLD2Data).getD 13 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row13Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD1Data 13 j =
      ((rectangularize 56 82 V4PLD2Data).getD 13 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row13Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD1Data 13 j =
      ((rectangularize 56 82 V4PLD2Data).getD 13 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row13Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD1Data 13 j =
      ((rectangularize 56 82 V4PLD2Data).getD 13 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row13Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD1Data 13 j =
      ((rectangularize 56 82 V4PLD2Data).getD 13 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row13Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD1Data 13 j =
      ((rectangularize 56 82 V4PLD2Data).getD 13 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row13Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD1Data 13 j =
      ((rectangularize 56 82 V4PLD2Data).getD 13 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row13Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD1Data 13 j =
      ((rectangularize 56 82 V4PLD2Data).getD 13 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row13Coeffs80To81_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 82) :
    mulCoeffTwo DData V4PLD1Data 13 j =
      ((rectangularize 56 82 V4PLD2Data).getD 13 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 := by
    omega
  rcases hCases with
    rfl | rfl <;> decide

private theorem v4PLD2Row13_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo DData V4PLD1Data 13 j =
      ((rectangularize 56 82 V4PLD2Data).getD 13 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD2Row13Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD2Row13Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD2Row13Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD2Row13Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD2Row13Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD2Row13Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD2Row13Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD2Row13Coeffs70To79_spec j (by omega) h80
  exact v4PLD2Row13Coeffs80To81_spec j (by omega) hj

private theorem v4PLD2Row13_spec :
    padOne 82 (mulRow DData V4PLD1Data 13) =
      (rectangularize 56 82 V4PLD2Data).getD 13 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 DData V4PLD1Data 13
    ((rectangularize 56 82 V4PLD2Data).getD 13 [])
  · decide
  · have hTargetSupport : (V4PLD2Data.getD 13 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 56 82 V4PLD2Data 13 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD2Row13_coefficients

private theorem v4PLD2Row14Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD1Data 14 j =
      ((rectangularize 56 82 V4PLD2Data).getD 14 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row14Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD1Data 14 j =
      ((rectangularize 56 82 V4PLD2Data).getD 14 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row14Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD1Data 14 j =
      ((rectangularize 56 82 V4PLD2Data).getD 14 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row14Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD1Data 14 j =
      ((rectangularize 56 82 V4PLD2Data).getD 14 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row14Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD1Data 14 j =
      ((rectangularize 56 82 V4PLD2Data).getD 14 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row14Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD1Data 14 j =
      ((rectangularize 56 82 V4PLD2Data).getD 14 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row14Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD1Data 14 j =
      ((rectangularize 56 82 V4PLD2Data).getD 14 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row14Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD1Data 14 j =
      ((rectangularize 56 82 V4PLD2Data).getD 14 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row14Coeffs80To81_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 82) :
    mulCoeffTwo DData V4PLD1Data 14 j =
      ((rectangularize 56 82 V4PLD2Data).getD 14 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 := by
    omega
  rcases hCases with
    rfl | rfl <;> decide

private theorem v4PLD2Row14_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo DData V4PLD1Data 14 j =
      ((rectangularize 56 82 V4PLD2Data).getD 14 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD2Row14Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD2Row14Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD2Row14Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD2Row14Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD2Row14Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD2Row14Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD2Row14Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD2Row14Coeffs70To79_spec j (by omega) h80
  exact v4PLD2Row14Coeffs80To81_spec j (by omega) hj

private theorem v4PLD2Row14_spec :
    padOne 82 (mulRow DData V4PLD1Data 14) =
      (rectangularize 56 82 V4PLD2Data).getD 14 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 DData V4PLD1Data 14
    ((rectangularize 56 82 V4PLD2Data).getD 14 [])
  · decide
  · have hTargetSupport : (V4PLD2Data.getD 14 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 56 82 V4PLD2Data 14 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD2Row14_coefficients

private theorem v4PLD2Row15Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD1Data 15 j =
      ((rectangularize 56 82 V4PLD2Data).getD 15 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row15Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD1Data 15 j =
      ((rectangularize 56 82 V4PLD2Data).getD 15 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row15Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD1Data 15 j =
      ((rectangularize 56 82 V4PLD2Data).getD 15 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row15Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD1Data 15 j =
      ((rectangularize 56 82 V4PLD2Data).getD 15 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row15Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD1Data 15 j =
      ((rectangularize 56 82 V4PLD2Data).getD 15 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row15Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD1Data 15 j =
      ((rectangularize 56 82 V4PLD2Data).getD 15 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row15Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD1Data 15 j =
      ((rectangularize 56 82 V4PLD2Data).getD 15 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row15Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD1Data 15 j =
      ((rectangularize 56 82 V4PLD2Data).getD 15 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row15Coeffs80To81_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 82) :
    mulCoeffTwo DData V4PLD1Data 15 j =
      ((rectangularize 56 82 V4PLD2Data).getD 15 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 := by
    omega
  rcases hCases with
    rfl | rfl <;> decide

private theorem v4PLD2Row15_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo DData V4PLD1Data 15 j =
      ((rectangularize 56 82 V4PLD2Data).getD 15 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD2Row15Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD2Row15Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD2Row15Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD2Row15Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD2Row15Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD2Row15Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD2Row15Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD2Row15Coeffs70To79_spec j (by omega) h80
  exact v4PLD2Row15Coeffs80To81_spec j (by omega) hj

private theorem v4PLD2Row15_spec :
    padOne 82 (mulRow DData V4PLD1Data 15) =
      (rectangularize 56 82 V4PLD2Data).getD 15 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 DData V4PLD1Data 15
    ((rectangularize 56 82 V4PLD2Data).getD 15 [])
  · decide
  · have hTargetSupport : (V4PLD2Data.getD 15 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 56 82 V4PLD2Data 15 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD2Row15_coefficients

private theorem v4PLD2Row16Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD1Data 16 j =
      ((rectangularize 56 82 V4PLD2Data).getD 16 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row16Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD1Data 16 j =
      ((rectangularize 56 82 V4PLD2Data).getD 16 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row16Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD1Data 16 j =
      ((rectangularize 56 82 V4PLD2Data).getD 16 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row16Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD1Data 16 j =
      ((rectangularize 56 82 V4PLD2Data).getD 16 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row16Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD1Data 16 j =
      ((rectangularize 56 82 V4PLD2Data).getD 16 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row16Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD1Data 16 j =
      ((rectangularize 56 82 V4PLD2Data).getD 16 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row16Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD1Data 16 j =
      ((rectangularize 56 82 V4PLD2Data).getD 16 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row16Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD1Data 16 j =
      ((rectangularize 56 82 V4PLD2Data).getD 16 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row16Coeffs80To81_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 82) :
    mulCoeffTwo DData V4PLD1Data 16 j =
      ((rectangularize 56 82 V4PLD2Data).getD 16 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 := by
    omega
  rcases hCases with
    rfl | rfl <;> decide

private theorem v4PLD2Row16_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo DData V4PLD1Data 16 j =
      ((rectangularize 56 82 V4PLD2Data).getD 16 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD2Row16Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD2Row16Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD2Row16Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD2Row16Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD2Row16Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD2Row16Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD2Row16Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD2Row16Coeffs70To79_spec j (by omega) h80
  exact v4PLD2Row16Coeffs80To81_spec j (by omega) hj

private theorem v4PLD2Row16_spec :
    padOne 82 (mulRow DData V4PLD1Data 16) =
      (rectangularize 56 82 V4PLD2Data).getD 16 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 DData V4PLD1Data 16
    ((rectangularize 56 82 V4PLD2Data).getD 16 [])
  · decide
  · have hTargetSupport : (V4PLD2Data.getD 16 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 56 82 V4PLD2Data 16 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD2Row16_coefficients

private theorem v4PLD2Row17Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD1Data 17 j =
      ((rectangularize 56 82 V4PLD2Data).getD 17 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row17Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD1Data 17 j =
      ((rectangularize 56 82 V4PLD2Data).getD 17 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row17Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD1Data 17 j =
      ((rectangularize 56 82 V4PLD2Data).getD 17 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row17Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD1Data 17 j =
      ((rectangularize 56 82 V4PLD2Data).getD 17 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row17Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD1Data 17 j =
      ((rectangularize 56 82 V4PLD2Data).getD 17 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row17Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD1Data 17 j =
      ((rectangularize 56 82 V4PLD2Data).getD 17 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row17Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD1Data 17 j =
      ((rectangularize 56 82 V4PLD2Data).getD 17 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row17Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD1Data 17 j =
      ((rectangularize 56 82 V4PLD2Data).getD 17 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row17Coeffs80To81_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 82) :
    mulCoeffTwo DData V4PLD1Data 17 j =
      ((rectangularize 56 82 V4PLD2Data).getD 17 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 := by
    omega
  rcases hCases with
    rfl | rfl <;> decide

private theorem v4PLD2Row17_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo DData V4PLD1Data 17 j =
      ((rectangularize 56 82 V4PLD2Data).getD 17 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD2Row17Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD2Row17Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD2Row17Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD2Row17Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD2Row17Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD2Row17Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD2Row17Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD2Row17Coeffs70To79_spec j (by omega) h80
  exact v4PLD2Row17Coeffs80To81_spec j (by omega) hj

private theorem v4PLD2Row17_spec :
    padOne 82 (mulRow DData V4PLD1Data 17) =
      (rectangularize 56 82 V4PLD2Data).getD 17 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 DData V4PLD1Data 17
    ((rectangularize 56 82 V4PLD2Data).getD 17 [])
  · decide
  · have hTargetSupport : (V4PLD2Data.getD 17 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 56 82 V4PLD2Data 17 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD2Row17_coefficients

private theorem v4PLD2Row18Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD1Data 18 j =
      ((rectangularize 56 82 V4PLD2Data).getD 18 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row18Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD1Data 18 j =
      ((rectangularize 56 82 V4PLD2Data).getD 18 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row18Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD1Data 18 j =
      ((rectangularize 56 82 V4PLD2Data).getD 18 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row18Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD1Data 18 j =
      ((rectangularize 56 82 V4PLD2Data).getD 18 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row18Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD1Data 18 j =
      ((rectangularize 56 82 V4PLD2Data).getD 18 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row18Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD1Data 18 j =
      ((rectangularize 56 82 V4PLD2Data).getD 18 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row18Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD1Data 18 j =
      ((rectangularize 56 82 V4PLD2Data).getD 18 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row18Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD1Data 18 j =
      ((rectangularize 56 82 V4PLD2Data).getD 18 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row18Coeffs80To81_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 82) :
    mulCoeffTwo DData V4PLD1Data 18 j =
      ((rectangularize 56 82 V4PLD2Data).getD 18 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 := by
    omega
  rcases hCases with
    rfl | rfl <;> decide

private theorem v4PLD2Row18_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo DData V4PLD1Data 18 j =
      ((rectangularize 56 82 V4PLD2Data).getD 18 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD2Row18Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD2Row18Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD2Row18Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD2Row18Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD2Row18Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD2Row18Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD2Row18Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD2Row18Coeffs70To79_spec j (by omega) h80
  exact v4PLD2Row18Coeffs80To81_spec j (by omega) hj

private theorem v4PLD2Row18_spec :
    padOne 82 (mulRow DData V4PLD1Data 18) =
      (rectangularize 56 82 V4PLD2Data).getD 18 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 DData V4PLD1Data 18
    ((rectangularize 56 82 V4PLD2Data).getD 18 [])
  · decide
  · have hTargetSupport : (V4PLD2Data.getD 18 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 56 82 V4PLD2Data 18 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD2Row18_coefficients

private theorem v4PLD2Row19Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD1Data 19 j =
      ((rectangularize 56 82 V4PLD2Data).getD 19 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row19Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD1Data 19 j =
      ((rectangularize 56 82 V4PLD2Data).getD 19 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row19Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD1Data 19 j =
      ((rectangularize 56 82 V4PLD2Data).getD 19 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row19Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD1Data 19 j =
      ((rectangularize 56 82 V4PLD2Data).getD 19 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row19Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD1Data 19 j =
      ((rectangularize 56 82 V4PLD2Data).getD 19 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row19Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD1Data 19 j =
      ((rectangularize 56 82 V4PLD2Data).getD 19 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row19Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD1Data 19 j =
      ((rectangularize 56 82 V4PLD2Data).getD 19 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row19Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD1Data 19 j =
      ((rectangularize 56 82 V4PLD2Data).getD 19 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row19Coeffs80To81_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 82) :
    mulCoeffTwo DData V4PLD1Data 19 j =
      ((rectangularize 56 82 V4PLD2Data).getD 19 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 := by
    omega
  rcases hCases with
    rfl | rfl <;> decide

private theorem v4PLD2Row19_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo DData V4PLD1Data 19 j =
      ((rectangularize 56 82 V4PLD2Data).getD 19 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD2Row19Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD2Row19Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD2Row19Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD2Row19Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD2Row19Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD2Row19Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD2Row19Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD2Row19Coeffs70To79_spec j (by omega) h80
  exact v4PLD2Row19Coeffs80To81_spec j (by omega) hj

private theorem v4PLD2Row19_spec :
    padOne 82 (mulRow DData V4PLD1Data 19) =
      (rectangularize 56 82 V4PLD2Data).getD 19 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 DData V4PLD1Data 19
    ((rectangularize 56 82 V4PLD2Data).getD 19 [])
  · decide
  · have hTargetSupport : (V4PLD2Data.getD 19 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 56 82 V4PLD2Data 19 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD2Row19_coefficients

private theorem v4PLD2Row20Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD1Data 20 j =
      ((rectangularize 56 82 V4PLD2Data).getD 20 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row20Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD1Data 20 j =
      ((rectangularize 56 82 V4PLD2Data).getD 20 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row20Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD1Data 20 j =
      ((rectangularize 56 82 V4PLD2Data).getD 20 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row20Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD1Data 20 j =
      ((rectangularize 56 82 V4PLD2Data).getD 20 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row20Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD1Data 20 j =
      ((rectangularize 56 82 V4PLD2Data).getD 20 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row20Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD1Data 20 j =
      ((rectangularize 56 82 V4PLD2Data).getD 20 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row20Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD1Data 20 j =
      ((rectangularize 56 82 V4PLD2Data).getD 20 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row20Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD1Data 20 j =
      ((rectangularize 56 82 V4PLD2Data).getD 20 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row20Coeffs80To81_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 82) :
    mulCoeffTwo DData V4PLD1Data 20 j =
      ((rectangularize 56 82 V4PLD2Data).getD 20 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 := by
    omega
  rcases hCases with
    rfl | rfl <;> decide

private theorem v4PLD2Row20_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo DData V4PLD1Data 20 j =
      ((rectangularize 56 82 V4PLD2Data).getD 20 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD2Row20Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD2Row20Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD2Row20Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD2Row20Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD2Row20Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD2Row20Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD2Row20Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD2Row20Coeffs70To79_spec j (by omega) h80
  exact v4PLD2Row20Coeffs80To81_spec j (by omega) hj

private theorem v4PLD2Row20_spec :
    padOne 82 (mulRow DData V4PLD1Data 20) =
      (rectangularize 56 82 V4PLD2Data).getD 20 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 DData V4PLD1Data 20
    ((rectangularize 56 82 V4PLD2Data).getD 20 [])
  · decide
  · have hTargetSupport : (V4PLD2Data.getD 20 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 56 82 V4PLD2Data 20 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD2Row20_coefficients

private theorem v4PLD2Row21Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD1Data 21 j =
      ((rectangularize 56 82 V4PLD2Data).getD 21 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row21Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD1Data 21 j =
      ((rectangularize 56 82 V4PLD2Data).getD 21 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row21Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD1Data 21 j =
      ((rectangularize 56 82 V4PLD2Data).getD 21 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row21Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD1Data 21 j =
      ((rectangularize 56 82 V4PLD2Data).getD 21 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row21Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD1Data 21 j =
      ((rectangularize 56 82 V4PLD2Data).getD 21 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row21Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD1Data 21 j =
      ((rectangularize 56 82 V4PLD2Data).getD 21 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row21Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD1Data 21 j =
      ((rectangularize 56 82 V4PLD2Data).getD 21 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row21Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD1Data 21 j =
      ((rectangularize 56 82 V4PLD2Data).getD 21 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row21Coeffs80To81_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 82) :
    mulCoeffTwo DData V4PLD1Data 21 j =
      ((rectangularize 56 82 V4PLD2Data).getD 21 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 := by
    omega
  rcases hCases with
    rfl | rfl <;> decide

private theorem v4PLD2Row21_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo DData V4PLD1Data 21 j =
      ((rectangularize 56 82 V4PLD2Data).getD 21 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD2Row21Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD2Row21Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD2Row21Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD2Row21Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD2Row21Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD2Row21Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD2Row21Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD2Row21Coeffs70To79_spec j (by omega) h80
  exact v4PLD2Row21Coeffs80To81_spec j (by omega) hj

private theorem v4PLD2Row21_spec :
    padOne 82 (mulRow DData V4PLD1Data 21) =
      (rectangularize 56 82 V4PLD2Data).getD 21 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 DData V4PLD1Data 21
    ((rectangularize 56 82 V4PLD2Data).getD 21 [])
  · decide
  · have hTargetSupport : (V4PLD2Data.getD 21 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 56 82 V4PLD2Data 21 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD2Row21_coefficients

private theorem v4PLD2Row22Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD1Data 22 j =
      ((rectangularize 56 82 V4PLD2Data).getD 22 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row22Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD1Data 22 j =
      ((rectangularize 56 82 V4PLD2Data).getD 22 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row22Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD1Data 22 j =
      ((rectangularize 56 82 V4PLD2Data).getD 22 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row22Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD1Data 22 j =
      ((rectangularize 56 82 V4PLD2Data).getD 22 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row22Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD1Data 22 j =
      ((rectangularize 56 82 V4PLD2Data).getD 22 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row22Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD1Data 22 j =
      ((rectangularize 56 82 V4PLD2Data).getD 22 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row22Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD1Data 22 j =
      ((rectangularize 56 82 V4PLD2Data).getD 22 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row22Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD1Data 22 j =
      ((rectangularize 56 82 V4PLD2Data).getD 22 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row22Coeffs80To81_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 82) :
    mulCoeffTwo DData V4PLD1Data 22 j =
      ((rectangularize 56 82 V4PLD2Data).getD 22 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 := by
    omega
  rcases hCases with
    rfl | rfl <;> decide

private theorem v4PLD2Row22_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo DData V4PLD1Data 22 j =
      ((rectangularize 56 82 V4PLD2Data).getD 22 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD2Row22Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD2Row22Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD2Row22Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD2Row22Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD2Row22Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD2Row22Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD2Row22Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD2Row22Coeffs70To79_spec j (by omega) h80
  exact v4PLD2Row22Coeffs80To81_spec j (by omega) hj

private theorem v4PLD2Row22_spec :
    padOne 82 (mulRow DData V4PLD1Data 22) =
      (rectangularize 56 82 V4PLD2Data).getD 22 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 DData V4PLD1Data 22
    ((rectangularize 56 82 V4PLD2Data).getD 22 [])
  · decide
  · have hTargetSupport : (V4PLD2Data.getD 22 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 56 82 V4PLD2Data 22 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD2Row22_coefficients

private theorem v4PLD2Row23Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD1Data 23 j =
      ((rectangularize 56 82 V4PLD2Data).getD 23 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row23Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD1Data 23 j =
      ((rectangularize 56 82 V4PLD2Data).getD 23 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row23Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD1Data 23 j =
      ((rectangularize 56 82 V4PLD2Data).getD 23 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row23Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD1Data 23 j =
      ((rectangularize 56 82 V4PLD2Data).getD 23 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row23Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD1Data 23 j =
      ((rectangularize 56 82 V4PLD2Data).getD 23 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row23Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD1Data 23 j =
      ((rectangularize 56 82 V4PLD2Data).getD 23 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row23Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD1Data 23 j =
      ((rectangularize 56 82 V4PLD2Data).getD 23 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row23Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD1Data 23 j =
      ((rectangularize 56 82 V4PLD2Data).getD 23 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row23Coeffs80To81_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 82) :
    mulCoeffTwo DData V4PLD1Data 23 j =
      ((rectangularize 56 82 V4PLD2Data).getD 23 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 := by
    omega
  rcases hCases with
    rfl | rfl <;> decide

private theorem v4PLD2Row23_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo DData V4PLD1Data 23 j =
      ((rectangularize 56 82 V4PLD2Data).getD 23 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD2Row23Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD2Row23Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD2Row23Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD2Row23Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD2Row23Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD2Row23Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD2Row23Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD2Row23Coeffs70To79_spec j (by omega) h80
  exact v4PLD2Row23Coeffs80To81_spec j (by omega) hj

private theorem v4PLD2Row23_spec :
    padOne 82 (mulRow DData V4PLD1Data 23) =
      (rectangularize 56 82 V4PLD2Data).getD 23 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 DData V4PLD1Data 23
    ((rectangularize 56 82 V4PLD2Data).getD 23 [])
  · decide
  · have hTargetSupport : (V4PLD2Data.getD 23 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 56 82 V4PLD2Data 23 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD2Row23_coefficients

private theorem v4PLD2Row24Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD1Data 24 j =
      ((rectangularize 56 82 V4PLD2Data).getD 24 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row24Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD1Data 24 j =
      ((rectangularize 56 82 V4PLD2Data).getD 24 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row24Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD1Data 24 j =
      ((rectangularize 56 82 V4PLD2Data).getD 24 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row24Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD1Data 24 j =
      ((rectangularize 56 82 V4PLD2Data).getD 24 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row24Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD1Data 24 j =
      ((rectangularize 56 82 V4PLD2Data).getD 24 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row24Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD1Data 24 j =
      ((rectangularize 56 82 V4PLD2Data).getD 24 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row24Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD1Data 24 j =
      ((rectangularize 56 82 V4PLD2Data).getD 24 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row24Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD1Data 24 j =
      ((rectangularize 56 82 V4PLD2Data).getD 24 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row24Coeffs80To81_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 82) :
    mulCoeffTwo DData V4PLD1Data 24 j =
      ((rectangularize 56 82 V4PLD2Data).getD 24 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 := by
    omega
  rcases hCases with
    rfl | rfl <;> decide

private theorem v4PLD2Row24_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo DData V4PLD1Data 24 j =
      ((rectangularize 56 82 V4PLD2Data).getD 24 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD2Row24Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD2Row24Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD2Row24Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD2Row24Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD2Row24Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD2Row24Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD2Row24Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD2Row24Coeffs70To79_spec j (by omega) h80
  exact v4PLD2Row24Coeffs80To81_spec j (by omega) hj

private theorem v4PLD2Row24_spec :
    padOne 82 (mulRow DData V4PLD1Data 24) =
      (rectangularize 56 82 V4PLD2Data).getD 24 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 DData V4PLD1Data 24
    ((rectangularize 56 82 V4PLD2Data).getD 24 [])
  · decide
  · have hTargetSupport : (V4PLD2Data.getD 24 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 56 82 V4PLD2Data 24 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD2Row24_coefficients

private theorem v4PLD2Row25Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD1Data 25 j =
      ((rectangularize 56 82 V4PLD2Data).getD 25 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row25Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD1Data 25 j =
      ((rectangularize 56 82 V4PLD2Data).getD 25 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row25Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD1Data 25 j =
      ((rectangularize 56 82 V4PLD2Data).getD 25 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row25Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD1Data 25 j =
      ((rectangularize 56 82 V4PLD2Data).getD 25 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row25Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD1Data 25 j =
      ((rectangularize 56 82 V4PLD2Data).getD 25 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row25Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD1Data 25 j =
      ((rectangularize 56 82 V4PLD2Data).getD 25 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row25Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD1Data 25 j =
      ((rectangularize 56 82 V4PLD2Data).getD 25 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row25Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD1Data 25 j =
      ((rectangularize 56 82 V4PLD2Data).getD 25 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row25Coeffs80To81_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 82) :
    mulCoeffTwo DData V4PLD1Data 25 j =
      ((rectangularize 56 82 V4PLD2Data).getD 25 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 := by
    omega
  rcases hCases with
    rfl | rfl <;> decide

private theorem v4PLD2Row25_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo DData V4PLD1Data 25 j =
      ((rectangularize 56 82 V4PLD2Data).getD 25 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD2Row25Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD2Row25Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD2Row25Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD2Row25Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD2Row25Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD2Row25Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD2Row25Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD2Row25Coeffs70To79_spec j (by omega) h80
  exact v4PLD2Row25Coeffs80To81_spec j (by omega) hj

private theorem v4PLD2Row25_spec :
    padOne 82 (mulRow DData V4PLD1Data 25) =
      (rectangularize 56 82 V4PLD2Data).getD 25 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 DData V4PLD1Data 25
    ((rectangularize 56 82 V4PLD2Data).getD 25 [])
  · decide
  · have hTargetSupport : (V4PLD2Data.getD 25 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 56 82 V4PLD2Data 25 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD2Row25_coefficients

private theorem v4PLD2Row26Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD1Data 26 j =
      ((rectangularize 56 82 V4PLD2Data).getD 26 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row26Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD1Data 26 j =
      ((rectangularize 56 82 V4PLD2Data).getD 26 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row26Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD1Data 26 j =
      ((rectangularize 56 82 V4PLD2Data).getD 26 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row26Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD1Data 26 j =
      ((rectangularize 56 82 V4PLD2Data).getD 26 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row26Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD1Data 26 j =
      ((rectangularize 56 82 V4PLD2Data).getD 26 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row26Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD1Data 26 j =
      ((rectangularize 56 82 V4PLD2Data).getD 26 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row26Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD1Data 26 j =
      ((rectangularize 56 82 V4PLD2Data).getD 26 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row26Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD1Data 26 j =
      ((rectangularize 56 82 V4PLD2Data).getD 26 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row26Coeffs80To81_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 82) :
    mulCoeffTwo DData V4PLD1Data 26 j =
      ((rectangularize 56 82 V4PLD2Data).getD 26 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 := by
    omega
  rcases hCases with
    rfl | rfl <;> decide

private theorem v4PLD2Row26_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo DData V4PLD1Data 26 j =
      ((rectangularize 56 82 V4PLD2Data).getD 26 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD2Row26Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD2Row26Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD2Row26Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD2Row26Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD2Row26Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD2Row26Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD2Row26Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD2Row26Coeffs70To79_spec j (by omega) h80
  exact v4PLD2Row26Coeffs80To81_spec j (by omega) hj

private theorem v4PLD2Row26_spec :
    padOne 82 (mulRow DData V4PLD1Data 26) =
      (rectangularize 56 82 V4PLD2Data).getD 26 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 DData V4PLD1Data 26
    ((rectangularize 56 82 V4PLD2Data).getD 26 [])
  · decide
  · have hTargetSupport : (V4PLD2Data.getD 26 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 56 82 V4PLD2Data 26 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD2Row26_coefficients

private theorem v4PLD2Row27Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD1Data 27 j =
      ((rectangularize 56 82 V4PLD2Data).getD 27 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row27Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD1Data 27 j =
      ((rectangularize 56 82 V4PLD2Data).getD 27 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row27Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD1Data 27 j =
      ((rectangularize 56 82 V4PLD2Data).getD 27 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row27Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD1Data 27 j =
      ((rectangularize 56 82 V4PLD2Data).getD 27 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row27Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD1Data 27 j =
      ((rectangularize 56 82 V4PLD2Data).getD 27 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row27Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD1Data 27 j =
      ((rectangularize 56 82 V4PLD2Data).getD 27 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row27Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD1Data 27 j =
      ((rectangularize 56 82 V4PLD2Data).getD 27 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row27Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD1Data 27 j =
      ((rectangularize 56 82 V4PLD2Data).getD 27 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row27Coeffs80To81_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 82) :
    mulCoeffTwo DData V4PLD1Data 27 j =
      ((rectangularize 56 82 V4PLD2Data).getD 27 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 := by
    omega
  rcases hCases with
    rfl | rfl <;> decide

private theorem v4PLD2Row27_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo DData V4PLD1Data 27 j =
      ((rectangularize 56 82 V4PLD2Data).getD 27 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD2Row27Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD2Row27Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD2Row27Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD2Row27Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD2Row27Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD2Row27Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD2Row27Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD2Row27Coeffs70To79_spec j (by omega) h80
  exact v4PLD2Row27Coeffs80To81_spec j (by omega) hj

private theorem v4PLD2Row27_spec :
    padOne 82 (mulRow DData V4PLD1Data 27) =
      (rectangularize 56 82 V4PLD2Data).getD 27 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 DData V4PLD1Data 27
    ((rectangularize 56 82 V4PLD2Data).getD 27 [])
  · decide
  · have hTargetSupport : (V4PLD2Data.getD 27 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 56 82 V4PLD2Data 27 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD2Row27_coefficients

private theorem v4PLD2Row28Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD1Data 28 j =
      ((rectangularize 56 82 V4PLD2Data).getD 28 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row28Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD1Data 28 j =
      ((rectangularize 56 82 V4PLD2Data).getD 28 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row28Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD1Data 28 j =
      ((rectangularize 56 82 V4PLD2Data).getD 28 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row28Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD1Data 28 j =
      ((rectangularize 56 82 V4PLD2Data).getD 28 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row28Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD1Data 28 j =
      ((rectangularize 56 82 V4PLD2Data).getD 28 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row28Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD1Data 28 j =
      ((rectangularize 56 82 V4PLD2Data).getD 28 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row28Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD1Data 28 j =
      ((rectangularize 56 82 V4PLD2Data).getD 28 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row28Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD1Data 28 j =
      ((rectangularize 56 82 V4PLD2Data).getD 28 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row28Coeffs80To81_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 82) :
    mulCoeffTwo DData V4PLD1Data 28 j =
      ((rectangularize 56 82 V4PLD2Data).getD 28 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 := by
    omega
  rcases hCases with
    rfl | rfl <;> decide

private theorem v4PLD2Row28_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo DData V4PLD1Data 28 j =
      ((rectangularize 56 82 V4PLD2Data).getD 28 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD2Row28Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD2Row28Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD2Row28Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD2Row28Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD2Row28Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD2Row28Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD2Row28Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD2Row28Coeffs70To79_spec j (by omega) h80
  exact v4PLD2Row28Coeffs80To81_spec j (by omega) hj

private theorem v4PLD2Row28_spec :
    padOne 82 (mulRow DData V4PLD1Data 28) =
      (rectangularize 56 82 V4PLD2Data).getD 28 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 DData V4PLD1Data 28
    ((rectangularize 56 82 V4PLD2Data).getD 28 [])
  · decide
  · have hTargetSupport : (V4PLD2Data.getD 28 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 56 82 V4PLD2Data 28 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD2Row28_coefficients

private theorem v4PLD2Row29Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD1Data 29 j =
      ((rectangularize 56 82 V4PLD2Data).getD 29 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row29Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD1Data 29 j =
      ((rectangularize 56 82 V4PLD2Data).getD 29 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row29Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD1Data 29 j =
      ((rectangularize 56 82 V4PLD2Data).getD 29 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row29Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD1Data 29 j =
      ((rectangularize 56 82 V4PLD2Data).getD 29 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row29Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD1Data 29 j =
      ((rectangularize 56 82 V4PLD2Data).getD 29 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row29Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD1Data 29 j =
      ((rectangularize 56 82 V4PLD2Data).getD 29 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row29Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD1Data 29 j =
      ((rectangularize 56 82 V4PLD2Data).getD 29 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row29Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD1Data 29 j =
      ((rectangularize 56 82 V4PLD2Data).getD 29 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row29Coeffs80To81_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 82) :
    mulCoeffTwo DData V4PLD1Data 29 j =
      ((rectangularize 56 82 V4PLD2Data).getD 29 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 := by
    omega
  rcases hCases with
    rfl | rfl <;> decide

private theorem v4PLD2Row29_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo DData V4PLD1Data 29 j =
      ((rectangularize 56 82 V4PLD2Data).getD 29 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD2Row29Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD2Row29Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD2Row29Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD2Row29Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD2Row29Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD2Row29Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD2Row29Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD2Row29Coeffs70To79_spec j (by omega) h80
  exact v4PLD2Row29Coeffs80To81_spec j (by omega) hj

private theorem v4PLD2Row29_spec :
    padOne 82 (mulRow DData V4PLD1Data 29) =
      (rectangularize 56 82 V4PLD2Data).getD 29 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 DData V4PLD1Data 29
    ((rectangularize 56 82 V4PLD2Data).getD 29 [])
  · decide
  · have hTargetSupport : (V4PLD2Data.getD 29 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 56 82 V4PLD2Data 29 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD2Row29_coefficients

private theorem v4PLD2Row30Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD1Data 30 j =
      ((rectangularize 56 82 V4PLD2Data).getD 30 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row30Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD1Data 30 j =
      ((rectangularize 56 82 V4PLD2Data).getD 30 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row30Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD1Data 30 j =
      ((rectangularize 56 82 V4PLD2Data).getD 30 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row30Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD1Data 30 j =
      ((rectangularize 56 82 V4PLD2Data).getD 30 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row30Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD1Data 30 j =
      ((rectangularize 56 82 V4PLD2Data).getD 30 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row30Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD1Data 30 j =
      ((rectangularize 56 82 V4PLD2Data).getD 30 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row30Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD1Data 30 j =
      ((rectangularize 56 82 V4PLD2Data).getD 30 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row30Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD1Data 30 j =
      ((rectangularize 56 82 V4PLD2Data).getD 30 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row30Coeffs80To81_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 82) :
    mulCoeffTwo DData V4PLD1Data 30 j =
      ((rectangularize 56 82 V4PLD2Data).getD 30 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 := by
    omega
  rcases hCases with
    rfl | rfl <;> decide

private theorem v4PLD2Row30_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo DData V4PLD1Data 30 j =
      ((rectangularize 56 82 V4PLD2Data).getD 30 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD2Row30Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD2Row30Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD2Row30Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD2Row30Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD2Row30Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD2Row30Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD2Row30Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD2Row30Coeffs70To79_spec j (by omega) h80
  exact v4PLD2Row30Coeffs80To81_spec j (by omega) hj

private theorem v4PLD2Row30_spec :
    padOne 82 (mulRow DData V4PLD1Data 30) =
      (rectangularize 56 82 V4PLD2Data).getD 30 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 DData V4PLD1Data 30
    ((rectangularize 56 82 V4PLD2Data).getD 30 [])
  · decide
  · have hTargetSupport : (V4PLD2Data.getD 30 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 56 82 V4PLD2Data 30 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD2Row30_coefficients

private theorem v4PLD2Row31Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD1Data 31 j =
      ((rectangularize 56 82 V4PLD2Data).getD 31 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row31Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD1Data 31 j =
      ((rectangularize 56 82 V4PLD2Data).getD 31 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row31Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD1Data 31 j =
      ((rectangularize 56 82 V4PLD2Data).getD 31 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row31Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD1Data 31 j =
      ((rectangularize 56 82 V4PLD2Data).getD 31 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row31Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD1Data 31 j =
      ((rectangularize 56 82 V4PLD2Data).getD 31 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row31Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD1Data 31 j =
      ((rectangularize 56 82 V4PLD2Data).getD 31 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row31Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD1Data 31 j =
      ((rectangularize 56 82 V4PLD2Data).getD 31 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row31Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD1Data 31 j =
      ((rectangularize 56 82 V4PLD2Data).getD 31 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row31Coeffs80To81_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 82) :
    mulCoeffTwo DData V4PLD1Data 31 j =
      ((rectangularize 56 82 V4PLD2Data).getD 31 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 := by
    omega
  rcases hCases with
    rfl | rfl <;> decide

private theorem v4PLD2Row31_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo DData V4PLD1Data 31 j =
      ((rectangularize 56 82 V4PLD2Data).getD 31 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD2Row31Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD2Row31Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD2Row31Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD2Row31Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD2Row31Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD2Row31Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD2Row31Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD2Row31Coeffs70To79_spec j (by omega) h80
  exact v4PLD2Row31Coeffs80To81_spec j (by omega) hj

private theorem v4PLD2Row31_spec :
    padOne 82 (mulRow DData V4PLD1Data 31) =
      (rectangularize 56 82 V4PLD2Data).getD 31 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 DData V4PLD1Data 31
    ((rectangularize 56 82 V4PLD2Data).getD 31 [])
  · decide
  · have hTargetSupport : (V4PLD2Data.getD 31 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 56 82 V4PLD2Data 31 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD2Row31_coefficients

private theorem v4PLD2Row32Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD1Data 32 j =
      ((rectangularize 56 82 V4PLD2Data).getD 32 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row32Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD1Data 32 j =
      ((rectangularize 56 82 V4PLD2Data).getD 32 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row32Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD1Data 32 j =
      ((rectangularize 56 82 V4PLD2Data).getD 32 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row32Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD1Data 32 j =
      ((rectangularize 56 82 V4PLD2Data).getD 32 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row32Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD1Data 32 j =
      ((rectangularize 56 82 V4PLD2Data).getD 32 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row32Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD1Data 32 j =
      ((rectangularize 56 82 V4PLD2Data).getD 32 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row32Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD1Data 32 j =
      ((rectangularize 56 82 V4PLD2Data).getD 32 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row32Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD1Data 32 j =
      ((rectangularize 56 82 V4PLD2Data).getD 32 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row32Coeffs80To81_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 82) :
    mulCoeffTwo DData V4PLD1Data 32 j =
      ((rectangularize 56 82 V4PLD2Data).getD 32 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 := by
    omega
  rcases hCases with
    rfl | rfl <;> decide

private theorem v4PLD2Row32_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo DData V4PLD1Data 32 j =
      ((rectangularize 56 82 V4PLD2Data).getD 32 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD2Row32Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD2Row32Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD2Row32Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD2Row32Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD2Row32Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD2Row32Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD2Row32Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD2Row32Coeffs70To79_spec j (by omega) h80
  exact v4PLD2Row32Coeffs80To81_spec j (by omega) hj

private theorem v4PLD2Row32_spec :
    padOne 82 (mulRow DData V4PLD1Data 32) =
      (rectangularize 56 82 V4PLD2Data).getD 32 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 DData V4PLD1Data 32
    ((rectangularize 56 82 V4PLD2Data).getD 32 [])
  · decide
  · have hTargetSupport : (V4PLD2Data.getD 32 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 56 82 V4PLD2Data 32 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD2Row32_coefficients

private theorem v4PLD2Row33Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD1Data 33 j =
      ((rectangularize 56 82 V4PLD2Data).getD 33 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row33Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD1Data 33 j =
      ((rectangularize 56 82 V4PLD2Data).getD 33 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row33Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD1Data 33 j =
      ((rectangularize 56 82 V4PLD2Data).getD 33 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row33Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD1Data 33 j =
      ((rectangularize 56 82 V4PLD2Data).getD 33 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row33Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD1Data 33 j =
      ((rectangularize 56 82 V4PLD2Data).getD 33 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row33Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD1Data 33 j =
      ((rectangularize 56 82 V4PLD2Data).getD 33 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row33Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD1Data 33 j =
      ((rectangularize 56 82 V4PLD2Data).getD 33 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row33Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD1Data 33 j =
      ((rectangularize 56 82 V4PLD2Data).getD 33 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row33Coeffs80To81_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 82) :
    mulCoeffTwo DData V4PLD1Data 33 j =
      ((rectangularize 56 82 V4PLD2Data).getD 33 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 := by
    omega
  rcases hCases with
    rfl | rfl <;> decide

private theorem v4PLD2Row33_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo DData V4PLD1Data 33 j =
      ((rectangularize 56 82 V4PLD2Data).getD 33 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD2Row33Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD2Row33Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD2Row33Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD2Row33Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD2Row33Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD2Row33Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD2Row33Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD2Row33Coeffs70To79_spec j (by omega) h80
  exact v4PLD2Row33Coeffs80To81_spec j (by omega) hj

private theorem v4PLD2Row33_spec :
    padOne 82 (mulRow DData V4PLD1Data 33) =
      (rectangularize 56 82 V4PLD2Data).getD 33 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 DData V4PLD1Data 33
    ((rectangularize 56 82 V4PLD2Data).getD 33 [])
  · decide
  · have hTargetSupport : (V4PLD2Data.getD 33 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 56 82 V4PLD2Data 33 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD2Row33_coefficients

private theorem v4PLD2Row34Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD1Data 34 j =
      ((rectangularize 56 82 V4PLD2Data).getD 34 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row34Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD1Data 34 j =
      ((rectangularize 56 82 V4PLD2Data).getD 34 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row34Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD1Data 34 j =
      ((rectangularize 56 82 V4PLD2Data).getD 34 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row34Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD1Data 34 j =
      ((rectangularize 56 82 V4PLD2Data).getD 34 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row34Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD1Data 34 j =
      ((rectangularize 56 82 V4PLD2Data).getD 34 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row34Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD1Data 34 j =
      ((rectangularize 56 82 V4PLD2Data).getD 34 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row34Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD1Data 34 j =
      ((rectangularize 56 82 V4PLD2Data).getD 34 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row34Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD1Data 34 j =
      ((rectangularize 56 82 V4PLD2Data).getD 34 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row34Coeffs80To81_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 82) :
    mulCoeffTwo DData V4PLD1Data 34 j =
      ((rectangularize 56 82 V4PLD2Data).getD 34 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 := by
    omega
  rcases hCases with
    rfl | rfl <;> decide

private theorem v4PLD2Row34_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo DData V4PLD1Data 34 j =
      ((rectangularize 56 82 V4PLD2Data).getD 34 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD2Row34Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD2Row34Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD2Row34Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD2Row34Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD2Row34Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD2Row34Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD2Row34Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD2Row34Coeffs70To79_spec j (by omega) h80
  exact v4PLD2Row34Coeffs80To81_spec j (by omega) hj

private theorem v4PLD2Row34_spec :
    padOne 82 (mulRow DData V4PLD1Data 34) =
      (rectangularize 56 82 V4PLD2Data).getD 34 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 DData V4PLD1Data 34
    ((rectangularize 56 82 V4PLD2Data).getD 34 [])
  · decide
  · have hTargetSupport : (V4PLD2Data.getD 34 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 56 82 V4PLD2Data 34 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD2Row34_coefficients

private theorem v4PLD2Row35Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD1Data 35 j =
      ((rectangularize 56 82 V4PLD2Data).getD 35 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row35Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD1Data 35 j =
      ((rectangularize 56 82 V4PLD2Data).getD 35 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row35Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD1Data 35 j =
      ((rectangularize 56 82 V4PLD2Data).getD 35 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row35Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD1Data 35 j =
      ((rectangularize 56 82 V4PLD2Data).getD 35 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row35Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD1Data 35 j =
      ((rectangularize 56 82 V4PLD2Data).getD 35 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row35Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD1Data 35 j =
      ((rectangularize 56 82 V4PLD2Data).getD 35 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row35Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD1Data 35 j =
      ((rectangularize 56 82 V4PLD2Data).getD 35 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row35Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD1Data 35 j =
      ((rectangularize 56 82 V4PLD2Data).getD 35 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row35Coeffs80To81_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 82) :
    mulCoeffTwo DData V4PLD1Data 35 j =
      ((rectangularize 56 82 V4PLD2Data).getD 35 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 := by
    omega
  rcases hCases with
    rfl | rfl <;> decide

private theorem v4PLD2Row35_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo DData V4PLD1Data 35 j =
      ((rectangularize 56 82 V4PLD2Data).getD 35 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD2Row35Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD2Row35Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD2Row35Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD2Row35Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD2Row35Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD2Row35Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD2Row35Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD2Row35Coeffs70To79_spec j (by omega) h80
  exact v4PLD2Row35Coeffs80To81_spec j (by omega) hj

private theorem v4PLD2Row35_spec :
    padOne 82 (mulRow DData V4PLD1Data 35) =
      (rectangularize 56 82 V4PLD2Data).getD 35 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 DData V4PLD1Data 35
    ((rectangularize 56 82 V4PLD2Data).getD 35 [])
  · decide
  · have hTargetSupport : (V4PLD2Data.getD 35 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 56 82 V4PLD2Data 35 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD2Row35_coefficients

private theorem v4PLD2Row36Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD1Data 36 j =
      ((rectangularize 56 82 V4PLD2Data).getD 36 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row36Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD1Data 36 j =
      ((rectangularize 56 82 V4PLD2Data).getD 36 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row36Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD1Data 36 j =
      ((rectangularize 56 82 V4PLD2Data).getD 36 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row36Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD1Data 36 j =
      ((rectangularize 56 82 V4PLD2Data).getD 36 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row36Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD1Data 36 j =
      ((rectangularize 56 82 V4PLD2Data).getD 36 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row36Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD1Data 36 j =
      ((rectangularize 56 82 V4PLD2Data).getD 36 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row36Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD1Data 36 j =
      ((rectangularize 56 82 V4PLD2Data).getD 36 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row36Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD1Data 36 j =
      ((rectangularize 56 82 V4PLD2Data).getD 36 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row36Coeffs80To81_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 82) :
    mulCoeffTwo DData V4PLD1Data 36 j =
      ((rectangularize 56 82 V4PLD2Data).getD 36 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 := by
    omega
  rcases hCases with
    rfl | rfl <;> decide

private theorem v4PLD2Row36_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo DData V4PLD1Data 36 j =
      ((rectangularize 56 82 V4PLD2Data).getD 36 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD2Row36Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD2Row36Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD2Row36Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD2Row36Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD2Row36Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD2Row36Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD2Row36Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD2Row36Coeffs70To79_spec j (by omega) h80
  exact v4PLD2Row36Coeffs80To81_spec j (by omega) hj

private theorem v4PLD2Row36_spec :
    padOne 82 (mulRow DData V4PLD1Data 36) =
      (rectangularize 56 82 V4PLD2Data).getD 36 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 DData V4PLD1Data 36
    ((rectangularize 56 82 V4PLD2Data).getD 36 [])
  · decide
  · have hTargetSupport : (V4PLD2Data.getD 36 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 56 82 V4PLD2Data 36 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD2Row36_coefficients

private theorem v4PLD2Row37Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD1Data 37 j =
      ((rectangularize 56 82 V4PLD2Data).getD 37 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row37Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD1Data 37 j =
      ((rectangularize 56 82 V4PLD2Data).getD 37 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row37Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD1Data 37 j =
      ((rectangularize 56 82 V4PLD2Data).getD 37 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row37Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD1Data 37 j =
      ((rectangularize 56 82 V4PLD2Data).getD 37 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row37Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD1Data 37 j =
      ((rectangularize 56 82 V4PLD2Data).getD 37 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row37Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD1Data 37 j =
      ((rectangularize 56 82 V4PLD2Data).getD 37 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row37Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD1Data 37 j =
      ((rectangularize 56 82 V4PLD2Data).getD 37 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row37Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD1Data 37 j =
      ((rectangularize 56 82 V4PLD2Data).getD 37 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row37Coeffs80To81_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 82) :
    mulCoeffTwo DData V4PLD1Data 37 j =
      ((rectangularize 56 82 V4PLD2Data).getD 37 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 := by
    omega
  rcases hCases with
    rfl | rfl <;> decide

private theorem v4PLD2Row37_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo DData V4PLD1Data 37 j =
      ((rectangularize 56 82 V4PLD2Data).getD 37 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD2Row37Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD2Row37Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD2Row37Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD2Row37Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD2Row37Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD2Row37Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD2Row37Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD2Row37Coeffs70To79_spec j (by omega) h80
  exact v4PLD2Row37Coeffs80To81_spec j (by omega) hj

private theorem v4PLD2Row37_spec :
    padOne 82 (mulRow DData V4PLD1Data 37) =
      (rectangularize 56 82 V4PLD2Data).getD 37 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 DData V4PLD1Data 37
    ((rectangularize 56 82 V4PLD2Data).getD 37 [])
  · decide
  · have hTargetSupport : (V4PLD2Data.getD 37 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 56 82 V4PLD2Data 37 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD2Row37_coefficients

private theorem v4PLD2Row38Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD1Data 38 j =
      ((rectangularize 56 82 V4PLD2Data).getD 38 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row38Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD1Data 38 j =
      ((rectangularize 56 82 V4PLD2Data).getD 38 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row38Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD1Data 38 j =
      ((rectangularize 56 82 V4PLD2Data).getD 38 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row38Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD1Data 38 j =
      ((rectangularize 56 82 V4PLD2Data).getD 38 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row38Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD1Data 38 j =
      ((rectangularize 56 82 V4PLD2Data).getD 38 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row38Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD1Data 38 j =
      ((rectangularize 56 82 V4PLD2Data).getD 38 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row38Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD1Data 38 j =
      ((rectangularize 56 82 V4PLD2Data).getD 38 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row38Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD1Data 38 j =
      ((rectangularize 56 82 V4PLD2Data).getD 38 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row38Coeffs80To81_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 82) :
    mulCoeffTwo DData V4PLD1Data 38 j =
      ((rectangularize 56 82 V4PLD2Data).getD 38 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 := by
    omega
  rcases hCases with
    rfl | rfl <;> decide

private theorem v4PLD2Row38_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo DData V4PLD1Data 38 j =
      ((rectangularize 56 82 V4PLD2Data).getD 38 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD2Row38Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD2Row38Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD2Row38Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD2Row38Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD2Row38Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD2Row38Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD2Row38Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD2Row38Coeffs70To79_spec j (by omega) h80
  exact v4PLD2Row38Coeffs80To81_spec j (by omega) hj

private theorem v4PLD2Row38_spec :
    padOne 82 (mulRow DData V4PLD1Data 38) =
      (rectangularize 56 82 V4PLD2Data).getD 38 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 DData V4PLD1Data 38
    ((rectangularize 56 82 V4PLD2Data).getD 38 [])
  · decide
  · have hTargetSupport : (V4PLD2Data.getD 38 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 56 82 V4PLD2Data 38 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD2Row38_coefficients

private theorem v4PLD2Row39Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD1Data 39 j =
      ((rectangularize 56 82 V4PLD2Data).getD 39 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row39Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD1Data 39 j =
      ((rectangularize 56 82 V4PLD2Data).getD 39 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row39Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD1Data 39 j =
      ((rectangularize 56 82 V4PLD2Data).getD 39 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row39Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD1Data 39 j =
      ((rectangularize 56 82 V4PLD2Data).getD 39 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row39Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD1Data 39 j =
      ((rectangularize 56 82 V4PLD2Data).getD 39 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row39Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD1Data 39 j =
      ((rectangularize 56 82 V4PLD2Data).getD 39 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row39Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD1Data 39 j =
      ((rectangularize 56 82 V4PLD2Data).getD 39 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row39Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD1Data 39 j =
      ((rectangularize 56 82 V4PLD2Data).getD 39 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row39Coeffs80To81_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 82) :
    mulCoeffTwo DData V4PLD1Data 39 j =
      ((rectangularize 56 82 V4PLD2Data).getD 39 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 := by
    omega
  rcases hCases with
    rfl | rfl <;> decide

private theorem v4PLD2Row39_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo DData V4PLD1Data 39 j =
      ((rectangularize 56 82 V4PLD2Data).getD 39 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD2Row39Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD2Row39Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD2Row39Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD2Row39Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD2Row39Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD2Row39Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD2Row39Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD2Row39Coeffs70To79_spec j (by omega) h80
  exact v4PLD2Row39Coeffs80To81_spec j (by omega) hj

private theorem v4PLD2Row39_spec :
    padOne 82 (mulRow DData V4PLD1Data 39) =
      (rectangularize 56 82 V4PLD2Data).getD 39 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 DData V4PLD1Data 39
    ((rectangularize 56 82 V4PLD2Data).getD 39 [])
  · decide
  · have hTargetSupport : (V4PLD2Data.getD 39 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 56 82 V4PLD2Data 39 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD2Row39_coefficients

private theorem v4PLD2Row40Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD1Data 40 j =
      ((rectangularize 56 82 V4PLD2Data).getD 40 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row40Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD1Data 40 j =
      ((rectangularize 56 82 V4PLD2Data).getD 40 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row40Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD1Data 40 j =
      ((rectangularize 56 82 V4PLD2Data).getD 40 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row40Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD1Data 40 j =
      ((rectangularize 56 82 V4PLD2Data).getD 40 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row40Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD1Data 40 j =
      ((rectangularize 56 82 V4PLD2Data).getD 40 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row40Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD1Data 40 j =
      ((rectangularize 56 82 V4PLD2Data).getD 40 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row40Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD1Data 40 j =
      ((rectangularize 56 82 V4PLD2Data).getD 40 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row40Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD1Data 40 j =
      ((rectangularize 56 82 V4PLD2Data).getD 40 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row40Coeffs80To81_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 82) :
    mulCoeffTwo DData V4PLD1Data 40 j =
      ((rectangularize 56 82 V4PLD2Data).getD 40 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 := by
    omega
  rcases hCases with
    rfl | rfl <;> decide

private theorem v4PLD2Row40_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo DData V4PLD1Data 40 j =
      ((rectangularize 56 82 V4PLD2Data).getD 40 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD2Row40Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD2Row40Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD2Row40Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD2Row40Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD2Row40Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD2Row40Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD2Row40Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD2Row40Coeffs70To79_spec j (by omega) h80
  exact v4PLD2Row40Coeffs80To81_spec j (by omega) hj

private theorem v4PLD2Row40_spec :
    padOne 82 (mulRow DData V4PLD1Data 40) =
      (rectangularize 56 82 V4PLD2Data).getD 40 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 DData V4PLD1Data 40
    ((rectangularize 56 82 V4PLD2Data).getD 40 [])
  · decide
  · have hTargetSupport : (V4PLD2Data.getD 40 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 56 82 V4PLD2Data 40 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD2Row40_coefficients

private theorem v4PLD2Row41Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD1Data 41 j =
      ((rectangularize 56 82 V4PLD2Data).getD 41 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row41Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD1Data 41 j =
      ((rectangularize 56 82 V4PLD2Data).getD 41 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row41Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD1Data 41 j =
      ((rectangularize 56 82 V4PLD2Data).getD 41 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row41Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD1Data 41 j =
      ((rectangularize 56 82 V4PLD2Data).getD 41 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row41Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD1Data 41 j =
      ((rectangularize 56 82 V4PLD2Data).getD 41 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row41Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD1Data 41 j =
      ((rectangularize 56 82 V4PLD2Data).getD 41 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row41Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD1Data 41 j =
      ((rectangularize 56 82 V4PLD2Data).getD 41 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row41Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD1Data 41 j =
      ((rectangularize 56 82 V4PLD2Data).getD 41 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD2Row41Coeffs80To81_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 82) :
    mulCoeffTwo DData V4PLD1Data 41 j =
      ((rectangularize 56 82 V4PLD2Data).getD 41 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 := by
    omega
  rcases hCases with
    rfl | rfl <;> decide

private theorem v4PLD2Row41_coefficients (j : ℕ) (hj : j < 82) :
    mulCoeffTwo DData V4PLD1Data 41 j =
      ((rectangularize 56 82 V4PLD2Data).getD 41 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD2Row41Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD2Row41Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD2Row41Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD2Row41Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD2Row41Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD2Row41Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD2Row41Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD2Row41Coeffs70To79_spec j (by omega) h80
  exact v4PLD2Row41Coeffs80To81_spec j (by omega) hj

private theorem v4PLD2Row41_spec :
    padOne 82 (mulRow DData V4PLD1Data 41) =
      (rectangularize 56 82 V4PLD2Data).getD 41 [] := by
  apply padOne_mulRow_eq_of_coefficients 82 DData V4PLD1Data 41
    ((rectangularize 56 82 V4PLD2Data).getD 41 [])
  · decide
  · have hTargetSupport : (V4PLD2Data.getD 41 []).length ≤ 82 := by
      decide
    rw [getD_rectangularize 56 82 V4PLD2Data 41 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD2Row41_coefficients

private theorem v4PLD2Row42_spec :
    padOne 82 (mulRow DData V4PLD1Data 42) =
      (rectangularize 56 82 V4PLD2Data).getD 42 [] := by
  decide

private theorem v4PLD2Row43_spec :
    padOne 82 (mulRow DData V4PLD1Data 43) =
      (rectangularize 56 82 V4PLD2Data).getD 43 [] := by
  decide

private theorem v4PLD2Row44_spec :
    padOne 82 (mulRow DData V4PLD1Data 44) =
      (rectangularize 56 82 V4PLD2Data).getD 44 [] := by
  decide

private theorem v4PLD2Row45_spec :
    padOne 82 (mulRow DData V4PLD1Data 45) =
      (rectangularize 56 82 V4PLD2Data).getD 45 [] := by
  decide

private theorem v4PLD2Row46_spec :
    padOne 82 (mulRow DData V4PLD1Data 46) =
      (rectangularize 56 82 V4PLD2Data).getD 46 [] := by
  decide

private theorem v4PLD2Row47_spec :
    padOne 82 (mulRow DData V4PLD1Data 47) =
      (rectangularize 56 82 V4PLD2Data).getD 47 [] := by
  decide

private theorem v4PLD2Row48_spec :
    padOne 82 (mulRow DData V4PLD1Data 48) =
      (rectangularize 56 82 V4PLD2Data).getD 48 [] := by
  decide

private theorem v4PLD2Row49_spec :
    padOne 82 (mulRow DData V4PLD1Data 49) =
      (rectangularize 56 82 V4PLD2Data).getD 49 [] := by
  decide

private theorem v4PLD2Row50_spec :
    padOne 82 (mulRow DData V4PLD1Data 50) =
      (rectangularize 56 82 V4PLD2Data).getD 50 [] := by
  decide

private theorem v4PLD2Row51_spec :
    padOne 82 (mulRow DData V4PLD1Data 51) =
      (rectangularize 56 82 V4PLD2Data).getD 51 [] := by
  decide

private theorem v4PLD2Row52_spec :
    padOne 82 (mulRow DData V4PLD1Data 52) =
      (rectangularize 56 82 V4PLD2Data).getD 52 [] := by
  decide

private theorem v4PLD2Row53_spec :
    padOne 82 (mulRow DData V4PLD1Data 53) =
      (rectangularize 56 82 V4PLD2Data).getD 53 [] := by
  decide

private theorem v4PLD2Row54_spec :
    padOne 82 (mulRow DData V4PLD1Data 54) =
      (rectangularize 56 82 V4PLD2Data).getD 54 [] := by
  decide

private theorem v4PLD2Row55_spec :
    padOne 82 (mulRow DData V4PLD1Data 55) =
      (rectangularize 56 82 V4PLD2Data).getD 55 [] := by
  decide

private theorem v4PLD2Rows_spec (n : ℕ) (hn : n < 56) :
    padOne 82 (mulRow DData V4PLD1Data n) =
      (rectangularize 56 82 V4PLD2Data).getD n [] := by
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
  · exact v4PLD2Row0_spec
  · exact v4PLD2Row1_spec
  · exact v4PLD2Row2_spec
  · exact v4PLD2Row3_spec
  · exact v4PLD2Row4_spec
  · exact v4PLD2Row5_spec
  · exact v4PLD2Row6_spec
  · exact v4PLD2Row7_spec
  · exact v4PLD2Row8_spec
  · exact v4PLD2Row9_spec
  · exact v4PLD2Row10_spec
  · exact v4PLD2Row11_spec
  · exact v4PLD2Row12_spec
  · exact v4PLD2Row13_spec
  · exact v4PLD2Row14_spec
  · exact v4PLD2Row15_spec
  · exact v4PLD2Row16_spec
  · exact v4PLD2Row17_spec
  · exact v4PLD2Row18_spec
  · exact v4PLD2Row19_spec
  · exact v4PLD2Row20_spec
  · exact v4PLD2Row21_spec
  · exact v4PLD2Row22_spec
  · exact v4PLD2Row23_spec
  · exact v4PLD2Row24_spec
  · exact v4PLD2Row25_spec
  · exact v4PLD2Row26_spec
  · exact v4PLD2Row27_spec
  · exact v4PLD2Row28_spec
  · exact v4PLD2Row29_spec
  · exact v4PLD2Row30_spec
  · exact v4PLD2Row31_spec
  · exact v4PLD2Row32_spec
  · exact v4PLD2Row33_spec
  · exact v4PLD2Row34_spec
  · exact v4PLD2Row35_spec
  · exact v4PLD2Row36_spec
  · exact v4PLD2Row37_spec
  · exact v4PLD2Row38_spec
  · exact v4PLD2Row39_spec
  · exact v4PLD2Row40_spec
  · exact v4PLD2Row41_spec
  · exact v4PLD2Row42_spec
  · exact v4PLD2Row43_spec
  · exact v4PLD2Row44_spec
  · exact v4PLD2Row45_spec
  · exact v4PLD2Row46_spec
  · exact v4PLD2Row47_spec
  · exact v4PLD2Row48_spec
  · exact v4PLD2Row49_spec
  · exact v4PLD2Row50_spec
  · exact v4PLD2Row51_spec
  · exact v4PLD2Row52_spec
  · exact v4PLD2Row53_spec
  · exact v4PLD2Row54_spec
  · exact v4PLD2Row55_spec

private theorem v4PLD2Left_length :
    (rectangularize 56 82 (Two.mul DData V4PLD1Data)).length = 56 := by
  decide

private theorem v4PLD2Right_length :
    (rectangularize 56 82 V4PLD2Data).length = 56 := by
  decide

-- Exact bidegree bound (55, 81); no row or column is discarded.
private theorem v4PLD2Data_spec :
    rectangularize 56 82 (Two.mul DData V4PLD1Data) =
      rectangularize 56 82 V4PLD2Data := by
  apply List.ext_getElem (v4PLD2Left_length.trans v4PLD2Right_length.symm)
  intro n hn _
  rw [List.getElem_eq_getD [], List.getElem_eq_getD []]
  rw [v4PLD2Left_length] at hn
  rw [getD_rectangularize 56 82 (Two.mul DData V4PLD1Data) n hn,
    ← mulRow_eq_getD]
  exact v4PLD2Rows_spec n hn

private theorem v4PLD3Row0_spec :
    padOne 85 (mulRow DData V4PLD2Data 0) =
      (rectangularize 58 85 V4PLD3Data).getD 0 [] := by
  decide

private theorem v4PLD3Row1_spec :
    padOne 85 (mulRow DData V4PLD2Data 1) =
      (rectangularize 58 85 V4PLD3Data).getD 1 [] := by
  decide

private theorem v4PLD3Row2_spec :
    padOne 85 (mulRow DData V4PLD2Data 2) =
      (rectangularize 58 85 V4PLD3Data).getD 2 [] := by
  decide

private theorem v4PLD3Row3_spec :
    padOne 85 (mulRow DData V4PLD2Data 3) =
      (rectangularize 58 85 V4PLD3Data).getD 3 [] := by
  decide

private theorem v4PLD3Row4_spec :
    padOne 85 (mulRow DData V4PLD2Data 4) =
      (rectangularize 58 85 V4PLD3Data).getD 4 [] := by
  decide

private theorem v4PLD3Row5_spec :
    padOne 85 (mulRow DData V4PLD2Data 5) =
      (rectangularize 58 85 V4PLD3Data).getD 5 [] := by
  decide

private theorem v4PLD3Row6_spec :
    padOne 85 (mulRow DData V4PLD2Data 6) =
      (rectangularize 58 85 V4PLD3Data).getD 6 [] := by
  decide

private theorem v4PLD3Row7_spec :
    padOne 85 (mulRow DData V4PLD2Data 7) =
      (rectangularize 58 85 V4PLD3Data).getD 7 [] := by
  decide

private theorem v4PLD3Row8_spec :
    padOne 85 (mulRow DData V4PLD2Data 8) =
      (rectangularize 58 85 V4PLD3Data).getD 8 [] := by
  decide

private theorem v4PLD3Row9_spec :
    padOne 85 (mulRow DData V4PLD2Data 9) =
      (rectangularize 58 85 V4PLD3Data).getD 9 [] := by
  decide

private theorem v4PLD3Row10_spec :
    padOne 85 (mulRow DData V4PLD2Data 10) =
      (rectangularize 58 85 V4PLD3Data).getD 10 [] := by
  decide

private theorem v4PLD3Row11Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD2Data 11 j =
      ((rectangularize 58 85 V4PLD3Data).getD 11 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row11Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD2Data 11 j =
      ((rectangularize 58 85 V4PLD3Data).getD 11 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row11Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD2Data 11 j =
      ((rectangularize 58 85 V4PLD3Data).getD 11 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row11Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD2Data 11 j =
      ((rectangularize 58 85 V4PLD3Data).getD 11 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row11Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD2Data 11 j =
      ((rectangularize 58 85 V4PLD3Data).getD 11 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row11Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD2Data 11 j =
      ((rectangularize 58 85 V4PLD3Data).getD 11 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row11Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD2Data 11 j =
      ((rectangularize 58 85 V4PLD3Data).getD 11 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row11Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD2Data 11 j =
      ((rectangularize 58 85 V4PLD3Data).getD 11 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row11Coeffs80To84_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 85) :
    mulCoeffTwo DData V4PLD2Data 11 j =
      ((rectangularize 58 85 V4PLD3Data).getD 11 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl <;> decide

private theorem v4PLD3Row11_coefficients (j : ℕ) (hj : j < 85) :
    mulCoeffTwo DData V4PLD2Data 11 j =
      ((rectangularize 58 85 V4PLD3Data).getD 11 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD3Row11Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD3Row11Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD3Row11Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD3Row11Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD3Row11Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD3Row11Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD3Row11Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD3Row11Coeffs70To79_spec j (by omega) h80
  exact v4PLD3Row11Coeffs80To84_spec j (by omega) hj

private theorem v4PLD3Row11_spec :
    padOne 85 (mulRow DData V4PLD2Data 11) =
      (rectangularize 58 85 V4PLD3Data).getD 11 [] := by
  apply padOne_mulRow_eq_of_coefficients 85 DData V4PLD2Data 11
    ((rectangularize 58 85 V4PLD3Data).getD 11 [])
  · decide
  · have hTargetSupport : (V4PLD3Data.getD 11 []).length ≤ 85 := by
      decide
    rw [getD_rectangularize 58 85 V4PLD3Data 11 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD3Row11_coefficients

private theorem v4PLD3Row12Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD2Data 12 j =
      ((rectangularize 58 85 V4PLD3Data).getD 12 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row12Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD2Data 12 j =
      ((rectangularize 58 85 V4PLD3Data).getD 12 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row12Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD2Data 12 j =
      ((rectangularize 58 85 V4PLD3Data).getD 12 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row12Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD2Data 12 j =
      ((rectangularize 58 85 V4PLD3Data).getD 12 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row12Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD2Data 12 j =
      ((rectangularize 58 85 V4PLD3Data).getD 12 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row12Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD2Data 12 j =
      ((rectangularize 58 85 V4PLD3Data).getD 12 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row12Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD2Data 12 j =
      ((rectangularize 58 85 V4PLD3Data).getD 12 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row12Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD2Data 12 j =
      ((rectangularize 58 85 V4PLD3Data).getD 12 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row12Coeffs80To84_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 85) :
    mulCoeffTwo DData V4PLD2Data 12 j =
      ((rectangularize 58 85 V4PLD3Data).getD 12 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl <;> decide

private theorem v4PLD3Row12_coefficients (j : ℕ) (hj : j < 85) :
    mulCoeffTwo DData V4PLD2Data 12 j =
      ((rectangularize 58 85 V4PLD3Data).getD 12 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD3Row12Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD3Row12Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD3Row12Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD3Row12Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD3Row12Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD3Row12Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD3Row12Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD3Row12Coeffs70To79_spec j (by omega) h80
  exact v4PLD3Row12Coeffs80To84_spec j (by omega) hj

private theorem v4PLD3Row12_spec :
    padOne 85 (mulRow DData V4PLD2Data 12) =
      (rectangularize 58 85 V4PLD3Data).getD 12 [] := by
  apply padOne_mulRow_eq_of_coefficients 85 DData V4PLD2Data 12
    ((rectangularize 58 85 V4PLD3Data).getD 12 [])
  · decide
  · have hTargetSupport : (V4PLD3Data.getD 12 []).length ≤ 85 := by
      decide
    rw [getD_rectangularize 58 85 V4PLD3Data 12 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD3Row12_coefficients

private theorem v4PLD3Row13Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD2Data 13 j =
      ((rectangularize 58 85 V4PLD3Data).getD 13 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row13Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD2Data 13 j =
      ((rectangularize 58 85 V4PLD3Data).getD 13 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row13Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD2Data 13 j =
      ((rectangularize 58 85 V4PLD3Data).getD 13 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row13Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD2Data 13 j =
      ((rectangularize 58 85 V4PLD3Data).getD 13 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row13Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD2Data 13 j =
      ((rectangularize 58 85 V4PLD3Data).getD 13 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row13Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD2Data 13 j =
      ((rectangularize 58 85 V4PLD3Data).getD 13 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row13Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD2Data 13 j =
      ((rectangularize 58 85 V4PLD3Data).getD 13 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row13Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD2Data 13 j =
      ((rectangularize 58 85 V4PLD3Data).getD 13 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row13Coeffs80To84_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 85) :
    mulCoeffTwo DData V4PLD2Data 13 j =
      ((rectangularize 58 85 V4PLD3Data).getD 13 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl <;> decide

private theorem v4PLD3Row13_coefficients (j : ℕ) (hj : j < 85) :
    mulCoeffTwo DData V4PLD2Data 13 j =
      ((rectangularize 58 85 V4PLD3Data).getD 13 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD3Row13Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD3Row13Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD3Row13Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD3Row13Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD3Row13Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD3Row13Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD3Row13Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD3Row13Coeffs70To79_spec j (by omega) h80
  exact v4PLD3Row13Coeffs80To84_spec j (by omega) hj

private theorem v4PLD3Row13_spec :
    padOne 85 (mulRow DData V4PLD2Data 13) =
      (rectangularize 58 85 V4PLD3Data).getD 13 [] := by
  apply padOne_mulRow_eq_of_coefficients 85 DData V4PLD2Data 13
    ((rectangularize 58 85 V4PLD3Data).getD 13 [])
  · decide
  · have hTargetSupport : (V4PLD3Data.getD 13 []).length ≤ 85 := by
      decide
    rw [getD_rectangularize 58 85 V4PLD3Data 13 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD3Row13_coefficients

private theorem v4PLD3Row14Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD2Data 14 j =
      ((rectangularize 58 85 V4PLD3Data).getD 14 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row14Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD2Data 14 j =
      ((rectangularize 58 85 V4PLD3Data).getD 14 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row14Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD2Data 14 j =
      ((rectangularize 58 85 V4PLD3Data).getD 14 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row14Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD2Data 14 j =
      ((rectangularize 58 85 V4PLD3Data).getD 14 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row14Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD2Data 14 j =
      ((rectangularize 58 85 V4PLD3Data).getD 14 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row14Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD2Data 14 j =
      ((rectangularize 58 85 V4PLD3Data).getD 14 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row14Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD2Data 14 j =
      ((rectangularize 58 85 V4PLD3Data).getD 14 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row14Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD2Data 14 j =
      ((rectangularize 58 85 V4PLD3Data).getD 14 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row14Coeffs80To84_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 85) :
    mulCoeffTwo DData V4PLD2Data 14 j =
      ((rectangularize 58 85 V4PLD3Data).getD 14 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl <;> decide

private theorem v4PLD3Row14_coefficients (j : ℕ) (hj : j < 85) :
    mulCoeffTwo DData V4PLD2Data 14 j =
      ((rectangularize 58 85 V4PLD3Data).getD 14 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD3Row14Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD3Row14Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD3Row14Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD3Row14Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD3Row14Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD3Row14Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD3Row14Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD3Row14Coeffs70To79_spec j (by omega) h80
  exact v4PLD3Row14Coeffs80To84_spec j (by omega) hj

private theorem v4PLD3Row14_spec :
    padOne 85 (mulRow DData V4PLD2Data 14) =
      (rectangularize 58 85 V4PLD3Data).getD 14 [] := by
  apply padOne_mulRow_eq_of_coefficients 85 DData V4PLD2Data 14
    ((rectangularize 58 85 V4PLD3Data).getD 14 [])
  · decide
  · have hTargetSupport : (V4PLD3Data.getD 14 []).length ≤ 85 := by
      decide
    rw [getD_rectangularize 58 85 V4PLD3Data 14 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD3Row14_coefficients

private theorem v4PLD3Row15Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD2Data 15 j =
      ((rectangularize 58 85 V4PLD3Data).getD 15 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row15Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD2Data 15 j =
      ((rectangularize 58 85 V4PLD3Data).getD 15 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row15Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD2Data 15 j =
      ((rectangularize 58 85 V4PLD3Data).getD 15 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row15Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD2Data 15 j =
      ((rectangularize 58 85 V4PLD3Data).getD 15 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row15Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD2Data 15 j =
      ((rectangularize 58 85 V4PLD3Data).getD 15 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row15Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD2Data 15 j =
      ((rectangularize 58 85 V4PLD3Data).getD 15 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row15Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD2Data 15 j =
      ((rectangularize 58 85 V4PLD3Data).getD 15 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row15Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD2Data 15 j =
      ((rectangularize 58 85 V4PLD3Data).getD 15 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row15Coeffs80To84_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 85) :
    mulCoeffTwo DData V4PLD2Data 15 j =
      ((rectangularize 58 85 V4PLD3Data).getD 15 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl <;> decide

private theorem v4PLD3Row15_coefficients (j : ℕ) (hj : j < 85) :
    mulCoeffTwo DData V4PLD2Data 15 j =
      ((rectangularize 58 85 V4PLD3Data).getD 15 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD3Row15Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD3Row15Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD3Row15Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD3Row15Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD3Row15Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD3Row15Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD3Row15Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD3Row15Coeffs70To79_spec j (by omega) h80
  exact v4PLD3Row15Coeffs80To84_spec j (by omega) hj

private theorem v4PLD3Row15_spec :
    padOne 85 (mulRow DData V4PLD2Data 15) =
      (rectangularize 58 85 V4PLD3Data).getD 15 [] := by
  apply padOne_mulRow_eq_of_coefficients 85 DData V4PLD2Data 15
    ((rectangularize 58 85 V4PLD3Data).getD 15 [])
  · decide
  · have hTargetSupport : (V4PLD3Data.getD 15 []).length ≤ 85 := by
      decide
    rw [getD_rectangularize 58 85 V4PLD3Data 15 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD3Row15_coefficients

private theorem v4PLD3Row16Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD2Data 16 j =
      ((rectangularize 58 85 V4PLD3Data).getD 16 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row16Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD2Data 16 j =
      ((rectangularize 58 85 V4PLD3Data).getD 16 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row16Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD2Data 16 j =
      ((rectangularize 58 85 V4PLD3Data).getD 16 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row16Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD2Data 16 j =
      ((rectangularize 58 85 V4PLD3Data).getD 16 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row16Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD2Data 16 j =
      ((rectangularize 58 85 V4PLD3Data).getD 16 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row16Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD2Data 16 j =
      ((rectangularize 58 85 V4PLD3Data).getD 16 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row16Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD2Data 16 j =
      ((rectangularize 58 85 V4PLD3Data).getD 16 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row16Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD2Data 16 j =
      ((rectangularize 58 85 V4PLD3Data).getD 16 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row16Coeffs80To84_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 85) :
    mulCoeffTwo DData V4PLD2Data 16 j =
      ((rectangularize 58 85 V4PLD3Data).getD 16 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl <;> decide

private theorem v4PLD3Row16_coefficients (j : ℕ) (hj : j < 85) :
    mulCoeffTwo DData V4PLD2Data 16 j =
      ((rectangularize 58 85 V4PLD3Data).getD 16 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD3Row16Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD3Row16Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD3Row16Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD3Row16Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD3Row16Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD3Row16Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD3Row16Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD3Row16Coeffs70To79_spec j (by omega) h80
  exact v4PLD3Row16Coeffs80To84_spec j (by omega) hj

private theorem v4PLD3Row16_spec :
    padOne 85 (mulRow DData V4PLD2Data 16) =
      (rectangularize 58 85 V4PLD3Data).getD 16 [] := by
  apply padOne_mulRow_eq_of_coefficients 85 DData V4PLD2Data 16
    ((rectangularize 58 85 V4PLD3Data).getD 16 [])
  · decide
  · have hTargetSupport : (V4PLD3Data.getD 16 []).length ≤ 85 := by
      decide
    rw [getD_rectangularize 58 85 V4PLD3Data 16 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD3Row16_coefficients

private theorem v4PLD3Row17Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD2Data 17 j =
      ((rectangularize 58 85 V4PLD3Data).getD 17 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row17Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD2Data 17 j =
      ((rectangularize 58 85 V4PLD3Data).getD 17 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row17Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD2Data 17 j =
      ((rectangularize 58 85 V4PLD3Data).getD 17 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row17Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD2Data 17 j =
      ((rectangularize 58 85 V4PLD3Data).getD 17 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row17Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD2Data 17 j =
      ((rectangularize 58 85 V4PLD3Data).getD 17 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row17Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD2Data 17 j =
      ((rectangularize 58 85 V4PLD3Data).getD 17 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row17Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD2Data 17 j =
      ((rectangularize 58 85 V4PLD3Data).getD 17 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row17Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD2Data 17 j =
      ((rectangularize 58 85 V4PLD3Data).getD 17 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row17Coeffs80To84_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 85) :
    mulCoeffTwo DData V4PLD2Data 17 j =
      ((rectangularize 58 85 V4PLD3Data).getD 17 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl <;> decide

private theorem v4PLD3Row17_coefficients (j : ℕ) (hj : j < 85) :
    mulCoeffTwo DData V4PLD2Data 17 j =
      ((rectangularize 58 85 V4PLD3Data).getD 17 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD3Row17Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD3Row17Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD3Row17Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD3Row17Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD3Row17Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD3Row17Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD3Row17Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD3Row17Coeffs70To79_spec j (by omega) h80
  exact v4PLD3Row17Coeffs80To84_spec j (by omega) hj

private theorem v4PLD3Row17_spec :
    padOne 85 (mulRow DData V4PLD2Data 17) =
      (rectangularize 58 85 V4PLD3Data).getD 17 [] := by
  apply padOne_mulRow_eq_of_coefficients 85 DData V4PLD2Data 17
    ((rectangularize 58 85 V4PLD3Data).getD 17 [])
  · decide
  · have hTargetSupport : (V4PLD3Data.getD 17 []).length ≤ 85 := by
      decide
    rw [getD_rectangularize 58 85 V4PLD3Data 17 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD3Row17_coefficients

private theorem v4PLD3Row18Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD2Data 18 j =
      ((rectangularize 58 85 V4PLD3Data).getD 18 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row18Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD2Data 18 j =
      ((rectangularize 58 85 V4PLD3Data).getD 18 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row18Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD2Data 18 j =
      ((rectangularize 58 85 V4PLD3Data).getD 18 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row18Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD2Data 18 j =
      ((rectangularize 58 85 V4PLD3Data).getD 18 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row18Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD2Data 18 j =
      ((rectangularize 58 85 V4PLD3Data).getD 18 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row18Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD2Data 18 j =
      ((rectangularize 58 85 V4PLD3Data).getD 18 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row18Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD2Data 18 j =
      ((rectangularize 58 85 V4PLD3Data).getD 18 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row18Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD2Data 18 j =
      ((rectangularize 58 85 V4PLD3Data).getD 18 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row18Coeffs80To84_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 85) :
    mulCoeffTwo DData V4PLD2Data 18 j =
      ((rectangularize 58 85 V4PLD3Data).getD 18 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl <;> decide

private theorem v4PLD3Row18_coefficients (j : ℕ) (hj : j < 85) :
    mulCoeffTwo DData V4PLD2Data 18 j =
      ((rectangularize 58 85 V4PLD3Data).getD 18 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD3Row18Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD3Row18Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD3Row18Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD3Row18Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD3Row18Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD3Row18Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD3Row18Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD3Row18Coeffs70To79_spec j (by omega) h80
  exact v4PLD3Row18Coeffs80To84_spec j (by omega) hj

private theorem v4PLD3Row18_spec :
    padOne 85 (mulRow DData V4PLD2Data 18) =
      (rectangularize 58 85 V4PLD3Data).getD 18 [] := by
  apply padOne_mulRow_eq_of_coefficients 85 DData V4PLD2Data 18
    ((rectangularize 58 85 V4PLD3Data).getD 18 [])
  · decide
  · have hTargetSupport : (V4PLD3Data.getD 18 []).length ≤ 85 := by
      decide
    rw [getD_rectangularize 58 85 V4PLD3Data 18 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD3Row18_coefficients

private theorem v4PLD3Row19Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD2Data 19 j =
      ((rectangularize 58 85 V4PLD3Data).getD 19 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row19Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD2Data 19 j =
      ((rectangularize 58 85 V4PLD3Data).getD 19 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row19Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD2Data 19 j =
      ((rectangularize 58 85 V4PLD3Data).getD 19 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row19Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD2Data 19 j =
      ((rectangularize 58 85 V4PLD3Data).getD 19 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row19Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD2Data 19 j =
      ((rectangularize 58 85 V4PLD3Data).getD 19 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row19Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD2Data 19 j =
      ((rectangularize 58 85 V4PLD3Data).getD 19 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row19Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD2Data 19 j =
      ((rectangularize 58 85 V4PLD3Data).getD 19 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row19Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD2Data 19 j =
      ((rectangularize 58 85 V4PLD3Data).getD 19 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row19Coeffs80To84_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 85) :
    mulCoeffTwo DData V4PLD2Data 19 j =
      ((rectangularize 58 85 V4PLD3Data).getD 19 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl <;> decide

private theorem v4PLD3Row19_coefficients (j : ℕ) (hj : j < 85) :
    mulCoeffTwo DData V4PLD2Data 19 j =
      ((rectangularize 58 85 V4PLD3Data).getD 19 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD3Row19Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD3Row19Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD3Row19Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD3Row19Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD3Row19Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD3Row19Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD3Row19Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD3Row19Coeffs70To79_spec j (by omega) h80
  exact v4PLD3Row19Coeffs80To84_spec j (by omega) hj

private theorem v4PLD3Row19_spec :
    padOne 85 (mulRow DData V4PLD2Data 19) =
      (rectangularize 58 85 V4PLD3Data).getD 19 [] := by
  apply padOne_mulRow_eq_of_coefficients 85 DData V4PLD2Data 19
    ((rectangularize 58 85 V4PLD3Data).getD 19 [])
  · decide
  · have hTargetSupport : (V4PLD3Data.getD 19 []).length ≤ 85 := by
      decide
    rw [getD_rectangularize 58 85 V4PLD3Data 19 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD3Row19_coefficients

private theorem v4PLD3Row20Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD2Data 20 j =
      ((rectangularize 58 85 V4PLD3Data).getD 20 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row20Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD2Data 20 j =
      ((rectangularize 58 85 V4PLD3Data).getD 20 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row20Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD2Data 20 j =
      ((rectangularize 58 85 V4PLD3Data).getD 20 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row20Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD2Data 20 j =
      ((rectangularize 58 85 V4PLD3Data).getD 20 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row20Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD2Data 20 j =
      ((rectangularize 58 85 V4PLD3Data).getD 20 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row20Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD2Data 20 j =
      ((rectangularize 58 85 V4PLD3Data).getD 20 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row20Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD2Data 20 j =
      ((rectangularize 58 85 V4PLD3Data).getD 20 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row20Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD2Data 20 j =
      ((rectangularize 58 85 V4PLD3Data).getD 20 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row20Coeffs80To84_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 85) :
    mulCoeffTwo DData V4PLD2Data 20 j =
      ((rectangularize 58 85 V4PLD3Data).getD 20 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl <;> decide

private theorem v4PLD3Row20_coefficients (j : ℕ) (hj : j < 85) :
    mulCoeffTwo DData V4PLD2Data 20 j =
      ((rectangularize 58 85 V4PLD3Data).getD 20 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD3Row20Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD3Row20Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD3Row20Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD3Row20Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD3Row20Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD3Row20Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD3Row20Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD3Row20Coeffs70To79_spec j (by omega) h80
  exact v4PLD3Row20Coeffs80To84_spec j (by omega) hj

private theorem v4PLD3Row20_spec :
    padOne 85 (mulRow DData V4PLD2Data 20) =
      (rectangularize 58 85 V4PLD3Data).getD 20 [] := by
  apply padOne_mulRow_eq_of_coefficients 85 DData V4PLD2Data 20
    ((rectangularize 58 85 V4PLD3Data).getD 20 [])
  · decide
  · have hTargetSupport : (V4PLD3Data.getD 20 []).length ≤ 85 := by
      decide
    rw [getD_rectangularize 58 85 V4PLD3Data 20 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD3Row20_coefficients

private theorem v4PLD3Row21Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD2Data 21 j =
      ((rectangularize 58 85 V4PLD3Data).getD 21 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row21Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD2Data 21 j =
      ((rectangularize 58 85 V4PLD3Data).getD 21 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row21Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD2Data 21 j =
      ((rectangularize 58 85 V4PLD3Data).getD 21 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row21Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD2Data 21 j =
      ((rectangularize 58 85 V4PLD3Data).getD 21 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row21Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD2Data 21 j =
      ((rectangularize 58 85 V4PLD3Data).getD 21 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row21Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD2Data 21 j =
      ((rectangularize 58 85 V4PLD3Data).getD 21 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row21Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD2Data 21 j =
      ((rectangularize 58 85 V4PLD3Data).getD 21 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row21Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD2Data 21 j =
      ((rectangularize 58 85 V4PLD3Data).getD 21 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row21Coeffs80To84_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 85) :
    mulCoeffTwo DData V4PLD2Data 21 j =
      ((rectangularize 58 85 V4PLD3Data).getD 21 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl <;> decide

private theorem v4PLD3Row21_coefficients (j : ℕ) (hj : j < 85) :
    mulCoeffTwo DData V4PLD2Data 21 j =
      ((rectangularize 58 85 V4PLD3Data).getD 21 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD3Row21Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD3Row21Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD3Row21Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD3Row21Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD3Row21Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD3Row21Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD3Row21Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD3Row21Coeffs70To79_spec j (by omega) h80
  exact v4PLD3Row21Coeffs80To84_spec j (by omega) hj

private theorem v4PLD3Row21_spec :
    padOne 85 (mulRow DData V4PLD2Data 21) =
      (rectangularize 58 85 V4PLD3Data).getD 21 [] := by
  apply padOne_mulRow_eq_of_coefficients 85 DData V4PLD2Data 21
    ((rectangularize 58 85 V4PLD3Data).getD 21 [])
  · decide
  · have hTargetSupport : (V4PLD3Data.getD 21 []).length ≤ 85 := by
      decide
    rw [getD_rectangularize 58 85 V4PLD3Data 21 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD3Row21_coefficients

private theorem v4PLD3Row22Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD2Data 22 j =
      ((rectangularize 58 85 V4PLD3Data).getD 22 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row22Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD2Data 22 j =
      ((rectangularize 58 85 V4PLD3Data).getD 22 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row22Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD2Data 22 j =
      ((rectangularize 58 85 V4PLD3Data).getD 22 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row22Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD2Data 22 j =
      ((rectangularize 58 85 V4PLD3Data).getD 22 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row22Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD2Data 22 j =
      ((rectangularize 58 85 V4PLD3Data).getD 22 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row22Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD2Data 22 j =
      ((rectangularize 58 85 V4PLD3Data).getD 22 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row22Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD2Data 22 j =
      ((rectangularize 58 85 V4PLD3Data).getD 22 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row22Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD2Data 22 j =
      ((rectangularize 58 85 V4PLD3Data).getD 22 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row22Coeffs80To84_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 85) :
    mulCoeffTwo DData V4PLD2Data 22 j =
      ((rectangularize 58 85 V4PLD3Data).getD 22 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl <;> decide

private theorem v4PLD3Row22_coefficients (j : ℕ) (hj : j < 85) :
    mulCoeffTwo DData V4PLD2Data 22 j =
      ((rectangularize 58 85 V4PLD3Data).getD 22 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD3Row22Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD3Row22Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD3Row22Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD3Row22Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD3Row22Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD3Row22Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD3Row22Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD3Row22Coeffs70To79_spec j (by omega) h80
  exact v4PLD3Row22Coeffs80To84_spec j (by omega) hj

private theorem v4PLD3Row22_spec :
    padOne 85 (mulRow DData V4PLD2Data 22) =
      (rectangularize 58 85 V4PLD3Data).getD 22 [] := by
  apply padOne_mulRow_eq_of_coefficients 85 DData V4PLD2Data 22
    ((rectangularize 58 85 V4PLD3Data).getD 22 [])
  · decide
  · have hTargetSupport : (V4PLD3Data.getD 22 []).length ≤ 85 := by
      decide
    rw [getD_rectangularize 58 85 V4PLD3Data 22 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD3Row22_coefficients

private theorem v4PLD3Row23Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD2Data 23 j =
      ((rectangularize 58 85 V4PLD3Data).getD 23 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row23Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD2Data 23 j =
      ((rectangularize 58 85 V4PLD3Data).getD 23 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row23Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD2Data 23 j =
      ((rectangularize 58 85 V4PLD3Data).getD 23 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row23Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD2Data 23 j =
      ((rectangularize 58 85 V4PLD3Data).getD 23 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row23Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD2Data 23 j =
      ((rectangularize 58 85 V4PLD3Data).getD 23 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row23Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD2Data 23 j =
      ((rectangularize 58 85 V4PLD3Data).getD 23 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row23Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD2Data 23 j =
      ((rectangularize 58 85 V4PLD3Data).getD 23 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row23Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD2Data 23 j =
      ((rectangularize 58 85 V4PLD3Data).getD 23 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row23Coeffs80To84_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 85) :
    mulCoeffTwo DData V4PLD2Data 23 j =
      ((rectangularize 58 85 V4PLD3Data).getD 23 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl <;> decide

private theorem v4PLD3Row23_coefficients (j : ℕ) (hj : j < 85) :
    mulCoeffTwo DData V4PLD2Data 23 j =
      ((rectangularize 58 85 V4PLD3Data).getD 23 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD3Row23Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD3Row23Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD3Row23Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD3Row23Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD3Row23Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD3Row23Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD3Row23Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD3Row23Coeffs70To79_spec j (by omega) h80
  exact v4PLD3Row23Coeffs80To84_spec j (by omega) hj

private theorem v4PLD3Row23_spec :
    padOne 85 (mulRow DData V4PLD2Data 23) =
      (rectangularize 58 85 V4PLD3Data).getD 23 [] := by
  apply padOne_mulRow_eq_of_coefficients 85 DData V4PLD2Data 23
    ((rectangularize 58 85 V4PLD3Data).getD 23 [])
  · decide
  · have hTargetSupport : (V4PLD3Data.getD 23 []).length ≤ 85 := by
      decide
    rw [getD_rectangularize 58 85 V4PLD3Data 23 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD3Row23_coefficients

private theorem v4PLD3Row24Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD2Data 24 j =
      ((rectangularize 58 85 V4PLD3Data).getD 24 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row24Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD2Data 24 j =
      ((rectangularize 58 85 V4PLD3Data).getD 24 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row24Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD2Data 24 j =
      ((rectangularize 58 85 V4PLD3Data).getD 24 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row24Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD2Data 24 j =
      ((rectangularize 58 85 V4PLD3Data).getD 24 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row24Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD2Data 24 j =
      ((rectangularize 58 85 V4PLD3Data).getD 24 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row24Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD2Data 24 j =
      ((rectangularize 58 85 V4PLD3Data).getD 24 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row24Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD2Data 24 j =
      ((rectangularize 58 85 V4PLD3Data).getD 24 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row24Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD2Data 24 j =
      ((rectangularize 58 85 V4PLD3Data).getD 24 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row24Coeffs80To84_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 85) :
    mulCoeffTwo DData V4PLD2Data 24 j =
      ((rectangularize 58 85 V4PLD3Data).getD 24 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl <;> decide

private theorem v4PLD3Row24_coefficients (j : ℕ) (hj : j < 85) :
    mulCoeffTwo DData V4PLD2Data 24 j =
      ((rectangularize 58 85 V4PLD3Data).getD 24 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD3Row24Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD3Row24Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD3Row24Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD3Row24Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD3Row24Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD3Row24Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD3Row24Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD3Row24Coeffs70To79_spec j (by omega) h80
  exact v4PLD3Row24Coeffs80To84_spec j (by omega) hj

private theorem v4PLD3Row24_spec :
    padOne 85 (mulRow DData V4PLD2Data 24) =
      (rectangularize 58 85 V4PLD3Data).getD 24 [] := by
  apply padOne_mulRow_eq_of_coefficients 85 DData V4PLD2Data 24
    ((rectangularize 58 85 V4PLD3Data).getD 24 [])
  · decide
  · have hTargetSupport : (V4PLD3Data.getD 24 []).length ≤ 85 := by
      decide
    rw [getD_rectangularize 58 85 V4PLD3Data 24 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD3Row24_coefficients

private theorem v4PLD3Row25Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD2Data 25 j =
      ((rectangularize 58 85 V4PLD3Data).getD 25 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row25Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD2Data 25 j =
      ((rectangularize 58 85 V4PLD3Data).getD 25 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row25Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD2Data 25 j =
      ((rectangularize 58 85 V4PLD3Data).getD 25 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row25Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD2Data 25 j =
      ((rectangularize 58 85 V4PLD3Data).getD 25 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row25Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD2Data 25 j =
      ((rectangularize 58 85 V4PLD3Data).getD 25 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row25Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD2Data 25 j =
      ((rectangularize 58 85 V4PLD3Data).getD 25 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row25Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD2Data 25 j =
      ((rectangularize 58 85 V4PLD3Data).getD 25 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row25Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD2Data 25 j =
      ((rectangularize 58 85 V4PLD3Data).getD 25 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row25Coeffs80To84_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 85) :
    mulCoeffTwo DData V4PLD2Data 25 j =
      ((rectangularize 58 85 V4PLD3Data).getD 25 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl <;> decide

private theorem v4PLD3Row25_coefficients (j : ℕ) (hj : j < 85) :
    mulCoeffTwo DData V4PLD2Data 25 j =
      ((rectangularize 58 85 V4PLD3Data).getD 25 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD3Row25Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD3Row25Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD3Row25Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD3Row25Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD3Row25Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD3Row25Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD3Row25Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD3Row25Coeffs70To79_spec j (by omega) h80
  exact v4PLD3Row25Coeffs80To84_spec j (by omega) hj

private theorem v4PLD3Row25_spec :
    padOne 85 (mulRow DData V4PLD2Data 25) =
      (rectangularize 58 85 V4PLD3Data).getD 25 [] := by
  apply padOne_mulRow_eq_of_coefficients 85 DData V4PLD2Data 25
    ((rectangularize 58 85 V4PLD3Data).getD 25 [])
  · decide
  · have hTargetSupport : (V4PLD3Data.getD 25 []).length ≤ 85 := by
      decide
    rw [getD_rectangularize 58 85 V4PLD3Data 25 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD3Row25_coefficients

private theorem v4PLD3Row26Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD2Data 26 j =
      ((rectangularize 58 85 V4PLD3Data).getD 26 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row26Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD2Data 26 j =
      ((rectangularize 58 85 V4PLD3Data).getD 26 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row26Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD2Data 26 j =
      ((rectangularize 58 85 V4PLD3Data).getD 26 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row26Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD2Data 26 j =
      ((rectangularize 58 85 V4PLD3Data).getD 26 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row26Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD2Data 26 j =
      ((rectangularize 58 85 V4PLD3Data).getD 26 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row26Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD2Data 26 j =
      ((rectangularize 58 85 V4PLD3Data).getD 26 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row26Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD2Data 26 j =
      ((rectangularize 58 85 V4PLD3Data).getD 26 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row26Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD2Data 26 j =
      ((rectangularize 58 85 V4PLD3Data).getD 26 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row26Coeffs80To84_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 85) :
    mulCoeffTwo DData V4PLD2Data 26 j =
      ((rectangularize 58 85 V4PLD3Data).getD 26 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl <;> decide

private theorem v4PLD3Row26_coefficients (j : ℕ) (hj : j < 85) :
    mulCoeffTwo DData V4PLD2Data 26 j =
      ((rectangularize 58 85 V4PLD3Data).getD 26 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD3Row26Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD3Row26Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD3Row26Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD3Row26Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD3Row26Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD3Row26Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD3Row26Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD3Row26Coeffs70To79_spec j (by omega) h80
  exact v4PLD3Row26Coeffs80To84_spec j (by omega) hj

private theorem v4PLD3Row26_spec :
    padOne 85 (mulRow DData V4PLD2Data 26) =
      (rectangularize 58 85 V4PLD3Data).getD 26 [] := by
  apply padOne_mulRow_eq_of_coefficients 85 DData V4PLD2Data 26
    ((rectangularize 58 85 V4PLD3Data).getD 26 [])
  · decide
  · have hTargetSupport : (V4PLD3Data.getD 26 []).length ≤ 85 := by
      decide
    rw [getD_rectangularize 58 85 V4PLD3Data 26 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD3Row26_coefficients

private theorem v4PLD3Row27Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD2Data 27 j =
      ((rectangularize 58 85 V4PLD3Data).getD 27 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row27Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD2Data 27 j =
      ((rectangularize 58 85 V4PLD3Data).getD 27 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row27Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD2Data 27 j =
      ((rectangularize 58 85 V4PLD3Data).getD 27 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row27Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD2Data 27 j =
      ((rectangularize 58 85 V4PLD3Data).getD 27 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row27Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD2Data 27 j =
      ((rectangularize 58 85 V4PLD3Data).getD 27 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row27Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD2Data 27 j =
      ((rectangularize 58 85 V4PLD3Data).getD 27 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row27Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD2Data 27 j =
      ((rectangularize 58 85 V4PLD3Data).getD 27 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row27Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD2Data 27 j =
      ((rectangularize 58 85 V4PLD3Data).getD 27 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row27Coeffs80To84_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 85) :
    mulCoeffTwo DData V4PLD2Data 27 j =
      ((rectangularize 58 85 V4PLD3Data).getD 27 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl <;> decide

private theorem v4PLD3Row27_coefficients (j : ℕ) (hj : j < 85) :
    mulCoeffTwo DData V4PLD2Data 27 j =
      ((rectangularize 58 85 V4PLD3Data).getD 27 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD3Row27Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD3Row27Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD3Row27Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD3Row27Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD3Row27Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD3Row27Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD3Row27Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD3Row27Coeffs70To79_spec j (by omega) h80
  exact v4PLD3Row27Coeffs80To84_spec j (by omega) hj

private theorem v4PLD3Row27_spec :
    padOne 85 (mulRow DData V4PLD2Data 27) =
      (rectangularize 58 85 V4PLD3Data).getD 27 [] := by
  apply padOne_mulRow_eq_of_coefficients 85 DData V4PLD2Data 27
    ((rectangularize 58 85 V4PLD3Data).getD 27 [])
  · decide
  · have hTargetSupport : (V4PLD3Data.getD 27 []).length ≤ 85 := by
      decide
    rw [getD_rectangularize 58 85 V4PLD3Data 27 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD3Row27_coefficients

private theorem v4PLD3Row28Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD2Data 28 j =
      ((rectangularize 58 85 V4PLD3Data).getD 28 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row28Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD2Data 28 j =
      ((rectangularize 58 85 V4PLD3Data).getD 28 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row28Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD2Data 28 j =
      ((rectangularize 58 85 V4PLD3Data).getD 28 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row28Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD2Data 28 j =
      ((rectangularize 58 85 V4PLD3Data).getD 28 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row28Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD2Data 28 j =
      ((rectangularize 58 85 V4PLD3Data).getD 28 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row28Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD2Data 28 j =
      ((rectangularize 58 85 V4PLD3Data).getD 28 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row28Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD2Data 28 j =
      ((rectangularize 58 85 V4PLD3Data).getD 28 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row28Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD2Data 28 j =
      ((rectangularize 58 85 V4PLD3Data).getD 28 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row28Coeffs80To84_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 85) :
    mulCoeffTwo DData V4PLD2Data 28 j =
      ((rectangularize 58 85 V4PLD3Data).getD 28 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl <;> decide

private theorem v4PLD3Row28_coefficients (j : ℕ) (hj : j < 85) :
    mulCoeffTwo DData V4PLD2Data 28 j =
      ((rectangularize 58 85 V4PLD3Data).getD 28 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD3Row28Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD3Row28Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD3Row28Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD3Row28Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD3Row28Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD3Row28Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD3Row28Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD3Row28Coeffs70To79_spec j (by omega) h80
  exact v4PLD3Row28Coeffs80To84_spec j (by omega) hj

private theorem v4PLD3Row28_spec :
    padOne 85 (mulRow DData V4PLD2Data 28) =
      (rectangularize 58 85 V4PLD3Data).getD 28 [] := by
  apply padOne_mulRow_eq_of_coefficients 85 DData V4PLD2Data 28
    ((rectangularize 58 85 V4PLD3Data).getD 28 [])
  · decide
  · have hTargetSupport : (V4PLD3Data.getD 28 []).length ≤ 85 := by
      decide
    rw [getD_rectangularize 58 85 V4PLD3Data 28 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD3Row28_coefficients

private theorem v4PLD3Row29Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD2Data 29 j =
      ((rectangularize 58 85 V4PLD3Data).getD 29 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row29Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD2Data 29 j =
      ((rectangularize 58 85 V4PLD3Data).getD 29 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row29Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD2Data 29 j =
      ((rectangularize 58 85 V4PLD3Data).getD 29 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row29Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD2Data 29 j =
      ((rectangularize 58 85 V4PLD3Data).getD 29 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row29Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD2Data 29 j =
      ((rectangularize 58 85 V4PLD3Data).getD 29 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row29Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD2Data 29 j =
      ((rectangularize 58 85 V4PLD3Data).getD 29 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row29Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD2Data 29 j =
      ((rectangularize 58 85 V4PLD3Data).getD 29 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row29Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD2Data 29 j =
      ((rectangularize 58 85 V4PLD3Data).getD 29 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row29Coeffs80To84_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 85) :
    mulCoeffTwo DData V4PLD2Data 29 j =
      ((rectangularize 58 85 V4PLD3Data).getD 29 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl <;> decide

private theorem v4PLD3Row29_coefficients (j : ℕ) (hj : j < 85) :
    mulCoeffTwo DData V4PLD2Data 29 j =
      ((rectangularize 58 85 V4PLD3Data).getD 29 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD3Row29Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD3Row29Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD3Row29Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD3Row29Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD3Row29Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD3Row29Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD3Row29Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD3Row29Coeffs70To79_spec j (by omega) h80
  exact v4PLD3Row29Coeffs80To84_spec j (by omega) hj

private theorem v4PLD3Row29_spec :
    padOne 85 (mulRow DData V4PLD2Data 29) =
      (rectangularize 58 85 V4PLD3Data).getD 29 [] := by
  apply padOne_mulRow_eq_of_coefficients 85 DData V4PLD2Data 29
    ((rectangularize 58 85 V4PLD3Data).getD 29 [])
  · decide
  · have hTargetSupport : (V4PLD3Data.getD 29 []).length ≤ 85 := by
      decide
    rw [getD_rectangularize 58 85 V4PLD3Data 29 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD3Row29_coefficients

private theorem v4PLD3Row30Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD2Data 30 j =
      ((rectangularize 58 85 V4PLD3Data).getD 30 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row30Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD2Data 30 j =
      ((rectangularize 58 85 V4PLD3Data).getD 30 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row30Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD2Data 30 j =
      ((rectangularize 58 85 V4PLD3Data).getD 30 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row30Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD2Data 30 j =
      ((rectangularize 58 85 V4PLD3Data).getD 30 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row30Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD2Data 30 j =
      ((rectangularize 58 85 V4PLD3Data).getD 30 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row30Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD2Data 30 j =
      ((rectangularize 58 85 V4PLD3Data).getD 30 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row30Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD2Data 30 j =
      ((rectangularize 58 85 V4PLD3Data).getD 30 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row30Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD2Data 30 j =
      ((rectangularize 58 85 V4PLD3Data).getD 30 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row30Coeffs80To84_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 85) :
    mulCoeffTwo DData V4PLD2Data 30 j =
      ((rectangularize 58 85 V4PLD3Data).getD 30 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl <;> decide

private theorem v4PLD3Row30_coefficients (j : ℕ) (hj : j < 85) :
    mulCoeffTwo DData V4PLD2Data 30 j =
      ((rectangularize 58 85 V4PLD3Data).getD 30 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD3Row30Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD3Row30Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD3Row30Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD3Row30Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD3Row30Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD3Row30Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD3Row30Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD3Row30Coeffs70To79_spec j (by omega) h80
  exact v4PLD3Row30Coeffs80To84_spec j (by omega) hj

private theorem v4PLD3Row30_spec :
    padOne 85 (mulRow DData V4PLD2Data 30) =
      (rectangularize 58 85 V4PLD3Data).getD 30 [] := by
  apply padOne_mulRow_eq_of_coefficients 85 DData V4PLD2Data 30
    ((rectangularize 58 85 V4PLD3Data).getD 30 [])
  · decide
  · have hTargetSupport : (V4PLD3Data.getD 30 []).length ≤ 85 := by
      decide
    rw [getD_rectangularize 58 85 V4PLD3Data 30 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD3Row30_coefficients

private theorem v4PLD3Row31Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD2Data 31 j =
      ((rectangularize 58 85 V4PLD3Data).getD 31 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row31Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD2Data 31 j =
      ((rectangularize 58 85 V4PLD3Data).getD 31 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row31Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD2Data 31 j =
      ((rectangularize 58 85 V4PLD3Data).getD 31 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row31Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD2Data 31 j =
      ((rectangularize 58 85 V4PLD3Data).getD 31 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row31Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD2Data 31 j =
      ((rectangularize 58 85 V4PLD3Data).getD 31 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row31Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD2Data 31 j =
      ((rectangularize 58 85 V4PLD3Data).getD 31 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row31Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD2Data 31 j =
      ((rectangularize 58 85 V4PLD3Data).getD 31 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row31Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD2Data 31 j =
      ((rectangularize 58 85 V4PLD3Data).getD 31 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row31Coeffs80To84_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 85) :
    mulCoeffTwo DData V4PLD2Data 31 j =
      ((rectangularize 58 85 V4PLD3Data).getD 31 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl <;> decide

private theorem v4PLD3Row31_coefficients (j : ℕ) (hj : j < 85) :
    mulCoeffTwo DData V4PLD2Data 31 j =
      ((rectangularize 58 85 V4PLD3Data).getD 31 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD3Row31Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD3Row31Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD3Row31Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD3Row31Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD3Row31Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD3Row31Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD3Row31Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD3Row31Coeffs70To79_spec j (by omega) h80
  exact v4PLD3Row31Coeffs80To84_spec j (by omega) hj

private theorem v4PLD3Row31_spec :
    padOne 85 (mulRow DData V4PLD2Data 31) =
      (rectangularize 58 85 V4PLD3Data).getD 31 [] := by
  apply padOne_mulRow_eq_of_coefficients 85 DData V4PLD2Data 31
    ((rectangularize 58 85 V4PLD3Data).getD 31 [])
  · decide
  · have hTargetSupport : (V4PLD3Data.getD 31 []).length ≤ 85 := by
      decide
    rw [getD_rectangularize 58 85 V4PLD3Data 31 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD3Row31_coefficients

private theorem v4PLD3Row32Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD2Data 32 j =
      ((rectangularize 58 85 V4PLD3Data).getD 32 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row32Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD2Data 32 j =
      ((rectangularize 58 85 V4PLD3Data).getD 32 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row32Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD2Data 32 j =
      ((rectangularize 58 85 V4PLD3Data).getD 32 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row32Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD2Data 32 j =
      ((rectangularize 58 85 V4PLD3Data).getD 32 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row32Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD2Data 32 j =
      ((rectangularize 58 85 V4PLD3Data).getD 32 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row32Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD2Data 32 j =
      ((rectangularize 58 85 V4PLD3Data).getD 32 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row32Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD2Data 32 j =
      ((rectangularize 58 85 V4PLD3Data).getD 32 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row32Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD2Data 32 j =
      ((rectangularize 58 85 V4PLD3Data).getD 32 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row32Coeffs80To84_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 85) :
    mulCoeffTwo DData V4PLD2Data 32 j =
      ((rectangularize 58 85 V4PLD3Data).getD 32 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl <;> decide

private theorem v4PLD3Row32_coefficients (j : ℕ) (hj : j < 85) :
    mulCoeffTwo DData V4PLD2Data 32 j =
      ((rectangularize 58 85 V4PLD3Data).getD 32 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD3Row32Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD3Row32Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD3Row32Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD3Row32Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD3Row32Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD3Row32Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD3Row32Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD3Row32Coeffs70To79_spec j (by omega) h80
  exact v4PLD3Row32Coeffs80To84_spec j (by omega) hj

private theorem v4PLD3Row32_spec :
    padOne 85 (mulRow DData V4PLD2Data 32) =
      (rectangularize 58 85 V4PLD3Data).getD 32 [] := by
  apply padOne_mulRow_eq_of_coefficients 85 DData V4PLD2Data 32
    ((rectangularize 58 85 V4PLD3Data).getD 32 [])
  · decide
  · have hTargetSupport : (V4PLD3Data.getD 32 []).length ≤ 85 := by
      decide
    rw [getD_rectangularize 58 85 V4PLD3Data 32 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD3Row32_coefficients

private theorem v4PLD3Row33Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD2Data 33 j =
      ((rectangularize 58 85 V4PLD3Data).getD 33 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row33Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD2Data 33 j =
      ((rectangularize 58 85 V4PLD3Data).getD 33 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row33Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD2Data 33 j =
      ((rectangularize 58 85 V4PLD3Data).getD 33 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row33Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD2Data 33 j =
      ((rectangularize 58 85 V4PLD3Data).getD 33 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row33Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD2Data 33 j =
      ((rectangularize 58 85 V4PLD3Data).getD 33 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row33Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD2Data 33 j =
      ((rectangularize 58 85 V4PLD3Data).getD 33 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row33Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD2Data 33 j =
      ((rectangularize 58 85 V4PLD3Data).getD 33 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row33Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD2Data 33 j =
      ((rectangularize 58 85 V4PLD3Data).getD 33 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row33Coeffs80To84_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 85) :
    mulCoeffTwo DData V4PLD2Data 33 j =
      ((rectangularize 58 85 V4PLD3Data).getD 33 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl <;> decide

private theorem v4PLD3Row33_coefficients (j : ℕ) (hj : j < 85) :
    mulCoeffTwo DData V4PLD2Data 33 j =
      ((rectangularize 58 85 V4PLD3Data).getD 33 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD3Row33Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD3Row33Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD3Row33Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD3Row33Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD3Row33Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD3Row33Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD3Row33Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD3Row33Coeffs70To79_spec j (by omega) h80
  exact v4PLD3Row33Coeffs80To84_spec j (by omega) hj

private theorem v4PLD3Row33_spec :
    padOne 85 (mulRow DData V4PLD2Data 33) =
      (rectangularize 58 85 V4PLD3Data).getD 33 [] := by
  apply padOne_mulRow_eq_of_coefficients 85 DData V4PLD2Data 33
    ((rectangularize 58 85 V4PLD3Data).getD 33 [])
  · decide
  · have hTargetSupport : (V4PLD3Data.getD 33 []).length ≤ 85 := by
      decide
    rw [getD_rectangularize 58 85 V4PLD3Data 33 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD3Row33_coefficients

private theorem v4PLD3Row34Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD2Data 34 j =
      ((rectangularize 58 85 V4PLD3Data).getD 34 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row34Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD2Data 34 j =
      ((rectangularize 58 85 V4PLD3Data).getD 34 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row34Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD2Data 34 j =
      ((rectangularize 58 85 V4PLD3Data).getD 34 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row34Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD2Data 34 j =
      ((rectangularize 58 85 V4PLD3Data).getD 34 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row34Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD2Data 34 j =
      ((rectangularize 58 85 V4PLD3Data).getD 34 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row34Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD2Data 34 j =
      ((rectangularize 58 85 V4PLD3Data).getD 34 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row34Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD2Data 34 j =
      ((rectangularize 58 85 V4PLD3Data).getD 34 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row34Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD2Data 34 j =
      ((rectangularize 58 85 V4PLD3Data).getD 34 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row34Coeffs80To84_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 85) :
    mulCoeffTwo DData V4PLD2Data 34 j =
      ((rectangularize 58 85 V4PLD3Data).getD 34 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl <;> decide

private theorem v4PLD3Row34_coefficients (j : ℕ) (hj : j < 85) :
    mulCoeffTwo DData V4PLD2Data 34 j =
      ((rectangularize 58 85 V4PLD3Data).getD 34 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD3Row34Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD3Row34Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD3Row34Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD3Row34Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD3Row34Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD3Row34Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD3Row34Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD3Row34Coeffs70To79_spec j (by omega) h80
  exact v4PLD3Row34Coeffs80To84_spec j (by omega) hj

private theorem v4PLD3Row34_spec :
    padOne 85 (mulRow DData V4PLD2Data 34) =
      (rectangularize 58 85 V4PLD3Data).getD 34 [] := by
  apply padOne_mulRow_eq_of_coefficients 85 DData V4PLD2Data 34
    ((rectangularize 58 85 V4PLD3Data).getD 34 [])
  · decide
  · have hTargetSupport : (V4PLD3Data.getD 34 []).length ≤ 85 := by
      decide
    rw [getD_rectangularize 58 85 V4PLD3Data 34 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD3Row34_coefficients

private theorem v4PLD3Row35Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD2Data 35 j =
      ((rectangularize 58 85 V4PLD3Data).getD 35 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row35Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD2Data 35 j =
      ((rectangularize 58 85 V4PLD3Data).getD 35 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row35Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD2Data 35 j =
      ((rectangularize 58 85 V4PLD3Data).getD 35 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row35Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD2Data 35 j =
      ((rectangularize 58 85 V4PLD3Data).getD 35 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row35Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD2Data 35 j =
      ((rectangularize 58 85 V4PLD3Data).getD 35 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row35Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD2Data 35 j =
      ((rectangularize 58 85 V4PLD3Data).getD 35 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row35Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD2Data 35 j =
      ((rectangularize 58 85 V4PLD3Data).getD 35 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row35Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD2Data 35 j =
      ((rectangularize 58 85 V4PLD3Data).getD 35 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row35Coeffs80To84_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 85) :
    mulCoeffTwo DData V4PLD2Data 35 j =
      ((rectangularize 58 85 V4PLD3Data).getD 35 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl <;> decide

private theorem v4PLD3Row35_coefficients (j : ℕ) (hj : j < 85) :
    mulCoeffTwo DData V4PLD2Data 35 j =
      ((rectangularize 58 85 V4PLD3Data).getD 35 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD3Row35Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD3Row35Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD3Row35Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD3Row35Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD3Row35Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD3Row35Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD3Row35Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD3Row35Coeffs70To79_spec j (by omega) h80
  exact v4PLD3Row35Coeffs80To84_spec j (by omega) hj

private theorem v4PLD3Row35_spec :
    padOne 85 (mulRow DData V4PLD2Data 35) =
      (rectangularize 58 85 V4PLD3Data).getD 35 [] := by
  apply padOne_mulRow_eq_of_coefficients 85 DData V4PLD2Data 35
    ((rectangularize 58 85 V4PLD3Data).getD 35 [])
  · decide
  · have hTargetSupport : (V4PLD3Data.getD 35 []).length ≤ 85 := by
      decide
    rw [getD_rectangularize 58 85 V4PLD3Data 35 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD3Row35_coefficients

private theorem v4PLD3Row36Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD2Data 36 j =
      ((rectangularize 58 85 V4PLD3Data).getD 36 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row36Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD2Data 36 j =
      ((rectangularize 58 85 V4PLD3Data).getD 36 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row36Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD2Data 36 j =
      ((rectangularize 58 85 V4PLD3Data).getD 36 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row36Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD2Data 36 j =
      ((rectangularize 58 85 V4PLD3Data).getD 36 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row36Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD2Data 36 j =
      ((rectangularize 58 85 V4PLD3Data).getD 36 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row36Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD2Data 36 j =
      ((rectangularize 58 85 V4PLD3Data).getD 36 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row36Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD2Data 36 j =
      ((rectangularize 58 85 V4PLD3Data).getD 36 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row36Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD2Data 36 j =
      ((rectangularize 58 85 V4PLD3Data).getD 36 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row36Coeffs80To84_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 85) :
    mulCoeffTwo DData V4PLD2Data 36 j =
      ((rectangularize 58 85 V4PLD3Data).getD 36 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl <;> decide

private theorem v4PLD3Row36_coefficients (j : ℕ) (hj : j < 85) :
    mulCoeffTwo DData V4PLD2Data 36 j =
      ((rectangularize 58 85 V4PLD3Data).getD 36 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD3Row36Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD3Row36Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD3Row36Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD3Row36Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD3Row36Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD3Row36Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD3Row36Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD3Row36Coeffs70To79_spec j (by omega) h80
  exact v4PLD3Row36Coeffs80To84_spec j (by omega) hj

private theorem v4PLD3Row36_spec :
    padOne 85 (mulRow DData V4PLD2Data 36) =
      (rectangularize 58 85 V4PLD3Data).getD 36 [] := by
  apply padOne_mulRow_eq_of_coefficients 85 DData V4PLD2Data 36
    ((rectangularize 58 85 V4PLD3Data).getD 36 [])
  · decide
  · have hTargetSupport : (V4PLD3Data.getD 36 []).length ≤ 85 := by
      decide
    rw [getD_rectangularize 58 85 V4PLD3Data 36 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD3Row36_coefficients

private theorem v4PLD3Row37Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD2Data 37 j =
      ((rectangularize 58 85 V4PLD3Data).getD 37 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row37Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD2Data 37 j =
      ((rectangularize 58 85 V4PLD3Data).getD 37 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row37Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD2Data 37 j =
      ((rectangularize 58 85 V4PLD3Data).getD 37 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row37Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD2Data 37 j =
      ((rectangularize 58 85 V4PLD3Data).getD 37 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row37Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD2Data 37 j =
      ((rectangularize 58 85 V4PLD3Data).getD 37 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row37Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD2Data 37 j =
      ((rectangularize 58 85 V4PLD3Data).getD 37 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row37Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD2Data 37 j =
      ((rectangularize 58 85 V4PLD3Data).getD 37 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row37Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD2Data 37 j =
      ((rectangularize 58 85 V4PLD3Data).getD 37 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row37Coeffs80To84_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 85) :
    mulCoeffTwo DData V4PLD2Data 37 j =
      ((rectangularize 58 85 V4PLD3Data).getD 37 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl <;> decide

private theorem v4PLD3Row37_coefficients (j : ℕ) (hj : j < 85) :
    mulCoeffTwo DData V4PLD2Data 37 j =
      ((rectangularize 58 85 V4PLD3Data).getD 37 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD3Row37Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD3Row37Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD3Row37Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD3Row37Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD3Row37Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD3Row37Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD3Row37Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD3Row37Coeffs70To79_spec j (by omega) h80
  exact v4PLD3Row37Coeffs80To84_spec j (by omega) hj

private theorem v4PLD3Row37_spec :
    padOne 85 (mulRow DData V4PLD2Data 37) =
      (rectangularize 58 85 V4PLD3Data).getD 37 [] := by
  apply padOne_mulRow_eq_of_coefficients 85 DData V4PLD2Data 37
    ((rectangularize 58 85 V4PLD3Data).getD 37 [])
  · decide
  · have hTargetSupport : (V4PLD3Data.getD 37 []).length ≤ 85 := by
      decide
    rw [getD_rectangularize 58 85 V4PLD3Data 37 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD3Row37_coefficients

private theorem v4PLD3Row38Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD2Data 38 j =
      ((rectangularize 58 85 V4PLD3Data).getD 38 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row38Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD2Data 38 j =
      ((rectangularize 58 85 V4PLD3Data).getD 38 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row38Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD2Data 38 j =
      ((rectangularize 58 85 V4PLD3Data).getD 38 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row38Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD2Data 38 j =
      ((rectangularize 58 85 V4PLD3Data).getD 38 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row38Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD2Data 38 j =
      ((rectangularize 58 85 V4PLD3Data).getD 38 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row38Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD2Data 38 j =
      ((rectangularize 58 85 V4PLD3Data).getD 38 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row38Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD2Data 38 j =
      ((rectangularize 58 85 V4PLD3Data).getD 38 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row38Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD2Data 38 j =
      ((rectangularize 58 85 V4PLD3Data).getD 38 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row38Coeffs80To84_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 85) :
    mulCoeffTwo DData V4PLD2Data 38 j =
      ((rectangularize 58 85 V4PLD3Data).getD 38 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl <;> decide

private theorem v4PLD3Row38_coefficients (j : ℕ) (hj : j < 85) :
    mulCoeffTwo DData V4PLD2Data 38 j =
      ((rectangularize 58 85 V4PLD3Data).getD 38 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD3Row38Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD3Row38Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD3Row38Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD3Row38Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD3Row38Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD3Row38Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD3Row38Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD3Row38Coeffs70To79_spec j (by omega) h80
  exact v4PLD3Row38Coeffs80To84_spec j (by omega) hj

private theorem v4PLD3Row38_spec :
    padOne 85 (mulRow DData V4PLD2Data 38) =
      (rectangularize 58 85 V4PLD3Data).getD 38 [] := by
  apply padOne_mulRow_eq_of_coefficients 85 DData V4PLD2Data 38
    ((rectangularize 58 85 V4PLD3Data).getD 38 [])
  · decide
  · have hTargetSupport : (V4PLD3Data.getD 38 []).length ≤ 85 := by
      decide
    rw [getD_rectangularize 58 85 V4PLD3Data 38 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD3Row38_coefficients

private theorem v4PLD3Row39Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD2Data 39 j =
      ((rectangularize 58 85 V4PLD3Data).getD 39 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row39Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD2Data 39 j =
      ((rectangularize 58 85 V4PLD3Data).getD 39 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row39Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD2Data 39 j =
      ((rectangularize 58 85 V4PLD3Data).getD 39 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row39Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD2Data 39 j =
      ((rectangularize 58 85 V4PLD3Data).getD 39 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row39Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD2Data 39 j =
      ((rectangularize 58 85 V4PLD3Data).getD 39 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row39Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD2Data 39 j =
      ((rectangularize 58 85 V4PLD3Data).getD 39 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row39Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD2Data 39 j =
      ((rectangularize 58 85 V4PLD3Data).getD 39 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row39Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD2Data 39 j =
      ((rectangularize 58 85 V4PLD3Data).getD 39 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row39Coeffs80To84_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 85) :
    mulCoeffTwo DData V4PLD2Data 39 j =
      ((rectangularize 58 85 V4PLD3Data).getD 39 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl <;> decide

private theorem v4PLD3Row39_coefficients (j : ℕ) (hj : j < 85) :
    mulCoeffTwo DData V4PLD2Data 39 j =
      ((rectangularize 58 85 V4PLD3Data).getD 39 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD3Row39Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD3Row39Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD3Row39Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD3Row39Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD3Row39Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD3Row39Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD3Row39Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD3Row39Coeffs70To79_spec j (by omega) h80
  exact v4PLD3Row39Coeffs80To84_spec j (by omega) hj

private theorem v4PLD3Row39_spec :
    padOne 85 (mulRow DData V4PLD2Data 39) =
      (rectangularize 58 85 V4PLD3Data).getD 39 [] := by
  apply padOne_mulRow_eq_of_coefficients 85 DData V4PLD2Data 39
    ((rectangularize 58 85 V4PLD3Data).getD 39 [])
  · decide
  · have hTargetSupport : (V4PLD3Data.getD 39 []).length ≤ 85 := by
      decide
    rw [getD_rectangularize 58 85 V4PLD3Data 39 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD3Row39_coefficients

private theorem v4PLD3Row40Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD2Data 40 j =
      ((rectangularize 58 85 V4PLD3Data).getD 40 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row40Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD2Data 40 j =
      ((rectangularize 58 85 V4PLD3Data).getD 40 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row40Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD2Data 40 j =
      ((rectangularize 58 85 V4PLD3Data).getD 40 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row40Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD2Data 40 j =
      ((rectangularize 58 85 V4PLD3Data).getD 40 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row40Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD2Data 40 j =
      ((rectangularize 58 85 V4PLD3Data).getD 40 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row40Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD2Data 40 j =
      ((rectangularize 58 85 V4PLD3Data).getD 40 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row40Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD2Data 40 j =
      ((rectangularize 58 85 V4PLD3Data).getD 40 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row40Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD2Data 40 j =
      ((rectangularize 58 85 V4PLD3Data).getD 40 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row40Coeffs80To84_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 85) :
    mulCoeffTwo DData V4PLD2Data 40 j =
      ((rectangularize 58 85 V4PLD3Data).getD 40 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl <;> decide

private theorem v4PLD3Row40_coefficients (j : ℕ) (hj : j < 85) :
    mulCoeffTwo DData V4PLD2Data 40 j =
      ((rectangularize 58 85 V4PLD3Data).getD 40 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD3Row40Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD3Row40Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD3Row40Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD3Row40Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD3Row40Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD3Row40Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD3Row40Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD3Row40Coeffs70To79_spec j (by omega) h80
  exact v4PLD3Row40Coeffs80To84_spec j (by omega) hj

private theorem v4PLD3Row40_spec :
    padOne 85 (mulRow DData V4PLD2Data 40) =
      (rectangularize 58 85 V4PLD3Data).getD 40 [] := by
  apply padOne_mulRow_eq_of_coefficients 85 DData V4PLD2Data 40
    ((rectangularize 58 85 V4PLD3Data).getD 40 [])
  · decide
  · have hTargetSupport : (V4PLD3Data.getD 40 []).length ≤ 85 := by
      decide
    rw [getD_rectangularize 58 85 V4PLD3Data 40 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD3Row40_coefficients

private theorem v4PLD3Row41Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD2Data 41 j =
      ((rectangularize 58 85 V4PLD3Data).getD 41 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row41Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD2Data 41 j =
      ((rectangularize 58 85 V4PLD3Data).getD 41 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row41Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD2Data 41 j =
      ((rectangularize 58 85 V4PLD3Data).getD 41 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row41Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD2Data 41 j =
      ((rectangularize 58 85 V4PLD3Data).getD 41 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row41Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD2Data 41 j =
      ((rectangularize 58 85 V4PLD3Data).getD 41 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row41Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD2Data 41 j =
      ((rectangularize 58 85 V4PLD3Data).getD 41 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row41Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD2Data 41 j =
      ((rectangularize 58 85 V4PLD3Data).getD 41 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row41Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD2Data 41 j =
      ((rectangularize 58 85 V4PLD3Data).getD 41 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row41Coeffs80To84_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 85) :
    mulCoeffTwo DData V4PLD2Data 41 j =
      ((rectangularize 58 85 V4PLD3Data).getD 41 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl <;> decide

private theorem v4PLD3Row41_coefficients (j : ℕ) (hj : j < 85) :
    mulCoeffTwo DData V4PLD2Data 41 j =
      ((rectangularize 58 85 V4PLD3Data).getD 41 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD3Row41Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD3Row41Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD3Row41Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD3Row41Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD3Row41Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD3Row41Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD3Row41Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD3Row41Coeffs70To79_spec j (by omega) h80
  exact v4PLD3Row41Coeffs80To84_spec j (by omega) hj

private theorem v4PLD3Row41_spec :
    padOne 85 (mulRow DData V4PLD2Data 41) =
      (rectangularize 58 85 V4PLD3Data).getD 41 [] := by
  apply padOne_mulRow_eq_of_coefficients 85 DData V4PLD2Data 41
    ((rectangularize 58 85 V4PLD3Data).getD 41 [])
  · decide
  · have hTargetSupport : (V4PLD3Data.getD 41 []).length ≤ 85 := by
      decide
    rw [getD_rectangularize 58 85 V4PLD3Data 41 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD3Row41_coefficients

private theorem v4PLD3Row42Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD2Data 42 j =
      ((rectangularize 58 85 V4PLD3Data).getD 42 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row42Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD2Data 42 j =
      ((rectangularize 58 85 V4PLD3Data).getD 42 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row42Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD2Data 42 j =
      ((rectangularize 58 85 V4PLD3Data).getD 42 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row42Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD2Data 42 j =
      ((rectangularize 58 85 V4PLD3Data).getD 42 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row42Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD2Data 42 j =
      ((rectangularize 58 85 V4PLD3Data).getD 42 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row42Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD2Data 42 j =
      ((rectangularize 58 85 V4PLD3Data).getD 42 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row42Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD2Data 42 j =
      ((rectangularize 58 85 V4PLD3Data).getD 42 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row42Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD2Data 42 j =
      ((rectangularize 58 85 V4PLD3Data).getD 42 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row42Coeffs80To84_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 85) :
    mulCoeffTwo DData V4PLD2Data 42 j =
      ((rectangularize 58 85 V4PLD3Data).getD 42 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl <;> decide

private theorem v4PLD3Row42_coefficients (j : ℕ) (hj : j < 85) :
    mulCoeffTwo DData V4PLD2Data 42 j =
      ((rectangularize 58 85 V4PLD3Data).getD 42 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD3Row42Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD3Row42Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD3Row42Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD3Row42Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD3Row42Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD3Row42Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD3Row42Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD3Row42Coeffs70To79_spec j (by omega) h80
  exact v4PLD3Row42Coeffs80To84_spec j (by omega) hj

private theorem v4PLD3Row42_spec :
    padOne 85 (mulRow DData V4PLD2Data 42) =
      (rectangularize 58 85 V4PLD3Data).getD 42 [] := by
  apply padOne_mulRow_eq_of_coefficients 85 DData V4PLD2Data 42
    ((rectangularize 58 85 V4PLD3Data).getD 42 [])
  · decide
  · have hTargetSupport : (V4PLD3Data.getD 42 []).length ≤ 85 := by
      decide
    rw [getD_rectangularize 58 85 V4PLD3Data 42 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD3Row42_coefficients

private theorem v4PLD3Row43Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD2Data 43 j =
      ((rectangularize 58 85 V4PLD3Data).getD 43 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row43Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD2Data 43 j =
      ((rectangularize 58 85 V4PLD3Data).getD 43 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row43Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD2Data 43 j =
      ((rectangularize 58 85 V4PLD3Data).getD 43 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row43Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD2Data 43 j =
      ((rectangularize 58 85 V4PLD3Data).getD 43 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row43Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD2Data 43 j =
      ((rectangularize 58 85 V4PLD3Data).getD 43 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row43Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD2Data 43 j =
      ((rectangularize 58 85 V4PLD3Data).getD 43 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row43Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD2Data 43 j =
      ((rectangularize 58 85 V4PLD3Data).getD 43 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row43Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD2Data 43 j =
      ((rectangularize 58 85 V4PLD3Data).getD 43 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row43Coeffs80To84_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 85) :
    mulCoeffTwo DData V4PLD2Data 43 j =
      ((rectangularize 58 85 V4PLD3Data).getD 43 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl <;> decide

private theorem v4PLD3Row43_coefficients (j : ℕ) (hj : j < 85) :
    mulCoeffTwo DData V4PLD2Data 43 j =
      ((rectangularize 58 85 V4PLD3Data).getD 43 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD3Row43Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD3Row43Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD3Row43Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD3Row43Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD3Row43Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD3Row43Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD3Row43Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD3Row43Coeffs70To79_spec j (by omega) h80
  exact v4PLD3Row43Coeffs80To84_spec j (by omega) hj

private theorem v4PLD3Row43_spec :
    padOne 85 (mulRow DData V4PLD2Data 43) =
      (rectangularize 58 85 V4PLD3Data).getD 43 [] := by
  apply padOne_mulRow_eq_of_coefficients 85 DData V4PLD2Data 43
    ((rectangularize 58 85 V4PLD3Data).getD 43 [])
  · decide
  · have hTargetSupport : (V4PLD3Data.getD 43 []).length ≤ 85 := by
      decide
    rw [getD_rectangularize 58 85 V4PLD3Data 43 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD3Row43_coefficients

private theorem v4PLD3Row44Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo DData V4PLD2Data 44 j =
      ((rectangularize 58 85 V4PLD3Data).getD 44 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row44Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo DData V4PLD2Data 44 j =
      ((rectangularize 58 85 V4PLD3Data).getD 44 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row44Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo DData V4PLD2Data 44 j =
      ((rectangularize 58 85 V4PLD3Data).getD 44 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row44Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo DData V4PLD2Data 44 j =
      ((rectangularize 58 85 V4PLD3Data).getD 44 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row44Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo DData V4PLD2Data 44 j =
      ((rectangularize 58 85 V4PLD3Data).getD 44 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row44Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo DData V4PLD2Data 44 j =
      ((rectangularize 58 85 V4PLD3Data).getD 44 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row44Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo DData V4PLD2Data 44 j =
      ((rectangularize 58 85 V4PLD3Data).getD 44 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row44Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo DData V4PLD2Data 44 j =
      ((rectangularize 58 85 V4PLD3Data).getD 44 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLD3Row44Coeffs80To84_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 85) :
    mulCoeffTwo DData V4PLD2Data 44 j =
      ((rectangularize 58 85 V4PLD3Data).getD 44 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl <;> decide

private theorem v4PLD3Row44_coefficients (j : ℕ) (hj : j < 85) :
    mulCoeffTwo DData V4PLD2Data 44 j =
      ((rectangularize 58 85 V4PLD3Data).getD 44 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLD3Row44Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLD3Row44Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLD3Row44Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLD3Row44Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLD3Row44Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLD3Row44Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLD3Row44Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLD3Row44Coeffs70To79_spec j (by omega) h80
  exact v4PLD3Row44Coeffs80To84_spec j (by omega) hj

private theorem v4PLD3Row44_spec :
    padOne 85 (mulRow DData V4PLD2Data 44) =
      (rectangularize 58 85 V4PLD3Data).getD 44 [] := by
  apply padOne_mulRow_eq_of_coefficients 85 DData V4PLD2Data 44
    ((rectangularize 58 85 V4PLD3Data).getD 44 [])
  · decide
  · have hTargetSupport : (V4PLD3Data.getD 44 []).length ≤ 85 := by
      decide
    rw [getD_rectangularize 58 85 V4PLD3Data 44 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLD3Row44_coefficients

private theorem v4PLD3Row45_spec :
    padOne 85 (mulRow DData V4PLD2Data 45) =
      (rectangularize 58 85 V4PLD3Data).getD 45 [] := by
  decide

private theorem v4PLD3Row46_spec :
    padOne 85 (mulRow DData V4PLD2Data 46) =
      (rectangularize 58 85 V4PLD3Data).getD 46 [] := by
  decide

private theorem v4PLD3Row47_spec :
    padOne 85 (mulRow DData V4PLD2Data 47) =
      (rectangularize 58 85 V4PLD3Data).getD 47 [] := by
  decide

private theorem v4PLD3Row48_spec :
    padOne 85 (mulRow DData V4PLD2Data 48) =
      (rectangularize 58 85 V4PLD3Data).getD 48 [] := by
  decide

private theorem v4PLD3Row49_spec :
    padOne 85 (mulRow DData V4PLD2Data 49) =
      (rectangularize 58 85 V4PLD3Data).getD 49 [] := by
  decide

private theorem v4PLD3Row50_spec :
    padOne 85 (mulRow DData V4PLD2Data 50) =
      (rectangularize 58 85 V4PLD3Data).getD 50 [] := by
  decide

private theorem v4PLD3Row51_spec :
    padOne 85 (mulRow DData V4PLD2Data 51) =
      (rectangularize 58 85 V4PLD3Data).getD 51 [] := by
  decide

private theorem v4PLD3Row52_spec :
    padOne 85 (mulRow DData V4PLD2Data 52) =
      (rectangularize 58 85 V4PLD3Data).getD 52 [] := by
  decide

private theorem v4PLD3Row53_spec :
    padOne 85 (mulRow DData V4PLD2Data 53) =
      (rectangularize 58 85 V4PLD3Data).getD 53 [] := by
  decide

private theorem v4PLD3Row54_spec :
    padOne 85 (mulRow DData V4PLD2Data 54) =
      (rectangularize 58 85 V4PLD3Data).getD 54 [] := by
  decide

private theorem v4PLD3Row55_spec :
    padOne 85 (mulRow DData V4PLD2Data 55) =
      (rectangularize 58 85 V4PLD3Data).getD 55 [] := by
  decide

private theorem v4PLD3Row56_spec :
    padOne 85 (mulRow DData V4PLD2Data 56) =
      (rectangularize 58 85 V4PLD3Data).getD 56 [] := by
  decide

private theorem v4PLD3Row57_spec :
    padOne 85 (mulRow DData V4PLD2Data 57) =
      (rectangularize 58 85 V4PLD3Data).getD 57 [] := by
  decide

private theorem v4PLD3Rows_spec (n : ℕ) (hn : n < 58) :
    padOne 85 (mulRow DData V4PLD2Data n) =
      (rectangularize 58 85 V4PLD3Data).getD n [] := by
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
  · exact v4PLD3Row0_spec
  · exact v4PLD3Row1_spec
  · exact v4PLD3Row2_spec
  · exact v4PLD3Row3_spec
  · exact v4PLD3Row4_spec
  · exact v4PLD3Row5_spec
  · exact v4PLD3Row6_spec
  · exact v4PLD3Row7_spec
  · exact v4PLD3Row8_spec
  · exact v4PLD3Row9_spec
  · exact v4PLD3Row10_spec
  · exact v4PLD3Row11_spec
  · exact v4PLD3Row12_spec
  · exact v4PLD3Row13_spec
  · exact v4PLD3Row14_spec
  · exact v4PLD3Row15_spec
  · exact v4PLD3Row16_spec
  · exact v4PLD3Row17_spec
  · exact v4PLD3Row18_spec
  · exact v4PLD3Row19_spec
  · exact v4PLD3Row20_spec
  · exact v4PLD3Row21_spec
  · exact v4PLD3Row22_spec
  · exact v4PLD3Row23_spec
  · exact v4PLD3Row24_spec
  · exact v4PLD3Row25_spec
  · exact v4PLD3Row26_spec
  · exact v4PLD3Row27_spec
  · exact v4PLD3Row28_spec
  · exact v4PLD3Row29_spec
  · exact v4PLD3Row30_spec
  · exact v4PLD3Row31_spec
  · exact v4PLD3Row32_spec
  · exact v4PLD3Row33_spec
  · exact v4PLD3Row34_spec
  · exact v4PLD3Row35_spec
  · exact v4PLD3Row36_spec
  · exact v4PLD3Row37_spec
  · exact v4PLD3Row38_spec
  · exact v4PLD3Row39_spec
  · exact v4PLD3Row40_spec
  · exact v4PLD3Row41_spec
  · exact v4PLD3Row42_spec
  · exact v4PLD3Row43_spec
  · exact v4PLD3Row44_spec
  · exact v4PLD3Row45_spec
  · exact v4PLD3Row46_spec
  · exact v4PLD3Row47_spec
  · exact v4PLD3Row48_spec
  · exact v4PLD3Row49_spec
  · exact v4PLD3Row50_spec
  · exact v4PLD3Row51_spec
  · exact v4PLD3Row52_spec
  · exact v4PLD3Row53_spec
  · exact v4PLD3Row54_spec
  · exact v4PLD3Row55_spec
  · exact v4PLD3Row56_spec
  · exact v4PLD3Row57_spec

private theorem v4PLD3Left_length :
    (rectangularize 58 85 (Two.mul DData V4PLD2Data)).length = 58 := by
  decide

private theorem v4PLD3Right_length :
    (rectangularize 58 85 V4PLD3Data).length = 58 := by
  decide

-- Exact bidegree bound (57, 84); no row or column is discarded.
private theorem v4PLD3Data_spec :
    rectangularize 58 85 (Two.mul DData V4PLD2Data) =
      rectangularize 58 85 V4PLD3Data := by
  apply List.ext_getElem (v4PLD3Left_length.trans v4PLD3Right_length.symm)
  intro n hn _
  rw [List.getElem_eq_getD [], List.getElem_eq_getD []]
  rw [v4PLD3Left_length] at hn
  rw [getD_rectangularize 58 85 (Two.mul DData V4PLD2Data) n hn,
    ← mulRow_eq_getD]
  exact v4PLD3Rows_spec n hn

private theorem v4PLLRow0_spec :
    padOne 89 (mulRow LData V4PLD3Data 0) =
      (rectangularize 61 89 V4PLLData).getD 0 [] := by
  decide

private theorem v4PLLRow1_spec :
    padOne 89 (mulRow LData V4PLD3Data 1) =
      (rectangularize 61 89 V4PLLData).getD 1 [] := by
  decide

private theorem v4PLLRow2_spec :
    padOne 89 (mulRow LData V4PLD3Data 2) =
      (rectangularize 61 89 V4PLLData).getD 2 [] := by
  decide

private theorem v4PLLRow3_spec :
    padOne 89 (mulRow LData V4PLD3Data 3) =
      (rectangularize 61 89 V4PLLData).getD 3 [] := by
  decide

private theorem v4PLLRow4_spec :
    padOne 89 (mulRow LData V4PLD3Data 4) =
      (rectangularize 61 89 V4PLLData).getD 4 [] := by
  decide

private theorem v4PLLRow5_spec :
    padOne 89 (mulRow LData V4PLD3Data 5) =
      (rectangularize 61 89 V4PLLData).getD 5 [] := by
  decide

private theorem v4PLLRow6_spec :
    padOne 89 (mulRow LData V4PLD3Data 6) =
      (rectangularize 61 89 V4PLLData).getD 6 [] := by
  decide

private theorem v4PLLRow7_spec :
    padOne 89 (mulRow LData V4PLD3Data 7) =
      (rectangularize 61 89 V4PLLData).getD 7 [] := by
  decide

private theorem v4PLLRow8Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo LData V4PLD3Data 8 j =
      ((rectangularize 61 89 V4PLLData).getD 8 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow8Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo LData V4PLD3Data 8 j =
      ((rectangularize 61 89 V4PLLData).getD 8 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow8Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo LData V4PLD3Data 8 j =
      ((rectangularize 61 89 V4PLLData).getD 8 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow8Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo LData V4PLD3Data 8 j =
      ((rectangularize 61 89 V4PLLData).getD 8 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow8Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo LData V4PLD3Data 8 j =
      ((rectangularize 61 89 V4PLLData).getD 8 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow8Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo LData V4PLD3Data 8 j =
      ((rectangularize 61 89 V4PLLData).getD 8 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow8Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo LData V4PLD3Data 8 j =
      ((rectangularize 61 89 V4PLLData).getD 8 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow8Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo LData V4PLD3Data 8 j =
      ((rectangularize 61 89 V4PLLData).getD 8 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow8Coeffs80To88_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 89) :
    mulCoeffTwo LData V4PLD3Data 8 j =
      ((rectangularize 61 89 V4PLLData).getD 8 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 ∨
    j = 85 ∨ j = 86 ∨ j = 87 ∨ j = 88 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLLRow8_coefficients (j : ℕ) (hj : j < 89) :
    mulCoeffTwo LData V4PLD3Data 8 j =
      ((rectangularize 61 89 V4PLLData).getD 8 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLLRow8Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLLRow8Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLLRow8Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLLRow8Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLLRow8Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLLRow8Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLLRow8Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLLRow8Coeffs70To79_spec j (by omega) h80
  exact v4PLLRow8Coeffs80To88_spec j (by omega) hj

private theorem v4PLLRow8_spec :
    padOne 89 (mulRow LData V4PLD3Data 8) =
      (rectangularize 61 89 V4PLLData).getD 8 [] := by
  apply padOne_mulRow_eq_of_coefficients 89 LData V4PLD3Data 8
    ((rectangularize 61 89 V4PLLData).getD 8 [])
  · decide
  · have hTargetSupport : (V4PLLData.getD 8 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4PLLData 8 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLLRow8_coefficients

private theorem v4PLLRow9Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo LData V4PLD3Data 9 j =
      ((rectangularize 61 89 V4PLLData).getD 9 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow9Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo LData V4PLD3Data 9 j =
      ((rectangularize 61 89 V4PLLData).getD 9 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow9Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo LData V4PLD3Data 9 j =
      ((rectangularize 61 89 V4PLLData).getD 9 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow9Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo LData V4PLD3Data 9 j =
      ((rectangularize 61 89 V4PLLData).getD 9 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow9Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo LData V4PLD3Data 9 j =
      ((rectangularize 61 89 V4PLLData).getD 9 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow9Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo LData V4PLD3Data 9 j =
      ((rectangularize 61 89 V4PLLData).getD 9 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow9Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo LData V4PLD3Data 9 j =
      ((rectangularize 61 89 V4PLLData).getD 9 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow9Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo LData V4PLD3Data 9 j =
      ((rectangularize 61 89 V4PLLData).getD 9 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow9Coeffs80To88_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 89) :
    mulCoeffTwo LData V4PLD3Data 9 j =
      ((rectangularize 61 89 V4PLLData).getD 9 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 ∨
    j = 85 ∨ j = 86 ∨ j = 87 ∨ j = 88 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLLRow9_coefficients (j : ℕ) (hj : j < 89) :
    mulCoeffTwo LData V4PLD3Data 9 j =
      ((rectangularize 61 89 V4PLLData).getD 9 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLLRow9Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLLRow9Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLLRow9Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLLRow9Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLLRow9Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLLRow9Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLLRow9Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLLRow9Coeffs70To79_spec j (by omega) h80
  exact v4PLLRow9Coeffs80To88_spec j (by omega) hj

private theorem v4PLLRow9_spec :
    padOne 89 (mulRow LData V4PLD3Data 9) =
      (rectangularize 61 89 V4PLLData).getD 9 [] := by
  apply padOne_mulRow_eq_of_coefficients 89 LData V4PLD3Data 9
    ((rectangularize 61 89 V4PLLData).getD 9 [])
  · decide
  · have hTargetSupport : (V4PLLData.getD 9 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4PLLData 9 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLLRow9_coefficients

private theorem v4PLLRow10Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo LData V4PLD3Data 10 j =
      ((rectangularize 61 89 V4PLLData).getD 10 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow10Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo LData V4PLD3Data 10 j =
      ((rectangularize 61 89 V4PLLData).getD 10 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow10Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo LData V4PLD3Data 10 j =
      ((rectangularize 61 89 V4PLLData).getD 10 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow10Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo LData V4PLD3Data 10 j =
      ((rectangularize 61 89 V4PLLData).getD 10 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow10Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo LData V4PLD3Data 10 j =
      ((rectangularize 61 89 V4PLLData).getD 10 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow10Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo LData V4PLD3Data 10 j =
      ((rectangularize 61 89 V4PLLData).getD 10 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow10Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo LData V4PLD3Data 10 j =
      ((rectangularize 61 89 V4PLLData).getD 10 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow10Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo LData V4PLD3Data 10 j =
      ((rectangularize 61 89 V4PLLData).getD 10 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow10Coeffs80To88_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 89) :
    mulCoeffTwo LData V4PLD3Data 10 j =
      ((rectangularize 61 89 V4PLLData).getD 10 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 ∨
    j = 85 ∨ j = 86 ∨ j = 87 ∨ j = 88 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLLRow10_coefficients (j : ℕ) (hj : j < 89) :
    mulCoeffTwo LData V4PLD3Data 10 j =
      ((rectangularize 61 89 V4PLLData).getD 10 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLLRow10Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLLRow10Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLLRow10Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLLRow10Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLLRow10Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLLRow10Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLLRow10Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLLRow10Coeffs70To79_spec j (by omega) h80
  exact v4PLLRow10Coeffs80To88_spec j (by omega) hj

private theorem v4PLLRow10_spec :
    padOne 89 (mulRow LData V4PLD3Data 10) =
      (rectangularize 61 89 V4PLLData).getD 10 [] := by
  apply padOne_mulRow_eq_of_coefficients 89 LData V4PLD3Data 10
    ((rectangularize 61 89 V4PLLData).getD 10 [])
  · decide
  · have hTargetSupport : (V4PLLData.getD 10 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4PLLData 10 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLLRow10_coefficients

private theorem v4PLLRow11Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo LData V4PLD3Data 11 j =
      ((rectangularize 61 89 V4PLLData).getD 11 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow11Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo LData V4PLD3Data 11 j =
      ((rectangularize 61 89 V4PLLData).getD 11 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow11Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo LData V4PLD3Data 11 j =
      ((rectangularize 61 89 V4PLLData).getD 11 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow11Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo LData V4PLD3Data 11 j =
      ((rectangularize 61 89 V4PLLData).getD 11 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow11Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo LData V4PLD3Data 11 j =
      ((rectangularize 61 89 V4PLLData).getD 11 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow11Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo LData V4PLD3Data 11 j =
      ((rectangularize 61 89 V4PLLData).getD 11 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow11Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo LData V4PLD3Data 11 j =
      ((rectangularize 61 89 V4PLLData).getD 11 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow11Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo LData V4PLD3Data 11 j =
      ((rectangularize 61 89 V4PLLData).getD 11 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow11Coeffs80To88_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 89) :
    mulCoeffTwo LData V4PLD3Data 11 j =
      ((rectangularize 61 89 V4PLLData).getD 11 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 ∨
    j = 85 ∨ j = 86 ∨ j = 87 ∨ j = 88 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLLRow11_coefficients (j : ℕ) (hj : j < 89) :
    mulCoeffTwo LData V4PLD3Data 11 j =
      ((rectangularize 61 89 V4PLLData).getD 11 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLLRow11Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLLRow11Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLLRow11Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLLRow11Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLLRow11Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLLRow11Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLLRow11Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLLRow11Coeffs70To79_spec j (by omega) h80
  exact v4PLLRow11Coeffs80To88_spec j (by omega) hj

private theorem v4PLLRow11_spec :
    padOne 89 (mulRow LData V4PLD3Data 11) =
      (rectangularize 61 89 V4PLLData).getD 11 [] := by
  apply padOne_mulRow_eq_of_coefficients 89 LData V4PLD3Data 11
    ((rectangularize 61 89 V4PLLData).getD 11 [])
  · decide
  · have hTargetSupport : (V4PLLData.getD 11 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4PLLData 11 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLLRow11_coefficients

private theorem v4PLLRow12Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo LData V4PLD3Data 12 j =
      ((rectangularize 61 89 V4PLLData).getD 12 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow12Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo LData V4PLD3Data 12 j =
      ((rectangularize 61 89 V4PLLData).getD 12 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow12Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo LData V4PLD3Data 12 j =
      ((rectangularize 61 89 V4PLLData).getD 12 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow12Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo LData V4PLD3Data 12 j =
      ((rectangularize 61 89 V4PLLData).getD 12 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow12Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo LData V4PLD3Data 12 j =
      ((rectangularize 61 89 V4PLLData).getD 12 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow12Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo LData V4PLD3Data 12 j =
      ((rectangularize 61 89 V4PLLData).getD 12 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow12Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo LData V4PLD3Data 12 j =
      ((rectangularize 61 89 V4PLLData).getD 12 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow12Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo LData V4PLD3Data 12 j =
      ((rectangularize 61 89 V4PLLData).getD 12 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow12Coeffs80To88_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 89) :
    mulCoeffTwo LData V4PLD3Data 12 j =
      ((rectangularize 61 89 V4PLLData).getD 12 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 ∨
    j = 85 ∨ j = 86 ∨ j = 87 ∨ j = 88 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLLRow12_coefficients (j : ℕ) (hj : j < 89) :
    mulCoeffTwo LData V4PLD3Data 12 j =
      ((rectangularize 61 89 V4PLLData).getD 12 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLLRow12Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLLRow12Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLLRow12Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLLRow12Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLLRow12Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLLRow12Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLLRow12Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLLRow12Coeffs70To79_spec j (by omega) h80
  exact v4PLLRow12Coeffs80To88_spec j (by omega) hj

private theorem v4PLLRow12_spec :
    padOne 89 (mulRow LData V4PLD3Data 12) =
      (rectangularize 61 89 V4PLLData).getD 12 [] := by
  apply padOne_mulRow_eq_of_coefficients 89 LData V4PLD3Data 12
    ((rectangularize 61 89 V4PLLData).getD 12 [])
  · decide
  · have hTargetSupport : (V4PLLData.getD 12 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4PLLData 12 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLLRow12_coefficients

private theorem v4PLLRow13Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo LData V4PLD3Data 13 j =
      ((rectangularize 61 89 V4PLLData).getD 13 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow13Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo LData V4PLD3Data 13 j =
      ((rectangularize 61 89 V4PLLData).getD 13 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow13Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo LData V4PLD3Data 13 j =
      ((rectangularize 61 89 V4PLLData).getD 13 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow13Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo LData V4PLD3Data 13 j =
      ((rectangularize 61 89 V4PLLData).getD 13 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow13Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo LData V4PLD3Data 13 j =
      ((rectangularize 61 89 V4PLLData).getD 13 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow13Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo LData V4PLD3Data 13 j =
      ((rectangularize 61 89 V4PLLData).getD 13 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow13Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo LData V4PLD3Data 13 j =
      ((rectangularize 61 89 V4PLLData).getD 13 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow13Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo LData V4PLD3Data 13 j =
      ((rectangularize 61 89 V4PLLData).getD 13 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow13Coeffs80To88_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 89) :
    mulCoeffTwo LData V4PLD3Data 13 j =
      ((rectangularize 61 89 V4PLLData).getD 13 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 ∨
    j = 85 ∨ j = 86 ∨ j = 87 ∨ j = 88 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLLRow13_coefficients (j : ℕ) (hj : j < 89) :
    mulCoeffTwo LData V4PLD3Data 13 j =
      ((rectangularize 61 89 V4PLLData).getD 13 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLLRow13Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLLRow13Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLLRow13Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLLRow13Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLLRow13Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLLRow13Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLLRow13Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLLRow13Coeffs70To79_spec j (by omega) h80
  exact v4PLLRow13Coeffs80To88_spec j (by omega) hj

private theorem v4PLLRow13_spec :
    padOne 89 (mulRow LData V4PLD3Data 13) =
      (rectangularize 61 89 V4PLLData).getD 13 [] := by
  apply padOne_mulRow_eq_of_coefficients 89 LData V4PLD3Data 13
    ((rectangularize 61 89 V4PLLData).getD 13 [])
  · decide
  · have hTargetSupport : (V4PLLData.getD 13 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4PLLData 13 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLLRow13_coefficients

private theorem v4PLLRow14Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo LData V4PLD3Data 14 j =
      ((rectangularize 61 89 V4PLLData).getD 14 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow14Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo LData V4PLD3Data 14 j =
      ((rectangularize 61 89 V4PLLData).getD 14 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow14Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo LData V4PLD3Data 14 j =
      ((rectangularize 61 89 V4PLLData).getD 14 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow14Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo LData V4PLD3Data 14 j =
      ((rectangularize 61 89 V4PLLData).getD 14 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow14Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo LData V4PLD3Data 14 j =
      ((rectangularize 61 89 V4PLLData).getD 14 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow14Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo LData V4PLD3Data 14 j =
      ((rectangularize 61 89 V4PLLData).getD 14 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow14Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo LData V4PLD3Data 14 j =
      ((rectangularize 61 89 V4PLLData).getD 14 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow14Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo LData V4PLD3Data 14 j =
      ((rectangularize 61 89 V4PLLData).getD 14 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow14Coeffs80To88_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 89) :
    mulCoeffTwo LData V4PLD3Data 14 j =
      ((rectangularize 61 89 V4PLLData).getD 14 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 ∨
    j = 85 ∨ j = 86 ∨ j = 87 ∨ j = 88 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLLRow14_coefficients (j : ℕ) (hj : j < 89) :
    mulCoeffTwo LData V4PLD3Data 14 j =
      ((rectangularize 61 89 V4PLLData).getD 14 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLLRow14Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLLRow14Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLLRow14Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLLRow14Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLLRow14Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLLRow14Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLLRow14Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLLRow14Coeffs70To79_spec j (by omega) h80
  exact v4PLLRow14Coeffs80To88_spec j (by omega) hj

private theorem v4PLLRow14_spec :
    padOne 89 (mulRow LData V4PLD3Data 14) =
      (rectangularize 61 89 V4PLLData).getD 14 [] := by
  apply padOne_mulRow_eq_of_coefficients 89 LData V4PLD3Data 14
    ((rectangularize 61 89 V4PLLData).getD 14 [])
  · decide
  · have hTargetSupport : (V4PLLData.getD 14 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4PLLData 14 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLLRow14_coefficients

private theorem v4PLLRow15Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo LData V4PLD3Data 15 j =
      ((rectangularize 61 89 V4PLLData).getD 15 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow15Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo LData V4PLD3Data 15 j =
      ((rectangularize 61 89 V4PLLData).getD 15 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow15Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo LData V4PLD3Data 15 j =
      ((rectangularize 61 89 V4PLLData).getD 15 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow15Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo LData V4PLD3Data 15 j =
      ((rectangularize 61 89 V4PLLData).getD 15 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow15Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo LData V4PLD3Data 15 j =
      ((rectangularize 61 89 V4PLLData).getD 15 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow15Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo LData V4PLD3Data 15 j =
      ((rectangularize 61 89 V4PLLData).getD 15 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow15Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo LData V4PLD3Data 15 j =
      ((rectangularize 61 89 V4PLLData).getD 15 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow15Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo LData V4PLD3Data 15 j =
      ((rectangularize 61 89 V4PLLData).getD 15 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow15Coeffs80To88_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 89) :
    mulCoeffTwo LData V4PLD3Data 15 j =
      ((rectangularize 61 89 V4PLLData).getD 15 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 ∨
    j = 85 ∨ j = 86 ∨ j = 87 ∨ j = 88 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLLRow15_coefficients (j : ℕ) (hj : j < 89) :
    mulCoeffTwo LData V4PLD3Data 15 j =
      ((rectangularize 61 89 V4PLLData).getD 15 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLLRow15Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLLRow15Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLLRow15Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLLRow15Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLLRow15Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLLRow15Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLLRow15Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLLRow15Coeffs70To79_spec j (by omega) h80
  exact v4PLLRow15Coeffs80To88_spec j (by omega) hj

private theorem v4PLLRow15_spec :
    padOne 89 (mulRow LData V4PLD3Data 15) =
      (rectangularize 61 89 V4PLLData).getD 15 [] := by
  apply padOne_mulRow_eq_of_coefficients 89 LData V4PLD3Data 15
    ((rectangularize 61 89 V4PLLData).getD 15 [])
  · decide
  · have hTargetSupport : (V4PLLData.getD 15 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4PLLData 15 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLLRow15_coefficients

private theorem v4PLLRow16Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo LData V4PLD3Data 16 j =
      ((rectangularize 61 89 V4PLLData).getD 16 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow16Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo LData V4PLD3Data 16 j =
      ((rectangularize 61 89 V4PLLData).getD 16 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow16Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo LData V4PLD3Data 16 j =
      ((rectangularize 61 89 V4PLLData).getD 16 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow16Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo LData V4PLD3Data 16 j =
      ((rectangularize 61 89 V4PLLData).getD 16 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow16Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo LData V4PLD3Data 16 j =
      ((rectangularize 61 89 V4PLLData).getD 16 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow16Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo LData V4PLD3Data 16 j =
      ((rectangularize 61 89 V4PLLData).getD 16 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow16Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo LData V4PLD3Data 16 j =
      ((rectangularize 61 89 V4PLLData).getD 16 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow16Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo LData V4PLD3Data 16 j =
      ((rectangularize 61 89 V4PLLData).getD 16 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow16Coeffs80To88_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 89) :
    mulCoeffTwo LData V4PLD3Data 16 j =
      ((rectangularize 61 89 V4PLLData).getD 16 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 ∨
    j = 85 ∨ j = 86 ∨ j = 87 ∨ j = 88 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLLRow16_coefficients (j : ℕ) (hj : j < 89) :
    mulCoeffTwo LData V4PLD3Data 16 j =
      ((rectangularize 61 89 V4PLLData).getD 16 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLLRow16Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLLRow16Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLLRow16Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLLRow16Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLLRow16Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLLRow16Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLLRow16Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLLRow16Coeffs70To79_spec j (by omega) h80
  exact v4PLLRow16Coeffs80To88_spec j (by omega) hj

private theorem v4PLLRow16_spec :
    padOne 89 (mulRow LData V4PLD3Data 16) =
      (rectangularize 61 89 V4PLLData).getD 16 [] := by
  apply padOne_mulRow_eq_of_coefficients 89 LData V4PLD3Data 16
    ((rectangularize 61 89 V4PLLData).getD 16 [])
  · decide
  · have hTargetSupport : (V4PLLData.getD 16 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4PLLData 16 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLLRow16_coefficients

private theorem v4PLLRow17Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo LData V4PLD3Data 17 j =
      ((rectangularize 61 89 V4PLLData).getD 17 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow17Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo LData V4PLD3Data 17 j =
      ((rectangularize 61 89 V4PLLData).getD 17 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow17Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo LData V4PLD3Data 17 j =
      ((rectangularize 61 89 V4PLLData).getD 17 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow17Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo LData V4PLD3Data 17 j =
      ((rectangularize 61 89 V4PLLData).getD 17 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow17Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo LData V4PLD3Data 17 j =
      ((rectangularize 61 89 V4PLLData).getD 17 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow17Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo LData V4PLD3Data 17 j =
      ((rectangularize 61 89 V4PLLData).getD 17 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow17Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo LData V4PLD3Data 17 j =
      ((rectangularize 61 89 V4PLLData).getD 17 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow17Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo LData V4PLD3Data 17 j =
      ((rectangularize 61 89 V4PLLData).getD 17 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow17Coeffs80To88_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 89) :
    mulCoeffTwo LData V4PLD3Data 17 j =
      ((rectangularize 61 89 V4PLLData).getD 17 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 ∨
    j = 85 ∨ j = 86 ∨ j = 87 ∨ j = 88 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLLRow17_coefficients (j : ℕ) (hj : j < 89) :
    mulCoeffTwo LData V4PLD3Data 17 j =
      ((rectangularize 61 89 V4PLLData).getD 17 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLLRow17Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLLRow17Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLLRow17Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLLRow17Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLLRow17Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLLRow17Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLLRow17Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLLRow17Coeffs70To79_spec j (by omega) h80
  exact v4PLLRow17Coeffs80To88_spec j (by omega) hj

private theorem v4PLLRow17_spec :
    padOne 89 (mulRow LData V4PLD3Data 17) =
      (rectangularize 61 89 V4PLLData).getD 17 [] := by
  apply padOne_mulRow_eq_of_coefficients 89 LData V4PLD3Data 17
    ((rectangularize 61 89 V4PLLData).getD 17 [])
  · decide
  · have hTargetSupport : (V4PLLData.getD 17 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4PLLData 17 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLLRow17_coefficients

private theorem v4PLLRow18Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo LData V4PLD3Data 18 j =
      ((rectangularize 61 89 V4PLLData).getD 18 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow18Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo LData V4PLD3Data 18 j =
      ((rectangularize 61 89 V4PLLData).getD 18 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow18Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo LData V4PLD3Data 18 j =
      ((rectangularize 61 89 V4PLLData).getD 18 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow18Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo LData V4PLD3Data 18 j =
      ((rectangularize 61 89 V4PLLData).getD 18 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow18Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo LData V4PLD3Data 18 j =
      ((rectangularize 61 89 V4PLLData).getD 18 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow18Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo LData V4PLD3Data 18 j =
      ((rectangularize 61 89 V4PLLData).getD 18 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow18Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo LData V4PLD3Data 18 j =
      ((rectangularize 61 89 V4PLLData).getD 18 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow18Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo LData V4PLD3Data 18 j =
      ((rectangularize 61 89 V4PLLData).getD 18 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow18Coeffs80To88_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 89) :
    mulCoeffTwo LData V4PLD3Data 18 j =
      ((rectangularize 61 89 V4PLLData).getD 18 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 ∨
    j = 85 ∨ j = 86 ∨ j = 87 ∨ j = 88 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLLRow18_coefficients (j : ℕ) (hj : j < 89) :
    mulCoeffTwo LData V4PLD3Data 18 j =
      ((rectangularize 61 89 V4PLLData).getD 18 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLLRow18Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLLRow18Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLLRow18Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLLRow18Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLLRow18Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLLRow18Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLLRow18Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLLRow18Coeffs70To79_spec j (by omega) h80
  exact v4PLLRow18Coeffs80To88_spec j (by omega) hj

private theorem v4PLLRow18_spec :
    padOne 89 (mulRow LData V4PLD3Data 18) =
      (rectangularize 61 89 V4PLLData).getD 18 [] := by
  apply padOne_mulRow_eq_of_coefficients 89 LData V4PLD3Data 18
    ((rectangularize 61 89 V4PLLData).getD 18 [])
  · decide
  · have hTargetSupport : (V4PLLData.getD 18 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4PLLData 18 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLLRow18_coefficients

private theorem v4PLLRow19Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo LData V4PLD3Data 19 j =
      ((rectangularize 61 89 V4PLLData).getD 19 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow19Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo LData V4PLD3Data 19 j =
      ((rectangularize 61 89 V4PLLData).getD 19 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow19Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo LData V4PLD3Data 19 j =
      ((rectangularize 61 89 V4PLLData).getD 19 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow19Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo LData V4PLD3Data 19 j =
      ((rectangularize 61 89 V4PLLData).getD 19 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow19Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo LData V4PLD3Data 19 j =
      ((rectangularize 61 89 V4PLLData).getD 19 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow19Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo LData V4PLD3Data 19 j =
      ((rectangularize 61 89 V4PLLData).getD 19 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow19Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo LData V4PLD3Data 19 j =
      ((rectangularize 61 89 V4PLLData).getD 19 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow19Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo LData V4PLD3Data 19 j =
      ((rectangularize 61 89 V4PLLData).getD 19 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow19Coeffs80To88_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 89) :
    mulCoeffTwo LData V4PLD3Data 19 j =
      ((rectangularize 61 89 V4PLLData).getD 19 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 ∨
    j = 85 ∨ j = 86 ∨ j = 87 ∨ j = 88 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLLRow19_coefficients (j : ℕ) (hj : j < 89) :
    mulCoeffTwo LData V4PLD3Data 19 j =
      ((rectangularize 61 89 V4PLLData).getD 19 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLLRow19Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLLRow19Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLLRow19Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLLRow19Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLLRow19Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLLRow19Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLLRow19Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLLRow19Coeffs70To79_spec j (by omega) h80
  exact v4PLLRow19Coeffs80To88_spec j (by omega) hj

private theorem v4PLLRow19_spec :
    padOne 89 (mulRow LData V4PLD3Data 19) =
      (rectangularize 61 89 V4PLLData).getD 19 [] := by
  apply padOne_mulRow_eq_of_coefficients 89 LData V4PLD3Data 19
    ((rectangularize 61 89 V4PLLData).getD 19 [])
  · decide
  · have hTargetSupport : (V4PLLData.getD 19 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4PLLData 19 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLLRow19_coefficients

private theorem v4PLLRow20Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo LData V4PLD3Data 20 j =
      ((rectangularize 61 89 V4PLLData).getD 20 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow20Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo LData V4PLD3Data 20 j =
      ((rectangularize 61 89 V4PLLData).getD 20 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow20Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo LData V4PLD3Data 20 j =
      ((rectangularize 61 89 V4PLLData).getD 20 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow20Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo LData V4PLD3Data 20 j =
      ((rectangularize 61 89 V4PLLData).getD 20 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow20Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo LData V4PLD3Data 20 j =
      ((rectangularize 61 89 V4PLLData).getD 20 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow20Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo LData V4PLD3Data 20 j =
      ((rectangularize 61 89 V4PLLData).getD 20 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow20Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo LData V4PLD3Data 20 j =
      ((rectangularize 61 89 V4PLLData).getD 20 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow20Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo LData V4PLD3Data 20 j =
      ((rectangularize 61 89 V4PLLData).getD 20 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow20Coeffs80To88_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 89) :
    mulCoeffTwo LData V4PLD3Data 20 j =
      ((rectangularize 61 89 V4PLLData).getD 20 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 ∨
    j = 85 ∨ j = 86 ∨ j = 87 ∨ j = 88 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLLRow20_coefficients (j : ℕ) (hj : j < 89) :
    mulCoeffTwo LData V4PLD3Data 20 j =
      ((rectangularize 61 89 V4PLLData).getD 20 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLLRow20Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLLRow20Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLLRow20Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLLRow20Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLLRow20Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLLRow20Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLLRow20Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLLRow20Coeffs70To79_spec j (by omega) h80
  exact v4PLLRow20Coeffs80To88_spec j (by omega) hj

private theorem v4PLLRow20_spec :
    padOne 89 (mulRow LData V4PLD3Data 20) =
      (rectangularize 61 89 V4PLLData).getD 20 [] := by
  apply padOne_mulRow_eq_of_coefficients 89 LData V4PLD3Data 20
    ((rectangularize 61 89 V4PLLData).getD 20 [])
  · decide
  · have hTargetSupport : (V4PLLData.getD 20 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4PLLData 20 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLLRow20_coefficients

private theorem v4PLLRow21Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo LData V4PLD3Data 21 j =
      ((rectangularize 61 89 V4PLLData).getD 21 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow21Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo LData V4PLD3Data 21 j =
      ((rectangularize 61 89 V4PLLData).getD 21 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow21Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo LData V4PLD3Data 21 j =
      ((rectangularize 61 89 V4PLLData).getD 21 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow21Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo LData V4PLD3Data 21 j =
      ((rectangularize 61 89 V4PLLData).getD 21 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow21Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo LData V4PLD3Data 21 j =
      ((rectangularize 61 89 V4PLLData).getD 21 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow21Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo LData V4PLD3Data 21 j =
      ((rectangularize 61 89 V4PLLData).getD 21 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow21Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo LData V4PLD3Data 21 j =
      ((rectangularize 61 89 V4PLLData).getD 21 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow21Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo LData V4PLD3Data 21 j =
      ((rectangularize 61 89 V4PLLData).getD 21 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow21Coeffs80To88_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 89) :
    mulCoeffTwo LData V4PLD3Data 21 j =
      ((rectangularize 61 89 V4PLLData).getD 21 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 ∨
    j = 85 ∨ j = 86 ∨ j = 87 ∨ j = 88 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLLRow21_coefficients (j : ℕ) (hj : j < 89) :
    mulCoeffTwo LData V4PLD3Data 21 j =
      ((rectangularize 61 89 V4PLLData).getD 21 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLLRow21Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLLRow21Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLLRow21Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLLRow21Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLLRow21Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLLRow21Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLLRow21Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLLRow21Coeffs70To79_spec j (by omega) h80
  exact v4PLLRow21Coeffs80To88_spec j (by omega) hj

private theorem v4PLLRow21_spec :
    padOne 89 (mulRow LData V4PLD3Data 21) =
      (rectangularize 61 89 V4PLLData).getD 21 [] := by
  apply padOne_mulRow_eq_of_coefficients 89 LData V4PLD3Data 21
    ((rectangularize 61 89 V4PLLData).getD 21 [])
  · decide
  · have hTargetSupport : (V4PLLData.getD 21 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4PLLData 21 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLLRow21_coefficients

private theorem v4PLLRow22Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo LData V4PLD3Data 22 j =
      ((rectangularize 61 89 V4PLLData).getD 22 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow22Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo LData V4PLD3Data 22 j =
      ((rectangularize 61 89 V4PLLData).getD 22 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow22Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo LData V4PLD3Data 22 j =
      ((rectangularize 61 89 V4PLLData).getD 22 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow22Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo LData V4PLD3Data 22 j =
      ((rectangularize 61 89 V4PLLData).getD 22 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow22Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo LData V4PLD3Data 22 j =
      ((rectangularize 61 89 V4PLLData).getD 22 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow22Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo LData V4PLD3Data 22 j =
      ((rectangularize 61 89 V4PLLData).getD 22 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow22Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo LData V4PLD3Data 22 j =
      ((rectangularize 61 89 V4PLLData).getD 22 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow22Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo LData V4PLD3Data 22 j =
      ((rectangularize 61 89 V4PLLData).getD 22 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow22Coeffs80To88_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 89) :
    mulCoeffTwo LData V4PLD3Data 22 j =
      ((rectangularize 61 89 V4PLLData).getD 22 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 ∨
    j = 85 ∨ j = 86 ∨ j = 87 ∨ j = 88 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLLRow22_coefficients (j : ℕ) (hj : j < 89) :
    mulCoeffTwo LData V4PLD3Data 22 j =
      ((rectangularize 61 89 V4PLLData).getD 22 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLLRow22Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLLRow22Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLLRow22Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLLRow22Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLLRow22Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLLRow22Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLLRow22Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLLRow22Coeffs70To79_spec j (by omega) h80
  exact v4PLLRow22Coeffs80To88_spec j (by omega) hj

private theorem v4PLLRow22_spec :
    padOne 89 (mulRow LData V4PLD3Data 22) =
      (rectangularize 61 89 V4PLLData).getD 22 [] := by
  apply padOne_mulRow_eq_of_coefficients 89 LData V4PLD3Data 22
    ((rectangularize 61 89 V4PLLData).getD 22 [])
  · decide
  · have hTargetSupport : (V4PLLData.getD 22 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4PLLData 22 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLLRow22_coefficients

private theorem v4PLLRow23Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo LData V4PLD3Data 23 j =
      ((rectangularize 61 89 V4PLLData).getD 23 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow23Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo LData V4PLD3Data 23 j =
      ((rectangularize 61 89 V4PLLData).getD 23 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow23Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo LData V4PLD3Data 23 j =
      ((rectangularize 61 89 V4PLLData).getD 23 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow23Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo LData V4PLD3Data 23 j =
      ((rectangularize 61 89 V4PLLData).getD 23 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow23Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo LData V4PLD3Data 23 j =
      ((rectangularize 61 89 V4PLLData).getD 23 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow23Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo LData V4PLD3Data 23 j =
      ((rectangularize 61 89 V4PLLData).getD 23 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow23Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo LData V4PLD3Data 23 j =
      ((rectangularize 61 89 V4PLLData).getD 23 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow23Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo LData V4PLD3Data 23 j =
      ((rectangularize 61 89 V4PLLData).getD 23 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow23Coeffs80To88_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 89) :
    mulCoeffTwo LData V4PLD3Data 23 j =
      ((rectangularize 61 89 V4PLLData).getD 23 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 ∨
    j = 85 ∨ j = 86 ∨ j = 87 ∨ j = 88 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLLRow23_coefficients (j : ℕ) (hj : j < 89) :
    mulCoeffTwo LData V4PLD3Data 23 j =
      ((rectangularize 61 89 V4PLLData).getD 23 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLLRow23Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLLRow23Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLLRow23Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLLRow23Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLLRow23Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLLRow23Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLLRow23Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLLRow23Coeffs70To79_spec j (by omega) h80
  exact v4PLLRow23Coeffs80To88_spec j (by omega) hj

private theorem v4PLLRow23_spec :
    padOne 89 (mulRow LData V4PLD3Data 23) =
      (rectangularize 61 89 V4PLLData).getD 23 [] := by
  apply padOne_mulRow_eq_of_coefficients 89 LData V4PLD3Data 23
    ((rectangularize 61 89 V4PLLData).getD 23 [])
  · decide
  · have hTargetSupport : (V4PLLData.getD 23 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4PLLData 23 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLLRow23_coefficients

private theorem v4PLLRow24Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo LData V4PLD3Data 24 j =
      ((rectangularize 61 89 V4PLLData).getD 24 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow24Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo LData V4PLD3Data 24 j =
      ((rectangularize 61 89 V4PLLData).getD 24 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow24Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo LData V4PLD3Data 24 j =
      ((rectangularize 61 89 V4PLLData).getD 24 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow24Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo LData V4PLD3Data 24 j =
      ((rectangularize 61 89 V4PLLData).getD 24 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow24Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo LData V4PLD3Data 24 j =
      ((rectangularize 61 89 V4PLLData).getD 24 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow24Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo LData V4PLD3Data 24 j =
      ((rectangularize 61 89 V4PLLData).getD 24 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow24Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo LData V4PLD3Data 24 j =
      ((rectangularize 61 89 V4PLLData).getD 24 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow24Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo LData V4PLD3Data 24 j =
      ((rectangularize 61 89 V4PLLData).getD 24 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow24Coeffs80To88_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 89) :
    mulCoeffTwo LData V4PLD3Data 24 j =
      ((rectangularize 61 89 V4PLLData).getD 24 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 ∨
    j = 85 ∨ j = 86 ∨ j = 87 ∨ j = 88 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLLRow24_coefficients (j : ℕ) (hj : j < 89) :
    mulCoeffTwo LData V4PLD3Data 24 j =
      ((rectangularize 61 89 V4PLLData).getD 24 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLLRow24Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLLRow24Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLLRow24Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLLRow24Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLLRow24Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLLRow24Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLLRow24Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLLRow24Coeffs70To79_spec j (by omega) h80
  exact v4PLLRow24Coeffs80To88_spec j (by omega) hj

private theorem v4PLLRow24_spec :
    padOne 89 (mulRow LData V4PLD3Data 24) =
      (rectangularize 61 89 V4PLLData).getD 24 [] := by
  apply padOne_mulRow_eq_of_coefficients 89 LData V4PLD3Data 24
    ((rectangularize 61 89 V4PLLData).getD 24 [])
  · decide
  · have hTargetSupport : (V4PLLData.getD 24 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4PLLData 24 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLLRow24_coefficients

private theorem v4PLLRow25Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo LData V4PLD3Data 25 j =
      ((rectangularize 61 89 V4PLLData).getD 25 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow25Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo LData V4PLD3Data 25 j =
      ((rectangularize 61 89 V4PLLData).getD 25 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow25Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo LData V4PLD3Data 25 j =
      ((rectangularize 61 89 V4PLLData).getD 25 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow25Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo LData V4PLD3Data 25 j =
      ((rectangularize 61 89 V4PLLData).getD 25 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow25Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo LData V4PLD3Data 25 j =
      ((rectangularize 61 89 V4PLLData).getD 25 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow25Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo LData V4PLD3Data 25 j =
      ((rectangularize 61 89 V4PLLData).getD 25 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow25Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo LData V4PLD3Data 25 j =
      ((rectangularize 61 89 V4PLLData).getD 25 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow25Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo LData V4PLD3Data 25 j =
      ((rectangularize 61 89 V4PLLData).getD 25 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow25Coeffs80To88_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 89) :
    mulCoeffTwo LData V4PLD3Data 25 j =
      ((rectangularize 61 89 V4PLLData).getD 25 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 ∨
    j = 85 ∨ j = 86 ∨ j = 87 ∨ j = 88 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLLRow25_coefficients (j : ℕ) (hj : j < 89) :
    mulCoeffTwo LData V4PLD3Data 25 j =
      ((rectangularize 61 89 V4PLLData).getD 25 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLLRow25Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLLRow25Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLLRow25Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLLRow25Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLLRow25Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLLRow25Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLLRow25Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLLRow25Coeffs70To79_spec j (by omega) h80
  exact v4PLLRow25Coeffs80To88_spec j (by omega) hj

private theorem v4PLLRow25_spec :
    padOne 89 (mulRow LData V4PLD3Data 25) =
      (rectangularize 61 89 V4PLLData).getD 25 [] := by
  apply padOne_mulRow_eq_of_coefficients 89 LData V4PLD3Data 25
    ((rectangularize 61 89 V4PLLData).getD 25 [])
  · decide
  · have hTargetSupport : (V4PLLData.getD 25 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4PLLData 25 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLLRow25_coefficients

private theorem v4PLLRow26Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo LData V4PLD3Data 26 j =
      ((rectangularize 61 89 V4PLLData).getD 26 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow26Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo LData V4PLD3Data 26 j =
      ((rectangularize 61 89 V4PLLData).getD 26 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow26Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo LData V4PLD3Data 26 j =
      ((rectangularize 61 89 V4PLLData).getD 26 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow26Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo LData V4PLD3Data 26 j =
      ((rectangularize 61 89 V4PLLData).getD 26 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow26Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo LData V4PLD3Data 26 j =
      ((rectangularize 61 89 V4PLLData).getD 26 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow26Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo LData V4PLD3Data 26 j =
      ((rectangularize 61 89 V4PLLData).getD 26 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow26Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo LData V4PLD3Data 26 j =
      ((rectangularize 61 89 V4PLLData).getD 26 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow26Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo LData V4PLD3Data 26 j =
      ((rectangularize 61 89 V4PLLData).getD 26 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow26Coeffs80To88_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 89) :
    mulCoeffTwo LData V4PLD3Data 26 j =
      ((rectangularize 61 89 V4PLLData).getD 26 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 ∨
    j = 85 ∨ j = 86 ∨ j = 87 ∨ j = 88 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLLRow26_coefficients (j : ℕ) (hj : j < 89) :
    mulCoeffTwo LData V4PLD3Data 26 j =
      ((rectangularize 61 89 V4PLLData).getD 26 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLLRow26Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLLRow26Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLLRow26Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLLRow26Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLLRow26Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLLRow26Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLLRow26Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLLRow26Coeffs70To79_spec j (by omega) h80
  exact v4PLLRow26Coeffs80To88_spec j (by omega) hj

private theorem v4PLLRow26_spec :
    padOne 89 (mulRow LData V4PLD3Data 26) =
      (rectangularize 61 89 V4PLLData).getD 26 [] := by
  apply padOne_mulRow_eq_of_coefficients 89 LData V4PLD3Data 26
    ((rectangularize 61 89 V4PLLData).getD 26 [])
  · decide
  · have hTargetSupport : (V4PLLData.getD 26 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4PLLData 26 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLLRow26_coefficients

private theorem v4PLLRow27Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo LData V4PLD3Data 27 j =
      ((rectangularize 61 89 V4PLLData).getD 27 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow27Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo LData V4PLD3Data 27 j =
      ((rectangularize 61 89 V4PLLData).getD 27 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow27Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo LData V4PLD3Data 27 j =
      ((rectangularize 61 89 V4PLLData).getD 27 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow27Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo LData V4PLD3Data 27 j =
      ((rectangularize 61 89 V4PLLData).getD 27 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow27Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo LData V4PLD3Data 27 j =
      ((rectangularize 61 89 V4PLLData).getD 27 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow27Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo LData V4PLD3Data 27 j =
      ((rectangularize 61 89 V4PLLData).getD 27 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow27Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo LData V4PLD3Data 27 j =
      ((rectangularize 61 89 V4PLLData).getD 27 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow27Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo LData V4PLD3Data 27 j =
      ((rectangularize 61 89 V4PLLData).getD 27 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow27Coeffs80To88_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 89) :
    mulCoeffTwo LData V4PLD3Data 27 j =
      ((rectangularize 61 89 V4PLLData).getD 27 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 ∨
    j = 85 ∨ j = 86 ∨ j = 87 ∨ j = 88 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLLRow27_coefficients (j : ℕ) (hj : j < 89) :
    mulCoeffTwo LData V4PLD3Data 27 j =
      ((rectangularize 61 89 V4PLLData).getD 27 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLLRow27Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLLRow27Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLLRow27Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLLRow27Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLLRow27Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLLRow27Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLLRow27Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLLRow27Coeffs70To79_spec j (by omega) h80
  exact v4PLLRow27Coeffs80To88_spec j (by omega) hj

private theorem v4PLLRow27_spec :
    padOne 89 (mulRow LData V4PLD3Data 27) =
      (rectangularize 61 89 V4PLLData).getD 27 [] := by
  apply padOne_mulRow_eq_of_coefficients 89 LData V4PLD3Data 27
    ((rectangularize 61 89 V4PLLData).getD 27 [])
  · decide
  · have hTargetSupport : (V4PLLData.getD 27 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4PLLData 27 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLLRow27_coefficients

private theorem v4PLLRow28Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo LData V4PLD3Data 28 j =
      ((rectangularize 61 89 V4PLLData).getD 28 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow28Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo LData V4PLD3Data 28 j =
      ((rectangularize 61 89 V4PLLData).getD 28 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow28Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo LData V4PLD3Data 28 j =
      ((rectangularize 61 89 V4PLLData).getD 28 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow28Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo LData V4PLD3Data 28 j =
      ((rectangularize 61 89 V4PLLData).getD 28 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow28Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo LData V4PLD3Data 28 j =
      ((rectangularize 61 89 V4PLLData).getD 28 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow28Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo LData V4PLD3Data 28 j =
      ((rectangularize 61 89 V4PLLData).getD 28 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow28Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo LData V4PLD3Data 28 j =
      ((rectangularize 61 89 V4PLLData).getD 28 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow28Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo LData V4PLD3Data 28 j =
      ((rectangularize 61 89 V4PLLData).getD 28 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow28Coeffs80To88_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 89) :
    mulCoeffTwo LData V4PLD3Data 28 j =
      ((rectangularize 61 89 V4PLLData).getD 28 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 ∨
    j = 85 ∨ j = 86 ∨ j = 87 ∨ j = 88 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLLRow28_coefficients (j : ℕ) (hj : j < 89) :
    mulCoeffTwo LData V4PLD3Data 28 j =
      ((rectangularize 61 89 V4PLLData).getD 28 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLLRow28Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLLRow28Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLLRow28Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLLRow28Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLLRow28Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLLRow28Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLLRow28Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLLRow28Coeffs70To79_spec j (by omega) h80
  exact v4PLLRow28Coeffs80To88_spec j (by omega) hj

private theorem v4PLLRow28_spec :
    padOne 89 (mulRow LData V4PLD3Data 28) =
      (rectangularize 61 89 V4PLLData).getD 28 [] := by
  apply padOne_mulRow_eq_of_coefficients 89 LData V4PLD3Data 28
    ((rectangularize 61 89 V4PLLData).getD 28 [])
  · decide
  · have hTargetSupport : (V4PLLData.getD 28 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4PLLData 28 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLLRow28_coefficients

private theorem v4PLLRow29Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo LData V4PLD3Data 29 j =
      ((rectangularize 61 89 V4PLLData).getD 29 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow29Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo LData V4PLD3Data 29 j =
      ((rectangularize 61 89 V4PLLData).getD 29 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow29Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo LData V4PLD3Data 29 j =
      ((rectangularize 61 89 V4PLLData).getD 29 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow29Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo LData V4PLD3Data 29 j =
      ((rectangularize 61 89 V4PLLData).getD 29 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow29Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo LData V4PLD3Data 29 j =
      ((rectangularize 61 89 V4PLLData).getD 29 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow29Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo LData V4PLD3Data 29 j =
      ((rectangularize 61 89 V4PLLData).getD 29 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow29Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo LData V4PLD3Data 29 j =
      ((rectangularize 61 89 V4PLLData).getD 29 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow29Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo LData V4PLD3Data 29 j =
      ((rectangularize 61 89 V4PLLData).getD 29 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow29Coeffs80To88_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 89) :
    mulCoeffTwo LData V4PLD3Data 29 j =
      ((rectangularize 61 89 V4PLLData).getD 29 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 ∨
    j = 85 ∨ j = 86 ∨ j = 87 ∨ j = 88 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLLRow29_coefficients (j : ℕ) (hj : j < 89) :
    mulCoeffTwo LData V4PLD3Data 29 j =
      ((rectangularize 61 89 V4PLLData).getD 29 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLLRow29Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLLRow29Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLLRow29Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLLRow29Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLLRow29Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLLRow29Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLLRow29Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLLRow29Coeffs70To79_spec j (by omega) h80
  exact v4PLLRow29Coeffs80To88_spec j (by omega) hj

private theorem v4PLLRow29_spec :
    padOne 89 (mulRow LData V4PLD3Data 29) =
      (rectangularize 61 89 V4PLLData).getD 29 [] := by
  apply padOne_mulRow_eq_of_coefficients 89 LData V4PLD3Data 29
    ((rectangularize 61 89 V4PLLData).getD 29 [])
  · decide
  · have hTargetSupport : (V4PLLData.getD 29 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4PLLData 29 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLLRow29_coefficients

private theorem v4PLLRow30Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo LData V4PLD3Data 30 j =
      ((rectangularize 61 89 V4PLLData).getD 30 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow30Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo LData V4PLD3Data 30 j =
      ((rectangularize 61 89 V4PLLData).getD 30 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow30Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo LData V4PLD3Data 30 j =
      ((rectangularize 61 89 V4PLLData).getD 30 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow30Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo LData V4PLD3Data 30 j =
      ((rectangularize 61 89 V4PLLData).getD 30 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow30Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo LData V4PLD3Data 30 j =
      ((rectangularize 61 89 V4PLLData).getD 30 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow30Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo LData V4PLD3Data 30 j =
      ((rectangularize 61 89 V4PLLData).getD 30 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow30Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo LData V4PLD3Data 30 j =
      ((rectangularize 61 89 V4PLLData).getD 30 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow30Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo LData V4PLD3Data 30 j =
      ((rectangularize 61 89 V4PLLData).getD 30 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow30Coeffs80To88_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 89) :
    mulCoeffTwo LData V4PLD3Data 30 j =
      ((rectangularize 61 89 V4PLLData).getD 30 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 ∨
    j = 85 ∨ j = 86 ∨ j = 87 ∨ j = 88 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLLRow30_coefficients (j : ℕ) (hj : j < 89) :
    mulCoeffTwo LData V4PLD3Data 30 j =
      ((rectangularize 61 89 V4PLLData).getD 30 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLLRow30Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLLRow30Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLLRow30Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLLRow30Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLLRow30Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLLRow30Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLLRow30Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLLRow30Coeffs70To79_spec j (by omega) h80
  exact v4PLLRow30Coeffs80To88_spec j (by omega) hj

private theorem v4PLLRow30_spec :
    padOne 89 (mulRow LData V4PLD3Data 30) =
      (rectangularize 61 89 V4PLLData).getD 30 [] := by
  apply padOne_mulRow_eq_of_coefficients 89 LData V4PLD3Data 30
    ((rectangularize 61 89 V4PLLData).getD 30 [])
  · decide
  · have hTargetSupport : (V4PLLData.getD 30 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4PLLData 30 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLLRow30_coefficients

private theorem v4PLLRow31Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo LData V4PLD3Data 31 j =
      ((rectangularize 61 89 V4PLLData).getD 31 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow31Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo LData V4PLD3Data 31 j =
      ((rectangularize 61 89 V4PLLData).getD 31 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow31Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo LData V4PLD3Data 31 j =
      ((rectangularize 61 89 V4PLLData).getD 31 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow31Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo LData V4PLD3Data 31 j =
      ((rectangularize 61 89 V4PLLData).getD 31 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow31Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo LData V4PLD3Data 31 j =
      ((rectangularize 61 89 V4PLLData).getD 31 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow31Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo LData V4PLD3Data 31 j =
      ((rectangularize 61 89 V4PLLData).getD 31 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow31Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo LData V4PLD3Data 31 j =
      ((rectangularize 61 89 V4PLLData).getD 31 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow31Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo LData V4PLD3Data 31 j =
      ((rectangularize 61 89 V4PLLData).getD 31 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow31Coeffs80To88_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 89) :
    mulCoeffTwo LData V4PLD3Data 31 j =
      ((rectangularize 61 89 V4PLLData).getD 31 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 ∨
    j = 85 ∨ j = 86 ∨ j = 87 ∨ j = 88 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLLRow31_coefficients (j : ℕ) (hj : j < 89) :
    mulCoeffTwo LData V4PLD3Data 31 j =
      ((rectangularize 61 89 V4PLLData).getD 31 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLLRow31Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLLRow31Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLLRow31Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLLRow31Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLLRow31Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLLRow31Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLLRow31Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLLRow31Coeffs70To79_spec j (by omega) h80
  exact v4PLLRow31Coeffs80To88_spec j (by omega) hj

private theorem v4PLLRow31_spec :
    padOne 89 (mulRow LData V4PLD3Data 31) =
      (rectangularize 61 89 V4PLLData).getD 31 [] := by
  apply padOne_mulRow_eq_of_coefficients 89 LData V4PLD3Data 31
    ((rectangularize 61 89 V4PLLData).getD 31 [])
  · decide
  · have hTargetSupport : (V4PLLData.getD 31 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4PLLData 31 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLLRow31_coefficients

private theorem v4PLLRow32Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo LData V4PLD3Data 32 j =
      ((rectangularize 61 89 V4PLLData).getD 32 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow32Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo LData V4PLD3Data 32 j =
      ((rectangularize 61 89 V4PLLData).getD 32 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow32Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo LData V4PLD3Data 32 j =
      ((rectangularize 61 89 V4PLLData).getD 32 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow32Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo LData V4PLD3Data 32 j =
      ((rectangularize 61 89 V4PLLData).getD 32 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow32Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo LData V4PLD3Data 32 j =
      ((rectangularize 61 89 V4PLLData).getD 32 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow32Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo LData V4PLD3Data 32 j =
      ((rectangularize 61 89 V4PLLData).getD 32 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow32Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo LData V4PLD3Data 32 j =
      ((rectangularize 61 89 V4PLLData).getD 32 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow32Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo LData V4PLD3Data 32 j =
      ((rectangularize 61 89 V4PLLData).getD 32 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow32Coeffs80To88_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 89) :
    mulCoeffTwo LData V4PLD3Data 32 j =
      ((rectangularize 61 89 V4PLLData).getD 32 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 ∨
    j = 85 ∨ j = 86 ∨ j = 87 ∨ j = 88 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLLRow32_coefficients (j : ℕ) (hj : j < 89) :
    mulCoeffTwo LData V4PLD3Data 32 j =
      ((rectangularize 61 89 V4PLLData).getD 32 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLLRow32Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLLRow32Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLLRow32Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLLRow32Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLLRow32Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLLRow32Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLLRow32Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLLRow32Coeffs70To79_spec j (by omega) h80
  exact v4PLLRow32Coeffs80To88_spec j (by omega) hj

private theorem v4PLLRow32_spec :
    padOne 89 (mulRow LData V4PLD3Data 32) =
      (rectangularize 61 89 V4PLLData).getD 32 [] := by
  apply padOne_mulRow_eq_of_coefficients 89 LData V4PLD3Data 32
    ((rectangularize 61 89 V4PLLData).getD 32 [])
  · decide
  · have hTargetSupport : (V4PLLData.getD 32 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4PLLData 32 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLLRow32_coefficients

private theorem v4PLLRow33Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo LData V4PLD3Data 33 j =
      ((rectangularize 61 89 V4PLLData).getD 33 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow33Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo LData V4PLD3Data 33 j =
      ((rectangularize 61 89 V4PLLData).getD 33 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow33Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo LData V4PLD3Data 33 j =
      ((rectangularize 61 89 V4PLLData).getD 33 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow33Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo LData V4PLD3Data 33 j =
      ((rectangularize 61 89 V4PLLData).getD 33 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow33Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo LData V4PLD3Data 33 j =
      ((rectangularize 61 89 V4PLLData).getD 33 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow33Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo LData V4PLD3Data 33 j =
      ((rectangularize 61 89 V4PLLData).getD 33 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow33Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo LData V4PLD3Data 33 j =
      ((rectangularize 61 89 V4PLLData).getD 33 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow33Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo LData V4PLD3Data 33 j =
      ((rectangularize 61 89 V4PLLData).getD 33 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow33Coeffs80To88_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 89) :
    mulCoeffTwo LData V4PLD3Data 33 j =
      ((rectangularize 61 89 V4PLLData).getD 33 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 ∨
    j = 85 ∨ j = 86 ∨ j = 87 ∨ j = 88 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLLRow33_coefficients (j : ℕ) (hj : j < 89) :
    mulCoeffTwo LData V4PLD3Data 33 j =
      ((rectangularize 61 89 V4PLLData).getD 33 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLLRow33Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLLRow33Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLLRow33Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLLRow33Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLLRow33Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLLRow33Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLLRow33Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLLRow33Coeffs70To79_spec j (by omega) h80
  exact v4PLLRow33Coeffs80To88_spec j (by omega) hj

private theorem v4PLLRow33_spec :
    padOne 89 (mulRow LData V4PLD3Data 33) =
      (rectangularize 61 89 V4PLLData).getD 33 [] := by
  apply padOne_mulRow_eq_of_coefficients 89 LData V4PLD3Data 33
    ((rectangularize 61 89 V4PLLData).getD 33 [])
  · decide
  · have hTargetSupport : (V4PLLData.getD 33 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4PLLData 33 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLLRow33_coefficients

private theorem v4PLLRow34Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo LData V4PLD3Data 34 j =
      ((rectangularize 61 89 V4PLLData).getD 34 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow34Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo LData V4PLD3Data 34 j =
      ((rectangularize 61 89 V4PLLData).getD 34 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow34Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo LData V4PLD3Data 34 j =
      ((rectangularize 61 89 V4PLLData).getD 34 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow34Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo LData V4PLD3Data 34 j =
      ((rectangularize 61 89 V4PLLData).getD 34 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow34Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo LData V4PLD3Data 34 j =
      ((rectangularize 61 89 V4PLLData).getD 34 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow34Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo LData V4PLD3Data 34 j =
      ((rectangularize 61 89 V4PLLData).getD 34 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow34Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo LData V4PLD3Data 34 j =
      ((rectangularize 61 89 V4PLLData).getD 34 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow34Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo LData V4PLD3Data 34 j =
      ((rectangularize 61 89 V4PLLData).getD 34 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow34Coeffs80To88_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 89) :
    mulCoeffTwo LData V4PLD3Data 34 j =
      ((rectangularize 61 89 V4PLLData).getD 34 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 ∨
    j = 85 ∨ j = 86 ∨ j = 87 ∨ j = 88 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLLRow34_coefficients (j : ℕ) (hj : j < 89) :
    mulCoeffTwo LData V4PLD3Data 34 j =
      ((rectangularize 61 89 V4PLLData).getD 34 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLLRow34Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLLRow34Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLLRow34Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLLRow34Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLLRow34Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLLRow34Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLLRow34Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLLRow34Coeffs70To79_spec j (by omega) h80
  exact v4PLLRow34Coeffs80To88_spec j (by omega) hj

private theorem v4PLLRow34_spec :
    padOne 89 (mulRow LData V4PLD3Data 34) =
      (rectangularize 61 89 V4PLLData).getD 34 [] := by
  apply padOne_mulRow_eq_of_coefficients 89 LData V4PLD3Data 34
    ((rectangularize 61 89 V4PLLData).getD 34 [])
  · decide
  · have hTargetSupport : (V4PLLData.getD 34 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4PLLData 34 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLLRow34_coefficients

private theorem v4PLLRow35Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo LData V4PLD3Data 35 j =
      ((rectangularize 61 89 V4PLLData).getD 35 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow35Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo LData V4PLD3Data 35 j =
      ((rectangularize 61 89 V4PLLData).getD 35 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow35Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo LData V4PLD3Data 35 j =
      ((rectangularize 61 89 V4PLLData).getD 35 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow35Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo LData V4PLD3Data 35 j =
      ((rectangularize 61 89 V4PLLData).getD 35 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow35Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo LData V4PLD3Data 35 j =
      ((rectangularize 61 89 V4PLLData).getD 35 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow35Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo LData V4PLD3Data 35 j =
      ((rectangularize 61 89 V4PLLData).getD 35 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow35Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo LData V4PLD3Data 35 j =
      ((rectangularize 61 89 V4PLLData).getD 35 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow35Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo LData V4PLD3Data 35 j =
      ((rectangularize 61 89 V4PLLData).getD 35 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow35Coeffs80To88_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 89) :
    mulCoeffTwo LData V4PLD3Data 35 j =
      ((rectangularize 61 89 V4PLLData).getD 35 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 ∨
    j = 85 ∨ j = 86 ∨ j = 87 ∨ j = 88 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLLRow35_coefficients (j : ℕ) (hj : j < 89) :
    mulCoeffTwo LData V4PLD3Data 35 j =
      ((rectangularize 61 89 V4PLLData).getD 35 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLLRow35Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLLRow35Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLLRow35Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLLRow35Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLLRow35Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLLRow35Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLLRow35Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLLRow35Coeffs70To79_spec j (by omega) h80
  exact v4PLLRow35Coeffs80To88_spec j (by omega) hj

private theorem v4PLLRow35_spec :
    padOne 89 (mulRow LData V4PLD3Data 35) =
      (rectangularize 61 89 V4PLLData).getD 35 [] := by
  apply padOne_mulRow_eq_of_coefficients 89 LData V4PLD3Data 35
    ((rectangularize 61 89 V4PLLData).getD 35 [])
  · decide
  · have hTargetSupport : (V4PLLData.getD 35 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4PLLData 35 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLLRow35_coefficients

private theorem v4PLLRow36Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo LData V4PLD3Data 36 j =
      ((rectangularize 61 89 V4PLLData).getD 36 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow36Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo LData V4PLD3Data 36 j =
      ((rectangularize 61 89 V4PLLData).getD 36 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow36Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo LData V4PLD3Data 36 j =
      ((rectangularize 61 89 V4PLLData).getD 36 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow36Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo LData V4PLD3Data 36 j =
      ((rectangularize 61 89 V4PLLData).getD 36 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow36Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo LData V4PLD3Data 36 j =
      ((rectangularize 61 89 V4PLLData).getD 36 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow36Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo LData V4PLD3Data 36 j =
      ((rectangularize 61 89 V4PLLData).getD 36 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow36Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo LData V4PLD3Data 36 j =
      ((rectangularize 61 89 V4PLLData).getD 36 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow36Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo LData V4PLD3Data 36 j =
      ((rectangularize 61 89 V4PLLData).getD 36 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow36Coeffs80To88_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 89) :
    mulCoeffTwo LData V4PLD3Data 36 j =
      ((rectangularize 61 89 V4PLLData).getD 36 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 ∨
    j = 85 ∨ j = 86 ∨ j = 87 ∨ j = 88 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLLRow36_coefficients (j : ℕ) (hj : j < 89) :
    mulCoeffTwo LData V4PLD3Data 36 j =
      ((rectangularize 61 89 V4PLLData).getD 36 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLLRow36Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLLRow36Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLLRow36Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLLRow36Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLLRow36Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLLRow36Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLLRow36Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLLRow36Coeffs70To79_spec j (by omega) h80
  exact v4PLLRow36Coeffs80To88_spec j (by omega) hj

private theorem v4PLLRow36_spec :
    padOne 89 (mulRow LData V4PLD3Data 36) =
      (rectangularize 61 89 V4PLLData).getD 36 [] := by
  apply padOne_mulRow_eq_of_coefficients 89 LData V4PLD3Data 36
    ((rectangularize 61 89 V4PLLData).getD 36 [])
  · decide
  · have hTargetSupport : (V4PLLData.getD 36 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4PLLData 36 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLLRow36_coefficients

private theorem v4PLLRow37Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo LData V4PLD3Data 37 j =
      ((rectangularize 61 89 V4PLLData).getD 37 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow37Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo LData V4PLD3Data 37 j =
      ((rectangularize 61 89 V4PLLData).getD 37 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow37Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo LData V4PLD3Data 37 j =
      ((rectangularize 61 89 V4PLLData).getD 37 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow37Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo LData V4PLD3Data 37 j =
      ((rectangularize 61 89 V4PLLData).getD 37 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow37Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo LData V4PLD3Data 37 j =
      ((rectangularize 61 89 V4PLLData).getD 37 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow37Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo LData V4PLD3Data 37 j =
      ((rectangularize 61 89 V4PLLData).getD 37 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow37Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo LData V4PLD3Data 37 j =
      ((rectangularize 61 89 V4PLLData).getD 37 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow37Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo LData V4PLD3Data 37 j =
      ((rectangularize 61 89 V4PLLData).getD 37 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow37Coeffs80To88_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 89) :
    mulCoeffTwo LData V4PLD3Data 37 j =
      ((rectangularize 61 89 V4PLLData).getD 37 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 ∨
    j = 85 ∨ j = 86 ∨ j = 87 ∨ j = 88 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLLRow37_coefficients (j : ℕ) (hj : j < 89) :
    mulCoeffTwo LData V4PLD3Data 37 j =
      ((rectangularize 61 89 V4PLLData).getD 37 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLLRow37Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLLRow37Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLLRow37Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLLRow37Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLLRow37Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLLRow37Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLLRow37Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLLRow37Coeffs70To79_spec j (by omega) h80
  exact v4PLLRow37Coeffs80To88_spec j (by omega) hj

private theorem v4PLLRow37_spec :
    padOne 89 (mulRow LData V4PLD3Data 37) =
      (rectangularize 61 89 V4PLLData).getD 37 [] := by
  apply padOne_mulRow_eq_of_coefficients 89 LData V4PLD3Data 37
    ((rectangularize 61 89 V4PLLData).getD 37 [])
  · decide
  · have hTargetSupport : (V4PLLData.getD 37 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4PLLData 37 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLLRow37_coefficients

private theorem v4PLLRow38Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo LData V4PLD3Data 38 j =
      ((rectangularize 61 89 V4PLLData).getD 38 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow38Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo LData V4PLD3Data 38 j =
      ((rectangularize 61 89 V4PLLData).getD 38 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow38Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo LData V4PLD3Data 38 j =
      ((rectangularize 61 89 V4PLLData).getD 38 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow38Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo LData V4PLD3Data 38 j =
      ((rectangularize 61 89 V4PLLData).getD 38 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow38Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo LData V4PLD3Data 38 j =
      ((rectangularize 61 89 V4PLLData).getD 38 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow38Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo LData V4PLD3Data 38 j =
      ((rectangularize 61 89 V4PLLData).getD 38 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow38Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo LData V4PLD3Data 38 j =
      ((rectangularize 61 89 V4PLLData).getD 38 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow38Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo LData V4PLD3Data 38 j =
      ((rectangularize 61 89 V4PLLData).getD 38 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow38Coeffs80To88_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 89) :
    mulCoeffTwo LData V4PLD3Data 38 j =
      ((rectangularize 61 89 V4PLLData).getD 38 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 ∨
    j = 85 ∨ j = 86 ∨ j = 87 ∨ j = 88 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLLRow38_coefficients (j : ℕ) (hj : j < 89) :
    mulCoeffTwo LData V4PLD3Data 38 j =
      ((rectangularize 61 89 V4PLLData).getD 38 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLLRow38Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLLRow38Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLLRow38Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLLRow38Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLLRow38Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLLRow38Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLLRow38Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLLRow38Coeffs70To79_spec j (by omega) h80
  exact v4PLLRow38Coeffs80To88_spec j (by omega) hj

private theorem v4PLLRow38_spec :
    padOne 89 (mulRow LData V4PLD3Data 38) =
      (rectangularize 61 89 V4PLLData).getD 38 [] := by
  apply padOne_mulRow_eq_of_coefficients 89 LData V4PLD3Data 38
    ((rectangularize 61 89 V4PLLData).getD 38 [])
  · decide
  · have hTargetSupport : (V4PLLData.getD 38 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4PLLData 38 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLLRow38_coefficients

private theorem v4PLLRow39Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo LData V4PLD3Data 39 j =
      ((rectangularize 61 89 V4PLLData).getD 39 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow39Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo LData V4PLD3Data 39 j =
      ((rectangularize 61 89 V4PLLData).getD 39 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow39Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo LData V4PLD3Data 39 j =
      ((rectangularize 61 89 V4PLLData).getD 39 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow39Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo LData V4PLD3Data 39 j =
      ((rectangularize 61 89 V4PLLData).getD 39 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow39Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo LData V4PLD3Data 39 j =
      ((rectangularize 61 89 V4PLLData).getD 39 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow39Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo LData V4PLD3Data 39 j =
      ((rectangularize 61 89 V4PLLData).getD 39 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow39Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo LData V4PLD3Data 39 j =
      ((rectangularize 61 89 V4PLLData).getD 39 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow39Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo LData V4PLD3Data 39 j =
      ((rectangularize 61 89 V4PLLData).getD 39 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow39Coeffs80To88_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 89) :
    mulCoeffTwo LData V4PLD3Data 39 j =
      ((rectangularize 61 89 V4PLLData).getD 39 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 ∨
    j = 85 ∨ j = 86 ∨ j = 87 ∨ j = 88 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLLRow39_coefficients (j : ℕ) (hj : j < 89) :
    mulCoeffTwo LData V4PLD3Data 39 j =
      ((rectangularize 61 89 V4PLLData).getD 39 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLLRow39Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLLRow39Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLLRow39Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLLRow39Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLLRow39Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLLRow39Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLLRow39Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLLRow39Coeffs70To79_spec j (by omega) h80
  exact v4PLLRow39Coeffs80To88_spec j (by omega) hj

private theorem v4PLLRow39_spec :
    padOne 89 (mulRow LData V4PLD3Data 39) =
      (rectangularize 61 89 V4PLLData).getD 39 [] := by
  apply padOne_mulRow_eq_of_coefficients 89 LData V4PLD3Data 39
    ((rectangularize 61 89 V4PLLData).getD 39 [])
  · decide
  · have hTargetSupport : (V4PLLData.getD 39 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4PLLData 39 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLLRow39_coefficients

private theorem v4PLLRow40Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo LData V4PLD3Data 40 j =
      ((rectangularize 61 89 V4PLLData).getD 40 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow40Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo LData V4PLD3Data 40 j =
      ((rectangularize 61 89 V4PLLData).getD 40 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow40Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo LData V4PLD3Data 40 j =
      ((rectangularize 61 89 V4PLLData).getD 40 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow40Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo LData V4PLD3Data 40 j =
      ((rectangularize 61 89 V4PLLData).getD 40 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow40Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo LData V4PLD3Data 40 j =
      ((rectangularize 61 89 V4PLLData).getD 40 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow40Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo LData V4PLD3Data 40 j =
      ((rectangularize 61 89 V4PLLData).getD 40 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow40Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo LData V4PLD3Data 40 j =
      ((rectangularize 61 89 V4PLLData).getD 40 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow40Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo LData V4PLD3Data 40 j =
      ((rectangularize 61 89 V4PLLData).getD 40 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow40Coeffs80To88_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 89) :
    mulCoeffTwo LData V4PLD3Data 40 j =
      ((rectangularize 61 89 V4PLLData).getD 40 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 ∨
    j = 85 ∨ j = 86 ∨ j = 87 ∨ j = 88 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLLRow40_coefficients (j : ℕ) (hj : j < 89) :
    mulCoeffTwo LData V4PLD3Data 40 j =
      ((rectangularize 61 89 V4PLLData).getD 40 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLLRow40Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLLRow40Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLLRow40Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLLRow40Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLLRow40Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLLRow40Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLLRow40Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLLRow40Coeffs70To79_spec j (by omega) h80
  exact v4PLLRow40Coeffs80To88_spec j (by omega) hj

private theorem v4PLLRow40_spec :
    padOne 89 (mulRow LData V4PLD3Data 40) =
      (rectangularize 61 89 V4PLLData).getD 40 [] := by
  apply padOne_mulRow_eq_of_coefficients 89 LData V4PLD3Data 40
    ((rectangularize 61 89 V4PLLData).getD 40 [])
  · decide
  · have hTargetSupport : (V4PLLData.getD 40 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4PLLData 40 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLLRow40_coefficients

private theorem v4PLLRow41Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo LData V4PLD3Data 41 j =
      ((rectangularize 61 89 V4PLLData).getD 41 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow41Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo LData V4PLD3Data 41 j =
      ((rectangularize 61 89 V4PLLData).getD 41 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow41Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo LData V4PLD3Data 41 j =
      ((rectangularize 61 89 V4PLLData).getD 41 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow41Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo LData V4PLD3Data 41 j =
      ((rectangularize 61 89 V4PLLData).getD 41 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow41Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo LData V4PLD3Data 41 j =
      ((rectangularize 61 89 V4PLLData).getD 41 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow41Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo LData V4PLD3Data 41 j =
      ((rectangularize 61 89 V4PLLData).getD 41 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow41Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo LData V4PLD3Data 41 j =
      ((rectangularize 61 89 V4PLLData).getD 41 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow41Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo LData V4PLD3Data 41 j =
      ((rectangularize 61 89 V4PLLData).getD 41 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow41Coeffs80To88_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 89) :
    mulCoeffTwo LData V4PLD3Data 41 j =
      ((rectangularize 61 89 V4PLLData).getD 41 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 ∨
    j = 85 ∨ j = 86 ∨ j = 87 ∨ j = 88 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLLRow41_coefficients (j : ℕ) (hj : j < 89) :
    mulCoeffTwo LData V4PLD3Data 41 j =
      ((rectangularize 61 89 V4PLLData).getD 41 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLLRow41Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLLRow41Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLLRow41Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLLRow41Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLLRow41Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLLRow41Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLLRow41Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLLRow41Coeffs70To79_spec j (by omega) h80
  exact v4PLLRow41Coeffs80To88_spec j (by omega) hj

private theorem v4PLLRow41_spec :
    padOne 89 (mulRow LData V4PLD3Data 41) =
      (rectangularize 61 89 V4PLLData).getD 41 [] := by
  apply padOne_mulRow_eq_of_coefficients 89 LData V4PLD3Data 41
    ((rectangularize 61 89 V4PLLData).getD 41 [])
  · decide
  · have hTargetSupport : (V4PLLData.getD 41 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4PLLData 41 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLLRow41_coefficients

private theorem v4PLLRow42Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo LData V4PLD3Data 42 j =
      ((rectangularize 61 89 V4PLLData).getD 42 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow42Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo LData V4PLD3Data 42 j =
      ((rectangularize 61 89 V4PLLData).getD 42 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow42Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo LData V4PLD3Data 42 j =
      ((rectangularize 61 89 V4PLLData).getD 42 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow42Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo LData V4PLD3Data 42 j =
      ((rectangularize 61 89 V4PLLData).getD 42 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow42Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo LData V4PLD3Data 42 j =
      ((rectangularize 61 89 V4PLLData).getD 42 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow42Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo LData V4PLD3Data 42 j =
      ((rectangularize 61 89 V4PLLData).getD 42 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow42Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo LData V4PLD3Data 42 j =
      ((rectangularize 61 89 V4PLLData).getD 42 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow42Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo LData V4PLD3Data 42 j =
      ((rectangularize 61 89 V4PLLData).getD 42 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow42Coeffs80To88_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 89) :
    mulCoeffTwo LData V4PLD3Data 42 j =
      ((rectangularize 61 89 V4PLLData).getD 42 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 ∨
    j = 85 ∨ j = 86 ∨ j = 87 ∨ j = 88 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLLRow42_coefficients (j : ℕ) (hj : j < 89) :
    mulCoeffTwo LData V4PLD3Data 42 j =
      ((rectangularize 61 89 V4PLLData).getD 42 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLLRow42Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLLRow42Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLLRow42Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLLRow42Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLLRow42Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLLRow42Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLLRow42Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLLRow42Coeffs70To79_spec j (by omega) h80
  exact v4PLLRow42Coeffs80To88_spec j (by omega) hj

private theorem v4PLLRow42_spec :
    padOne 89 (mulRow LData V4PLD3Data 42) =
      (rectangularize 61 89 V4PLLData).getD 42 [] := by
  apply padOne_mulRow_eq_of_coefficients 89 LData V4PLD3Data 42
    ((rectangularize 61 89 V4PLLData).getD 42 [])
  · decide
  · have hTargetSupport : (V4PLLData.getD 42 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4PLLData 42 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLLRow42_coefficients

private theorem v4PLLRow43Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo LData V4PLD3Data 43 j =
      ((rectangularize 61 89 V4PLLData).getD 43 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow43Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo LData V4PLD3Data 43 j =
      ((rectangularize 61 89 V4PLLData).getD 43 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow43Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo LData V4PLD3Data 43 j =
      ((rectangularize 61 89 V4PLLData).getD 43 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow43Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo LData V4PLD3Data 43 j =
      ((rectangularize 61 89 V4PLLData).getD 43 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow43Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo LData V4PLD3Data 43 j =
      ((rectangularize 61 89 V4PLLData).getD 43 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow43Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo LData V4PLD3Data 43 j =
      ((rectangularize 61 89 V4PLLData).getD 43 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow43Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo LData V4PLD3Data 43 j =
      ((rectangularize 61 89 V4PLLData).getD 43 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow43Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo LData V4PLD3Data 43 j =
      ((rectangularize 61 89 V4PLLData).getD 43 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow43Coeffs80To88_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 89) :
    mulCoeffTwo LData V4PLD3Data 43 j =
      ((rectangularize 61 89 V4PLLData).getD 43 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 ∨
    j = 85 ∨ j = 86 ∨ j = 87 ∨ j = 88 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLLRow43_coefficients (j : ℕ) (hj : j < 89) :
    mulCoeffTwo LData V4PLD3Data 43 j =
      ((rectangularize 61 89 V4PLLData).getD 43 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLLRow43Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLLRow43Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLLRow43Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLLRow43Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLLRow43Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLLRow43Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLLRow43Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLLRow43Coeffs70To79_spec j (by omega) h80
  exact v4PLLRow43Coeffs80To88_spec j (by omega) hj

private theorem v4PLLRow43_spec :
    padOne 89 (mulRow LData V4PLD3Data 43) =
      (rectangularize 61 89 V4PLLData).getD 43 [] := by
  apply padOne_mulRow_eq_of_coefficients 89 LData V4PLD3Data 43
    ((rectangularize 61 89 V4PLLData).getD 43 [])
  · decide
  · have hTargetSupport : (V4PLLData.getD 43 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4PLLData 43 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLLRow43_coefficients

private theorem v4PLLRow44Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo LData V4PLD3Data 44 j =
      ((rectangularize 61 89 V4PLLData).getD 44 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow44Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo LData V4PLD3Data 44 j =
      ((rectangularize 61 89 V4PLLData).getD 44 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow44Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo LData V4PLD3Data 44 j =
      ((rectangularize 61 89 V4PLLData).getD 44 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow44Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo LData V4PLD3Data 44 j =
      ((rectangularize 61 89 V4PLLData).getD 44 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow44Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo LData V4PLD3Data 44 j =
      ((rectangularize 61 89 V4PLLData).getD 44 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow44Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo LData V4PLD3Data 44 j =
      ((rectangularize 61 89 V4PLLData).getD 44 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow44Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo LData V4PLD3Data 44 j =
      ((rectangularize 61 89 V4PLLData).getD 44 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow44Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo LData V4PLD3Data 44 j =
      ((rectangularize 61 89 V4PLLData).getD 44 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow44Coeffs80To88_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 89) :
    mulCoeffTwo LData V4PLD3Data 44 j =
      ((rectangularize 61 89 V4PLLData).getD 44 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 ∨
    j = 85 ∨ j = 86 ∨ j = 87 ∨ j = 88 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLLRow44_coefficients (j : ℕ) (hj : j < 89) :
    mulCoeffTwo LData V4PLD3Data 44 j =
      ((rectangularize 61 89 V4PLLData).getD 44 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLLRow44Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLLRow44Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLLRow44Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLLRow44Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLLRow44Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLLRow44Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLLRow44Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLLRow44Coeffs70To79_spec j (by omega) h80
  exact v4PLLRow44Coeffs80To88_spec j (by omega) hj

private theorem v4PLLRow44_spec :
    padOne 89 (mulRow LData V4PLD3Data 44) =
      (rectangularize 61 89 V4PLLData).getD 44 [] := by
  apply padOne_mulRow_eq_of_coefficients 89 LData V4PLD3Data 44
    ((rectangularize 61 89 V4PLLData).getD 44 [])
  · decide
  · have hTargetSupport : (V4PLLData.getD 44 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4PLLData 44 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLLRow44_coefficients

private theorem v4PLLRow45Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo LData V4PLD3Data 45 j =
      ((rectangularize 61 89 V4PLLData).getD 45 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow45Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo LData V4PLD3Data 45 j =
      ((rectangularize 61 89 V4PLLData).getD 45 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow45Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo LData V4PLD3Data 45 j =
      ((rectangularize 61 89 V4PLLData).getD 45 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow45Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo LData V4PLD3Data 45 j =
      ((rectangularize 61 89 V4PLLData).getD 45 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow45Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo LData V4PLD3Data 45 j =
      ((rectangularize 61 89 V4PLLData).getD 45 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow45Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo LData V4PLD3Data 45 j =
      ((rectangularize 61 89 V4PLLData).getD 45 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow45Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo LData V4PLD3Data 45 j =
      ((rectangularize 61 89 V4PLLData).getD 45 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow45Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo LData V4PLD3Data 45 j =
      ((rectangularize 61 89 V4PLLData).getD 45 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow45Coeffs80To88_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 89) :
    mulCoeffTwo LData V4PLD3Data 45 j =
      ((rectangularize 61 89 V4PLLData).getD 45 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 ∨
    j = 85 ∨ j = 86 ∨ j = 87 ∨ j = 88 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLLRow45_coefficients (j : ℕ) (hj : j < 89) :
    mulCoeffTwo LData V4PLD3Data 45 j =
      ((rectangularize 61 89 V4PLLData).getD 45 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLLRow45Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLLRow45Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLLRow45Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLLRow45Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLLRow45Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLLRow45Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLLRow45Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLLRow45Coeffs70To79_spec j (by omega) h80
  exact v4PLLRow45Coeffs80To88_spec j (by omega) hj

private theorem v4PLLRow45_spec :
    padOne 89 (mulRow LData V4PLD3Data 45) =
      (rectangularize 61 89 V4PLLData).getD 45 [] := by
  apply padOne_mulRow_eq_of_coefficients 89 LData V4PLD3Data 45
    ((rectangularize 61 89 V4PLLData).getD 45 [])
  · decide
  · have hTargetSupport : (V4PLLData.getD 45 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4PLLData 45 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLLRow45_coefficients

private theorem v4PLLRow46Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo LData V4PLD3Data 46 j =
      ((rectangularize 61 89 V4PLLData).getD 46 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow46Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo LData V4PLD3Data 46 j =
      ((rectangularize 61 89 V4PLLData).getD 46 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow46Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo LData V4PLD3Data 46 j =
      ((rectangularize 61 89 V4PLLData).getD 46 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow46Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo LData V4PLD3Data 46 j =
      ((rectangularize 61 89 V4PLLData).getD 46 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow46Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo LData V4PLD3Data 46 j =
      ((rectangularize 61 89 V4PLLData).getD 46 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow46Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo LData V4PLD3Data 46 j =
      ((rectangularize 61 89 V4PLLData).getD 46 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow46Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo LData V4PLD3Data 46 j =
      ((rectangularize 61 89 V4PLLData).getD 46 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow46Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo LData V4PLD3Data 46 j =
      ((rectangularize 61 89 V4PLLData).getD 46 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow46Coeffs80To88_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 89) :
    mulCoeffTwo LData V4PLD3Data 46 j =
      ((rectangularize 61 89 V4PLLData).getD 46 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 ∨
    j = 85 ∨ j = 86 ∨ j = 87 ∨ j = 88 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLLRow46_coefficients (j : ℕ) (hj : j < 89) :
    mulCoeffTwo LData V4PLD3Data 46 j =
      ((rectangularize 61 89 V4PLLData).getD 46 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLLRow46Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLLRow46Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLLRow46Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLLRow46Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLLRow46Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLLRow46Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLLRow46Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLLRow46Coeffs70To79_spec j (by omega) h80
  exact v4PLLRow46Coeffs80To88_spec j (by omega) hj

private theorem v4PLLRow46_spec :
    padOne 89 (mulRow LData V4PLD3Data 46) =
      (rectangularize 61 89 V4PLLData).getD 46 [] := by
  apply padOne_mulRow_eq_of_coefficients 89 LData V4PLD3Data 46
    ((rectangularize 61 89 V4PLLData).getD 46 [])
  · decide
  · have hTargetSupport : (V4PLLData.getD 46 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4PLLData 46 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLLRow46_coefficients

private theorem v4PLLRow47Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo LData V4PLD3Data 47 j =
      ((rectangularize 61 89 V4PLLData).getD 47 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow47Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo LData V4PLD3Data 47 j =
      ((rectangularize 61 89 V4PLLData).getD 47 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow47Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo LData V4PLD3Data 47 j =
      ((rectangularize 61 89 V4PLLData).getD 47 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow47Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo LData V4PLD3Data 47 j =
      ((rectangularize 61 89 V4PLLData).getD 47 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow47Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo LData V4PLD3Data 47 j =
      ((rectangularize 61 89 V4PLLData).getD 47 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow47Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo LData V4PLD3Data 47 j =
      ((rectangularize 61 89 V4PLLData).getD 47 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow47Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo LData V4PLD3Data 47 j =
      ((rectangularize 61 89 V4PLLData).getD 47 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow47Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo LData V4PLD3Data 47 j =
      ((rectangularize 61 89 V4PLLData).getD 47 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow47Coeffs80To88_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 89) :
    mulCoeffTwo LData V4PLD3Data 47 j =
      ((rectangularize 61 89 V4PLLData).getD 47 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 ∨
    j = 85 ∨ j = 86 ∨ j = 87 ∨ j = 88 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLLRow47_coefficients (j : ℕ) (hj : j < 89) :
    mulCoeffTwo LData V4PLD3Data 47 j =
      ((rectangularize 61 89 V4PLLData).getD 47 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLLRow47Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLLRow47Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLLRow47Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLLRow47Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLLRow47Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLLRow47Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLLRow47Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLLRow47Coeffs70To79_spec j (by omega) h80
  exact v4PLLRow47Coeffs80To88_spec j (by omega) hj

private theorem v4PLLRow47_spec :
    padOne 89 (mulRow LData V4PLD3Data 47) =
      (rectangularize 61 89 V4PLLData).getD 47 [] := by
  apply padOne_mulRow_eq_of_coefficients 89 LData V4PLD3Data 47
    ((rectangularize 61 89 V4PLLData).getD 47 [])
  · decide
  · have hTargetSupport : (V4PLLData.getD 47 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4PLLData 47 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLLRow47_coefficients

private theorem v4PLLRow48Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo LData V4PLD3Data 48 j =
      ((rectangularize 61 89 V4PLLData).getD 48 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow48Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo LData V4PLD3Data 48 j =
      ((rectangularize 61 89 V4PLLData).getD 48 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow48Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo LData V4PLD3Data 48 j =
      ((rectangularize 61 89 V4PLLData).getD 48 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow48Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo LData V4PLD3Data 48 j =
      ((rectangularize 61 89 V4PLLData).getD 48 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow48Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo LData V4PLD3Data 48 j =
      ((rectangularize 61 89 V4PLLData).getD 48 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow48Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo LData V4PLD3Data 48 j =
      ((rectangularize 61 89 V4PLLData).getD 48 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow48Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo LData V4PLD3Data 48 j =
      ((rectangularize 61 89 V4PLLData).getD 48 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow48Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo LData V4PLD3Data 48 j =
      ((rectangularize 61 89 V4PLLData).getD 48 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow48Coeffs80To88_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 89) :
    mulCoeffTwo LData V4PLD3Data 48 j =
      ((rectangularize 61 89 V4PLLData).getD 48 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 ∨
    j = 85 ∨ j = 86 ∨ j = 87 ∨ j = 88 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLLRow48_coefficients (j : ℕ) (hj : j < 89) :
    mulCoeffTwo LData V4PLD3Data 48 j =
      ((rectangularize 61 89 V4PLLData).getD 48 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLLRow48Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLLRow48Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLLRow48Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLLRow48Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLLRow48Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLLRow48Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLLRow48Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLLRow48Coeffs70To79_spec j (by omega) h80
  exact v4PLLRow48Coeffs80To88_spec j (by omega) hj

private theorem v4PLLRow48_spec :
    padOne 89 (mulRow LData V4PLD3Data 48) =
      (rectangularize 61 89 V4PLLData).getD 48 [] := by
  apply padOne_mulRow_eq_of_coefficients 89 LData V4PLD3Data 48
    ((rectangularize 61 89 V4PLLData).getD 48 [])
  · decide
  · have hTargetSupport : (V4PLLData.getD 48 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4PLLData 48 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLLRow48_coefficients

private theorem v4PLLRow49Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo LData V4PLD3Data 49 j =
      ((rectangularize 61 89 V4PLLData).getD 49 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow49Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo LData V4PLD3Data 49 j =
      ((rectangularize 61 89 V4PLLData).getD 49 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow49Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo LData V4PLD3Data 49 j =
      ((rectangularize 61 89 V4PLLData).getD 49 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow49Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo LData V4PLD3Data 49 j =
      ((rectangularize 61 89 V4PLLData).getD 49 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow49Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo LData V4PLD3Data 49 j =
      ((rectangularize 61 89 V4PLLData).getD 49 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow49Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo LData V4PLD3Data 49 j =
      ((rectangularize 61 89 V4PLLData).getD 49 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow49Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo LData V4PLD3Data 49 j =
      ((rectangularize 61 89 V4PLLData).getD 49 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow49Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo LData V4PLD3Data 49 j =
      ((rectangularize 61 89 V4PLLData).getD 49 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 ∨ j = 76 ∨ j = 77 ∨ j = 78 ∨ j = 79 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem v4PLLRow49Coeffs80To88_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 89) :
    mulCoeffTwo LData V4PLD3Data 49 j =
      ((rectangularize 61 89 V4PLLData).getD 49 []).getD j 0 := by
  have hCases :
    j = 80 ∨ j = 81 ∨ j = 82 ∨ j = 83 ∨ j = 84 ∨
    j = 85 ∨ j = 86 ∨ j = 87 ∨ j = 88 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

private theorem v4PLLRow49_coefficients (j : ℕ) (hj : j < 89) :
    mulCoeffTwo LData V4PLD3Data 49 j =
      ((rectangularize 61 89 V4PLLData).getD 49 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4PLLRow49Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4PLLRow49Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4PLLRow49Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4PLLRow49Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4PLLRow49Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4PLLRow49Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4PLLRow49Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact v4PLLRow49Coeffs70To79_spec j (by omega) h80
  exact v4PLLRow49Coeffs80To88_spec j (by omega) hj

private theorem v4PLLRow49_spec :
    padOne 89 (mulRow LData V4PLD3Data 49) =
      (rectangularize 61 89 V4PLLData).getD 49 [] := by
  apply padOne_mulRow_eq_of_coefficients 89 LData V4PLD3Data 49
    ((rectangularize 61 89 V4PLLData).getD 49 [])
  · decide
  · have hTargetSupport : (V4PLLData.getD 49 []).length ≤ 89 := by
      decide
    rw [getD_rectangularize 61 89 V4PLLData 49 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4PLLRow49_coefficients

private theorem v4PLLRow50_spec :
    padOne 89 (mulRow LData V4PLD3Data 50) =
      (rectangularize 61 89 V4PLLData).getD 50 [] := by
  decide

private theorem v4PLLRow51_spec :
    padOne 89 (mulRow LData V4PLD3Data 51) =
      (rectangularize 61 89 V4PLLData).getD 51 [] := by
  decide

private theorem v4PLLRow52_spec :
    padOne 89 (mulRow LData V4PLD3Data 52) =
      (rectangularize 61 89 V4PLLData).getD 52 [] := by
  decide

private theorem v4PLLRow53_spec :
    padOne 89 (mulRow LData V4PLD3Data 53) =
      (rectangularize 61 89 V4PLLData).getD 53 [] := by
  decide

private theorem v4PLLRow54_spec :
    padOne 89 (mulRow LData V4PLD3Data 54) =
      (rectangularize 61 89 V4PLLData).getD 54 [] := by
  decide

private theorem v4PLLRow55_spec :
    padOne 89 (mulRow LData V4PLD3Data 55) =
      (rectangularize 61 89 V4PLLData).getD 55 [] := by
  decide

private theorem v4PLLRow56_spec :
    padOne 89 (mulRow LData V4PLD3Data 56) =
      (rectangularize 61 89 V4PLLData).getD 56 [] := by
  decide

private theorem v4PLLRow57_spec :
    padOne 89 (mulRow LData V4PLD3Data 57) =
      (rectangularize 61 89 V4PLLData).getD 57 [] := by
  decide

private theorem v4PLLRow58_spec :
    padOne 89 (mulRow LData V4PLD3Data 58) =
      (rectangularize 61 89 V4PLLData).getD 58 [] := by
  decide

private theorem v4PLLRow59_spec :
    padOne 89 (mulRow LData V4PLD3Data 59) =
      (rectangularize 61 89 V4PLLData).getD 59 [] := by
  decide

private theorem v4PLLRow60_spec :
    padOne 89 (mulRow LData V4PLD3Data 60) =
      (rectangularize 61 89 V4PLLData).getD 60 [] := by
  decide

private theorem v4PLLRows_spec (n : ℕ) (hn : n < 61) :
    padOne 89 (mulRow LData V4PLD3Data n) =
      (rectangularize 61 89 V4PLLData).getD n [] := by
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
    n = 55 ∨ n = 56 ∨ n = 57 ∨ n = 58 ∨ n = 59 ∨
    n = 60 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · exact v4PLLRow0_spec
  · exact v4PLLRow1_spec
  · exact v4PLLRow2_spec
  · exact v4PLLRow3_spec
  · exact v4PLLRow4_spec
  · exact v4PLLRow5_spec
  · exact v4PLLRow6_spec
  · exact v4PLLRow7_spec
  · exact v4PLLRow8_spec
  · exact v4PLLRow9_spec
  · exact v4PLLRow10_spec
  · exact v4PLLRow11_spec
  · exact v4PLLRow12_spec
  · exact v4PLLRow13_spec
  · exact v4PLLRow14_spec
  · exact v4PLLRow15_spec
  · exact v4PLLRow16_spec
  · exact v4PLLRow17_spec
  · exact v4PLLRow18_spec
  · exact v4PLLRow19_spec
  · exact v4PLLRow20_spec
  · exact v4PLLRow21_spec
  · exact v4PLLRow22_spec
  · exact v4PLLRow23_spec
  · exact v4PLLRow24_spec
  · exact v4PLLRow25_spec
  · exact v4PLLRow26_spec
  · exact v4PLLRow27_spec
  · exact v4PLLRow28_spec
  · exact v4PLLRow29_spec
  · exact v4PLLRow30_spec
  · exact v4PLLRow31_spec
  · exact v4PLLRow32_spec
  · exact v4PLLRow33_spec
  · exact v4PLLRow34_spec
  · exact v4PLLRow35_spec
  · exact v4PLLRow36_spec
  · exact v4PLLRow37_spec
  · exact v4PLLRow38_spec
  · exact v4PLLRow39_spec
  · exact v4PLLRow40_spec
  · exact v4PLLRow41_spec
  · exact v4PLLRow42_spec
  · exact v4PLLRow43_spec
  · exact v4PLLRow44_spec
  · exact v4PLLRow45_spec
  · exact v4PLLRow46_spec
  · exact v4PLLRow47_spec
  · exact v4PLLRow48_spec
  · exact v4PLLRow49_spec
  · exact v4PLLRow50_spec
  · exact v4PLLRow51_spec
  · exact v4PLLRow52_spec
  · exact v4PLLRow53_spec
  · exact v4PLLRow54_spec
  · exact v4PLLRow55_spec
  · exact v4PLLRow56_spec
  · exact v4PLLRow57_spec
  · exact v4PLLRow58_spec
  · exact v4PLLRow59_spec
  · exact v4PLLRow60_spec

private theorem v4PLLLeft_length :
    (rectangularize 61 89 (Two.mul LData V4PLD3Data)).length = 61 := by
  decide

private theorem v4PLLRight_length :
    (rectangularize 61 89 V4PLLData).length = 61 := by
  decide

-- Exact bidegree bound (60, 88); no row or column is discarded.
private theorem v4PLLData_spec :
    rectangularize 61 89 (Two.mul LData V4PLD3Data) =
      rectangularize 61 89 V4PLLData := by
  apply List.ext_getElem (v4PLLLeft_length.trans v4PLLRight_length.symm)
  intro n hn _
  rw [List.getElem_eq_getD [], List.getElem_eq_getD []]
  rw [v4PLLLeft_length] at hn
  rw [getD_rectangularize 61 89 (Two.mul LData V4PLD3Data) n hn,
    ← mulRow_eq_getD]
  exact v4PLLRows_spec n hn

/-- Evaluation of the checked `D^3 * L` branch of the canonical `P9`. -/
theorem eval_v4PLeftData (r s : ℚ) :
    Two.eval V4PLLData r s =
      OrderTwentyFiveRelationZeroCertificate.Internal.L r s *
        OrderTwentyFiveRelationZeroCertificate.Internal.D r s ^ 3 *
          Two.eval V4JData r s := by
  have hD1 := congrArg (fun p => Two.eval p r s) v4PLD1Data_spec
  have hD2 := congrArg (fun p => Two.eval p r s) v4PLD2Data_spec
  have hD3 := congrArg (fun p => Two.eval p r s) v4PLD3Data_spec
  have hL := congrArg (fun p => Two.eval p r s) v4PLLData_spec
  simp only [eval_rectangularize, Two.eval_mul] at hD1 hD2 hD3 hL
  calc
    Two.eval V4PLLData r s =
        Two.eval LData r s * Two.eval V4PLD3Data r s := hL.symm
    _ = Two.eval LData r s *
        (Two.eval DData r s * Two.eval V4PLD2Data r s) := by rw [← hD3]
    _ = Two.eval LData r s *
        (Two.eval DData r s *
          (Two.eval DData r s * Two.eval V4PLD1Data r s)) := by rw [← hD2]
    _ = OrderTwentyFiveRelationZeroCertificate.Internal.L r s *
        OrderTwentyFiveRelationZeroCertificate.Internal.D r s ^ 3 *
          Two.eval V4JData r s := by
      rw [← hD1, eval_LData, eval_DData]
      ring

end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
