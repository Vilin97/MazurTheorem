/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialAssemblyTermSixStageFourSupport
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialWindow
import Mathlib.Tactic.IntervalCases

/-!
# Rows 8 through 15 of the fourth stage of the sixth assembly term
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveDensePolynomialRectangular
open OrderTwentyFiveDensePolynomialRowCertificate

private theorem term6Stage4Row8Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 8 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 8 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row8Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 8 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 8 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row8Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 8 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 8 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row8Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 8 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 8 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row8Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 8 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 8 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row8Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 8 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 8 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row8Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 8 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 8 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row8Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 8 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 8 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row8Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 8 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 8 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row8Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 8 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 8 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row8_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 8 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 8 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row8Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row8Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row8Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row8Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row8Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row8Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row8Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row8Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row8Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row8Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row8_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 8) =
      (rectangularize 62 93 Term6Stage4Data).getD 8 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 8
    ((rectangularize 62 93 Term6Stage4Data).getD 8 [])
  · exact term6Stage4_mulRow_length_le 8
  · rw [getD_rectangularize 62 93 Term6Stage4Data 8 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 8
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row8_coefficients

private theorem term6Stage4Row9Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 9 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 9 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row9Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 9 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 9 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row9Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 9 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 9 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row9Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 9 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 9 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row9Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 9 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 9 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row9Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 9 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 9 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row9Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 9 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 9 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row9Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 9 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 9 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row9Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 9 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 9 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row9Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 9 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 9 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row9_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 9 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 9 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row9Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row9Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row9Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row9Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row9Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row9Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row9Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row9Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row9Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row9Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row9_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 9) =
      (rectangularize 62 93 Term6Stage4Data).getD 9 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 9
    ((rectangularize 62 93 Term6Stage4Data).getD 9 [])
  · exact term6Stage4_mulRow_length_le 9
  · rw [getD_rectangularize 62 93 Term6Stage4Data 9 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 9
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row9_coefficients

private theorem term6Stage4Row10Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 10 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 10 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row10Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 10 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 10 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row10Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 10 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 10 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row10Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 10 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 10 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row10Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 10 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 10 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row10Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 10 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 10 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row10Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 10 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 10 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row10Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 10 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 10 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row10Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 10 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 10 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row10Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 10 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 10 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row10_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 10 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 10 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row10Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row10Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row10Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row10Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row10Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row10Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row10Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row10Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row10Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row10Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row10_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 10) =
      (rectangularize 62 93 Term6Stage4Data).getD 10 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 10
    ((rectangularize 62 93 Term6Stage4Data).getD 10 [])
  · exact term6Stage4_mulRow_length_le 10
  · rw [getD_rectangularize 62 93 Term6Stage4Data 10 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 10
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row10_coefficients

private theorem term6Stage4Row11Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 11 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 11 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row11Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 11 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 11 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row11Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 11 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 11 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row11Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 11 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 11 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row11Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 11 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 11 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row11Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 11 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 11 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row11Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 11 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 11 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row11Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 11 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 11 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row11Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 11 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 11 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row11Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 11 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 11 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row11_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 11 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 11 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row11Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row11Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row11Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row11Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row11Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row11Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row11Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row11Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row11Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row11Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row11_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 11) =
      (rectangularize 62 93 Term6Stage4Data).getD 11 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 11
    ((rectangularize 62 93 Term6Stage4Data).getD 11 [])
  · exact term6Stage4_mulRow_length_le 11
  · rw [getD_rectangularize 62 93 Term6Stage4Data 11 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 11
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row11_coefficients

private theorem term6Stage4Row12Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 12 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 12 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row12Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 12 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 12 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row12Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 12 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 12 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row12Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 12 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 12 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row12Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 12 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 12 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row12Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 12 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 12 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row12Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 12 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 12 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row12Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 12 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 12 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row12Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 12 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 12 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row12Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 12 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 12 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row12_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 12 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 12 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row12Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row12Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row12Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row12Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row12Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row12Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row12Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row12Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row12Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row12Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row12_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 12) =
      (rectangularize 62 93 Term6Stage4Data).getD 12 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 12
    ((rectangularize 62 93 Term6Stage4Data).getD 12 [])
  · exact term6Stage4_mulRow_length_le 12
  · rw [getD_rectangularize 62 93 Term6Stage4Data 12 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 12
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row12_coefficients

private theorem term6Stage4Row13Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 13 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 13 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row13Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 13 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 13 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row13Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 13 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 13 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row13Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 13 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 13 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row13Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 13 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 13 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row13Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 13 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 13 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row13Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 13 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 13 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row13Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 13 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 13 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row13Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 13 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 13 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row13Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 13 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 13 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row13_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 13 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 13 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row13Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row13Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row13Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row13Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row13Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row13Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row13Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row13Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row13Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row13Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row13_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 13) =
      (rectangularize 62 93 Term6Stage4Data).getD 13 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 13
    ((rectangularize 62 93 Term6Stage4Data).getD 13 [])
  · exact term6Stage4_mulRow_length_le 13
  · rw [getD_rectangularize 62 93 Term6Stage4Data 13 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 13
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row13_coefficients

private theorem term6Stage4Row14Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 14 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 14 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row14Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 14 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 14 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row14Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 14 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 14 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row14Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 14 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 14 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row14Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 14 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 14 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row14Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 14 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 14 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row14Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 14 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 14 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row14Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 14 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 14 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row14Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 14 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 14 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row14Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 14 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 14 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row14_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 14 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 14 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row14Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row14Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row14Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row14Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row14Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row14Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row14Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row14Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row14Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row14Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row14_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 14) =
      (rectangularize 62 93 Term6Stage4Data).getD 14 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 14
    ((rectangularize 62 93 Term6Stage4Data).getD 14 [])
  · exact term6Stage4_mulRow_length_le 14
  · rw [getD_rectangularize 62 93 Term6Stage4Data 14 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 14
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row14_coefficients

private theorem term6Stage4Row15Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 15 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 15 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row15Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 15 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 15 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row15Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 15 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 15 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row15Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 15 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 15 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row15Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 15 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 15 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row15Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 15 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 15 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row15Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 15 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 15 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row15Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 15 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 15 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 15 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row15Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 15 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 15 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 15 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row15Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 15 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 15 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 15 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row15_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 15 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 15 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row15Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row15Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row15Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row15Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row15Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row15Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row15Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row15Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row15Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row15Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row15_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 15) =
      (rectangularize 62 93 Term6Stage4Data).getD 15 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 15
    ((rectangularize 62 93 Term6Stage4Data).getD 15 [])
  · exact term6Stage4_mulRow_length_le 15
  · rw [getD_rectangularize 62 93 Term6Stage4Data 15 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 15
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row15_coefficients

theorem term6Stage4_rows8To15 (n : ℕ) (hLo : 8 ≤ n) (hHi : n < 16) :
    padOne 93 (mulRow V3Data Term6Stage3Data n) =
      (rectangularize 62 93 Term6Stage4Data).getD n [] := by
  interval_cases n
  · exact term6Stage4Row8_spec
  · exact term6Stage4Row9_spec
  · exact term6Stage4Row10_spec
  · exact term6Stage4Row11_spec
  · exact term6Stage4Row12_spec
  · exact term6Stage4Row13_spec
  · exact term6Stage4Row14_spec
  · exact term6Stage4Row15_spec

end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
