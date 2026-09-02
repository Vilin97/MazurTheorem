/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialAssemblyTermSixStageFourSupport
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialWindow
import Mathlib.Tactic.IntervalCases

/-!
# Rows 16 through 23 of the fourth stage of the sixth assembly term
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveDensePolynomialRectangular
open OrderTwentyFiveDensePolynomialRowCertificate

private theorem term6Stage4Row16Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 16 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 16 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 16 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 8 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row16Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 16 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 16 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 16 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 8 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row16Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 16 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 16 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 16 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 8 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row16Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 16 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 16 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 16 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 8 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row16Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 16 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 16 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 16 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 8 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row16Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 16 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 16 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 16 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 8 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row16Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 16 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 16 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 16 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 8 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row16Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 16 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 16 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 16 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 8 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row16Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 16 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 16 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 16 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 8 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row16Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 16 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 16 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 16 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 8 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row16_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 16 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 16 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row16Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row16Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row16Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row16Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row16Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row16Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row16Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row16Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row16Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row16Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row16_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 16) =
      (rectangularize 62 93 Term6Stage4Data).getD 16 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 16
    ((rectangularize 62 93 Term6Stage4Data).getD 16 [])
  · exact term6Stage4_mulRow_length_le 16
  · rw [getD_rectangularize 62 93 Term6Stage4Data 16 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 16
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row16_coefficients

private theorem term6Stage4Row17Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 17 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 17 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 17 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 9 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row17Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 17 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 17 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 17 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 9 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row17Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 17 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 17 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 17 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 9 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row17Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 17 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 17 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 17 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 9 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row17Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 17 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 17 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 17 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 9 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row17Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 17 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 17 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 17 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 9 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row17Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 17 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 17 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 17 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 9 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row17Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 17 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 17 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 17 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 9 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row17Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 17 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 17 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 17 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 9 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row17Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 17 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 17 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 17 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 9 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row17_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 17 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 17 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row17Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row17Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row17Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row17Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row17Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row17Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row17Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row17Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row17Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row17Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row17_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 17) =
      (rectangularize 62 93 Term6Stage4Data).getD 17 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 17
    ((rectangularize 62 93 Term6Stage4Data).getD 17 [])
  · exact term6Stage4_mulRow_length_le 17
  · rw [getD_rectangularize 62 93 Term6Stage4Data 17 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 17
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row17_coefficients

private theorem term6Stage4Row18Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 18 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 18 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 18 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 10 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row18Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 18 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 18 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 18 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 10 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row18Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 18 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 18 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 18 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 10 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row18Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 18 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 18 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 18 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 10 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row18Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 18 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 18 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 18 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 10 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row18Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 18 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 18 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 18 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 10 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row18Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 18 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 18 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 18 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 10 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row18Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 18 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 18 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 18 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 10 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row18Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 18 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 18 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 18 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 10 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row18Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 18 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 18 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 18 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 10 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row18_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 18 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 18 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row18Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row18Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row18Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row18Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row18Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row18Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row18Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row18Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row18Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row18Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row18_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 18) =
      (rectangularize 62 93 Term6Stage4Data).getD 18 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 18
    ((rectangularize 62 93 Term6Stage4Data).getD 18 [])
  · exact term6Stage4_mulRow_length_le 18
  · rw [getD_rectangularize 62 93 Term6Stage4Data 18 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 18
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row18_coefficients

private theorem term6Stage4Row19Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 19 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 19 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 19 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 11 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row19Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 19 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 19 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 19 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 11 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row19Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 19 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 19 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 19 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 11 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row19Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 19 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 19 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 19 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 11 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row19Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 19 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 19 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 19 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 11 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row19Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 19 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 19 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 19 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 11 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row19Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 19 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 19 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 19 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 11 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row19Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 19 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 19 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 19 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 11 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row19Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 19 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 19 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 19 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 11 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row19Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 19 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 19 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 19 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 11 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row19_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 19 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 19 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row19Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row19Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row19Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row19Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row19Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row19Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row19Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row19Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row19Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row19Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row19_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 19) =
      (rectangularize 62 93 Term6Stage4Data).getD 19 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 19
    ((rectangularize 62 93 Term6Stage4Data).getD 19 [])
  · exact term6Stage4_mulRow_length_le 19
  · rw [getD_rectangularize 62 93 Term6Stage4Data 19 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 19
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row19_coefficients

private theorem term6Stage4Row20Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 20 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 20 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 20 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 12 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row20Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 20 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 20 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 20 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 12 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row20Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 20 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 20 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 20 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 12 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row20Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 20 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 20 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 20 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 12 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row20Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 20 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 20 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 20 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 12 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row20Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 20 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 20 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 20 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 12 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row20Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 20 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 20 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 20 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 12 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row20Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 20 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 20 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 20 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 12 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row20Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 20 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 20 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 20 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 12 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row20Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 20 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 20 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 20 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 12 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row20_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 20 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 20 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row20Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row20Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row20Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row20Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row20Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row20Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row20Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row20Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row20Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row20Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row20_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 20) =
      (rectangularize 62 93 Term6Stage4Data).getD 20 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 20
    ((rectangularize 62 93 Term6Stage4Data).getD 20 [])
  · exact term6Stage4_mulRow_length_le 20
  · rw [getD_rectangularize 62 93 Term6Stage4Data 20 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 20
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row20_coefficients

private theorem term6Stage4Row21Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 21 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 21 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 21 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 13 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row21Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 21 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 21 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 21 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 13 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row21Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 21 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 21 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 21 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 13 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row21Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 21 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 21 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 21 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 13 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row21Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 21 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 21 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 21 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 13 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row21Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 21 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 21 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 21 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 13 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row21Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 21 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 21 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 21 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 13 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row21Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 21 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 21 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 21 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 13 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row21Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 21 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 21 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 21 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 13 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row21Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 21 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 21 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 21 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 13 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row21_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 21 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 21 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row21Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row21Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row21Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row21Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row21Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row21Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row21Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row21Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row21Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row21Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row21_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 21) =
      (rectangularize 62 93 Term6Stage4Data).getD 21 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 21
    ((rectangularize 62 93 Term6Stage4Data).getD 21 [])
  · exact term6Stage4_mulRow_length_le 21
  · rw [getD_rectangularize 62 93 Term6Stage4Data 21 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 21
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row21_coefficients

private theorem term6Stage4Row22Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 22 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 22 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 22 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 14 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row22Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 22 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 22 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 22 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 14 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row22Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 22 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 22 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 22 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 14 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row22Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 22 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 22 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 22 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 14 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row22Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 22 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 22 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 22 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 14 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row22Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 22 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 22 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 22 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 14 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row22Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 22 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 22 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 22 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 14 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row22Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 22 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 22 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 22 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 14 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row22Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 22 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 22 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 22 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 14 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row22Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 22 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 22 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 22 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 14 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row22_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 22 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 22 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row22Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row22Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row22Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row22Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row22Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row22Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row22Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row22Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row22Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row22Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row22_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 22) =
      (rectangularize 62 93 Term6Stage4Data).getD 22 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 22
    ((rectangularize 62 93 Term6Stage4Data).getD 22 [])
  · exact term6Stage4_mulRow_length_le 22
  · rw [getD_rectangularize 62 93 Term6Stage4Data 22 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 22
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row22_coefficients

private theorem term6Stage4Row23Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 23 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 23 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 23 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 15 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row23Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 23 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 23 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 23 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 15 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row23Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 23 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 23 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 23 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 15 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row23Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 23 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 23 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 23 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 15 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row23Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 23 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 23 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 23 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 15 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row23Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 23 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 23 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 23 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 15 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row23Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 23 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 23 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 23 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 15 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row23Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 23 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 23 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 23 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 15 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row23Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 23 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 23 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 23 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 15 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row23Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 23 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 23 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 23 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 15 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row23_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 23 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 23 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row23Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row23Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row23Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row23Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row23Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row23Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row23Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row23Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row23Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row23Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row23_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 23) =
      (rectangularize 62 93 Term6Stage4Data).getD 23 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 23
    ((rectangularize 62 93 Term6Stage4Data).getD 23 [])
  · exact term6Stage4_mulRow_length_le 23
  · rw [getD_rectangularize 62 93 Term6Stage4Data 23 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 23
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row23_coefficients

theorem term6Stage4_rows16To23 (n : ℕ) (hLo : 16 ≤ n) (hHi : n < 24) :
    padOne 93 (mulRow V3Data Term6Stage3Data n) =
      (rectangularize 62 93 Term6Stage4Data).getD n [] := by
  interval_cases n
  · exact term6Stage4Row16_spec
  · exact term6Stage4Row17_spec
  · exact term6Stage4Row18_spec
  · exact term6Stage4Row19_spec
  · exact term6Stage4Row20_spec
  · exact term6Stage4Row21_spec
  · exact term6Stage4Row22_spec
  · exact term6Stage4Row23_spec

end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

