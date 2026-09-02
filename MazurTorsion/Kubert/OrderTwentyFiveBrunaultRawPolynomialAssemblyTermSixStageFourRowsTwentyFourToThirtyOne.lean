/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialAssemblyTermSixStageFourSupport
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialWindow
import Mathlib.Tactic.IntervalCases

/-!
# Rows 24 through 31 of the fourth stage of the sixth assembly term
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveDensePolynomialRectangular
open OrderTwentyFiveDensePolynomialRowCertificate

private theorem term6Stage4Row24Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 24 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 24 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 24 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 16 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 8 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row24Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 24 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 24 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 24 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 16 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 8 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row24Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 24 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 24 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 24 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 16 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 8 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row24Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 24 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 24 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 24 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 16 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 8 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row24Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 24 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 24 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 24 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 16 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 8 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row24Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 24 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 24 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 24 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 16 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 8 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row24Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 24 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 24 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 24 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 16 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 8 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row24Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 24 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 24 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 24 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 16 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 8 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row24Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 24 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 24 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 24 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 16 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 8 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row24Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 24 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 24 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 24 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 16 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 8 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row24_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 24 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 24 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row24Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row24Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row24Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row24Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row24Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row24Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row24Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row24Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row24Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row24Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row24_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 24) =
      (rectangularize 62 93 Term6Stage4Data).getD 24 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 24
    ((rectangularize 62 93 Term6Stage4Data).getD 24 [])
  · exact term6Stage4_mulRow_length_le 24
  · rw [getD_rectangularize 62 93 Term6Stage4Data 24 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 24
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row24_coefficients

private theorem term6Stage4Row25Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 25 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 25 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 25 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 17 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 9 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row25Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 25 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 25 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 25 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 17 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 9 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row25Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 25 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 25 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 25 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 17 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 9 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row25Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 25 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 25 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 25 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 17 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 9 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row25Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 25 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 25 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 25 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 17 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 9 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row25Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 25 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 25 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 25 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 17 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 9 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row25Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 25 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 25 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 25 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 17 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 9 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row25Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 25 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 25 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 25 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 17 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 9 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row25Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 25 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 25 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 25 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 17 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 9 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row25Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 25 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 25 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 25 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 17 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 9 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row25_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 25 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 25 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row25Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row25Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row25Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row25Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row25Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row25Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row25Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row25Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row25Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row25Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row25_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 25) =
      (rectangularize 62 93 Term6Stage4Data).getD 25 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 25
    ((rectangularize 62 93 Term6Stage4Data).getD 25 [])
  · exact term6Stage4_mulRow_length_le 25
  · rw [getD_rectangularize 62 93 Term6Stage4Data 25 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 25
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row25_coefficients

private theorem term6Stage4Row26Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 26 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 26 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 26 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 18 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 10 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row26Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 26 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 26 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 26 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 18 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 10 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row26Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 26 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 26 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 26 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 18 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 10 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row26Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 26 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 26 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 26 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 18 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 10 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row26Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 26 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 26 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 26 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 18 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 10 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row26Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 26 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 26 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 26 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 18 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 10 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row26Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 26 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 26 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 26 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 18 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 10 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row26Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 26 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 26 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 26 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 18 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 10 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row26Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 26 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 26 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 26 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 18 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 10 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row26Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 26 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 26 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 26 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 18 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 10 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row26_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 26 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 26 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row26Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row26Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row26Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row26Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row26Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row26Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row26Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row26Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row26Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row26Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row26_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 26) =
      (rectangularize 62 93 Term6Stage4Data).getD 26 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 26
    ((rectangularize 62 93 Term6Stage4Data).getD 26 [])
  · exact term6Stage4_mulRow_length_le 26
  · rw [getD_rectangularize 62 93 Term6Stage4Data 26 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 26
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row26_coefficients

private theorem term6Stage4Row27Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 27 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 27 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 27 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 19 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 11 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row27Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 27 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 27 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 27 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 19 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 11 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row27Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 27 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 27 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 27 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 19 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 11 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row27Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 27 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 27 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 27 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 19 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 11 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row27Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 27 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 27 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 27 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 19 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 11 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row27Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 27 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 27 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 27 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 19 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 11 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row27Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 27 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 27 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 27 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 19 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 11 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row27Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 27 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 27 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 27 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 19 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 11 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row27Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 27 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 27 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 27 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 19 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 11 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row27Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 27 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 27 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 27 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 19 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 11 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row27_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 27 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 27 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row27Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row27Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row27Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row27Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row27Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row27Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row27Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row27Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row27Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row27Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row27_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 27) =
      (rectangularize 62 93 Term6Stage4Data).getD 27 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 27
    ((rectangularize 62 93 Term6Stage4Data).getD 27 [])
  · exact term6Stage4_mulRow_length_le 27
  · rw [getD_rectangularize 62 93 Term6Stage4Data 27 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 27
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row27_coefficients

private theorem term6Stage4Row28Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 28 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 28 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 28 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 20 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 12 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row28Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 28 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 28 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 28 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 20 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 12 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row28Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 28 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 28 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 28 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 20 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 12 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row28Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 28 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 28 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 28 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 20 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 12 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row28Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 28 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 28 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 28 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 20 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 12 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row28Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 28 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 28 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 28 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 20 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 12 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row28Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 28 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 28 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 28 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 20 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 12 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row28Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 28 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 28 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 28 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 20 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 12 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row28Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 28 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 28 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 28 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 20 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 12 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row28Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 28 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 28 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 28 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 20 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 12 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row28_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 28 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 28 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row28Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row28Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row28Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row28Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row28Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row28Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row28Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row28Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row28Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row28Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row28_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 28) =
      (rectangularize 62 93 Term6Stage4Data).getD 28 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 28
    ((rectangularize 62 93 Term6Stage4Data).getD 28 [])
  · exact term6Stage4_mulRow_length_le 28
  · rw [getD_rectangularize 62 93 Term6Stage4Data 28 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 28
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row28_coefficients

private theorem term6Stage4Row29Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 29 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 29 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 29 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 21 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 13 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row29Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 29 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 29 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 29 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 21 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 13 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row29Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 29 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 29 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 29 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 21 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 13 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row29Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 29 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 29 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 29 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 21 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 13 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row29Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 29 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 29 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 29 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 21 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 13 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row29Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 29 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 29 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 29 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 21 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 13 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row29Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 29 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 29 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 29 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 21 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 13 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row29Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 29 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 29 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 29 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 21 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 13 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row29Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 29 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 29 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 29 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 21 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 13 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row29Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 29 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 29 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      29 (j - 66) 66 term6Stage4_v3Data_innerSupport,
    mulCoeffTwo_take_drop_outer_split V3Data
      (dropInner (j - 66) Term6Stage3Data)
    8 29 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8)
      (dropInner (j - 66) Term6Stage3Data)
    8 21 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8)
      (dropInner (j - 66) Term6Stage3Data)
    8 13 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row29_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 29 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 29 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row29Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row29Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row29Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row29Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row29Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row29Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row29Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row29Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row29Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row29Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row29_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 29) =
      (rectangularize 62 93 Term6Stage4Data).getD 29 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 29
    ((rectangularize 62 93 Term6Stage4Data).getD 29 [])
  · exact term6Stage4_mulRow_length_le 29
  · rw [getD_rectangularize 62 93 Term6Stage4Data 29 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 29
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row29_coefficients

private theorem term6Stage4Row30Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 30 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 30 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 30 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 22 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 14 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row30Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 30 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 30 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 30 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 22 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 14 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row30Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 30 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 30 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 30 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 22 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 14 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row30Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 30 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 30 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 30 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 22 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 14 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row30Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 30 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 30 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 30 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 22 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 14 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row30Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 30 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 30 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 30 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 22 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 14 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row30Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 30 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 30 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 30 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 22 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 14 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row30Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 30 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 30 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 30 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 22 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 14 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row30Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 30 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 30 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 30 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 22 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 14 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row30Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 30 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 30 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      30 (j - 66) 66 term6Stage4_v3Data_innerSupport,
    mulCoeffTwo_take_drop_outer_split V3Data
      (dropInner (j - 66) Term6Stage3Data)
    8 30 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8)
      (dropInner (j - 66) Term6Stage3Data)
    8 22 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8)
      (dropInner (j - 66) Term6Stage3Data)
    8 14 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row30_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 30 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 30 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row30Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row30Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row30Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row30Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row30Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row30Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row30Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row30Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row30Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row30Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row30_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 30) =
      (rectangularize 62 93 Term6Stage4Data).getD 30 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 30
    ((rectangularize 62 93 Term6Stage4Data).getD 30 [])
  · exact term6Stage4_mulRow_length_le 30
  · rw [getD_rectangularize 62 93 Term6Stage4Data 30 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 30
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row30_coefficients

private theorem term6Stage4Row31Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 31 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 31 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 31 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 23 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 15 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row31Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 31 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 31 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 31 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 23 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 15 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row31Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 31 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 31 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 31 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 23 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 15 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row31Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 31 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 31 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 31 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 23 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 15 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row31Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 31 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 31 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 31 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 23 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 15 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row31Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 31 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 31 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 31 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 23 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 15 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row31Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 31 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 31 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 31 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 23 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 15 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row31Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 31 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 31 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 31 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 23 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 15 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row31Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 31 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 31 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 31 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 23 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 15 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row31Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 31 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 31 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      31 (j - 66) 66 term6Stage4_v3Data_innerSupport,
    mulCoeffTwo_take_drop_outer_split V3Data
      (dropInner (j - 66) Term6Stage3Data)
    8 31 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8)
      (dropInner (j - 66) Term6Stage3Data)
    8 23 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8)
      (dropInner (j - 66) Term6Stage3Data)
    8 15 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row31_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 31 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 31 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row31Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row31Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row31Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row31Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row31Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row31Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row31Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row31Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row31Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row31Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row31_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 31) =
      (rectangularize 62 93 Term6Stage4Data).getD 31 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 31
    ((rectangularize 62 93 Term6Stage4Data).getD 31 [])
  · exact term6Stage4_mulRow_length_le 31
  · rw [getD_rectangularize 62 93 Term6Stage4Data 31 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 31
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row31_coefficients

theorem term6Stage4_rows24To31 (n : ℕ) (hLo : 24 ≤ n) (hHi : n < 32) :
    padOne 93 (mulRow V3Data Term6Stage3Data n) =
      (rectangularize 62 93 Term6Stage4Data).getD n [] := by
  interval_cases n
  · exact term6Stage4Row24_spec
  · exact term6Stage4Row25_spec
  · exact term6Stage4Row26_spec
  · exact term6Stage4Row27_spec
  · exact term6Stage4Row28_spec
  · exact term6Stage4Row29_spec
  · exact term6Stage4Row30_spec
  · exact term6Stage4Row31_spec

end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
