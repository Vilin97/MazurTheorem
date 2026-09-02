/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialAssemblyTermSixStageFourSupport
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialWindow
import Mathlib.Tactic.IntervalCases

/-!
# Rows 32 through 39 of the fourth stage of the sixth assembly term
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveDensePolynomialRectangular
open OrderTwentyFiveDensePolynomialRowCertificate

private theorem term6Stage4Row32Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 32 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 32 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 32 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 24 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 16 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 8 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row32Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 32 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 32 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 32 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 24 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 16 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 8 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row32Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 32 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 32 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 32 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 24 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 16 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 8 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row32Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 32 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 32 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 32 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 24 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 16 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 8 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row32Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 32 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 32 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 32 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 24 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 16 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 8 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row32Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 32 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 32 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 32 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 24 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 16 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 8 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row32Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 32 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 32 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 32 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 24 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 16 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 8 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row32Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 32 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 32 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      32 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 32 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 24 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 16 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 8 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row32Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 32 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 32 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      32 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 32 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 24 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 16 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 8 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row32Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 32 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 32 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      32 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 32 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 24 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 16 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 8 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row32_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 32 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 32 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row32Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row32Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row32Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row32Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row32Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row32Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row32Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row32Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row32Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row32Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row32_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 32) =
      (rectangularize 62 93 Term6Stage4Data).getD 32 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 32
    ((rectangularize 62 93 Term6Stage4Data).getD 32 [])
  · exact term6Stage4_mulRow_length_le 32
  · rw [getD_rectangularize 62 93 Term6Stage4Data 32 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 32
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row32_coefficients

private theorem term6Stage4Row33Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 33 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 33 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 33 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 25 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 17 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 9 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row33Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 33 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 33 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 33 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 25 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 17 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 9 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row33Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 33 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 33 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 33 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 25 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 17 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 9 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row33Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 33 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 33 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 33 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 25 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 17 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 9 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row33Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 33 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 33 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 33 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 25 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 17 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 9 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row33Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 33 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 33 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 33 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 25 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 17 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 9 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row33Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 33 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 33 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 33 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 25 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 17 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 9 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row33Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 33 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 33 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      33 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 33 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 25 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 17 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 9 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row33Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 33 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 33 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      33 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 33 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 25 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 17 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 9 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row33Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 33 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 33 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      33 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 33 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 25 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 17 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 9 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row33_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 33 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 33 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row33Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row33Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row33Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row33Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row33Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row33Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row33Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row33Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row33Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row33Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row33_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 33) =
      (rectangularize 62 93 Term6Stage4Data).getD 33 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 33
    ((rectangularize 62 93 Term6Stage4Data).getD 33 [])
  · exact term6Stage4_mulRow_length_le 33
  · rw [getD_rectangularize 62 93 Term6Stage4Data 33 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 33
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row33_coefficients

private theorem term6Stage4Row34Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 34 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 34 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 34 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 26 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 18 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 10 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row34Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 34 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 34 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 34 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 26 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 18 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 10 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row34Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 34 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 34 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 34 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 26 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 18 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 10 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row34Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 34 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 34 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 34 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 26 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 18 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 10 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row34Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 34 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 34 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 34 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 26 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 18 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 10 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row34Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 34 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 34 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 34 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 26 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 18 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 10 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row34Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 34 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 34 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 34 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 26 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 18 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 10 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row34Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 34 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 34 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      34 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 34 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 26 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 18 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 10 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row34Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 34 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 34 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      34 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 34 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 26 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 18 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 10 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row34Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 34 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 34 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      34 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 34 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 26 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 18 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 10 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row34_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 34 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 34 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row34Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row34Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row34Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row34Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row34Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row34Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row34Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row34Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row34Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row34Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row34_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 34) =
      (rectangularize 62 93 Term6Stage4Data).getD 34 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 34
    ((rectangularize 62 93 Term6Stage4Data).getD 34 [])
  · exact term6Stage4_mulRow_length_le 34
  · rw [getD_rectangularize 62 93 Term6Stage4Data 34 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 34
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row34_coefficients

private theorem term6Stage4Row35Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 35 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 35 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 35 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 27 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 19 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 11 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row35Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 35 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 35 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 35 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 27 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 19 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 11 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row35Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 35 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 35 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 35 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 27 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 19 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 11 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row35Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 35 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 35 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 35 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 27 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 19 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 11 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row35Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 35 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 35 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 35 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 27 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 19 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 11 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row35Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 35 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 35 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 35 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 27 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 19 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 11 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row35Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 35 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 35 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 35 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 27 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 19 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 11 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row35Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 35 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 35 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      35 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 35 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 27 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 19 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 11 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row35Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 35 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 35 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      35 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 35 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 27 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 19 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 11 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row35Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 35 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 35 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      35 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 35 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 27 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 19 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 11 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row35_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 35 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 35 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row35Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row35Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row35Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row35Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row35Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row35Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row35Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row35Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row35Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row35Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row35_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 35) =
      (rectangularize 62 93 Term6Stage4Data).getD 35 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 35
    ((rectangularize 62 93 Term6Stage4Data).getD 35 [])
  · exact term6Stage4_mulRow_length_le 35
  · rw [getD_rectangularize 62 93 Term6Stage4Data 35 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 35
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row35_coefficients

private theorem term6Stage4Row36Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 36 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 36 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 36 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 28 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 20 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 12 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row36Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 36 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 36 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 36 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 28 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 20 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 12 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row36Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 36 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 36 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 36 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 28 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 20 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 12 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row36Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 36 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 36 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 36 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 28 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 20 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 12 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row36Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 36 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 36 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 36 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 28 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 20 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 12 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row36Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 36 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 36 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 36 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 28 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 20 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 12 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row36Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 36 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 36 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 36 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 28 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 20 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 12 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row36Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 36 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 36 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      36 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 36 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 28 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 20 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 12 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row36Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 36 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 36 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      36 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 36 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 28 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 20 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 12 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row36Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 36 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 36 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      36 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 36 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 28 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 20 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 12 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row36_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 36 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 36 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row36Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row36Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row36Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row36Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row36Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row36Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row36Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row36Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row36Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row36Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row36_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 36) =
      (rectangularize 62 93 Term6Stage4Data).getD 36 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 36
    ((rectangularize 62 93 Term6Stage4Data).getD 36 [])
  · exact term6Stage4_mulRow_length_le 36
  · rw [getD_rectangularize 62 93 Term6Stage4Data 36 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 36
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row36_coefficients

private theorem term6Stage4Row37Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 37 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 37 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 37 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 29 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 21 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 13 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row37Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 37 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 37 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 37 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 29 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 21 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 13 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row37Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 37 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 37 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 37 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 29 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 21 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 13 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row37Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 37 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 37 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 37 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 29 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 21 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 13 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row37Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 37 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 37 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 37 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 29 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 21 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 13 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row37Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 37 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 37 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 37 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 29 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 21 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 13 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row37Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 37 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 37 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 37 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 29 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 21 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 13 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row37Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 37 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 37 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      37 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 37 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 29 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 21 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 13 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row37Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 37 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 37 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      37 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 37 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 29 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 21 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 13 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row37Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 37 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 37 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      37 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 37 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 29 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 21 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 13 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row37_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 37 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 37 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row37Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row37Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row37Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row37Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row37Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row37Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row37Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row37Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row37Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row37Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row37_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 37) =
      (rectangularize 62 93 Term6Stage4Data).getD 37 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 37
    ((rectangularize 62 93 Term6Stage4Data).getD 37 [])
  · exact term6Stage4_mulRow_length_le 37
  · rw [getD_rectangularize 62 93 Term6Stage4Data 37 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 37
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row37_coefficients

private theorem term6Stage4Row38Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 38 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 38 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 38 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 30 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 22 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 14 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row38Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 38 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 38 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 38 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 30 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 22 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 14 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row38Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 38 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 38 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 38 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 30 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 22 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 14 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row38Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 38 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 38 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 38 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 30 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 22 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 14 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row38Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 38 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 38 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 38 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 30 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 22 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 14 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row38Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 38 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 38 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 38 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 30 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 22 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 14 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row38Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 38 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 38 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 38 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 30 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 22 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 14 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row38Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 38 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 38 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      38 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 38 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 30 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 22 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 14 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row38Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 38 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 38 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      38 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 38 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 30 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 22 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 14 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row38Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 38 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 38 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      38 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 38 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 30 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 22 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 14 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row38_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 38 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 38 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row38Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row38Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row38Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row38Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row38Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row38Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row38Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row38Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row38Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row38Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row38_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 38) =
      (rectangularize 62 93 Term6Stage4Data).getD 38 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 38
    ((rectangularize 62 93 Term6Stage4Data).getD 38 [])
  · exact term6Stage4_mulRow_length_le 38
  · rw [getD_rectangularize 62 93 Term6Stage4Data 38 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 38
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row38_coefficients

private theorem term6Stage4Row39Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 39 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 39 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 39 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 31 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 23 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 15 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row39Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 39 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 39 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 39 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 31 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 23 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 15 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row39Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 39 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 39 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 39 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 31 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 23 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 15 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row39Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 39 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 39 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 39 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 31 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 23 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 15 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row39Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 39 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 39 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 39 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 31 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 23 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 15 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row39Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 39 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 39 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 39 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 31 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 23 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 15 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row39Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 39 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 39 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 39 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 31 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 23 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 15 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row39Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 39 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 39 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      39 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 39 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 31 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 23 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 15 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row39Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 39 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 39 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      39 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 39 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 31 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 23 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 15 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row39Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 39 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 39 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      39 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 39 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 31 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 23 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 15 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row39_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 39 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 39 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row39Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row39Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row39Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row39Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row39Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row39Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row39Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row39Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row39Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row39Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row39_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 39) =
      (rectangularize 62 93 Term6Stage4Data).getD 39 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 39
    ((rectangularize 62 93 Term6Stage4Data).getD 39 [])
  · exact term6Stage4_mulRow_length_le 39
  · rw [getD_rectangularize 62 93 Term6Stage4Data 39 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 39
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row39_coefficients

theorem term6Stage4_rows32To39 (n : ℕ) (hLo : 32 ≤ n) (hHi : n < 40) :
    padOne 93 (mulRow V3Data Term6Stage3Data n) =
      (rectangularize 62 93 Term6Stage4Data).getD n [] := by
  interval_cases n
  · exact term6Stage4Row32_spec
  · exact term6Stage4Row33_spec
  · exact term6Stage4Row34_spec
  · exact term6Stage4Row35_spec
  · exact term6Stage4Row36_spec
  · exact term6Stage4Row37_spec
  · exact term6Stage4Row38_spec
  · exact term6Stage4Row39_spec

end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

