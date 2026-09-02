/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialAssemblyTermSixStageFourSupport
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialWindow
import Mathlib.Tactic.IntervalCases

/-!
# Rows 40 through 47 of the fourth stage of the sixth assembly term
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveDensePolynomialRectangular
open OrderTwentyFiveDensePolynomialRowCertificate

private theorem term6Stage4Row40Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 40 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 40 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 40 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 32 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 24 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 16 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 8 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row40Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 40 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 40 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 40 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 32 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 24 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 16 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 8 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row40Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 40 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 40 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 40 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 32 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 24 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 16 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 8 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row40Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 40 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 40 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 40 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 32 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 24 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 16 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 8 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row40Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 40 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 40 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 40 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 32 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 24 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 16 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 8 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row40Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 40 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 40 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 40 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 32 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 24 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 16 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 8 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row40Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 40 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 40 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 40 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 32 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 24 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 16 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 8 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row40Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 40 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 40 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      40 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 40 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 32 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 24 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 16 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 8 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row40Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 40 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 40 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      40 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 40 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 32 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 24 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 16 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 8 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row40Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 40 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 40 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      40 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 40 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 32 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 24 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 16 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 8 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row40_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 40 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 40 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row40Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row40Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row40Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row40Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row40Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row40Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row40Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row40Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row40Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row40Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row40_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 40) =
      (rectangularize 62 93 Term6Stage4Data).getD 40 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 40
    ((rectangularize 62 93 Term6Stage4Data).getD 40 [])
  · exact term6Stage4_mulRow_length_le 40
  · rw [getD_rectangularize 62 93 Term6Stage4Data 40 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 40
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row40_coefficients

private theorem term6Stage4Row41Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 41 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 41 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 41 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 33 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 25 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 17 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 9 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row41Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 41 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 41 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 41 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 33 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 25 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 17 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 9 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row41Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 41 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 41 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 41 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 33 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 25 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 17 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 9 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row41Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 41 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 41 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 41 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 33 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 25 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 17 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 9 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row41Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 41 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 41 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 41 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 33 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 25 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 17 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 9 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row41Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 41 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 41 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 41 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 33 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 25 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 17 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 9 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row41Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 41 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 41 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 41 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 33 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 25 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 17 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 9 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row41Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 41 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 41 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      41 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 41 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 33 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 25 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 17 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 9 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row41Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 41 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 41 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      41 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 41 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 33 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 25 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 17 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 9 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row41Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 41 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 41 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      41 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 41 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 33 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 25 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 17 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 9 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row41_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 41 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 41 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row41Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row41Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row41Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row41Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row41Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row41Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row41Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row41Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row41Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row41Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row41_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 41) =
      (rectangularize 62 93 Term6Stage4Data).getD 41 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 41
    ((rectangularize 62 93 Term6Stage4Data).getD 41 [])
  · exact term6Stage4_mulRow_length_le 41
  · rw [getD_rectangularize 62 93 Term6Stage4Data 41 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 41
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row41_coefficients

private theorem term6Stage4Row42Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 42 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 42 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 42 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 34 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 26 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 18 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 10 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row42Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 42 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 42 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 42 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 34 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 26 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 18 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 10 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row42Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 42 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 42 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 42 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 34 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 26 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 18 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 10 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row42Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 42 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 42 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 42 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 34 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 26 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 18 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 10 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row42Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 42 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 42 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 42 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 34 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 26 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 18 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 10 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row42Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 42 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 42 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 42 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 34 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 26 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 18 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 10 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row42Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 42 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 42 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 42 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 34 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 26 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 18 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 10 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row42Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 42 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 42 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      42 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 42 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 34 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 26 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 18 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 10 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row42Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 42 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 42 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      42 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 42 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 34 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 26 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 18 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 10 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row42Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 42 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 42 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      42 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 42 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 34 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 26 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 18 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 10 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row42_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 42 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 42 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row42Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row42Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row42Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row42Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row42Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row42Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row42Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row42Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row42Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row42Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row42_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 42) =
      (rectangularize 62 93 Term6Stage4Data).getD 42 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 42
    ((rectangularize 62 93 Term6Stage4Data).getD 42 [])
  · exact term6Stage4_mulRow_length_le 42
  · rw [getD_rectangularize 62 93 Term6Stage4Data 42 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 42
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row42_coefficients

private theorem term6Stage4Row43Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 43 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 43 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 43 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 35 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 27 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 19 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 11 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row43Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 43 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 43 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 43 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 35 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 27 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 19 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 11 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row43Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 43 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 43 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 43 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 35 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 27 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 19 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 11 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row43Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 43 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 43 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 43 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 35 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 27 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 19 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 11 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row43Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 43 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 43 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 43 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 35 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 27 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 19 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 11 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row43Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 43 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 43 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 43 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 35 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 27 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 19 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 11 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row43Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 43 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 43 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 43 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 35 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 27 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 19 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 11 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row43Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 43 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 43 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      43 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 43 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 35 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 27 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 19 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 11 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row43Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 43 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 43 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      43 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 43 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 35 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 27 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 19 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 11 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row43Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 43 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 43 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      43 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 43 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 35 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 27 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 19 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 11 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row43_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 43 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 43 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row43Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row43Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row43Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row43Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row43Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row43Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row43Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row43Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row43Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row43Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row43_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 43) =
      (rectangularize 62 93 Term6Stage4Data).getD 43 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 43
    ((rectangularize 62 93 Term6Stage4Data).getD 43 [])
  · exact term6Stage4_mulRow_length_le 43
  · rw [getD_rectangularize 62 93 Term6Stage4Data 43 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 43
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row43_coefficients

private theorem term6Stage4Row44Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 44 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 44 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 44 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 36 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 28 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 20 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 12 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row44Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 44 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 44 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 44 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 36 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 28 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 20 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 12 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row44Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 44 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 44 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 44 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 36 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 28 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 20 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 12 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row44Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 44 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 44 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 44 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 36 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 28 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 20 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 12 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row44Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 44 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 44 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 44 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 36 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 28 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 20 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 12 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row44Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 44 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 44 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 44 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 36 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 28 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 20 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 12 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row44Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 44 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 44 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 44 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 36 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 28 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 20 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 12 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row44Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 44 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 44 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      44 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 44 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 36 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 28 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 20 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 12 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row44Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 44 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 44 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      44 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 44 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 36 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 28 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 20 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 12 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row44Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 44 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 44 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      44 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 44 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 36 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 28 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 20 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 12 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row44_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 44 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 44 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row44Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row44Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row44Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row44Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row44Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row44Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row44Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row44Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row44Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row44Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row44_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 44) =
      (rectangularize 62 93 Term6Stage4Data).getD 44 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 44
    ((rectangularize 62 93 Term6Stage4Data).getD 44 [])
  · exact term6Stage4_mulRow_length_le 44
  · rw [getD_rectangularize 62 93 Term6Stage4Data 44 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 44
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row44_coefficients

private theorem term6Stage4Row45Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 45 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 45 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 45 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 37 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 29 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 21 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 13 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row45Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 45 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 45 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 45 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 37 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 29 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 21 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 13 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row45Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 45 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 45 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 45 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 37 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 29 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 21 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 13 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row45Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 45 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 45 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 45 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 37 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 29 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 21 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 13 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row45Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 45 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 45 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 45 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 37 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 29 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 21 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 13 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row45Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 45 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 45 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 45 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 37 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 29 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 21 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 13 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row45Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 45 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 45 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 45 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 37 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 29 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 21 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 13 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row45Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 45 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 45 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      45 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 45 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 37 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 29 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 21 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 13 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row45Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 45 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 45 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      45 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 45 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 37 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 29 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 21 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 13 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row45Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 45 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 45 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      45 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 45 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 37 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 29 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 21 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 13 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row45_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 45 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 45 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row45Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row45Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row45Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row45Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row45Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row45Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row45Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row45Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row45Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row45Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row45_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 45) =
      (rectangularize 62 93 Term6Stage4Data).getD 45 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 45
    ((rectangularize 62 93 Term6Stage4Data).getD 45 [])
  · exact term6Stage4_mulRow_length_le 45
  · rw [getD_rectangularize 62 93 Term6Stage4Data 45 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 45
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row45_coefficients

private theorem term6Stage4Row46Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 46 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 46 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 46 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 38 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 30 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 22 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 14 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row46Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 46 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 46 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 46 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 38 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 30 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 22 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 14 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row46Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 46 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 46 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 46 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 38 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 30 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 22 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 14 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row46Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 46 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 46 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 46 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 38 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 30 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 22 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 14 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row46Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 46 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 46 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 46 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 38 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 30 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 22 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 14 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row46Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 46 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 46 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 46 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 38 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 30 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 22 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 14 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row46Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 46 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 46 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 46 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 38 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 30 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 22 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 14 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row46Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 46 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 46 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      46 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 46 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 38 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 30 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 22 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 14 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row46Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 46 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 46 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      46 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 46 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 38 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 30 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 22 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 14 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row46Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 46 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 46 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      46 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 46 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 38 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 30 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 22 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 14 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row46_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 46 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 46 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row46Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row46Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row46Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row46Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row46Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row46Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row46Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row46Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row46Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row46Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row46_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 46) =
      (rectangularize 62 93 Term6Stage4Data).getD 46 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 46
    ((rectangularize 62 93 Term6Stage4Data).getD 46 [])
  · exact term6Stage4_mulRow_length_le 46
  · rw [getD_rectangularize 62 93 Term6Stage4Data 46 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 46
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row46_coefficients

private theorem term6Stage4Row47Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 47 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 47 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 47 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 39 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 31 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 23 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 15 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row47Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 47 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 47 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 47 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 39 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 31 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 23 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 15 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row47Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 47 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 47 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 47 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 39 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 31 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 23 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 15 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row47Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 47 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 47 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 47 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 39 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 31 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 23 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 15 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row47Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 47 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 47 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 47 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 39 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 31 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 23 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 15 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row47Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 47 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 47 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 47 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 39 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 31 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 23 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 15 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row47Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 47 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 47 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 47 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 39 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 31 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 23 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 15 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row47Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 47 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 47 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      47 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 47 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 39 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 31 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 23 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 15 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row47Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 47 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 47 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      47 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 47 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 39 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 31 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 23 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 15 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row47Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 47 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 47 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      47 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 47 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 39 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 31 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 23 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 15 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row47_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 47 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 47 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row47Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row47Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row47Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row47Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row47Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row47Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row47Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row47Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row47Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row47Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row47_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 47) =
      (rectangularize 62 93 Term6Stage4Data).getD 47 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 47
    ((rectangularize 62 93 Term6Stage4Data).getD 47 [])
  · exact term6Stage4_mulRow_length_le 47
  · rw [getD_rectangularize 62 93 Term6Stage4Data 47 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 47
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row47_coefficients

theorem term6Stage4_rows40To47 (n : ℕ) (hLo : 40 ≤ n) (hHi : n < 48) :
    padOne 93 (mulRow V3Data Term6Stage3Data n) =
      (rectangularize 62 93 Term6Stage4Data).getD n [] := by
  interval_cases n
  · exact term6Stage4Row40_spec
  · exact term6Stage4Row41_spec
  · exact term6Stage4Row42_spec
  · exact term6Stage4Row43_spec
  · exact term6Stage4Row44_spec
  · exact term6Stage4Row45_spec
  · exact term6Stage4Row46_spec
  · exact term6Stage4Row47_spec

end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

