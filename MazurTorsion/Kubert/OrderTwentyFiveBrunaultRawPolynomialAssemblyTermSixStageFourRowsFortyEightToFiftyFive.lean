/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialAssemblyTermSixStageFourSupport
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialWindow
import Mathlib.Tactic.IntervalCases

/-!
# Rows 48 through 55 of the fourth stage of the sixth assembly term
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveDensePolynomialRectangular
open OrderTwentyFiveDensePolynomialRowCertificate

private theorem term6Stage4Row48Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 48 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 48 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 48 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 40 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 32 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 24 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 16 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row48Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 48 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 48 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 48 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 40 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 32 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 24 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 16 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row48Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 48 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 48 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 48 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 40 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 32 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 24 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 16 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row48Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 48 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 48 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 48 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 40 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 32 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 24 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 16 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row48Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 48 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 48 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 48 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 40 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 32 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 24 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 16 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row48Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 48 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 48 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 48 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 40 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 32 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 24 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 16 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row48Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 48 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 48 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 48 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 40 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 32 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 24 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 16 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row48Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 48 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 48 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      48 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 48 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 40 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 32 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 24 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 16 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row48Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 48 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 48 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      48 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 48 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 40 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 32 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 24 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 16 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row48Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 48 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 48 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      48 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 48 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 40 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 32 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 24 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 16 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row48_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 48 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 48 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row48Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row48Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row48Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row48Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row48Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row48Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row48Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row48Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row48Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row48Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row48_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 48) =
      (rectangularize 62 93 Term6Stage4Data).getD 48 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 48
    ((rectangularize 62 93 Term6Stage4Data).getD 48 [])
  · exact term6Stage4_mulRow_length_le 48
  · rw [getD_rectangularize 62 93 Term6Stage4Data 48 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 48
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row48_coefficients

private theorem term6Stage4Row49Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 49 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 49 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 49 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 41 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 33 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 25 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 17 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row49Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 49 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 49 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 49 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 41 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 33 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 25 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 17 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row49Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 49 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 49 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 49 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 41 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 33 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 25 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 17 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row49Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 49 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 49 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 49 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 41 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 33 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 25 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 17 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row49Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 49 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 49 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 49 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 41 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 33 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 25 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 17 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row49Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 49 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 49 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 49 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 41 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 33 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 25 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 17 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row49Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 49 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 49 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 49 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 41 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 33 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 25 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 17 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row49Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 49 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 49 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      49 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 49 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 41 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 33 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 25 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 17 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row49Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 49 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 49 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      49 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 49 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 41 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 33 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 25 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 17 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row49Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 49 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 49 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      49 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 49 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 41 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 33 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 25 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 17 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row49_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 49 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 49 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row49Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row49Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row49Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row49Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row49Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row49Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row49Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row49Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row49Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row49Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row49_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 49) =
      (rectangularize 62 93 Term6Stage4Data).getD 49 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 49
    ((rectangularize 62 93 Term6Stage4Data).getD 49 [])
  · exact term6Stage4_mulRow_length_le 49
  · rw [getD_rectangularize 62 93 Term6Stage4Data 49 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 49
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row49_coefficients

private theorem term6Stage4Row50Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 50 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 50 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 50 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 42 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 34 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 26 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 18 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row50Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 50 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 50 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 50 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 42 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 34 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 26 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 18 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row50Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 50 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 50 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 50 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 42 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 34 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 26 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 18 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row50Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 50 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 50 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 50 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 42 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 34 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 26 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 18 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row50Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 50 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 50 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 50 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 42 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 34 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 26 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 18 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row50Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 50 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 50 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 50 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 42 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 34 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 26 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 18 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row50Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 50 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 50 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 50 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 42 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 34 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 26 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 18 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row50Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 50 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 50 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      50 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 50 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 42 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 34 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 26 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 18 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row50Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 50 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 50 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      50 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 50 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 42 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 34 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 26 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 18 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row50Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 50 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 50 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      50 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 50 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 42 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 34 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 26 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 18 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row50_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 50 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 50 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row50Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row50Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row50Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row50Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row50Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row50Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row50Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row50Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row50Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row50Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row50_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 50) =
      (rectangularize 62 93 Term6Stage4Data).getD 50 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 50
    ((rectangularize 62 93 Term6Stage4Data).getD 50 [])
  · exact term6Stage4_mulRow_length_le 50
  · rw [getD_rectangularize 62 93 Term6Stage4Data 50 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 50
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row50_coefficients

private theorem term6Stage4Row51Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 51 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 51 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 51 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 43 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 35 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 27 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 19 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row51Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 51 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 51 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 51 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 43 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 35 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 27 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 19 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row51Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 51 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 51 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 51 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 43 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 35 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 27 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 19 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row51Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 51 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 51 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 51 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 43 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 35 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 27 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 19 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row51Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 51 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 51 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 51 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 43 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 35 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 27 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 19 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row51Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 51 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 51 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 51 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 43 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 35 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 27 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 19 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row51Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 51 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 51 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 51 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 43 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 35 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 27 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 19 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row51Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 51 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 51 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      51 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 51 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 43 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 35 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 27 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 19 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row51Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 51 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 51 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      51 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 51 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 43 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 35 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 27 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 19 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row51Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 51 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 51 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      51 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 51 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 43 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 35 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 27 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 19 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row51_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 51 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 51 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row51Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row51Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row51Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row51Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row51Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row51Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row51Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row51Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row51Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row51Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row51_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 51) =
      (rectangularize 62 93 Term6Stage4Data).getD 51 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 51
    ((rectangularize 62 93 Term6Stage4Data).getD 51 [])
  · exact term6Stage4_mulRow_length_le 51
  · rw [getD_rectangularize 62 93 Term6Stage4Data 51 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 51
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row51_coefficients

private theorem term6Stage4Row52Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 52 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 52 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 52 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 44 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 36 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 28 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 20 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row52Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 52 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 52 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 52 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 44 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 36 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 28 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 20 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row52Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 52 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 52 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 52 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 44 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 36 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 28 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 20 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row52Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 52 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 52 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 52 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 44 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 36 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 28 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 20 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row52Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 52 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 52 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 52 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 44 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 36 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 28 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 20 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row52Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 52 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 52 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 52 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 44 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 36 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 28 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 20 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row52Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 52 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 52 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 52 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 44 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 36 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 28 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 20 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row52Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 52 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 52 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      52 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 52 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 44 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 36 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 28 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 20 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row52Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 52 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 52 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      52 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 52 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 44 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 36 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 28 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 20 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row52Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 52 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 52 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      52 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 52 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 44 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 36 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 28 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 20 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row52_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 52 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 52 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row52Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row52Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row52Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row52Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row52Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row52Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row52Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row52Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row52Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row52Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row52_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 52) =
      (rectangularize 62 93 Term6Stage4Data).getD 52 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 52
    ((rectangularize 62 93 Term6Stage4Data).getD 52 [])
  · exact term6Stage4_mulRow_length_le 52
  · rw [getD_rectangularize 62 93 Term6Stage4Data 52 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 52
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row52_coefficients

private theorem term6Stage4Row53Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 53 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 53 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 53 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 45 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 37 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 29 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 21 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row53Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 53 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 53 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 53 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 45 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 37 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 29 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 21 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row53Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 53 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 53 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 53 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 45 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 37 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 29 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 21 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row53Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 53 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 53 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 53 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 45 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 37 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 29 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 21 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row53Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 53 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 53 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 53 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 45 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 37 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 29 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 21 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row53Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 53 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 53 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 53 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 45 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 37 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 29 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 21 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row53Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 53 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 53 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 53 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 45 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 37 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 29 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 21 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row53Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 53 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 53 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      53 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 53 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 45 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 37 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 29 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 21 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row53Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 53 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 53 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      53 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 53 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 45 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 37 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 29 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 21 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row53Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 53 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 53 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      53 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 53 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 45 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 37 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 29 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 21 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row53_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 53 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 53 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row53Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row53Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row53Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row53Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row53Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row53Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row53Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row53Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row53Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row53Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row53_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 53) =
      (rectangularize 62 93 Term6Stage4Data).getD 53 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 53
    ((rectangularize 62 93 Term6Stage4Data).getD 53 [])
  · exact term6Stage4_mulRow_length_le 53
  · rw [getD_rectangularize 62 93 Term6Stage4Data 53 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 53
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row53_coefficients

private theorem term6Stage4Row54Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 54 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 54 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 54 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 46 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 38 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 30 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 22 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row54Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 54 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 54 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 54 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 46 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 38 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 30 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 22 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row54Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 54 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 54 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 54 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 46 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 38 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 30 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 22 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row54Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 54 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 54 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 54 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 46 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 38 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 30 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 22 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row54Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 54 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 54 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 54 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 46 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 38 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 30 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 22 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row54Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 54 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 54 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 54 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 46 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 38 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 30 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 22 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row54Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 54 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 54 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 54 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 46 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 38 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 30 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 22 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row54Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 54 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 54 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      54 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 54 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 46 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 38 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 30 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 22 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row54Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 54 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 54 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      54 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 54 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 46 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 38 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 30 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 22 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row54Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 54 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 54 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      54 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 54 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 46 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 38 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 30 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 22 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row54_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 54 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 54 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row54Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row54Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row54Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row54Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row54Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row54Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row54Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row54Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row54Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row54Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row54_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 54) =
      (rectangularize 62 93 Term6Stage4Data).getD 54 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 54
    ((rectangularize 62 93 Term6Stage4Data).getD 54 [])
  · exact term6Stage4_mulRow_length_le 54
  · rw [getD_rectangularize 62 93 Term6Stage4Data 54 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 54
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row54_coefficients

private theorem term6Stage4Row55Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 55 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 55 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 55 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 47 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 39 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 31 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 23 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row55Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 55 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 55 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 55 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 47 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 39 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 31 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 23 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row55Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 55 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 55 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 55 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 47 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 39 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 31 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 23 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row55Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 55 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 55 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 55 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 47 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 39 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 31 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 23 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row55Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 55 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 55 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 55 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 47 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 39 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 31 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 23 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row55Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 55 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 55 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 55 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 47 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 39 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 31 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 23 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row55Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 55 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 55 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 55 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 47 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 39 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 31 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 23 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row55Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 55 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 55 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      55 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 55 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 47 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 39 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 31 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 23 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row55Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 55 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 55 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      55 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 55 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 47 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 39 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 31 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 23 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row55Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 55 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 55 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      55 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 55 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 47 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 39 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 31 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 23 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row55_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 55 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 55 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row55Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row55Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row55Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row55Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row55Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row55Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row55Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row55Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row55Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row55Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row55_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 55) =
      (rectangularize 62 93 Term6Stage4Data).getD 55 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 55
    ((rectangularize 62 93 Term6Stage4Data).getD 55 [])
  · exact term6Stage4_mulRow_length_le 55
  · rw [getD_rectangularize 62 93 Term6Stage4Data 55 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 55
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row55_coefficients

theorem term6Stage4_rows48To55 (n : ℕ) (hLo : 48 ≤ n) (hHi : n < 56) :
    padOne 93 (mulRow V3Data Term6Stage3Data n) =
      (rectangularize 62 93 Term6Stage4Data).getD n [] := by
  interval_cases n
  · exact term6Stage4Row48_spec
  · exact term6Stage4Row49_spec
  · exact term6Stage4Row50_spec
  · exact term6Stage4Row51_spec
  · exact term6Stage4Row52_spec
  · exact term6Stage4Row53_spec
  · exact term6Stage4Row54_spec
  · exact term6Stage4Row55_spec

end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

