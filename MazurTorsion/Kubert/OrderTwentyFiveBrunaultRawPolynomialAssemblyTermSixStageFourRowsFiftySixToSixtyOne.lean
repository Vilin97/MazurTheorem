/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialAssemblyTermSixStageFourSupport
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialWindow
import Mathlib.Tactic.IntervalCases

/-!
# Rows 56 through 61 of the fourth stage of the sixth assembly term
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveDensePolynomialRectangular
open OrderTwentyFiveDensePolynomialRowCertificate

private theorem term6Stage4Row56Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 56 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 56 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 56 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 48 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 40 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 32 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 24 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row56Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 56 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 56 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 56 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 48 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 40 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 32 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 24 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row56Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 56 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 56 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 56 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 48 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 40 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 32 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 24 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row56Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 56 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 56 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 56 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 48 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 40 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 32 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 24 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row56Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 56 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 56 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 56 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 48 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 40 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 32 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 24 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row56Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 56 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 56 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 56 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 48 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 40 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 32 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 24 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row56Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 56 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 56 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 56 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 48 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 40 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 32 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 24 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row56Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 56 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 56 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      56 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 56 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 48 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 40 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 32 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 24 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row56Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 56 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 56 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      56 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 56 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 48 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 40 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 32 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 24 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row56Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 56 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 56 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      56 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 56 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 48 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 40 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 32 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 24 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row56_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 56 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 56 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row56Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row56Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row56Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row56Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row56Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row56Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row56Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row56Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row56Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row56Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row56_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 56) =
      (rectangularize 62 93 Term6Stage4Data).getD 56 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 56
    ((rectangularize 62 93 Term6Stage4Data).getD 56 [])
  · exact term6Stage4_mulRow_length_le 56
  · rw [getD_rectangularize 62 93 Term6Stage4Data 56 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 56
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row56_coefficients

private theorem term6Stage4Row57Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 57 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 57 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 57 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 49 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 41 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 33 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 25 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row57Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 57 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 57 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 57 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 49 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 41 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 33 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 25 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row57Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 57 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 57 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 57 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 49 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 41 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 33 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 25 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row57Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 57 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 57 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 57 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 49 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 41 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 33 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 25 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row57Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 57 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 57 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 57 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 49 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 41 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 33 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 25 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row57Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 57 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 57 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 57 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 49 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 41 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 33 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 25 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row57Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 57 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 57 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 57 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 49 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 41 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 33 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 25 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row57Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 57 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 57 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      57 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 57 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 49 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 41 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 33 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 25 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row57Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 57 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 57 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      57 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 57 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 49 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 41 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 33 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 25 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row57Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 57 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 57 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      57 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 57 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 49 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 41 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 33 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 25 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row57_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 57 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 57 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row57Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row57Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row57Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row57Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row57Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row57Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row57Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row57Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row57Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row57Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row57_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 57) =
      (rectangularize 62 93 Term6Stage4Data).getD 57 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 57
    ((rectangularize 62 93 Term6Stage4Data).getD 57 [])
  · exact term6Stage4_mulRow_length_le 57
  · rw [getD_rectangularize 62 93 Term6Stage4Data 57 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 57
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row57_coefficients

private theorem term6Stage4Row58Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 58 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 58 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 58 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 50 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 42 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 34 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 26 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row58Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 58 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 58 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 58 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 50 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 42 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 34 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 26 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row58Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 58 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 58 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 58 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 50 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 42 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 34 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 26 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row58Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 58 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 58 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 58 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 50 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 42 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 34 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 26 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row58Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 58 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 58 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 58 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 50 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 42 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 34 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 26 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row58Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 58 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 58 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 58 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 50 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 42 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 34 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 26 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row58Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 58 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 58 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 58 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 50 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 42 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 34 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 26 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row58Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 58 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 58 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      58 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 58 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 50 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 42 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 34 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 26 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row58Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 58 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 58 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      58 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 58 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 50 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 42 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 34 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 26 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row58Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 58 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 58 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      58 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 58 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 50 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 42 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 34 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 26 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row58_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 58 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 58 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row58Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row58Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row58Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row58Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row58Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row58Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row58Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row58Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row58Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row58Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row58_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 58) =
      (rectangularize 62 93 Term6Stage4Data).getD 58 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 58
    ((rectangularize 62 93 Term6Stage4Data).getD 58 [])
  · exact term6Stage4_mulRow_length_le 58
  · rw [getD_rectangularize 62 93 Term6Stage4Data 58 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 58
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row58_coefficients

private theorem term6Stage4Row59Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 59 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 59 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 59 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 51 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 43 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 35 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 27 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row59Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 59 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 59 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 59 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 51 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 43 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 35 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 27 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row59Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 59 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 59 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 59 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 51 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 43 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 35 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 27 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row59Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 59 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 59 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 59 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 51 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 43 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 35 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 27 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row59Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 59 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 59 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 59 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 51 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 43 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 35 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 27 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row59Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 59 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 59 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 59 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 51 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 43 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 35 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 27 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row59Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 59 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 59 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 59 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 51 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 43 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 35 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 27 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row59Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 59 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 59 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      59 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 59 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 51 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 43 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 35 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 27 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row59Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 59 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 59 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      59 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 59 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 51 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 43 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 35 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 27 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row59Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 59 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 59 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      59 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 59 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 51 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 43 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 35 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 27 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row59_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 59 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 59 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row59Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row59Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row59Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row59Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row59Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row59Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row59Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row59Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row59Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row59Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row59_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 59) =
      (rectangularize 62 93 Term6Stage4Data).getD 59 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 59
    ((rectangularize 62 93 Term6Stage4Data).getD 59 [])
  · exact term6Stage4_mulRow_length_le 59
  · rw [getD_rectangularize 62 93 Term6Stage4Data 59 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 59
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row59_coefficients

private theorem term6Stage4Row60Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 60 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 60 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 60 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 52 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 44 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 36 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 28 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row60Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 60 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 60 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 60 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 52 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 44 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 36 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 28 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row60Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 60 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 60 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 60 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 52 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 44 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 36 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 28 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row60Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 60 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 60 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 60 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 52 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 44 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 36 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 28 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row60Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 60 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 60 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 60 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 52 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 44 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 36 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 28 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row60Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 60 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 60 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 60 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 52 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 44 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 36 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 28 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row60Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 60 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 60 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 60 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 52 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 44 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 36 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 28 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row60Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 60 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 60 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      60 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 60 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 52 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 44 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 36 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 28 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row60Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 60 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 60 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      60 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 60 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 52 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 44 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 36 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 28 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row60Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 60 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 60 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      60 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 60 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 52 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 44 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 36 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 28 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row60_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 60 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 60 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row60Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row60Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row60Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row60Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row60Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row60Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row60Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row60Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row60Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row60Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row60_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 60) =
      (rectangularize 62 93 Term6Stage4Data).getD 60 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 60
    ((rectangularize 62 93 Term6Stage4Data).getD 60 [])
  · exact term6Stage4_mulRow_length_le 60
  · rw [getD_rectangularize 62 93 Term6Stage4Data 60 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 60
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row60_coefficients

private theorem term6Stage4Row61Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 61 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 61 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 61 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 53 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 45 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 37 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 29 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row61Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 61 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 61 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 61 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 53 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 45 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 37 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 29 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row61Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 61 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 61 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 61 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 53 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 45 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 37 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 29 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row61Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 61 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 61 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 61 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 53 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 45 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 37 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 29 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row61Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 61 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 61 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 61 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 53 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 45 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 37 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 29 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row61Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 61 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 61 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 61 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 53 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 45 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 37 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 29 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row61Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 61 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 61 []).getD j 0 := by
  rw [mulCoeffTwo_take_drop_outer_split V3Data Term6Stage3Data
    8 61 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) Term6Stage3Data
    8 53 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) Term6Stage3Data
    8 45 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) Term6Stage3Data
    8 37 j (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) Term6Stage3Data
    8 29 j (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row61Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 61 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 61 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      61 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 61 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 53 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 45 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 37 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 29 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row61Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 61 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 61 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      61 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 61 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 53 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 45 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 37 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 29 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row61Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 61 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 61 []).getD j 0 := by
  rw [show j = (j - 66) + 66 by omega,
    mulCoeffTwo_dropInner_window V3Data Term6Stage3Data
      61 (j - 66) 66 term6Stage4_v3Data_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split V3Data (dropInner (j - 66) Term6Stage3Data)
    8 61 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (V3Data.drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 53 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((V3Data.drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 45 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split (((V3Data.drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 37 66 (by decide) (by omega)]
  rw [mulCoeffTwo_take_drop_outer_split ((((V3Data.drop 8).drop 8).drop 8).drop 8) (dropInner (j - 66) Term6Stage3Data)
    8 29 66 (by decide) (by omega)]
  interval_cases j <;> decide

private theorem term6Stage4Row61_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 61 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 61 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row61Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row61Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row61Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row61Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row61Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row61Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row61Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row61Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row61Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row61Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row61_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 61) =
      (rectangularize 62 93 Term6Stage4Data).getD 61 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 61
    ((rectangularize 62 93 Term6Stage4Data).getD 61 [])
  · exact term6Stage4_mulRow_length_le 61
  · rw [getD_rectangularize 62 93 Term6Stage4Data 61 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 61
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row61_coefficients

theorem term6Stage4_rows56To61 (n : ℕ) (hLo : 56 ≤ n) (hHi : n < 62) :
    padOne 93 (mulRow V3Data Term6Stage3Data n) =
      (rectangularize 62 93 Term6Stage4Data).getD n [] := by
  interval_cases n
  · exact term6Stage4Row56_spec
  · exact term6Stage4Row57_spec
  · exact term6Stage4Row58_spec
  · exact term6Stage4Row59_spec
  · exact term6Stage4Row60_spec
  · exact term6Stage4Row61_spec

end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

