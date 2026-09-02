/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialAssemblyTermSixStageFourSupport
import Mathlib.Tactic.IntervalCases

/-!
# Low rows of the fourth stage of the sixth assembly term
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveDensePolynomialRectangular
open OrderTwentyFiveDensePolynomialRowCertificate

private theorem term6Stage4Row0_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 0) =
      (rectangularize 62 93 Term6Stage4Data).getD 0 [] := by
  decide

private theorem term6Stage4Row1_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 1) =
      (rectangularize 62 93 Term6Stage4Data).getD 1 [] := by
  decide

private theorem term6Stage4Row2_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 2) =
      (rectangularize 62 93 Term6Stage4Data).getD 2 [] := by
  decide

private theorem term6Stage4Row3_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 3) =
      (rectangularize 62 93 Term6Stage4Data).getD 3 [] := by
  decide

private theorem term6Stage4Row4_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 4) =
      (rectangularize 62 93 Term6Stage4Data).getD 4 [] := by
  decide

private theorem term6Stage4Row5_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 5) =
      (rectangularize 62 93 Term6Stage4Data).getD 5 [] := by
  decide

private theorem term6Stage4Row6_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 6) =
      (rectangularize 62 93 Term6Stage4Data).getD 6 [] := by
  decide

private theorem term6Stage4Row7Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo V3Data Term6Stage3Data 7 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 7 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row7Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo V3Data Term6Stage3Data 7 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 7 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row7Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo V3Data Term6Stage3Data 7 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 7 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row7Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo V3Data Term6Stage3Data 7 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 7 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row7Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo V3Data Term6Stage3Data 7 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 7 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row7Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo V3Data Term6Stage3Data 7 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 7 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row7Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo V3Data Term6Stage3Data 7 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 7 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row7Coeffs70To79_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 80) :
    mulCoeffTwo V3Data Term6Stage3Data 7 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 7 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row7Coeffs80To89_spec
    (j : ℕ) (hLo : 80 ≤ j) (hHi : j < 90) :
    mulCoeffTwo V3Data Term6Stage3Data 7 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 7 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row7Coeffs90To92_spec
    (j : ℕ) (hLo : 90 ≤ j) (hHi : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 7 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 7 []).getD j 0 := by
  interval_cases j <;> decide

private theorem term6Stage4Row7_coefficients (j : ℕ) (hj : j < 93) :
    mulCoeffTwo V3Data Term6Stage3Data 7 j =
      ((rectangularize 62 93 Term6Stage4Data).getD 7 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact term6Stage4Row7Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact term6Stage4Row7Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact term6Stage4Row7Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact term6Stage4Row7Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact term6Stage4Row7Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact term6Stage4Row7Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact term6Stage4Row7Coeffs60To69_spec j (by omega) h70
  by_cases h80 : j < 80
  · exact term6Stage4Row7Coeffs70To79_spec j (by omega) h80
  by_cases h90 : j < 90
  · exact term6Stage4Row7Coeffs80To89_spec j (by omega) h90
  exact term6Stage4Row7Coeffs90To92_spec j (by omega) hj

private theorem term6Stage4Row7_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 7) =
      (rectangularize 62 93 Term6Stage4Data).getD 7 [] := by
  apply padOne_mulRow_eq_of_coefficients 93 V3Data Term6Stage3Data 7
    ((rectangularize 62 93 Term6Stage4Data).getD 7 [])
  · exact term6Stage4_mulRow_length_le 7
  · rw [getD_rectangularize 62 93 Term6Stage4Data 7 (by omega)]
    have hTarget := term6Stage4Data_row_length_le 7
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact term6Stage4Row7_coefficients

theorem term6Stage4_rows0To7 (n : ℕ) (hn : n < 8) :
    padOne 93 (mulRow V3Data Term6Stage3Data n) =
      (rectangularize 62 93 Term6Stage4Data).getD n [] := by
  interval_cases n
  · exact term6Stage4Row0_spec
  · exact term6Stage4Row1_spec
  · exact term6Stage4Row2_spec
  · exact term6Stage4Row3_spec
  · exact term6Stage4Row4_spec
  · exact term6Stage4Row5_spec
  · exact term6Stage4Row6_spec
  · exact term6Stage4Row7_spec

end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
