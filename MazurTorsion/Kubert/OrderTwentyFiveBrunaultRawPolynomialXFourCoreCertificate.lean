/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroDenseFactors
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialXThreeCertificate
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialXFourRData
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialXFourKOneData
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialXFourKTwoData
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialXFourKThreeData
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialXFourMData
import MazurTorsion.Kubert.OrderTwentyFiveDensePolynomialRectangular

/-!
# Checked primitive core of the raw X fourth-power table

Every stated rectangle is an exact bidegree bound, and `rectangularize` only
appends zeros.  The row-sharded equalities therefore check all coefficients
and all possible tails.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveRelationZeroCertificate.Dense
open OrderTwentyFiveDensePolynomialRectangular

-- Exact bidegree bound (40, 54).
theorem x4RData_spec :
    rectangularize 41 55 (Two.mul RData X3Data) =
      rectangularize 41 55 X4RData := by
  decide

-- Exact bidegree bound (41, 56).
theorem x4K1Data_spec :
    rectangularize 42 57 (Two.mul KData X4RData) =
      rectangularize 42 57 X4K1Data := by
  decide

-- Exact bidegree bound (42, 58).
theorem x4K2Data_spec :
    rectangularize 43 59 (Two.mul KData X4K1Data) =
      rectangularize 43 59 X4K2Data := by
  decide

-- Exact bidegree bound (43, 60).
theorem x4K3Data_spec :
    rectangularize 44 61 (Two.mul KData X4K2Data) =
      rectangularize 44 61 X4K3Data := by
  decide

private theorem x4MRow0_spec :
    (rectangularize 48 66 (Two.mul MData X4K3Data)).getD 0 [] =
      (rectangularize 48 66 X4MData).getD 0 [] := by
  decide

private theorem x4MRow1_spec :
    (rectangularize 48 66 (Two.mul MData X4K3Data)).getD 1 [] =
      (rectangularize 48 66 X4MData).getD 1 [] := by
  decide

private theorem x4MRow2_spec :
    (rectangularize 48 66 (Two.mul MData X4K3Data)).getD 2 [] =
      (rectangularize 48 66 X4MData).getD 2 [] := by
  decide

private theorem x4MRow3_spec :
    (rectangularize 48 66 (Two.mul MData X4K3Data)).getD 3 [] =
      (rectangularize 48 66 X4MData).getD 3 [] := by
  decide

private theorem x4MRow4_spec :
    (rectangularize 48 66 (Two.mul MData X4K3Data)).getD 4 [] =
      (rectangularize 48 66 X4MData).getD 4 [] := by
  decide

private theorem x4MRow5_spec :
    (rectangularize 48 66 (Two.mul MData X4K3Data)).getD 5 [] =
      (rectangularize 48 66 X4MData).getD 5 [] := by
  decide

private theorem x4MRow6_spec :
    (rectangularize 48 66 (Two.mul MData X4K3Data)).getD 6 [] =
      (rectangularize 48 66 X4MData).getD 6 [] := by
  decide

private theorem x4MRow7_spec :
    (rectangularize 48 66 (Two.mul MData X4K3Data)).getD 7 [] =
      (rectangularize 48 66 X4MData).getD 7 [] := by
  decide

private theorem x4MRow8_spec :
    (rectangularize 48 66 (Two.mul MData X4K3Data)).getD 8 [] =
      (rectangularize 48 66 X4MData).getD 8 [] := by
  decide

private theorem x4MRow9_spec :
    (rectangularize 48 66 (Two.mul MData X4K3Data)).getD 9 [] =
      (rectangularize 48 66 X4MData).getD 9 [] := by
  decide

private theorem x4MRow10_spec :
    (rectangularize 48 66 (Two.mul MData X4K3Data)).getD 10 [] =
      (rectangularize 48 66 X4MData).getD 10 [] := by
  decide

private theorem x4MRow11_spec :
    (rectangularize 48 66 (Two.mul MData X4K3Data)).getD 11 [] =
      (rectangularize 48 66 X4MData).getD 11 [] := by
  decide

private theorem x4MRow12_spec :
    (rectangularize 48 66 (Two.mul MData X4K3Data)).getD 12 [] =
      (rectangularize 48 66 X4MData).getD 12 [] := by
  decide

private theorem x4MRow13_spec :
    (rectangularize 48 66 (Two.mul MData X4K3Data)).getD 13 [] =
      (rectangularize 48 66 X4MData).getD 13 [] := by
  decide

private theorem x4MRow14_spec :
    (rectangularize 48 66 (Two.mul MData X4K3Data)).getD 14 [] =
      (rectangularize 48 66 X4MData).getD 14 [] := by
  decide

private theorem x4MRow15_spec :
    (rectangularize 48 66 (Two.mul MData X4K3Data)).getD 15 [] =
      (rectangularize 48 66 X4MData).getD 15 [] := by
  decide

private theorem x4MRow16_spec :
    (rectangularize 48 66 (Two.mul MData X4K3Data)).getD 16 [] =
      (rectangularize 48 66 X4MData).getD 16 [] := by
  decide

private theorem x4MRow17_spec :
    (rectangularize 48 66 (Two.mul MData X4K3Data)).getD 17 [] =
      (rectangularize 48 66 X4MData).getD 17 [] := by
  decide

private theorem x4MRow18_spec :
    (rectangularize 48 66 (Two.mul MData X4K3Data)).getD 18 [] =
      (rectangularize 48 66 X4MData).getD 18 [] := by
  decide

private theorem x4MRow19_spec :
    (rectangularize 48 66 (Two.mul MData X4K3Data)).getD 19 [] =
      (rectangularize 48 66 X4MData).getD 19 [] := by
  decide

private theorem x4MRow20_spec :
    (rectangularize 48 66 (Two.mul MData X4K3Data)).getD 20 [] =
      (rectangularize 48 66 X4MData).getD 20 [] := by
  decide

private theorem x4MRow21_spec :
    (rectangularize 48 66 (Two.mul MData X4K3Data)).getD 21 [] =
      (rectangularize 48 66 X4MData).getD 21 [] := by
  decide

private theorem x4MRow22_spec :
    (rectangularize 48 66 (Two.mul MData X4K3Data)).getD 22 [] =
      (rectangularize 48 66 X4MData).getD 22 [] := by
  decide

private theorem x4MRow23_spec :
    (rectangularize 48 66 (Two.mul MData X4K3Data)).getD 23 [] =
      (rectangularize 48 66 X4MData).getD 23 [] := by
  decide

private theorem x4MRow24_spec :
    (rectangularize 48 66 (Two.mul MData X4K3Data)).getD 24 [] =
      (rectangularize 48 66 X4MData).getD 24 [] := by
  decide

private theorem x4MRow25_spec :
    (rectangularize 48 66 (Two.mul MData X4K3Data)).getD 25 [] =
      (rectangularize 48 66 X4MData).getD 25 [] := by
  decide

private theorem x4MRow26_spec :
    (rectangularize 48 66 (Two.mul MData X4K3Data)).getD 26 [] =
      (rectangularize 48 66 X4MData).getD 26 [] := by
  decide

private theorem x4MRow27_spec :
    (rectangularize 48 66 (Two.mul MData X4K3Data)).getD 27 [] =
      (rectangularize 48 66 X4MData).getD 27 [] := by
  decide

private theorem x4MRow28_spec :
    (rectangularize 48 66 (Two.mul MData X4K3Data)).getD 28 [] =
      (rectangularize 48 66 X4MData).getD 28 [] := by
  decide

private theorem x4MRow29_spec :
    (rectangularize 48 66 (Two.mul MData X4K3Data)).getD 29 [] =
      (rectangularize 48 66 X4MData).getD 29 [] := by
  decide

private theorem x4MRow30_spec :
    (rectangularize 48 66 (Two.mul MData X4K3Data)).getD 30 [] =
      (rectangularize 48 66 X4MData).getD 30 [] := by
  decide

private theorem x4MRow31_spec :
    (rectangularize 48 66 (Two.mul MData X4K3Data)).getD 31 [] =
      (rectangularize 48 66 X4MData).getD 31 [] := by
  decide

private theorem x4MRow32_spec :
    (rectangularize 48 66 (Two.mul MData X4K3Data)).getD 32 [] =
      (rectangularize 48 66 X4MData).getD 32 [] := by
  decide

private theorem x4MRow33_spec :
    (rectangularize 48 66 (Two.mul MData X4K3Data)).getD 33 [] =
      (rectangularize 48 66 X4MData).getD 33 [] := by
  decide

private theorem x4MRow34_spec :
    (rectangularize 48 66 (Two.mul MData X4K3Data)).getD 34 [] =
      (rectangularize 48 66 X4MData).getD 34 [] := by
  decide

private theorem x4MRow35_spec :
    (rectangularize 48 66 (Two.mul MData X4K3Data)).getD 35 [] =
      (rectangularize 48 66 X4MData).getD 35 [] := by
  decide

private theorem x4MRow36_spec :
    (rectangularize 48 66 (Two.mul MData X4K3Data)).getD 36 [] =
      (rectangularize 48 66 X4MData).getD 36 [] := by
  decide

private theorem x4MRow37_spec :
    (rectangularize 48 66 (Two.mul MData X4K3Data)).getD 37 [] =
      (rectangularize 48 66 X4MData).getD 37 [] := by
  decide

private theorem x4MRow38_spec :
    (rectangularize 48 66 (Two.mul MData X4K3Data)).getD 38 [] =
      (rectangularize 48 66 X4MData).getD 38 [] := by
  decide

private theorem x4MRow39_spec :
    (rectangularize 48 66 (Two.mul MData X4K3Data)).getD 39 [] =
      (rectangularize 48 66 X4MData).getD 39 [] := by
  decide

private theorem x4MRow40_spec :
    (rectangularize 48 66 (Two.mul MData X4K3Data)).getD 40 [] =
      (rectangularize 48 66 X4MData).getD 40 [] := by
  decide

private theorem x4MRow41_spec :
    (rectangularize 48 66 (Two.mul MData X4K3Data)).getD 41 [] =
      (rectangularize 48 66 X4MData).getD 41 [] := by
  decide

private theorem x4MRow42_spec :
    (rectangularize 48 66 (Two.mul MData X4K3Data)).getD 42 [] =
      (rectangularize 48 66 X4MData).getD 42 [] := by
  decide

private theorem x4MRow43_spec :
    (rectangularize 48 66 (Two.mul MData X4K3Data)).getD 43 [] =
      (rectangularize 48 66 X4MData).getD 43 [] := by
  decide

private theorem x4MRow44_spec :
    (rectangularize 48 66 (Two.mul MData X4K3Data)).getD 44 [] =
      (rectangularize 48 66 X4MData).getD 44 [] := by
  decide

private theorem x4MRow45_spec :
    (rectangularize 48 66 (Two.mul MData X4K3Data)).getD 45 [] =
      (rectangularize 48 66 X4MData).getD 45 [] := by
  decide

private theorem x4MRow46_spec :
    (rectangularize 48 66 (Two.mul MData X4K3Data)).getD 46 [] =
      (rectangularize 48 66 X4MData).getD 46 [] := by
  decide

private theorem x4MRow47_spec :
    (rectangularize 48 66 (Two.mul MData X4K3Data)).getD 47 [] =
      (rectangularize 48 66 X4MData).getD 47 [] := by
  decide

private theorem x4MRows_spec (n : ℕ) (hn : n < 48) :
    (rectangularize 48 66 (Two.mul MData X4K3Data)).getD n [] =
      (rectangularize 48 66 X4MData).getD n [] := by
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
    n = 45 ∨ n = 46 ∨ n = 47 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact x4MRow0_spec
  · exact x4MRow1_spec
  · exact x4MRow2_spec
  · exact x4MRow3_spec
  · exact x4MRow4_spec
  · exact x4MRow5_spec
  · exact x4MRow6_spec
  · exact x4MRow7_spec
  · exact x4MRow8_spec
  · exact x4MRow9_spec
  · exact x4MRow10_spec
  · exact x4MRow11_spec
  · exact x4MRow12_spec
  · exact x4MRow13_spec
  · exact x4MRow14_spec
  · exact x4MRow15_spec
  · exact x4MRow16_spec
  · exact x4MRow17_spec
  · exact x4MRow18_spec
  · exact x4MRow19_spec
  · exact x4MRow20_spec
  · exact x4MRow21_spec
  · exact x4MRow22_spec
  · exact x4MRow23_spec
  · exact x4MRow24_spec
  · exact x4MRow25_spec
  · exact x4MRow26_spec
  · exact x4MRow27_spec
  · exact x4MRow28_spec
  · exact x4MRow29_spec
  · exact x4MRow30_spec
  · exact x4MRow31_spec
  · exact x4MRow32_spec
  · exact x4MRow33_spec
  · exact x4MRow34_spec
  · exact x4MRow35_spec
  · exact x4MRow36_spec
  · exact x4MRow37_spec
  · exact x4MRow38_spec
  · exact x4MRow39_spec
  · exact x4MRow40_spec
  · exact x4MRow41_spec
  · exact x4MRow42_spec
  · exact x4MRow43_spec
  · exact x4MRow44_spec
  · exact x4MRow45_spec
  · exact x4MRow46_spec
  · exact x4MRow47_spec

private theorem x4MLeft_length :
    (rectangularize 48 66 (Two.mul MData X4K3Data)).length = 48 := by
  decide

private theorem x4MRight_length :
    (rectangularize 48 66 X4MData).length = 48 := by
  decide

-- Exact bidegree bound (47, 65); no row or column is discarded.
theorem x4MData_spec :
    rectangularize 48 66 (Two.mul MData X4K3Data) =
      rectangularize 48 66 X4MData := by
  apply List.ext_getElem (x4MLeft_length.trans x4MRight_length.symm)
  intro n hn _
  rw [List.getElem_eq_getD [], List.getElem_eq_getD []]
  rw [x4MLeft_length] at hn
  exact x4MRows_spec n hn

/-- Evaluation of the checked primitive branch in the fourth power of `X`. -/
theorem eval_x4MData (r s : ℚ) :
    Two.eval X4MData r s =
      Two.eval MData r s * Two.eval KData r s ^ 3 *
        Two.eval RData r s * Two.eval X3Data r s := by
  have hR := congrArg (fun p => Two.eval p r s) x4RData_spec
  have hK1 := congrArg (fun p => Two.eval p r s) x4K1Data_spec
  have hK2 := congrArg (fun p => Two.eval p r s) x4K2Data_spec
  have hK3 := congrArg (fun p => Two.eval p r s) x4K3Data_spec
  have hM := congrArg (fun p => Two.eval p r s) x4MData_spec
  simp only [eval_rectangularize, Two.eval_mul] at hR hK1 hK2 hK3 hM
  calc
    Two.eval X4MData r s =
        Two.eval MData r s * Two.eval X4K3Data r s := hM.symm
    _ = Two.eval MData r s *
        (Two.eval KData r s * Two.eval X4K2Data r s) := by rw [← hK3]
    _ = Two.eval MData r s *
        (Two.eval KData r s *
          (Two.eval KData r s * Two.eval X4K1Data r s)) := by rw [← hK2]
    _ = Two.eval MData r s *
        (Two.eval KData r s *
          (Two.eval KData r s *
            (Two.eval KData r s * Two.eval X4RData r s))) := by rw [← hK1]
    _ = Two.eval MData r s * Two.eval KData r s ^ 3 *
        Two.eval RData r s * Two.eval X3Data r s := by rw [← hR]; ring

end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
