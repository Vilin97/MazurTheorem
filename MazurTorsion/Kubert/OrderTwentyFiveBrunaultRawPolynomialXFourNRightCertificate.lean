/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialXFourCoreCertificate
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialAuxiliaryFactorData
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialXFourNRightData
import MazurTorsion.Kubert.OrderTwentyFiveDensePolynomialRowCertificate

/-!
# Checked right branch of the canonical N factor

Every stated rectangle is an exact bidegree bound, and `rectangularize` only
appends zeros.  The row-sharded equalities therefore check all coefficients
and all possible tails.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveRelationZeroCertificate.Dense
open OrderTwentyFiveDensePolynomialRectangular
open OrderTwentyFiveDensePolynomialRowCertificate

private theorem x4NRSRow0_spec :
    (rectangularize 48 67 (Two.mul SData X4MData)).getD 0 [] =
      (rectangularize 48 67 X4NRSData).getD 0 [] := by
  decide

private theorem x4NRSRow1_spec :
    (rectangularize 48 67 (Two.mul SData X4MData)).getD 1 [] =
      (rectangularize 48 67 X4NRSData).getD 1 [] := by
  decide

private theorem x4NRSRow2_spec :
    (rectangularize 48 67 (Two.mul SData X4MData)).getD 2 [] =
      (rectangularize 48 67 X4NRSData).getD 2 [] := by
  decide

private theorem x4NRSRow3_spec :
    (rectangularize 48 67 (Two.mul SData X4MData)).getD 3 [] =
      (rectangularize 48 67 X4NRSData).getD 3 [] := by
  decide

private theorem x4NRSRow4_spec :
    (rectangularize 48 67 (Two.mul SData X4MData)).getD 4 [] =
      (rectangularize 48 67 X4NRSData).getD 4 [] := by
  decide

private theorem x4NRSRow5_spec :
    (rectangularize 48 67 (Two.mul SData X4MData)).getD 5 [] =
      (rectangularize 48 67 X4NRSData).getD 5 [] := by
  decide

private theorem x4NRSRow6_spec :
    (rectangularize 48 67 (Two.mul SData X4MData)).getD 6 [] =
      (rectangularize 48 67 X4NRSData).getD 6 [] := by
  decide

private theorem x4NRSRow7_spec :
    (rectangularize 48 67 (Two.mul SData X4MData)).getD 7 [] =
      (rectangularize 48 67 X4NRSData).getD 7 [] := by
  decide

private theorem x4NRSRow8_spec :
    (rectangularize 48 67 (Two.mul SData X4MData)).getD 8 [] =
      (rectangularize 48 67 X4NRSData).getD 8 [] := by
  decide

private theorem x4NRSRow9_spec :
    (rectangularize 48 67 (Two.mul SData X4MData)).getD 9 [] =
      (rectangularize 48 67 X4NRSData).getD 9 [] := by
  decide

private theorem x4NRSRow10_spec :
    (rectangularize 48 67 (Two.mul SData X4MData)).getD 10 [] =
      (rectangularize 48 67 X4NRSData).getD 10 [] := by
  decide

private theorem x4NRSRow11_spec :
    (rectangularize 48 67 (Two.mul SData X4MData)).getD 11 [] =
      (rectangularize 48 67 X4NRSData).getD 11 [] := by
  decide

private theorem x4NRSRow12_spec :
    (rectangularize 48 67 (Two.mul SData X4MData)).getD 12 [] =
      (rectangularize 48 67 X4NRSData).getD 12 [] := by
  decide

private theorem x4NRSRow13_spec :
    (rectangularize 48 67 (Two.mul SData X4MData)).getD 13 [] =
      (rectangularize 48 67 X4NRSData).getD 13 [] := by
  decide

private theorem x4NRSRow14_spec :
    (rectangularize 48 67 (Two.mul SData X4MData)).getD 14 [] =
      (rectangularize 48 67 X4NRSData).getD 14 [] := by
  decide

private theorem x4NRSRow15_spec :
    (rectangularize 48 67 (Two.mul SData X4MData)).getD 15 [] =
      (rectangularize 48 67 X4NRSData).getD 15 [] := by
  decide

private theorem x4NRSRow16_spec :
    (rectangularize 48 67 (Two.mul SData X4MData)).getD 16 [] =
      (rectangularize 48 67 X4NRSData).getD 16 [] := by
  decide

private theorem x4NRSRow17_spec :
    (rectangularize 48 67 (Two.mul SData X4MData)).getD 17 [] =
      (rectangularize 48 67 X4NRSData).getD 17 [] := by
  decide

private theorem x4NRSRow18_spec :
    (rectangularize 48 67 (Two.mul SData X4MData)).getD 18 [] =
      (rectangularize 48 67 X4NRSData).getD 18 [] := by
  decide

private theorem x4NRSRow19_spec :
    (rectangularize 48 67 (Two.mul SData X4MData)).getD 19 [] =
      (rectangularize 48 67 X4NRSData).getD 19 [] := by
  decide

private theorem x4NRSRow20_spec :
    (rectangularize 48 67 (Two.mul SData X4MData)).getD 20 [] =
      (rectangularize 48 67 X4NRSData).getD 20 [] := by
  decide

private theorem x4NRSRow21_spec :
    (rectangularize 48 67 (Two.mul SData X4MData)).getD 21 [] =
      (rectangularize 48 67 X4NRSData).getD 21 [] := by
  decide

private theorem x4NRSRow22_spec :
    (rectangularize 48 67 (Two.mul SData X4MData)).getD 22 [] =
      (rectangularize 48 67 X4NRSData).getD 22 [] := by
  decide

private theorem x4NRSRow23_spec :
    (rectangularize 48 67 (Two.mul SData X4MData)).getD 23 [] =
      (rectangularize 48 67 X4NRSData).getD 23 [] := by
  decide

private theorem x4NRSRow24_spec :
    (rectangularize 48 67 (Two.mul SData X4MData)).getD 24 [] =
      (rectangularize 48 67 X4NRSData).getD 24 [] := by
  decide

private theorem x4NRSRow25_spec :
    (rectangularize 48 67 (Two.mul SData X4MData)).getD 25 [] =
      (rectangularize 48 67 X4NRSData).getD 25 [] := by
  decide

private theorem x4NRSRow26_spec :
    (rectangularize 48 67 (Two.mul SData X4MData)).getD 26 [] =
      (rectangularize 48 67 X4NRSData).getD 26 [] := by
  decide

private theorem x4NRSRow27_spec :
    (rectangularize 48 67 (Two.mul SData X4MData)).getD 27 [] =
      (rectangularize 48 67 X4NRSData).getD 27 [] := by
  decide

private theorem x4NRSRow28_spec :
    (rectangularize 48 67 (Two.mul SData X4MData)).getD 28 [] =
      (rectangularize 48 67 X4NRSData).getD 28 [] := by
  decide

private theorem x4NRSRow29_spec :
    (rectangularize 48 67 (Two.mul SData X4MData)).getD 29 [] =
      (rectangularize 48 67 X4NRSData).getD 29 [] := by
  decide

private theorem x4NRSRow30_spec :
    (rectangularize 48 67 (Two.mul SData X4MData)).getD 30 [] =
      (rectangularize 48 67 X4NRSData).getD 30 [] := by
  decide

private theorem x4NRSRow31_spec :
    (rectangularize 48 67 (Two.mul SData X4MData)).getD 31 [] =
      (rectangularize 48 67 X4NRSData).getD 31 [] := by
  decide

private theorem x4NRSRow32_spec :
    (rectangularize 48 67 (Two.mul SData X4MData)).getD 32 [] =
      (rectangularize 48 67 X4NRSData).getD 32 [] := by
  decide

private theorem x4NRSRow33_spec :
    (rectangularize 48 67 (Two.mul SData X4MData)).getD 33 [] =
      (rectangularize 48 67 X4NRSData).getD 33 [] := by
  decide

private theorem x4NRSRow34_spec :
    (rectangularize 48 67 (Two.mul SData X4MData)).getD 34 [] =
      (rectangularize 48 67 X4NRSData).getD 34 [] := by
  decide

private theorem x4NRSRow35_spec :
    (rectangularize 48 67 (Two.mul SData X4MData)).getD 35 [] =
      (rectangularize 48 67 X4NRSData).getD 35 [] := by
  decide

private theorem x4NRSRow36_spec :
    (rectangularize 48 67 (Two.mul SData X4MData)).getD 36 [] =
      (rectangularize 48 67 X4NRSData).getD 36 [] := by
  decide

private theorem x4NRSRow37_spec :
    (rectangularize 48 67 (Two.mul SData X4MData)).getD 37 [] =
      (rectangularize 48 67 X4NRSData).getD 37 [] := by
  decide

private theorem x4NRSRow38_spec :
    (rectangularize 48 67 (Two.mul SData X4MData)).getD 38 [] =
      (rectangularize 48 67 X4NRSData).getD 38 [] := by
  decide

private theorem x4NRSRow39_spec :
    (rectangularize 48 67 (Two.mul SData X4MData)).getD 39 [] =
      (rectangularize 48 67 X4NRSData).getD 39 [] := by
  decide

private theorem x4NRSRow40_spec :
    (rectangularize 48 67 (Two.mul SData X4MData)).getD 40 [] =
      (rectangularize 48 67 X4NRSData).getD 40 [] := by
  decide

private theorem x4NRSRow41_spec :
    (rectangularize 48 67 (Two.mul SData X4MData)).getD 41 [] =
      (rectangularize 48 67 X4NRSData).getD 41 [] := by
  decide

private theorem x4NRSRow42_spec :
    (rectangularize 48 67 (Two.mul SData X4MData)).getD 42 [] =
      (rectangularize 48 67 X4NRSData).getD 42 [] := by
  decide

private theorem x4NRSRow43_spec :
    (rectangularize 48 67 (Two.mul SData X4MData)).getD 43 [] =
      (rectangularize 48 67 X4NRSData).getD 43 [] := by
  decide

private theorem x4NRSRow44_spec :
    (rectangularize 48 67 (Two.mul SData X4MData)).getD 44 [] =
      (rectangularize 48 67 X4NRSData).getD 44 [] := by
  decide

private theorem x4NRSRow45_spec :
    (rectangularize 48 67 (Two.mul SData X4MData)).getD 45 [] =
      (rectangularize 48 67 X4NRSData).getD 45 [] := by
  decide

private theorem x4NRSRow46_spec :
    (rectangularize 48 67 (Two.mul SData X4MData)).getD 46 [] =
      (rectangularize 48 67 X4NRSData).getD 46 [] := by
  decide

private theorem x4NRSRow47_spec :
    (rectangularize 48 67 (Two.mul SData X4MData)).getD 47 [] =
      (rectangularize 48 67 X4NRSData).getD 47 [] := by
  decide

private theorem x4NRSRows_spec (n : ℕ) (hn : n < 48) :
    (rectangularize 48 67 (Two.mul SData X4MData)).getD n [] =
      (rectangularize 48 67 X4NRSData).getD n [] := by
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
  · exact x4NRSRow0_spec
  · exact x4NRSRow1_spec
  · exact x4NRSRow2_spec
  · exact x4NRSRow3_spec
  · exact x4NRSRow4_spec
  · exact x4NRSRow5_spec
  · exact x4NRSRow6_spec
  · exact x4NRSRow7_spec
  · exact x4NRSRow8_spec
  · exact x4NRSRow9_spec
  · exact x4NRSRow10_spec
  · exact x4NRSRow11_spec
  · exact x4NRSRow12_spec
  · exact x4NRSRow13_spec
  · exact x4NRSRow14_spec
  · exact x4NRSRow15_spec
  · exact x4NRSRow16_spec
  · exact x4NRSRow17_spec
  · exact x4NRSRow18_spec
  · exact x4NRSRow19_spec
  · exact x4NRSRow20_spec
  · exact x4NRSRow21_spec
  · exact x4NRSRow22_spec
  · exact x4NRSRow23_spec
  · exact x4NRSRow24_spec
  · exact x4NRSRow25_spec
  · exact x4NRSRow26_spec
  · exact x4NRSRow27_spec
  · exact x4NRSRow28_spec
  · exact x4NRSRow29_spec
  · exact x4NRSRow30_spec
  · exact x4NRSRow31_spec
  · exact x4NRSRow32_spec
  · exact x4NRSRow33_spec
  · exact x4NRSRow34_spec
  · exact x4NRSRow35_spec
  · exact x4NRSRow36_spec
  · exact x4NRSRow37_spec
  · exact x4NRSRow38_spec
  · exact x4NRSRow39_spec
  · exact x4NRSRow40_spec
  · exact x4NRSRow41_spec
  · exact x4NRSRow42_spec
  · exact x4NRSRow43_spec
  · exact x4NRSRow44_spec
  · exact x4NRSRow45_spec
  · exact x4NRSRow46_spec
  · exact x4NRSRow47_spec

private theorem x4NRSLeft_length :
    (rectangularize 48 67 (Two.mul SData X4MData)).length = 48 := by
  decide

private theorem x4NRSRight_length :
    (rectangularize 48 67 X4NRSData).length = 48 := by
  decide

-- Exact bidegree bound (47, 66); no row or column is discarded.
private theorem x4NRSData_spec :
    rectangularize 48 67 (Two.mul SData X4MData) =
      rectangularize 48 67 X4NRSData := by
  apply List.ext_getElem (x4NRSLeft_length.trans x4NRSRight_length.symm)
  intro n hn _
  rw [List.getElem_eq_getD [], List.getElem_eq_getD []]
  rw [x4NRSLeft_length] at hn
  exact x4NRSRows_spec n hn

private theorem x4NRC1Row0_spec :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).getD 0 [] =
      (rectangularize 49 68 X4NRC1Data).getD 0 [] := by
  decide

private theorem x4NRC1Row1_spec :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).getD 1 [] =
      (rectangularize 49 68 X4NRC1Data).getD 1 [] := by
  decide

private theorem x4NRC1Row2_spec :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).getD 2 [] =
      (rectangularize 49 68 X4NRC1Data).getD 2 [] := by
  decide

private theorem x4NRC1Row3_spec :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).getD 3 [] =
      (rectangularize 49 68 X4NRC1Data).getD 3 [] := by
  decide

private theorem x4NRC1Row4_spec :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).getD 4 [] =
      (rectangularize 49 68 X4NRC1Data).getD 4 [] := by
  decide

private theorem x4NRC1Row5_spec :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).getD 5 [] =
      (rectangularize 49 68 X4NRC1Data).getD 5 [] := by
  decide

private theorem x4NRC1Row6_spec :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).getD 6 [] =
      (rectangularize 49 68 X4NRC1Data).getD 6 [] := by
  decide

private theorem x4NRC1Row7_spec :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).getD 7 [] =
      (rectangularize 49 68 X4NRC1Data).getD 7 [] := by
  decide

private theorem x4NRC1Row8_spec :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).getD 8 [] =
      (rectangularize 49 68 X4NRC1Data).getD 8 [] := by
  decide

private theorem x4NRC1Row9_spec :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).getD 9 [] =
      (rectangularize 49 68 X4NRC1Data).getD 9 [] := by
  decide

private theorem x4NRC1Row10_spec :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).getD 10 [] =
      (rectangularize 49 68 X4NRC1Data).getD 10 [] := by
  decide

private theorem x4NRC1Row11_spec :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).getD 11 [] =
      (rectangularize 49 68 X4NRC1Data).getD 11 [] := by
  decide

private theorem x4NRC1Row12_spec :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).getD 12 [] =
      (rectangularize 49 68 X4NRC1Data).getD 12 [] := by
  decide

private theorem x4NRC1Row13_spec :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).getD 13 [] =
      (rectangularize 49 68 X4NRC1Data).getD 13 [] := by
  decide

private theorem x4NRC1Row14_spec :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).getD 14 [] =
      (rectangularize 49 68 X4NRC1Data).getD 14 [] := by
  decide

private theorem x4NRC1Row15_spec :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).getD 15 [] =
      (rectangularize 49 68 X4NRC1Data).getD 15 [] := by
  decide

private theorem x4NRC1Row16_spec :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).getD 16 [] =
      (rectangularize 49 68 X4NRC1Data).getD 16 [] := by
  decide

private theorem x4NRC1Row17_spec :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).getD 17 [] =
      (rectangularize 49 68 X4NRC1Data).getD 17 [] := by
  decide

private theorem x4NRC1Row18_spec :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).getD 18 [] =
      (rectangularize 49 68 X4NRC1Data).getD 18 [] := by
  decide

private theorem x4NRC1Row19_spec :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).getD 19 [] =
      (rectangularize 49 68 X4NRC1Data).getD 19 [] := by
  decide

private theorem x4NRC1Row20_spec :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).getD 20 [] =
      (rectangularize 49 68 X4NRC1Data).getD 20 [] := by
  decide

private theorem x4NRC1Row21_spec :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).getD 21 [] =
      (rectangularize 49 68 X4NRC1Data).getD 21 [] := by
  decide

private theorem x4NRC1Row22_spec :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).getD 22 [] =
      (rectangularize 49 68 X4NRC1Data).getD 22 [] := by
  decide

private theorem x4NRC1Row23_spec :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).getD 23 [] =
      (rectangularize 49 68 X4NRC1Data).getD 23 [] := by
  decide

private theorem x4NRC1Row24_spec :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).getD 24 [] =
      (rectangularize 49 68 X4NRC1Data).getD 24 [] := by
  decide

private theorem x4NRC1Row25_spec :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).getD 25 [] =
      (rectangularize 49 68 X4NRC1Data).getD 25 [] := by
  decide

private theorem x4NRC1Row26_spec :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).getD 26 [] =
      (rectangularize 49 68 X4NRC1Data).getD 26 [] := by
  decide

private theorem x4NRC1Row27_spec :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).getD 27 [] =
      (rectangularize 49 68 X4NRC1Data).getD 27 [] := by
  decide

private theorem x4NRC1Row28_spec :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).getD 28 [] =
      (rectangularize 49 68 X4NRC1Data).getD 28 [] := by
  decide

private theorem x4NRC1Row29_spec :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).getD 29 [] =
      (rectangularize 49 68 X4NRC1Data).getD 29 [] := by
  decide

private theorem x4NRC1Row30_spec :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).getD 30 [] =
      (rectangularize 49 68 X4NRC1Data).getD 30 [] := by
  decide

private theorem x4NRC1Row31_spec :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).getD 31 [] =
      (rectangularize 49 68 X4NRC1Data).getD 31 [] := by
  decide

private theorem x4NRC1Row32_spec :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).getD 32 [] =
      (rectangularize 49 68 X4NRC1Data).getD 32 [] := by
  decide

private theorem x4NRC1Row33_spec :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).getD 33 [] =
      (rectangularize 49 68 X4NRC1Data).getD 33 [] := by
  decide

private theorem x4NRC1Row34_spec :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).getD 34 [] =
      (rectangularize 49 68 X4NRC1Data).getD 34 [] := by
  decide

private theorem x4NRC1Row35_spec :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).getD 35 [] =
      (rectangularize 49 68 X4NRC1Data).getD 35 [] := by
  decide

private theorem x4NRC1Row36_spec :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).getD 36 [] =
      (rectangularize 49 68 X4NRC1Data).getD 36 [] := by
  decide

private theorem x4NRC1Row37_spec :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).getD 37 [] =
      (rectangularize 49 68 X4NRC1Data).getD 37 [] := by
  decide

private theorem x4NRC1Row38_spec :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).getD 38 [] =
      (rectangularize 49 68 X4NRC1Data).getD 38 [] := by
  decide

private theorem x4NRC1Row39_spec :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).getD 39 [] =
      (rectangularize 49 68 X4NRC1Data).getD 39 [] := by
  decide

private theorem x4NRC1Row40_spec :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).getD 40 [] =
      (rectangularize 49 68 X4NRC1Data).getD 40 [] := by
  decide

private theorem x4NRC1Row41_spec :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).getD 41 [] =
      (rectangularize 49 68 X4NRC1Data).getD 41 [] := by
  decide

private theorem x4NRC1Row42_spec :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).getD 42 [] =
      (rectangularize 49 68 X4NRC1Data).getD 42 [] := by
  decide

private theorem x4NRC1Row43_spec :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).getD 43 [] =
      (rectangularize 49 68 X4NRC1Data).getD 43 [] := by
  decide

private theorem x4NRC1Row44_spec :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).getD 44 [] =
      (rectangularize 49 68 X4NRC1Data).getD 44 [] := by
  decide

private theorem x4NRC1Row45_spec :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).getD 45 [] =
      (rectangularize 49 68 X4NRC1Data).getD 45 [] := by
  decide

private theorem x4NRC1Row46_spec :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).getD 46 [] =
      (rectangularize 49 68 X4NRC1Data).getD 46 [] := by
  decide

private theorem x4NRC1Row47_spec :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).getD 47 [] =
      (rectangularize 49 68 X4NRC1Data).getD 47 [] := by
  decide

private theorem x4NRC1Row48_spec :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).getD 48 [] =
      (rectangularize 49 68 X4NRC1Data).getD 48 [] := by
  decide

private theorem x4NRC1Rows_spec (n : ℕ) (hn : n < 49) :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).getD n [] =
      (rectangularize 49 68 X4NRC1Data).getD n [] := by
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
    n = 45 ∨ n = 46 ∨ n = 47 ∨ n = 48 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  · exact x4NRC1Row0_spec
  · exact x4NRC1Row1_spec
  · exact x4NRC1Row2_spec
  · exact x4NRC1Row3_spec
  · exact x4NRC1Row4_spec
  · exact x4NRC1Row5_spec
  · exact x4NRC1Row6_spec
  · exact x4NRC1Row7_spec
  · exact x4NRC1Row8_spec
  · exact x4NRC1Row9_spec
  · exact x4NRC1Row10_spec
  · exact x4NRC1Row11_spec
  · exact x4NRC1Row12_spec
  · exact x4NRC1Row13_spec
  · exact x4NRC1Row14_spec
  · exact x4NRC1Row15_spec
  · exact x4NRC1Row16_spec
  · exact x4NRC1Row17_spec
  · exact x4NRC1Row18_spec
  · exact x4NRC1Row19_spec
  · exact x4NRC1Row20_spec
  · exact x4NRC1Row21_spec
  · exact x4NRC1Row22_spec
  · exact x4NRC1Row23_spec
  · exact x4NRC1Row24_spec
  · exact x4NRC1Row25_spec
  · exact x4NRC1Row26_spec
  · exact x4NRC1Row27_spec
  · exact x4NRC1Row28_spec
  · exact x4NRC1Row29_spec
  · exact x4NRC1Row30_spec
  · exact x4NRC1Row31_spec
  · exact x4NRC1Row32_spec
  · exact x4NRC1Row33_spec
  · exact x4NRC1Row34_spec
  · exact x4NRC1Row35_spec
  · exact x4NRC1Row36_spec
  · exact x4NRC1Row37_spec
  · exact x4NRC1Row38_spec
  · exact x4NRC1Row39_spec
  · exact x4NRC1Row40_spec
  · exact x4NRC1Row41_spec
  · exact x4NRC1Row42_spec
  · exact x4NRC1Row43_spec
  · exact x4NRC1Row44_spec
  · exact x4NRC1Row45_spec
  · exact x4NRC1Row46_spec
  · exact x4NRC1Row47_spec
  · exact x4NRC1Row48_spec

private theorem x4NRC1Left_length :
    (rectangularize 49 68 (Two.mul CData X4NRSData)).length = 49 := by
  decide

private theorem x4NRC1Right_length :
    (rectangularize 49 68 X4NRC1Data).length = 49 := by
  decide

-- Exact bidegree bound (48, 67); no row or column is discarded.
private theorem x4NRC1Data_spec :
    rectangularize 49 68 (Two.mul CData X4NRSData) =
      rectangularize 49 68 X4NRC1Data := by
  apply List.ext_getElem (x4NRC1Left_length.trans x4NRC1Right_length.symm)
  intro n hn _
  rw [List.getElem_eq_getD [], List.getElem_eq_getD []]
  rw [x4NRC1Left_length] at hn
  exact x4NRC1Rows_spec n hn

private theorem x4NRC2Row0_spec :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD 0 [] =
      (rectangularize 50 69 X4NRC2Data).getD 0 [] := by
  decide

private theorem x4NRC2Row1_spec :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD 1 [] =
      (rectangularize 50 69 X4NRC2Data).getD 1 [] := by
  decide

private theorem x4NRC2Row2_spec :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD 2 [] =
      (rectangularize 50 69 X4NRC2Data).getD 2 [] := by
  decide

private theorem x4NRC2Row3_spec :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD 3 [] =
      (rectangularize 50 69 X4NRC2Data).getD 3 [] := by
  decide

private theorem x4NRC2Row4_spec :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD 4 [] =
      (rectangularize 50 69 X4NRC2Data).getD 4 [] := by
  decide

private theorem x4NRC2Row5_spec :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD 5 [] =
      (rectangularize 50 69 X4NRC2Data).getD 5 [] := by
  decide

private theorem x4NRC2Row6_spec :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD 6 [] =
      (rectangularize 50 69 X4NRC2Data).getD 6 [] := by
  decide

private theorem x4NRC2Row7_spec :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD 7 [] =
      (rectangularize 50 69 X4NRC2Data).getD 7 [] := by
  decide

private theorem x4NRC2Row8_spec :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD 8 [] =
      (rectangularize 50 69 X4NRC2Data).getD 8 [] := by
  decide

private theorem x4NRC2Row9_spec :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD 9 [] =
      (rectangularize 50 69 X4NRC2Data).getD 9 [] := by
  decide

private theorem x4NRC2Row10_spec :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD 10 [] =
      (rectangularize 50 69 X4NRC2Data).getD 10 [] := by
  decide

private theorem x4NRC2Row11_spec :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD 11 [] =
      (rectangularize 50 69 X4NRC2Data).getD 11 [] := by
  decide

private theorem x4NRC2Row12_spec :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD 12 [] =
      (rectangularize 50 69 X4NRC2Data).getD 12 [] := by
  decide

private theorem x4NRC2Row13_spec :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD 13 [] =
      (rectangularize 50 69 X4NRC2Data).getD 13 [] := by
  decide

private theorem x4NRC2Row14_spec :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD 14 [] =
      (rectangularize 50 69 X4NRC2Data).getD 14 [] := by
  decide

private theorem x4NRC2Row15_spec :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD 15 [] =
      (rectangularize 50 69 X4NRC2Data).getD 15 [] := by
  decide

private theorem x4NRC2Row16_spec :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD 16 [] =
      (rectangularize 50 69 X4NRC2Data).getD 16 [] := by
  decide

private theorem x4NRC2Row17_spec :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD 17 [] =
      (rectangularize 50 69 X4NRC2Data).getD 17 [] := by
  decide

private theorem x4NRC2Row18_spec :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD 18 [] =
      (rectangularize 50 69 X4NRC2Data).getD 18 [] := by
  decide

private theorem x4NRC2Row19_spec :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD 19 [] =
      (rectangularize 50 69 X4NRC2Data).getD 19 [] := by
  decide

private theorem x4NRC2Row20_spec :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD 20 [] =
      (rectangularize 50 69 X4NRC2Data).getD 20 [] := by
  decide

private theorem x4NRC2Row21_spec :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD 21 [] =
      (rectangularize 50 69 X4NRC2Data).getD 21 [] := by
  decide

private theorem x4NRC2Row22_spec :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD 22 [] =
      (rectangularize 50 69 X4NRC2Data).getD 22 [] := by
  decide

private theorem x4NRC2Row23_spec :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD 23 [] =
      (rectangularize 50 69 X4NRC2Data).getD 23 [] := by
  decide

private theorem x4NRC2Row24_spec :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD 24 [] =
      (rectangularize 50 69 X4NRC2Data).getD 24 [] := by
  decide

private theorem x4NRC2Row25_spec :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD 25 [] =
      (rectangularize 50 69 X4NRC2Data).getD 25 [] := by
  decide

private theorem x4NRC2Row26_spec :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD 26 [] =
      (rectangularize 50 69 X4NRC2Data).getD 26 [] := by
  decide

private theorem x4NRC2Row27_spec :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD 27 [] =
      (rectangularize 50 69 X4NRC2Data).getD 27 [] := by
  decide

private theorem x4NRC2Row28_spec :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD 28 [] =
      (rectangularize 50 69 X4NRC2Data).getD 28 [] := by
  decide

private theorem x4NRC2Row29_spec :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD 29 [] =
      (rectangularize 50 69 X4NRC2Data).getD 29 [] := by
  decide

private theorem x4NRC2Row30_spec :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD 30 [] =
      (rectangularize 50 69 X4NRC2Data).getD 30 [] := by
  decide

private theorem x4NRC2Row31_spec :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD 31 [] =
      (rectangularize 50 69 X4NRC2Data).getD 31 [] := by
  decide

private theorem x4NRC2Row32_spec :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD 32 [] =
      (rectangularize 50 69 X4NRC2Data).getD 32 [] := by
  decide

private theorem x4NRC2Row33_spec :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD 33 [] =
      (rectangularize 50 69 X4NRC2Data).getD 33 [] := by
  decide

private theorem x4NRC2Row34_spec :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD 34 [] =
      (rectangularize 50 69 X4NRC2Data).getD 34 [] := by
  decide

private theorem x4NRC2Row35_spec :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD 35 [] =
      (rectangularize 50 69 X4NRC2Data).getD 35 [] := by
  decide

private theorem x4NRC2Row36_spec :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD 36 [] =
      (rectangularize 50 69 X4NRC2Data).getD 36 [] := by
  decide

private theorem x4NRC2Row37_spec :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD 37 [] =
      (rectangularize 50 69 X4NRC2Data).getD 37 [] := by
  decide

private theorem x4NRC2Row38_spec :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD 38 [] =
      (rectangularize 50 69 X4NRC2Data).getD 38 [] := by
  decide

private theorem x4NRC2Row39_spec :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD 39 [] =
      (rectangularize 50 69 X4NRC2Data).getD 39 [] := by
  decide

private theorem x4NRC2Row40_spec :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD 40 [] =
      (rectangularize 50 69 X4NRC2Data).getD 40 [] := by
  decide

private theorem x4NRC2Row41_spec :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD 41 [] =
      (rectangularize 50 69 X4NRC2Data).getD 41 [] := by
  decide

private theorem x4NRC2Row42_spec :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD 42 [] =
      (rectangularize 50 69 X4NRC2Data).getD 42 [] := by
  decide

private theorem x4NRC2Row43_spec :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD 43 [] =
      (rectangularize 50 69 X4NRC2Data).getD 43 [] := by
  decide

private theorem x4NRC2Row44_spec :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD 44 [] =
      (rectangularize 50 69 X4NRC2Data).getD 44 [] := by
  decide

private theorem x4NRC2Row45_spec :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD 45 [] =
      (rectangularize 50 69 X4NRC2Data).getD 45 [] := by
  decide

private theorem x4NRC2Row46_spec :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD 46 [] =
      (rectangularize 50 69 X4NRC2Data).getD 46 [] := by
  decide

private theorem x4NRC2Row47_spec :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD 47 [] =
      (rectangularize 50 69 X4NRC2Data).getD 47 [] := by
  decide

private theorem x4NRC2Row48_spec :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD 48 [] =
      (rectangularize 50 69 X4NRC2Data).getD 48 [] := by
  decide

private theorem x4NRC2Row49_spec :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD 49 [] =
      (rectangularize 50 69 X4NRC2Data).getD 49 [] := by
  decide

private theorem x4NRC2Rows_spec (n : ℕ) (hn : n < 50) :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).getD n [] =
      (rectangularize 50 69 X4NRC2Data).getD n [] := by
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
    n = 45 ∨ n = 46 ∨ n = 47 ∨ n = 48 ∨ n = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRC2Row0_spec
  · exact x4NRC2Row1_spec
  · exact x4NRC2Row2_spec
  · exact x4NRC2Row3_spec
  · exact x4NRC2Row4_spec
  · exact x4NRC2Row5_spec
  · exact x4NRC2Row6_spec
  · exact x4NRC2Row7_spec
  · exact x4NRC2Row8_spec
  · exact x4NRC2Row9_spec
  · exact x4NRC2Row10_spec
  · exact x4NRC2Row11_spec
  · exact x4NRC2Row12_spec
  · exact x4NRC2Row13_spec
  · exact x4NRC2Row14_spec
  · exact x4NRC2Row15_spec
  · exact x4NRC2Row16_spec
  · exact x4NRC2Row17_spec
  · exact x4NRC2Row18_spec
  · exact x4NRC2Row19_spec
  · exact x4NRC2Row20_spec
  · exact x4NRC2Row21_spec
  · exact x4NRC2Row22_spec
  · exact x4NRC2Row23_spec
  · exact x4NRC2Row24_spec
  · exact x4NRC2Row25_spec
  · exact x4NRC2Row26_spec
  · exact x4NRC2Row27_spec
  · exact x4NRC2Row28_spec
  · exact x4NRC2Row29_spec
  · exact x4NRC2Row30_spec
  · exact x4NRC2Row31_spec
  · exact x4NRC2Row32_spec
  · exact x4NRC2Row33_spec
  · exact x4NRC2Row34_spec
  · exact x4NRC2Row35_spec
  · exact x4NRC2Row36_spec
  · exact x4NRC2Row37_spec
  · exact x4NRC2Row38_spec
  · exact x4NRC2Row39_spec
  · exact x4NRC2Row40_spec
  · exact x4NRC2Row41_spec
  · exact x4NRC2Row42_spec
  · exact x4NRC2Row43_spec
  · exact x4NRC2Row44_spec
  · exact x4NRC2Row45_spec
  · exact x4NRC2Row46_spec
  · exact x4NRC2Row47_spec
  · exact x4NRC2Row48_spec
  · exact x4NRC2Row49_spec

private theorem x4NRC2Left_length :
    (rectangularize 50 69 (Two.mul CData X4NRC1Data)).length = 50 := by
  decide

private theorem x4NRC2Right_length :
    (rectangularize 50 69 X4NRC2Data).length = 50 := by
  decide

-- Exact bidegree bound (49, 68); no row or column is discarded.
private theorem x4NRC2Data_spec :
    rectangularize 50 69 (Two.mul CData X4NRC1Data) =
      rectangularize 50 69 X4NRC2Data := by
  apply List.ext_getElem (x4NRC2Left_length.trans x4NRC2Right_length.symm)
  intro n hn _
  rw [List.getElem_eq_getD [], List.getElem_eq_getD []]
  rw [x4NRC2Left_length] at hn
  exact x4NRC2Rows_spec n hn

private theorem x4NRC3Row0_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 0 [] =
      (rectangularize 51 70 X4NRC3Data).getD 0 [] := by
  decide

private theorem x4NRC3Row1_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 1 [] =
      (rectangularize 51 70 X4NRC3Data).getD 1 [] := by
  decide

private theorem x4NRC3Row2_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 2 [] =
      (rectangularize 51 70 X4NRC3Data).getD 2 [] := by
  decide

private theorem x4NRC3Row3_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 3 [] =
      (rectangularize 51 70 X4NRC3Data).getD 3 [] := by
  decide

private theorem x4NRC3Row4_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 4 [] =
      (rectangularize 51 70 X4NRC3Data).getD 4 [] := by
  decide

private theorem x4NRC3Row5_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 5 [] =
      (rectangularize 51 70 X4NRC3Data).getD 5 [] := by
  decide

private theorem x4NRC3Row6_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 6 [] =
      (rectangularize 51 70 X4NRC3Data).getD 6 [] := by
  decide

private theorem x4NRC3Row7_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 7 [] =
      (rectangularize 51 70 X4NRC3Data).getD 7 [] := by
  decide

private theorem x4NRC3Row8_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 8 [] =
      (rectangularize 51 70 X4NRC3Data).getD 8 [] := by
  decide

private theorem x4NRC3Row9_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 9 [] =
      (rectangularize 51 70 X4NRC3Data).getD 9 [] := by
  decide

private theorem x4NRC3Row10_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 10 [] =
      (rectangularize 51 70 X4NRC3Data).getD 10 [] := by
  decide

private theorem x4NRC3Row11_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 11 [] =
      (rectangularize 51 70 X4NRC3Data).getD 11 [] := by
  decide

private theorem x4NRC3Row12_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 12 [] =
      (rectangularize 51 70 X4NRC3Data).getD 12 [] := by
  decide

private theorem x4NRC3Row13_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 13 [] =
      (rectangularize 51 70 X4NRC3Data).getD 13 [] := by
  decide

private theorem x4NRC3Row14_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 14 [] =
      (rectangularize 51 70 X4NRC3Data).getD 14 [] := by
  decide

private theorem x4NRC3Row15_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 15 [] =
      (rectangularize 51 70 X4NRC3Data).getD 15 [] := by
  decide

private theorem x4NRC3Row16_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 16 [] =
      (rectangularize 51 70 X4NRC3Data).getD 16 [] := by
  decide

private theorem x4NRC3Row17_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 17 [] =
      (rectangularize 51 70 X4NRC3Data).getD 17 [] := by
  decide

private theorem x4NRC3Row18_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 18 [] =
      (rectangularize 51 70 X4NRC3Data).getD 18 [] := by
  decide

private theorem x4NRC3Row19_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 19 [] =
      (rectangularize 51 70 X4NRC3Data).getD 19 [] := by
  decide

private theorem x4NRC3Row20_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 20 [] =
      (rectangularize 51 70 X4NRC3Data).getD 20 [] := by
  decide

private theorem x4NRC3Row21_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 21 [] =
      (rectangularize 51 70 X4NRC3Data).getD 21 [] := by
  decide

private theorem x4NRC3Row22_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 22 [] =
      (rectangularize 51 70 X4NRC3Data).getD 22 [] := by
  decide

private theorem x4NRC3Row23_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 23 [] =
      (rectangularize 51 70 X4NRC3Data).getD 23 [] := by
  decide

private theorem x4NRC3Row24_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 24 [] =
      (rectangularize 51 70 X4NRC3Data).getD 24 [] := by
  decide

private theorem x4NRC3Row25_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 25 [] =
      (rectangularize 51 70 X4NRC3Data).getD 25 [] := by
  decide

private theorem x4NRC3Row26_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 26 [] =
      (rectangularize 51 70 X4NRC3Data).getD 26 [] := by
  decide

private theorem x4NRC3Row27_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 27 [] =
      (rectangularize 51 70 X4NRC3Data).getD 27 [] := by
  decide

private theorem x4NRC3Row28_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 28 [] =
      (rectangularize 51 70 X4NRC3Data).getD 28 [] := by
  decide

private theorem x4NRC3Row29_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 29 [] =
      (rectangularize 51 70 X4NRC3Data).getD 29 [] := by
  decide

private theorem x4NRC3Row30_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 30 [] =
      (rectangularize 51 70 X4NRC3Data).getD 30 [] := by
  decide

private theorem x4NRC3Row31_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 31 [] =
      (rectangularize 51 70 X4NRC3Data).getD 31 [] := by
  decide

private theorem x4NRC3Row32_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 32 [] =
      (rectangularize 51 70 X4NRC3Data).getD 32 [] := by
  decide

private theorem x4NRC3Row33_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 33 [] =
      (rectangularize 51 70 X4NRC3Data).getD 33 [] := by
  decide

private theorem x4NRC3Row34_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 34 [] =
      (rectangularize 51 70 X4NRC3Data).getD 34 [] := by
  decide

private theorem x4NRC3Row35_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 35 [] =
      (rectangularize 51 70 X4NRC3Data).getD 35 [] := by
  decide

private theorem x4NRC3Row36_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 36 [] =
      (rectangularize 51 70 X4NRC3Data).getD 36 [] := by
  decide

private theorem x4NRC3Row37_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 37 [] =
      (rectangularize 51 70 X4NRC3Data).getD 37 [] := by
  decide

private theorem x4NRC3Row38_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 38 [] =
      (rectangularize 51 70 X4NRC3Data).getD 38 [] := by
  decide

private theorem x4NRC3Row39_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 39 [] =
      (rectangularize 51 70 X4NRC3Data).getD 39 [] := by
  decide

private theorem x4NRC3Row40_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 40 [] =
      (rectangularize 51 70 X4NRC3Data).getD 40 [] := by
  decide

private theorem x4NRC3Row41_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 41 [] =
      (rectangularize 51 70 X4NRC3Data).getD 41 [] := by
  decide

private theorem x4NRC3Row42_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 42 [] =
      (rectangularize 51 70 X4NRC3Data).getD 42 [] := by
  decide

private theorem x4NRC3Row43_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 43 [] =
      (rectangularize 51 70 X4NRC3Data).getD 43 [] := by
  decide

private theorem x4NRC3Row44_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 44 [] =
      (rectangularize 51 70 X4NRC3Data).getD 44 [] := by
  decide

private theorem x4NRC3Row45_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 45 [] =
      (rectangularize 51 70 X4NRC3Data).getD 45 [] := by
  decide

private theorem x4NRC3Row46_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 46 [] =
      (rectangularize 51 70 X4NRC3Data).getD 46 [] := by
  decide

private theorem x4NRC3Row47_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 47 [] =
      (rectangularize 51 70 X4NRC3Data).getD 47 [] := by
  decide

private theorem x4NRC3Row48_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 48 [] =
      (rectangularize 51 70 X4NRC3Data).getD 48 [] := by
  decide

private theorem x4NRC3Row49_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 49 [] =
      (rectangularize 51 70 X4NRC3Data).getD 49 [] := by
  decide

private theorem x4NRC3Row50_spec :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD 50 [] =
      (rectangularize 51 70 X4NRC3Data).getD 50 [] := by
  decide

private theorem x4NRC3Rows_spec (n : ℕ) (hn : n < 51) :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).getD n [] =
      (rectangularize 51 70 X4NRC3Data).getD n [] := by
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
    n = 50 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  · exact x4NRC3Row0_spec
  · exact x4NRC3Row1_spec
  · exact x4NRC3Row2_spec
  · exact x4NRC3Row3_spec
  · exact x4NRC3Row4_spec
  · exact x4NRC3Row5_spec
  · exact x4NRC3Row6_spec
  · exact x4NRC3Row7_spec
  · exact x4NRC3Row8_spec
  · exact x4NRC3Row9_spec
  · exact x4NRC3Row10_spec
  · exact x4NRC3Row11_spec
  · exact x4NRC3Row12_spec
  · exact x4NRC3Row13_spec
  · exact x4NRC3Row14_spec
  · exact x4NRC3Row15_spec
  · exact x4NRC3Row16_spec
  · exact x4NRC3Row17_spec
  · exact x4NRC3Row18_spec
  · exact x4NRC3Row19_spec
  · exact x4NRC3Row20_spec
  · exact x4NRC3Row21_spec
  · exact x4NRC3Row22_spec
  · exact x4NRC3Row23_spec
  · exact x4NRC3Row24_spec
  · exact x4NRC3Row25_spec
  · exact x4NRC3Row26_spec
  · exact x4NRC3Row27_spec
  · exact x4NRC3Row28_spec
  · exact x4NRC3Row29_spec
  · exact x4NRC3Row30_spec
  · exact x4NRC3Row31_spec
  · exact x4NRC3Row32_spec
  · exact x4NRC3Row33_spec
  · exact x4NRC3Row34_spec
  · exact x4NRC3Row35_spec
  · exact x4NRC3Row36_spec
  · exact x4NRC3Row37_spec
  · exact x4NRC3Row38_spec
  · exact x4NRC3Row39_spec
  · exact x4NRC3Row40_spec
  · exact x4NRC3Row41_spec
  · exact x4NRC3Row42_spec
  · exact x4NRC3Row43_spec
  · exact x4NRC3Row44_spec
  · exact x4NRC3Row45_spec
  · exact x4NRC3Row46_spec
  · exact x4NRC3Row47_spec
  · exact x4NRC3Row48_spec
  · exact x4NRC3Row49_spec
  · exact x4NRC3Row50_spec

private theorem x4NRC3Left_length :
    (rectangularize 51 70 (Two.mul CData X4NRC2Data)).length = 51 := by
  decide

private theorem x4NRC3Right_length :
    (rectangularize 51 70 X4NRC3Data).length = 51 := by
  decide

-- Exact bidegree bound (50, 69); no row or column is discarded.
private theorem x4NRC3Data_spec :
    rectangularize 51 70 (Two.mul CData X4NRC2Data) =
      rectangularize 51 70 X4NRC3Data := by
  apply List.ext_getElem (x4NRC3Left_length.trans x4NRC3Right_length.symm)
  intro n hn _
  rw [List.getElem_eq_getD [], List.getElem_eq_getD []]
  rw [x4NRC3Left_length] at hn
  exact x4NRC3Rows_spec n hn

private theorem x4NRGRow0_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 0 [] =
      (rectangularize 52 72 X4NRGData).getD 0 [] := by
  decide

private theorem x4NRGRow1_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 1 [] =
      (rectangularize 52 72 X4NRGData).getD 1 [] := by
  decide

private theorem x4NRGRow2_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 2 [] =
      (rectangularize 52 72 X4NRGData).getD 2 [] := by
  decide

private theorem x4NRGRow3_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 3 [] =
      (rectangularize 52 72 X4NRGData).getD 3 [] := by
  decide

private theorem x4NRGRow4_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 4 [] =
      (rectangularize 52 72 X4NRGData).getD 4 [] := by
  decide

private theorem x4NRGRow5_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 5 [] =
      (rectangularize 52 72 X4NRGData).getD 5 [] := by
  decide

private theorem x4NRGRow6_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 6 [] =
      (rectangularize 52 72 X4NRGData).getD 6 [] := by
  decide

private theorem x4NRGRow7_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 7 [] =
      (rectangularize 52 72 X4NRGData).getD 7 [] := by
  decide

private theorem x4NRGRow8_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 8 [] =
      (rectangularize 52 72 X4NRGData).getD 8 [] := by
  decide

private theorem x4NRGRow9_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 9 [] =
      (rectangularize 52 72 X4NRGData).getD 9 [] := by
  decide

private theorem x4NRGRow10_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 10 [] =
      (rectangularize 52 72 X4NRGData).getD 10 [] := by
  decide

private theorem x4NRGRow11_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 11 [] =
      (rectangularize 52 72 X4NRGData).getD 11 [] := by
  decide

private theorem x4NRGRow12_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 12 [] =
      (rectangularize 52 72 X4NRGData).getD 12 [] := by
  decide

private theorem x4NRGRow13_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 13 [] =
      (rectangularize 52 72 X4NRGData).getD 13 [] := by
  decide

private theorem x4NRGRow14_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 14 [] =
      (rectangularize 52 72 X4NRGData).getD 14 [] := by
  decide

private theorem x4NRGRow15_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 15 [] =
      (rectangularize 52 72 X4NRGData).getD 15 [] := by
  decide

private theorem x4NRGRow16_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 16 [] =
      (rectangularize 52 72 X4NRGData).getD 16 [] := by
  decide

private theorem x4NRGRow17_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 17 [] =
      (rectangularize 52 72 X4NRGData).getD 17 [] := by
  decide

private theorem x4NRGRow18_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 18 [] =
      (rectangularize 52 72 X4NRGData).getD 18 [] := by
  decide

private theorem x4NRGRow19Coeff0_spec :
    mulCoeffTwo GData X4NRC3Data 19 0 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 0 0 := by
  decide

private theorem x4NRGRow19Coeff1_spec :
    mulCoeffTwo GData X4NRC3Data 19 1 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 1 0 := by
  decide

private theorem x4NRGRow19Coeff2_spec :
    mulCoeffTwo GData X4NRC3Data 19 2 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 2 0 := by
  decide

private theorem x4NRGRow19Coeff3_spec :
    mulCoeffTwo GData X4NRC3Data 19 3 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 3 0 := by
  decide

private theorem x4NRGRow19Coeff4_spec :
    mulCoeffTwo GData X4NRC3Data 19 4 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 4 0 := by
  decide

private theorem x4NRGRow19Coeff5_spec :
    mulCoeffTwo GData X4NRC3Data 19 5 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 5 0 := by
  decide

private theorem x4NRGRow19Coeff6_spec :
    mulCoeffTwo GData X4NRC3Data 19 6 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 6 0 := by
  decide

private theorem x4NRGRow19Coeff7_spec :
    mulCoeffTwo GData X4NRC3Data 19 7 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 7 0 := by
  decide

private theorem x4NRGRow19Coeff8_spec :
    mulCoeffTwo GData X4NRC3Data 19 8 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 8 0 := by
  decide

private theorem x4NRGRow19Coeff9_spec :
    mulCoeffTwo GData X4NRC3Data 19 9 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 9 0 := by
  decide

private theorem x4NRGRow19Coeff10_spec :
    mulCoeffTwo GData X4NRC3Data 19 10 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 10 0 := by
  decide

private theorem x4NRGRow19Coeff11_spec :
    mulCoeffTwo GData X4NRC3Data 19 11 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 11 0 := by
  decide

private theorem x4NRGRow19Coeff12_spec :
    mulCoeffTwo GData X4NRC3Data 19 12 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 12 0 := by
  decide

private theorem x4NRGRow19Coeff13_spec :
    mulCoeffTwo GData X4NRC3Data 19 13 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 13 0 := by
  decide

private theorem x4NRGRow19Coeff14_spec :
    mulCoeffTwo GData X4NRC3Data 19 14 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 14 0 := by
  decide

private theorem x4NRGRow19Coeff15_spec :
    mulCoeffTwo GData X4NRC3Data 19 15 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 15 0 := by
  decide

private theorem x4NRGRow19Coeff16_spec :
    mulCoeffTwo GData X4NRC3Data 19 16 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 16 0 := by
  decide

private theorem x4NRGRow19Coeff17_spec :
    mulCoeffTwo GData X4NRC3Data 19 17 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 17 0 := by
  decide

private theorem x4NRGRow19Coeff18_spec :
    mulCoeffTwo GData X4NRC3Data 19 18 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 18 0 := by
  decide

private theorem x4NRGRow19Coeff19_spec :
    mulCoeffTwo GData X4NRC3Data 19 19 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 19 0 := by
  decide

private theorem x4NRGRow19Coeff20_spec :
    mulCoeffTwo GData X4NRC3Data 19 20 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 20 0 := by
  decide

private theorem x4NRGRow19Coeff21_spec :
    mulCoeffTwo GData X4NRC3Data 19 21 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 21 0 := by
  decide

private theorem x4NRGRow19Coeff22_spec :
    mulCoeffTwo GData X4NRC3Data 19 22 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 22 0 := by
  decide

private theorem x4NRGRow19Coeff23_spec :
    mulCoeffTwo GData X4NRC3Data 19 23 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 23 0 := by
  decide

private theorem x4NRGRow19Coeff24_spec :
    mulCoeffTwo GData X4NRC3Data 19 24 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 24 0 := by
  decide

private theorem x4NRGRow19Coeff25_spec :
    mulCoeffTwo GData X4NRC3Data 19 25 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 25 0 := by
  decide

private theorem x4NRGRow19Coeff26_spec :
    mulCoeffTwo GData X4NRC3Data 19 26 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 26 0 := by
  decide

private theorem x4NRGRow19Coeff27_spec :
    mulCoeffTwo GData X4NRC3Data 19 27 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 27 0 := by
  decide

private theorem x4NRGRow19Coeff28_spec :
    mulCoeffTwo GData X4NRC3Data 19 28 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 28 0 := by
  decide

private theorem x4NRGRow19Coeff29_spec :
    mulCoeffTwo GData X4NRC3Data 19 29 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 29 0 := by
  decide

private theorem x4NRGRow19Coeff30_spec :
    mulCoeffTwo GData X4NRC3Data 19 30 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 30 0 := by
  decide

private theorem x4NRGRow19Coeff31_spec :
    mulCoeffTwo GData X4NRC3Data 19 31 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 31 0 := by
  decide

private theorem x4NRGRow19Coeff32_spec :
    mulCoeffTwo GData X4NRC3Data 19 32 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 32 0 := by
  decide

private theorem x4NRGRow19Coeff33_spec :
    mulCoeffTwo GData X4NRC3Data 19 33 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 33 0 := by
  decide

private theorem x4NRGRow19Coeff34_spec :
    mulCoeffTwo GData X4NRC3Data 19 34 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 34 0 := by
  decide

private theorem x4NRGRow19Coeff35_spec :
    mulCoeffTwo GData X4NRC3Data 19 35 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 35 0 := by
  decide

private theorem x4NRGRow19Coeff36_spec :
    mulCoeffTwo GData X4NRC3Data 19 36 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 36 0 := by
  decide

private theorem x4NRGRow19Coeff37_spec :
    mulCoeffTwo GData X4NRC3Data 19 37 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 37 0 := by
  decide

private theorem x4NRGRow19Coeff38_spec :
    mulCoeffTwo GData X4NRC3Data 19 38 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 38 0 := by
  decide

private theorem x4NRGRow19Coeff39_spec :
    mulCoeffTwo GData X4NRC3Data 19 39 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 39 0 := by
  decide

private theorem x4NRGRow19Coeff40_spec :
    mulCoeffTwo GData X4NRC3Data 19 40 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 40 0 := by
  decide

private theorem x4NRGRow19Coeff41_spec :
    mulCoeffTwo GData X4NRC3Data 19 41 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 41 0 := by
  decide

private theorem x4NRGRow19Coeff42_spec :
    mulCoeffTwo GData X4NRC3Data 19 42 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 42 0 := by
  decide

private theorem x4NRGRow19Coeff43_spec :
    mulCoeffTwo GData X4NRC3Data 19 43 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 43 0 := by
  decide

private theorem x4NRGRow19Coeff44_spec :
    mulCoeffTwo GData X4NRC3Data 19 44 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 44 0 := by
  decide

private theorem x4NRGRow19Coeff45_spec :
    mulCoeffTwo GData X4NRC3Data 19 45 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 45 0 := by
  decide

private theorem x4NRGRow19Coeff46_spec :
    mulCoeffTwo GData X4NRC3Data 19 46 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 46 0 := by
  decide

private theorem x4NRGRow19Coeff47_spec :
    mulCoeffTwo GData X4NRC3Data 19 47 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 47 0 := by
  decide

private theorem x4NRGRow19Coeff48_spec :
    mulCoeffTwo GData X4NRC3Data 19 48 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 48 0 := by
  decide

private theorem x4NRGRow19Coeff49_spec :
    mulCoeffTwo GData X4NRC3Data 19 49 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 49 0 := by
  decide

private theorem x4NRGRow19Coeff50_spec :
    mulCoeffTwo GData X4NRC3Data 19 50 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 50 0 := by
  decide

private theorem x4NRGRow19Coeff51_spec :
    mulCoeffTwo GData X4NRC3Data 19 51 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 51 0 := by
  decide

private theorem x4NRGRow19Coeff52_spec :
    mulCoeffTwo GData X4NRC3Data 19 52 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 52 0 := by
  decide

private theorem x4NRGRow19Coeff53_spec :
    mulCoeffTwo GData X4NRC3Data 19 53 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 53 0 := by
  decide

private theorem x4NRGRow19Coeff54_spec :
    mulCoeffTwo GData X4NRC3Data 19 54 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 54 0 := by
  decide

private theorem x4NRGRow19Coeff55_spec :
    mulCoeffTwo GData X4NRC3Data 19 55 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 55 0 := by
  decide

private theorem x4NRGRow19Coeff56_spec :
    mulCoeffTwo GData X4NRC3Data 19 56 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 56 0 := by
  decide

private theorem x4NRGRow19Coeff57_spec :
    mulCoeffTwo GData X4NRC3Data 19 57 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 57 0 := by
  decide

private theorem x4NRGRow19Coeff58_spec :
    mulCoeffTwo GData X4NRC3Data 19 58 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 58 0 := by
  decide

private theorem x4NRGRow19Coeff59_spec :
    mulCoeffTwo GData X4NRC3Data 19 59 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 59 0 := by
  decide

private theorem x4NRGRow19Coeff60_spec :
    mulCoeffTwo GData X4NRC3Data 19 60 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 60 0 := by
  decide

private theorem x4NRGRow19Coeff61_spec :
    mulCoeffTwo GData X4NRC3Data 19 61 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 61 0 := by
  decide

private theorem x4NRGRow19Coeff62_spec :
    mulCoeffTwo GData X4NRC3Data 19 62 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 62 0 := by
  decide

private theorem x4NRGRow19Coeff63_spec :
    mulCoeffTwo GData X4NRC3Data 19 63 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 63 0 := by
  decide

private theorem x4NRGRow19Coeff64_spec :
    mulCoeffTwo GData X4NRC3Data 19 64 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 64 0 := by
  decide

private theorem x4NRGRow19Coeff65_spec :
    mulCoeffTwo GData X4NRC3Data 19 65 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 65 0 := by
  decide

private theorem x4NRGRow19Coeff66_spec :
    mulCoeffTwo GData X4NRC3Data 19 66 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 66 0 := by
  decide

private theorem x4NRGRow19Coeff67_spec :
    mulCoeffTwo GData X4NRC3Data 19 67 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 67 0 := by
  decide

private theorem x4NRGRow19Coeff68_spec :
    mulCoeffTwo GData X4NRC3Data 19 68 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 68 0 := by
  decide

private theorem x4NRGRow19Coeff69_spec :
    mulCoeffTwo GData X4NRC3Data 19 69 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 69 0 := by
  decide

private theorem x4NRGRow19Coeff70_spec :
    mulCoeffTwo GData X4NRC3Data 19 70 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 70 0 := by
  decide

private theorem x4NRGRow19Coeff71_spec :
    mulCoeffTwo GData X4NRC3Data 19 71 =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD 71 0 := by
  decide

private theorem x4NRGRow19Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo GData X4NRC3Data 19 j =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow19Coeff0_spec
  · exact x4NRGRow19Coeff1_spec
  · exact x4NRGRow19Coeff2_spec
  · exact x4NRGRow19Coeff3_spec
  · exact x4NRGRow19Coeff4_spec
  · exact x4NRGRow19Coeff5_spec
  · exact x4NRGRow19Coeff6_spec
  · exact x4NRGRow19Coeff7_spec
  · exact x4NRGRow19Coeff8_spec
  · exact x4NRGRow19Coeff9_spec

private theorem x4NRGRow19Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo GData X4NRC3Data 19 j =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow19Coeff10_spec
  · exact x4NRGRow19Coeff11_spec
  · exact x4NRGRow19Coeff12_spec
  · exact x4NRGRow19Coeff13_spec
  · exact x4NRGRow19Coeff14_spec
  · exact x4NRGRow19Coeff15_spec
  · exact x4NRGRow19Coeff16_spec
  · exact x4NRGRow19Coeff17_spec
  · exact x4NRGRow19Coeff18_spec
  · exact x4NRGRow19Coeff19_spec

private theorem x4NRGRow19Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo GData X4NRC3Data 19 j =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow19Coeff20_spec
  · exact x4NRGRow19Coeff21_spec
  · exact x4NRGRow19Coeff22_spec
  · exact x4NRGRow19Coeff23_spec
  · exact x4NRGRow19Coeff24_spec
  · exact x4NRGRow19Coeff25_spec
  · exact x4NRGRow19Coeff26_spec
  · exact x4NRGRow19Coeff27_spec
  · exact x4NRGRow19Coeff28_spec
  · exact x4NRGRow19Coeff29_spec

private theorem x4NRGRow19Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo GData X4NRC3Data 19 j =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow19Coeff30_spec
  · exact x4NRGRow19Coeff31_spec
  · exact x4NRGRow19Coeff32_spec
  · exact x4NRGRow19Coeff33_spec
  · exact x4NRGRow19Coeff34_spec
  · exact x4NRGRow19Coeff35_spec
  · exact x4NRGRow19Coeff36_spec
  · exact x4NRGRow19Coeff37_spec
  · exact x4NRGRow19Coeff38_spec
  · exact x4NRGRow19Coeff39_spec

private theorem x4NRGRow19Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo GData X4NRC3Data 19 j =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow19Coeff40_spec
  · exact x4NRGRow19Coeff41_spec
  · exact x4NRGRow19Coeff42_spec
  · exact x4NRGRow19Coeff43_spec
  · exact x4NRGRow19Coeff44_spec
  · exact x4NRGRow19Coeff45_spec
  · exact x4NRGRow19Coeff46_spec
  · exact x4NRGRow19Coeff47_spec
  · exact x4NRGRow19Coeff48_spec
  · exact x4NRGRow19Coeff49_spec

private theorem x4NRGRow19Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo GData X4NRC3Data 19 j =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow19Coeff50_spec
  · exact x4NRGRow19Coeff51_spec
  · exact x4NRGRow19Coeff52_spec
  · exact x4NRGRow19Coeff53_spec
  · exact x4NRGRow19Coeff54_spec
  · exact x4NRGRow19Coeff55_spec
  · exact x4NRGRow19Coeff56_spec
  · exact x4NRGRow19Coeff57_spec
  · exact x4NRGRow19Coeff58_spec
  · exact x4NRGRow19Coeff59_spec

private theorem x4NRGRow19Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo GData X4NRC3Data 19 j =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow19Coeff60_spec
  · exact x4NRGRow19Coeff61_spec
  · exact x4NRGRow19Coeff62_spec
  · exact x4NRGRow19Coeff63_spec
  · exact x4NRGRow19Coeff64_spec
  · exact x4NRGRow19Coeff65_spec
  · exact x4NRGRow19Coeff66_spec
  · exact x4NRGRow19Coeff67_spec
  · exact x4NRGRow19Coeff68_spec
  · exact x4NRGRow19Coeff69_spec

private theorem x4NRGRow19Coeffs70To71_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 72) :
    mulCoeffTwo GData X4NRC3Data 19 j =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 := by
    omega
  rcases hCases with
    rfl | rfl
  · exact x4NRGRow19Coeff70_spec
  · exact x4NRGRow19Coeff71_spec

private theorem x4NRGRow19_coefficients (j : ℕ) (hj : j < 72) :
    mulCoeffTwo GData X4NRC3Data 19 j =
      ((rectangularize 52 72 X4NRGData).getD 19 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact x4NRGRow19Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact x4NRGRow19Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact x4NRGRow19Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact x4NRGRow19Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact x4NRGRow19Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact x4NRGRow19Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact x4NRGRow19Coeffs60To69_spec j (by omega) h70
  exact x4NRGRow19Coeffs70To71_spec j (by omega) hj

private theorem x4NRGRow19Padded_spec :
    padOne 72 (mulRow GData X4NRC3Data 19) =
      (rectangularize 52 72 X4NRGData).getD 19 [] := by
  apply padOne_mulRow_eq_of_coefficients 72 GData X4NRC3Data 19
    ((rectangularize 52 72 X4NRGData).getD 19 [])
  · decide
  · have hTargetSupport : (X4NRGData.getD 19 []).length ≤ 72 := by
      decide
    rw [getD_rectangularize 52 72 X4NRGData 19 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact x4NRGRow19_coefficients

private theorem x4NRGRow19_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 19 [] =
      (rectangularize 52 72 X4NRGData).getD 19 [] := by
  rw [getD_rectangularize 52 72 (Two.mul GData X4NRC3Data) 19 (by omega),
    ← mulRow_eq_getD]
  exact x4NRGRow19Padded_spec

private theorem x4NRGRow20Coeff0_spec :
    mulCoeffTwo GData X4NRC3Data 20 0 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 0 0 := by
  decide

private theorem x4NRGRow20Coeff1_spec :
    mulCoeffTwo GData X4NRC3Data 20 1 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 1 0 := by
  decide

private theorem x4NRGRow20Coeff2_spec :
    mulCoeffTwo GData X4NRC3Data 20 2 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 2 0 := by
  decide

private theorem x4NRGRow20Coeff3_spec :
    mulCoeffTwo GData X4NRC3Data 20 3 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 3 0 := by
  decide

private theorem x4NRGRow20Coeff4_spec :
    mulCoeffTwo GData X4NRC3Data 20 4 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 4 0 := by
  decide

private theorem x4NRGRow20Coeff5_spec :
    mulCoeffTwo GData X4NRC3Data 20 5 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 5 0 := by
  decide

private theorem x4NRGRow20Coeff6_spec :
    mulCoeffTwo GData X4NRC3Data 20 6 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 6 0 := by
  decide

private theorem x4NRGRow20Coeff7_spec :
    mulCoeffTwo GData X4NRC3Data 20 7 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 7 0 := by
  decide

private theorem x4NRGRow20Coeff8_spec :
    mulCoeffTwo GData X4NRC3Data 20 8 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 8 0 := by
  decide

private theorem x4NRGRow20Coeff9_spec :
    mulCoeffTwo GData X4NRC3Data 20 9 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 9 0 := by
  decide

private theorem x4NRGRow20Coeff10_spec :
    mulCoeffTwo GData X4NRC3Data 20 10 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 10 0 := by
  decide

private theorem x4NRGRow20Coeff11_spec :
    mulCoeffTwo GData X4NRC3Data 20 11 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 11 0 := by
  decide

private theorem x4NRGRow20Coeff12_spec :
    mulCoeffTwo GData X4NRC3Data 20 12 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 12 0 := by
  decide

private theorem x4NRGRow20Coeff13_spec :
    mulCoeffTwo GData X4NRC3Data 20 13 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 13 0 := by
  decide

private theorem x4NRGRow20Coeff14_spec :
    mulCoeffTwo GData X4NRC3Data 20 14 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 14 0 := by
  decide

private theorem x4NRGRow20Coeff15_spec :
    mulCoeffTwo GData X4NRC3Data 20 15 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 15 0 := by
  decide

private theorem x4NRGRow20Coeff16_spec :
    mulCoeffTwo GData X4NRC3Data 20 16 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 16 0 := by
  decide

private theorem x4NRGRow20Coeff17_spec :
    mulCoeffTwo GData X4NRC3Data 20 17 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 17 0 := by
  decide

private theorem x4NRGRow20Coeff18_spec :
    mulCoeffTwo GData X4NRC3Data 20 18 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 18 0 := by
  decide

private theorem x4NRGRow20Coeff19_spec :
    mulCoeffTwo GData X4NRC3Data 20 19 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 19 0 := by
  decide

private theorem x4NRGRow20Coeff20_spec :
    mulCoeffTwo GData X4NRC3Data 20 20 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 20 0 := by
  decide

private theorem x4NRGRow20Coeff21_spec :
    mulCoeffTwo GData X4NRC3Data 20 21 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 21 0 := by
  decide

private theorem x4NRGRow20Coeff22_spec :
    mulCoeffTwo GData X4NRC3Data 20 22 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 22 0 := by
  decide

private theorem x4NRGRow20Coeff23_spec :
    mulCoeffTwo GData X4NRC3Data 20 23 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 23 0 := by
  decide

private theorem x4NRGRow20Coeff24_spec :
    mulCoeffTwo GData X4NRC3Data 20 24 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 24 0 := by
  decide

private theorem x4NRGRow20Coeff25_spec :
    mulCoeffTwo GData X4NRC3Data 20 25 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 25 0 := by
  decide

private theorem x4NRGRow20Coeff26_spec :
    mulCoeffTwo GData X4NRC3Data 20 26 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 26 0 := by
  decide

private theorem x4NRGRow20Coeff27_spec :
    mulCoeffTwo GData X4NRC3Data 20 27 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 27 0 := by
  decide

private theorem x4NRGRow20Coeff28_spec :
    mulCoeffTwo GData X4NRC3Data 20 28 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 28 0 := by
  decide

private theorem x4NRGRow20Coeff29_spec :
    mulCoeffTwo GData X4NRC3Data 20 29 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 29 0 := by
  decide

private theorem x4NRGRow20Coeff30_spec :
    mulCoeffTwo GData X4NRC3Data 20 30 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 30 0 := by
  decide

private theorem x4NRGRow20Coeff31_spec :
    mulCoeffTwo GData X4NRC3Data 20 31 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 31 0 := by
  decide

private theorem x4NRGRow20Coeff32_spec :
    mulCoeffTwo GData X4NRC3Data 20 32 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 32 0 := by
  decide

private theorem x4NRGRow20Coeff33_spec :
    mulCoeffTwo GData X4NRC3Data 20 33 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 33 0 := by
  decide

private theorem x4NRGRow20Coeff34_spec :
    mulCoeffTwo GData X4NRC3Data 20 34 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 34 0 := by
  decide

private theorem x4NRGRow20Coeff35_spec :
    mulCoeffTwo GData X4NRC3Data 20 35 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 35 0 := by
  decide

private theorem x4NRGRow20Coeff36_spec :
    mulCoeffTwo GData X4NRC3Data 20 36 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 36 0 := by
  decide

private theorem x4NRGRow20Coeff37_spec :
    mulCoeffTwo GData X4NRC3Data 20 37 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 37 0 := by
  decide

private theorem x4NRGRow20Coeff38_spec :
    mulCoeffTwo GData X4NRC3Data 20 38 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 38 0 := by
  decide

private theorem x4NRGRow20Coeff39_spec :
    mulCoeffTwo GData X4NRC3Data 20 39 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 39 0 := by
  decide

private theorem x4NRGRow20Coeff40_spec :
    mulCoeffTwo GData X4NRC3Data 20 40 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 40 0 := by
  decide

private theorem x4NRGRow20Coeff41_spec :
    mulCoeffTwo GData X4NRC3Data 20 41 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 41 0 := by
  decide

private theorem x4NRGRow20Coeff42_spec :
    mulCoeffTwo GData X4NRC3Data 20 42 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 42 0 := by
  decide

private theorem x4NRGRow20Coeff43_spec :
    mulCoeffTwo GData X4NRC3Data 20 43 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 43 0 := by
  decide

private theorem x4NRGRow20Coeff44_spec :
    mulCoeffTwo GData X4NRC3Data 20 44 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 44 0 := by
  decide

private theorem x4NRGRow20Coeff45_spec :
    mulCoeffTwo GData X4NRC3Data 20 45 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 45 0 := by
  decide

private theorem x4NRGRow20Coeff46_spec :
    mulCoeffTwo GData X4NRC3Data 20 46 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 46 0 := by
  decide

private theorem x4NRGRow20Coeff47_spec :
    mulCoeffTwo GData X4NRC3Data 20 47 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 47 0 := by
  decide

private theorem x4NRGRow20Coeff48_spec :
    mulCoeffTwo GData X4NRC3Data 20 48 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 48 0 := by
  decide

private theorem x4NRGRow20Coeff49_spec :
    mulCoeffTwo GData X4NRC3Data 20 49 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 49 0 := by
  decide

private theorem x4NRGRow20Coeff50_spec :
    mulCoeffTwo GData X4NRC3Data 20 50 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 50 0 := by
  decide

private theorem x4NRGRow20Coeff51_spec :
    mulCoeffTwo GData X4NRC3Data 20 51 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 51 0 := by
  decide

private theorem x4NRGRow20Coeff52_spec :
    mulCoeffTwo GData X4NRC3Data 20 52 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 52 0 := by
  decide

private theorem x4NRGRow20Coeff53_spec :
    mulCoeffTwo GData X4NRC3Data 20 53 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 53 0 := by
  decide

private theorem x4NRGRow20Coeff54_spec :
    mulCoeffTwo GData X4NRC3Data 20 54 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 54 0 := by
  decide

private theorem x4NRGRow20Coeff55_spec :
    mulCoeffTwo GData X4NRC3Data 20 55 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 55 0 := by
  decide

private theorem x4NRGRow20Coeff56_spec :
    mulCoeffTwo GData X4NRC3Data 20 56 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 56 0 := by
  decide

private theorem x4NRGRow20Coeff57_spec :
    mulCoeffTwo GData X4NRC3Data 20 57 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 57 0 := by
  decide

private theorem x4NRGRow20Coeff58_spec :
    mulCoeffTwo GData X4NRC3Data 20 58 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 58 0 := by
  decide

private theorem x4NRGRow20Coeff59_spec :
    mulCoeffTwo GData X4NRC3Data 20 59 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 59 0 := by
  decide

private theorem x4NRGRow20Coeff60_spec :
    mulCoeffTwo GData X4NRC3Data 20 60 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 60 0 := by
  decide

private theorem x4NRGRow20Coeff61_spec :
    mulCoeffTwo GData X4NRC3Data 20 61 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 61 0 := by
  decide

private theorem x4NRGRow20Coeff62_spec :
    mulCoeffTwo GData X4NRC3Data 20 62 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 62 0 := by
  decide

private theorem x4NRGRow20Coeff63_spec :
    mulCoeffTwo GData X4NRC3Data 20 63 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 63 0 := by
  decide

private theorem x4NRGRow20Coeff64_spec :
    mulCoeffTwo GData X4NRC3Data 20 64 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 64 0 := by
  decide

private theorem x4NRGRow20Coeff65_spec :
    mulCoeffTwo GData X4NRC3Data 20 65 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 65 0 := by
  decide

private theorem x4NRGRow20Coeff66_spec :
    mulCoeffTwo GData X4NRC3Data 20 66 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 66 0 := by
  decide

private theorem x4NRGRow20Coeff67_spec :
    mulCoeffTwo GData X4NRC3Data 20 67 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 67 0 := by
  decide

private theorem x4NRGRow20Coeff68_spec :
    mulCoeffTwo GData X4NRC3Data 20 68 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 68 0 := by
  decide

private theorem x4NRGRow20Coeff69_spec :
    mulCoeffTwo GData X4NRC3Data 20 69 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 69 0 := by
  decide

private theorem x4NRGRow20Coeff70_spec :
    mulCoeffTwo GData X4NRC3Data 20 70 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 70 0 := by
  decide

private theorem x4NRGRow20Coeff71_spec :
    mulCoeffTwo GData X4NRC3Data 20 71 =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD 71 0 := by
  decide

private theorem x4NRGRow20Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo GData X4NRC3Data 20 j =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow20Coeff0_spec
  · exact x4NRGRow20Coeff1_spec
  · exact x4NRGRow20Coeff2_spec
  · exact x4NRGRow20Coeff3_spec
  · exact x4NRGRow20Coeff4_spec
  · exact x4NRGRow20Coeff5_spec
  · exact x4NRGRow20Coeff6_spec
  · exact x4NRGRow20Coeff7_spec
  · exact x4NRGRow20Coeff8_spec
  · exact x4NRGRow20Coeff9_spec

private theorem x4NRGRow20Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo GData X4NRC3Data 20 j =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow20Coeff10_spec
  · exact x4NRGRow20Coeff11_spec
  · exact x4NRGRow20Coeff12_spec
  · exact x4NRGRow20Coeff13_spec
  · exact x4NRGRow20Coeff14_spec
  · exact x4NRGRow20Coeff15_spec
  · exact x4NRGRow20Coeff16_spec
  · exact x4NRGRow20Coeff17_spec
  · exact x4NRGRow20Coeff18_spec
  · exact x4NRGRow20Coeff19_spec

private theorem x4NRGRow20Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo GData X4NRC3Data 20 j =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow20Coeff20_spec
  · exact x4NRGRow20Coeff21_spec
  · exact x4NRGRow20Coeff22_spec
  · exact x4NRGRow20Coeff23_spec
  · exact x4NRGRow20Coeff24_spec
  · exact x4NRGRow20Coeff25_spec
  · exact x4NRGRow20Coeff26_spec
  · exact x4NRGRow20Coeff27_spec
  · exact x4NRGRow20Coeff28_spec
  · exact x4NRGRow20Coeff29_spec

private theorem x4NRGRow20Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo GData X4NRC3Data 20 j =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow20Coeff30_spec
  · exact x4NRGRow20Coeff31_spec
  · exact x4NRGRow20Coeff32_spec
  · exact x4NRGRow20Coeff33_spec
  · exact x4NRGRow20Coeff34_spec
  · exact x4NRGRow20Coeff35_spec
  · exact x4NRGRow20Coeff36_spec
  · exact x4NRGRow20Coeff37_spec
  · exact x4NRGRow20Coeff38_spec
  · exact x4NRGRow20Coeff39_spec

private theorem x4NRGRow20Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo GData X4NRC3Data 20 j =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow20Coeff40_spec
  · exact x4NRGRow20Coeff41_spec
  · exact x4NRGRow20Coeff42_spec
  · exact x4NRGRow20Coeff43_spec
  · exact x4NRGRow20Coeff44_spec
  · exact x4NRGRow20Coeff45_spec
  · exact x4NRGRow20Coeff46_spec
  · exact x4NRGRow20Coeff47_spec
  · exact x4NRGRow20Coeff48_spec
  · exact x4NRGRow20Coeff49_spec

private theorem x4NRGRow20Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo GData X4NRC3Data 20 j =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow20Coeff50_spec
  · exact x4NRGRow20Coeff51_spec
  · exact x4NRGRow20Coeff52_spec
  · exact x4NRGRow20Coeff53_spec
  · exact x4NRGRow20Coeff54_spec
  · exact x4NRGRow20Coeff55_spec
  · exact x4NRGRow20Coeff56_spec
  · exact x4NRGRow20Coeff57_spec
  · exact x4NRGRow20Coeff58_spec
  · exact x4NRGRow20Coeff59_spec

private theorem x4NRGRow20Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo GData X4NRC3Data 20 j =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow20Coeff60_spec
  · exact x4NRGRow20Coeff61_spec
  · exact x4NRGRow20Coeff62_spec
  · exact x4NRGRow20Coeff63_spec
  · exact x4NRGRow20Coeff64_spec
  · exact x4NRGRow20Coeff65_spec
  · exact x4NRGRow20Coeff66_spec
  · exact x4NRGRow20Coeff67_spec
  · exact x4NRGRow20Coeff68_spec
  · exact x4NRGRow20Coeff69_spec

private theorem x4NRGRow20Coeffs70To71_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 72) :
    mulCoeffTwo GData X4NRC3Data 20 j =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 := by
    omega
  rcases hCases with
    rfl | rfl
  · exact x4NRGRow20Coeff70_spec
  · exact x4NRGRow20Coeff71_spec

private theorem x4NRGRow20_coefficients (j : ℕ) (hj : j < 72) :
    mulCoeffTwo GData X4NRC3Data 20 j =
      ((rectangularize 52 72 X4NRGData).getD 20 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact x4NRGRow20Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact x4NRGRow20Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact x4NRGRow20Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact x4NRGRow20Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact x4NRGRow20Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact x4NRGRow20Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact x4NRGRow20Coeffs60To69_spec j (by omega) h70
  exact x4NRGRow20Coeffs70To71_spec j (by omega) hj

private theorem x4NRGRow20Padded_spec :
    padOne 72 (mulRow GData X4NRC3Data 20) =
      (rectangularize 52 72 X4NRGData).getD 20 [] := by
  apply padOne_mulRow_eq_of_coefficients 72 GData X4NRC3Data 20
    ((rectangularize 52 72 X4NRGData).getD 20 [])
  · decide
  · have hTargetSupport : (X4NRGData.getD 20 []).length ≤ 72 := by
      decide
    rw [getD_rectangularize 52 72 X4NRGData 20 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact x4NRGRow20_coefficients

private theorem x4NRGRow20_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 20 [] =
      (rectangularize 52 72 X4NRGData).getD 20 [] := by
  rw [getD_rectangularize 52 72 (Two.mul GData X4NRC3Data) 20 (by omega),
    ← mulRow_eq_getD]
  exact x4NRGRow20Padded_spec

private theorem x4NRGRow21Coeff0_spec :
    mulCoeffTwo GData X4NRC3Data 21 0 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 0 0 := by
  decide

private theorem x4NRGRow21Coeff1_spec :
    mulCoeffTwo GData X4NRC3Data 21 1 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 1 0 := by
  decide

private theorem x4NRGRow21Coeff2_spec :
    mulCoeffTwo GData X4NRC3Data 21 2 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 2 0 := by
  decide

private theorem x4NRGRow21Coeff3_spec :
    mulCoeffTwo GData X4NRC3Data 21 3 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 3 0 := by
  decide

private theorem x4NRGRow21Coeff4_spec :
    mulCoeffTwo GData X4NRC3Data 21 4 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 4 0 := by
  decide

private theorem x4NRGRow21Coeff5_spec :
    mulCoeffTwo GData X4NRC3Data 21 5 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 5 0 := by
  decide

private theorem x4NRGRow21Coeff6_spec :
    mulCoeffTwo GData X4NRC3Data 21 6 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 6 0 := by
  decide

private theorem x4NRGRow21Coeff7_spec :
    mulCoeffTwo GData X4NRC3Data 21 7 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 7 0 := by
  decide

private theorem x4NRGRow21Coeff8_spec :
    mulCoeffTwo GData X4NRC3Data 21 8 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 8 0 := by
  decide

private theorem x4NRGRow21Coeff9_spec :
    mulCoeffTwo GData X4NRC3Data 21 9 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 9 0 := by
  decide

private theorem x4NRGRow21Coeff10_spec :
    mulCoeffTwo GData X4NRC3Data 21 10 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 10 0 := by
  decide

private theorem x4NRGRow21Coeff11_spec :
    mulCoeffTwo GData X4NRC3Data 21 11 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 11 0 := by
  decide

private theorem x4NRGRow21Coeff12_spec :
    mulCoeffTwo GData X4NRC3Data 21 12 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 12 0 := by
  decide

private theorem x4NRGRow21Coeff13_spec :
    mulCoeffTwo GData X4NRC3Data 21 13 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 13 0 := by
  decide

private theorem x4NRGRow21Coeff14_spec :
    mulCoeffTwo GData X4NRC3Data 21 14 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 14 0 := by
  decide

private theorem x4NRGRow21Coeff15_spec :
    mulCoeffTwo GData X4NRC3Data 21 15 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 15 0 := by
  decide

private theorem x4NRGRow21Coeff16_spec :
    mulCoeffTwo GData X4NRC3Data 21 16 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 16 0 := by
  decide

private theorem x4NRGRow21Coeff17_spec :
    mulCoeffTwo GData X4NRC3Data 21 17 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 17 0 := by
  decide

private theorem x4NRGRow21Coeff18_spec :
    mulCoeffTwo GData X4NRC3Data 21 18 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 18 0 := by
  decide

private theorem x4NRGRow21Coeff19_spec :
    mulCoeffTwo GData X4NRC3Data 21 19 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 19 0 := by
  decide

private theorem x4NRGRow21Coeff20_spec :
    mulCoeffTwo GData X4NRC3Data 21 20 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 20 0 := by
  decide

private theorem x4NRGRow21Coeff21_spec :
    mulCoeffTwo GData X4NRC3Data 21 21 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 21 0 := by
  decide

private theorem x4NRGRow21Coeff22_spec :
    mulCoeffTwo GData X4NRC3Data 21 22 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 22 0 := by
  decide

private theorem x4NRGRow21Coeff23_spec :
    mulCoeffTwo GData X4NRC3Data 21 23 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 23 0 := by
  decide

private theorem x4NRGRow21Coeff24_spec :
    mulCoeffTwo GData X4NRC3Data 21 24 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 24 0 := by
  decide

private theorem x4NRGRow21Coeff25_spec :
    mulCoeffTwo GData X4NRC3Data 21 25 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 25 0 := by
  decide

private theorem x4NRGRow21Coeff26_spec :
    mulCoeffTwo GData X4NRC3Data 21 26 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 26 0 := by
  decide

private theorem x4NRGRow21Coeff27_spec :
    mulCoeffTwo GData X4NRC3Data 21 27 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 27 0 := by
  decide

private theorem x4NRGRow21Coeff28_spec :
    mulCoeffTwo GData X4NRC3Data 21 28 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 28 0 := by
  decide

private theorem x4NRGRow21Coeff29_spec :
    mulCoeffTwo GData X4NRC3Data 21 29 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 29 0 := by
  decide

private theorem x4NRGRow21Coeff30_spec :
    mulCoeffTwo GData X4NRC3Data 21 30 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 30 0 := by
  decide

private theorem x4NRGRow21Coeff31_spec :
    mulCoeffTwo GData X4NRC3Data 21 31 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 31 0 := by
  decide

private theorem x4NRGRow21Coeff32_spec :
    mulCoeffTwo GData X4NRC3Data 21 32 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 32 0 := by
  decide

private theorem x4NRGRow21Coeff33_spec :
    mulCoeffTwo GData X4NRC3Data 21 33 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 33 0 := by
  decide

private theorem x4NRGRow21Coeff34_spec :
    mulCoeffTwo GData X4NRC3Data 21 34 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 34 0 := by
  decide

private theorem x4NRGRow21Coeff35_spec :
    mulCoeffTwo GData X4NRC3Data 21 35 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 35 0 := by
  decide

private theorem x4NRGRow21Coeff36_spec :
    mulCoeffTwo GData X4NRC3Data 21 36 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 36 0 := by
  decide

private theorem x4NRGRow21Coeff37_spec :
    mulCoeffTwo GData X4NRC3Data 21 37 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 37 0 := by
  decide

private theorem x4NRGRow21Coeff38_spec :
    mulCoeffTwo GData X4NRC3Data 21 38 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 38 0 := by
  decide

private theorem x4NRGRow21Coeff39_spec :
    mulCoeffTwo GData X4NRC3Data 21 39 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 39 0 := by
  decide

private theorem x4NRGRow21Coeff40_spec :
    mulCoeffTwo GData X4NRC3Data 21 40 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 40 0 := by
  decide

private theorem x4NRGRow21Coeff41_spec :
    mulCoeffTwo GData X4NRC3Data 21 41 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 41 0 := by
  decide

private theorem x4NRGRow21Coeff42_spec :
    mulCoeffTwo GData X4NRC3Data 21 42 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 42 0 := by
  decide

private theorem x4NRGRow21Coeff43_spec :
    mulCoeffTwo GData X4NRC3Data 21 43 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 43 0 := by
  decide

private theorem x4NRGRow21Coeff44_spec :
    mulCoeffTwo GData X4NRC3Data 21 44 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 44 0 := by
  decide

private theorem x4NRGRow21Coeff45_spec :
    mulCoeffTwo GData X4NRC3Data 21 45 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 45 0 := by
  decide

private theorem x4NRGRow21Coeff46_spec :
    mulCoeffTwo GData X4NRC3Data 21 46 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 46 0 := by
  decide

private theorem x4NRGRow21Coeff47_spec :
    mulCoeffTwo GData X4NRC3Data 21 47 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 47 0 := by
  decide

private theorem x4NRGRow21Coeff48_spec :
    mulCoeffTwo GData X4NRC3Data 21 48 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 48 0 := by
  decide

private theorem x4NRGRow21Coeff49_spec :
    mulCoeffTwo GData X4NRC3Data 21 49 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 49 0 := by
  decide

private theorem x4NRGRow21Coeff50_spec :
    mulCoeffTwo GData X4NRC3Data 21 50 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 50 0 := by
  decide

private theorem x4NRGRow21Coeff51_spec :
    mulCoeffTwo GData X4NRC3Data 21 51 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 51 0 := by
  decide

private theorem x4NRGRow21Coeff52_spec :
    mulCoeffTwo GData X4NRC3Data 21 52 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 52 0 := by
  decide

private theorem x4NRGRow21Coeff53_spec :
    mulCoeffTwo GData X4NRC3Data 21 53 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 53 0 := by
  decide

private theorem x4NRGRow21Coeff54_spec :
    mulCoeffTwo GData X4NRC3Data 21 54 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 54 0 := by
  decide

private theorem x4NRGRow21Coeff55_spec :
    mulCoeffTwo GData X4NRC3Data 21 55 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 55 0 := by
  decide

private theorem x4NRGRow21Coeff56_spec :
    mulCoeffTwo GData X4NRC3Data 21 56 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 56 0 := by
  decide

private theorem x4NRGRow21Coeff57_spec :
    mulCoeffTwo GData X4NRC3Data 21 57 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 57 0 := by
  decide

private theorem x4NRGRow21Coeff58_spec :
    mulCoeffTwo GData X4NRC3Data 21 58 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 58 0 := by
  decide

private theorem x4NRGRow21Coeff59_spec :
    mulCoeffTwo GData X4NRC3Data 21 59 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 59 0 := by
  decide

private theorem x4NRGRow21Coeff60_spec :
    mulCoeffTwo GData X4NRC3Data 21 60 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 60 0 := by
  decide

private theorem x4NRGRow21Coeff61_spec :
    mulCoeffTwo GData X4NRC3Data 21 61 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 61 0 := by
  decide

private theorem x4NRGRow21Coeff62_spec :
    mulCoeffTwo GData X4NRC3Data 21 62 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 62 0 := by
  decide

private theorem x4NRGRow21Coeff63_spec :
    mulCoeffTwo GData X4NRC3Data 21 63 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 63 0 := by
  decide

private theorem x4NRGRow21Coeff64_spec :
    mulCoeffTwo GData X4NRC3Data 21 64 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 64 0 := by
  decide

private theorem x4NRGRow21Coeff65_spec :
    mulCoeffTwo GData X4NRC3Data 21 65 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 65 0 := by
  decide

private theorem x4NRGRow21Coeff66_spec :
    mulCoeffTwo GData X4NRC3Data 21 66 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 66 0 := by
  decide

private theorem x4NRGRow21Coeff67_spec :
    mulCoeffTwo GData X4NRC3Data 21 67 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 67 0 := by
  decide

private theorem x4NRGRow21Coeff68_spec :
    mulCoeffTwo GData X4NRC3Data 21 68 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 68 0 := by
  decide

private theorem x4NRGRow21Coeff69_spec :
    mulCoeffTwo GData X4NRC3Data 21 69 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 69 0 := by
  decide

private theorem x4NRGRow21Coeff70_spec :
    mulCoeffTwo GData X4NRC3Data 21 70 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 70 0 := by
  decide

private theorem x4NRGRow21Coeff71_spec :
    mulCoeffTwo GData X4NRC3Data 21 71 =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD 71 0 := by
  decide

private theorem x4NRGRow21Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo GData X4NRC3Data 21 j =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow21Coeff0_spec
  · exact x4NRGRow21Coeff1_spec
  · exact x4NRGRow21Coeff2_spec
  · exact x4NRGRow21Coeff3_spec
  · exact x4NRGRow21Coeff4_spec
  · exact x4NRGRow21Coeff5_spec
  · exact x4NRGRow21Coeff6_spec
  · exact x4NRGRow21Coeff7_spec
  · exact x4NRGRow21Coeff8_spec
  · exact x4NRGRow21Coeff9_spec

private theorem x4NRGRow21Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo GData X4NRC3Data 21 j =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow21Coeff10_spec
  · exact x4NRGRow21Coeff11_spec
  · exact x4NRGRow21Coeff12_spec
  · exact x4NRGRow21Coeff13_spec
  · exact x4NRGRow21Coeff14_spec
  · exact x4NRGRow21Coeff15_spec
  · exact x4NRGRow21Coeff16_spec
  · exact x4NRGRow21Coeff17_spec
  · exact x4NRGRow21Coeff18_spec
  · exact x4NRGRow21Coeff19_spec

private theorem x4NRGRow21Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo GData X4NRC3Data 21 j =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow21Coeff20_spec
  · exact x4NRGRow21Coeff21_spec
  · exact x4NRGRow21Coeff22_spec
  · exact x4NRGRow21Coeff23_spec
  · exact x4NRGRow21Coeff24_spec
  · exact x4NRGRow21Coeff25_spec
  · exact x4NRGRow21Coeff26_spec
  · exact x4NRGRow21Coeff27_spec
  · exact x4NRGRow21Coeff28_spec
  · exact x4NRGRow21Coeff29_spec

private theorem x4NRGRow21Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo GData X4NRC3Data 21 j =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow21Coeff30_spec
  · exact x4NRGRow21Coeff31_spec
  · exact x4NRGRow21Coeff32_spec
  · exact x4NRGRow21Coeff33_spec
  · exact x4NRGRow21Coeff34_spec
  · exact x4NRGRow21Coeff35_spec
  · exact x4NRGRow21Coeff36_spec
  · exact x4NRGRow21Coeff37_spec
  · exact x4NRGRow21Coeff38_spec
  · exact x4NRGRow21Coeff39_spec

private theorem x4NRGRow21Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo GData X4NRC3Data 21 j =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow21Coeff40_spec
  · exact x4NRGRow21Coeff41_spec
  · exact x4NRGRow21Coeff42_spec
  · exact x4NRGRow21Coeff43_spec
  · exact x4NRGRow21Coeff44_spec
  · exact x4NRGRow21Coeff45_spec
  · exact x4NRGRow21Coeff46_spec
  · exact x4NRGRow21Coeff47_spec
  · exact x4NRGRow21Coeff48_spec
  · exact x4NRGRow21Coeff49_spec

private theorem x4NRGRow21Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo GData X4NRC3Data 21 j =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow21Coeff50_spec
  · exact x4NRGRow21Coeff51_spec
  · exact x4NRGRow21Coeff52_spec
  · exact x4NRGRow21Coeff53_spec
  · exact x4NRGRow21Coeff54_spec
  · exact x4NRGRow21Coeff55_spec
  · exact x4NRGRow21Coeff56_spec
  · exact x4NRGRow21Coeff57_spec
  · exact x4NRGRow21Coeff58_spec
  · exact x4NRGRow21Coeff59_spec

private theorem x4NRGRow21Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo GData X4NRC3Data 21 j =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow21Coeff60_spec
  · exact x4NRGRow21Coeff61_spec
  · exact x4NRGRow21Coeff62_spec
  · exact x4NRGRow21Coeff63_spec
  · exact x4NRGRow21Coeff64_spec
  · exact x4NRGRow21Coeff65_spec
  · exact x4NRGRow21Coeff66_spec
  · exact x4NRGRow21Coeff67_spec
  · exact x4NRGRow21Coeff68_spec
  · exact x4NRGRow21Coeff69_spec

private theorem x4NRGRow21Coeffs70To71_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 72) :
    mulCoeffTwo GData X4NRC3Data 21 j =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 := by
    omega
  rcases hCases with
    rfl | rfl
  · exact x4NRGRow21Coeff70_spec
  · exact x4NRGRow21Coeff71_spec

private theorem x4NRGRow21_coefficients (j : ℕ) (hj : j < 72) :
    mulCoeffTwo GData X4NRC3Data 21 j =
      ((rectangularize 52 72 X4NRGData).getD 21 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact x4NRGRow21Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact x4NRGRow21Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact x4NRGRow21Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact x4NRGRow21Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact x4NRGRow21Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact x4NRGRow21Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact x4NRGRow21Coeffs60To69_spec j (by omega) h70
  exact x4NRGRow21Coeffs70To71_spec j (by omega) hj

private theorem x4NRGRow21Padded_spec :
    padOne 72 (mulRow GData X4NRC3Data 21) =
      (rectangularize 52 72 X4NRGData).getD 21 [] := by
  apply padOne_mulRow_eq_of_coefficients 72 GData X4NRC3Data 21
    ((rectangularize 52 72 X4NRGData).getD 21 [])
  · decide
  · have hTargetSupport : (X4NRGData.getD 21 []).length ≤ 72 := by
      decide
    rw [getD_rectangularize 52 72 X4NRGData 21 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact x4NRGRow21_coefficients

private theorem x4NRGRow21_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 21 [] =
      (rectangularize 52 72 X4NRGData).getD 21 [] := by
  rw [getD_rectangularize 52 72 (Two.mul GData X4NRC3Data) 21 (by omega),
    ← mulRow_eq_getD]
  exact x4NRGRow21Padded_spec

private theorem x4NRGRow22Coeff0_spec :
    mulCoeffTwo GData X4NRC3Data 22 0 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 0 0 := by
  decide

private theorem x4NRGRow22Coeff1_spec :
    mulCoeffTwo GData X4NRC3Data 22 1 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 1 0 := by
  decide

private theorem x4NRGRow22Coeff2_spec :
    mulCoeffTwo GData X4NRC3Data 22 2 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 2 0 := by
  decide

private theorem x4NRGRow22Coeff3_spec :
    mulCoeffTwo GData X4NRC3Data 22 3 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 3 0 := by
  decide

private theorem x4NRGRow22Coeff4_spec :
    mulCoeffTwo GData X4NRC3Data 22 4 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 4 0 := by
  decide

private theorem x4NRGRow22Coeff5_spec :
    mulCoeffTwo GData X4NRC3Data 22 5 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 5 0 := by
  decide

private theorem x4NRGRow22Coeff6_spec :
    mulCoeffTwo GData X4NRC3Data 22 6 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 6 0 := by
  decide

private theorem x4NRGRow22Coeff7_spec :
    mulCoeffTwo GData X4NRC3Data 22 7 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 7 0 := by
  decide

private theorem x4NRGRow22Coeff8_spec :
    mulCoeffTwo GData X4NRC3Data 22 8 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 8 0 := by
  decide

private theorem x4NRGRow22Coeff9_spec :
    mulCoeffTwo GData X4NRC3Data 22 9 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 9 0 := by
  decide

private theorem x4NRGRow22Coeff10_spec :
    mulCoeffTwo GData X4NRC3Data 22 10 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 10 0 := by
  decide

private theorem x4NRGRow22Coeff11_spec :
    mulCoeffTwo GData X4NRC3Data 22 11 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 11 0 := by
  decide

private theorem x4NRGRow22Coeff12_spec :
    mulCoeffTwo GData X4NRC3Data 22 12 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 12 0 := by
  decide

private theorem x4NRGRow22Coeff13_spec :
    mulCoeffTwo GData X4NRC3Data 22 13 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 13 0 := by
  decide

private theorem x4NRGRow22Coeff14_spec :
    mulCoeffTwo GData X4NRC3Data 22 14 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 14 0 := by
  decide

private theorem x4NRGRow22Coeff15_spec :
    mulCoeffTwo GData X4NRC3Data 22 15 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 15 0 := by
  decide

private theorem x4NRGRow22Coeff16_spec :
    mulCoeffTwo GData X4NRC3Data 22 16 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 16 0 := by
  decide

private theorem x4NRGRow22Coeff17_spec :
    mulCoeffTwo GData X4NRC3Data 22 17 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 17 0 := by
  decide

private theorem x4NRGRow22Coeff18_spec :
    mulCoeffTwo GData X4NRC3Data 22 18 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 18 0 := by
  decide

private theorem x4NRGRow22Coeff19_spec :
    mulCoeffTwo GData X4NRC3Data 22 19 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 19 0 := by
  decide

private theorem x4NRGRow22Coeff20_spec :
    mulCoeffTwo GData X4NRC3Data 22 20 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 20 0 := by
  decide

private theorem x4NRGRow22Coeff21_spec :
    mulCoeffTwo GData X4NRC3Data 22 21 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 21 0 := by
  decide

private theorem x4NRGRow22Coeff22_spec :
    mulCoeffTwo GData X4NRC3Data 22 22 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 22 0 := by
  decide

private theorem x4NRGRow22Coeff23_spec :
    mulCoeffTwo GData X4NRC3Data 22 23 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 23 0 := by
  decide

private theorem x4NRGRow22Coeff24_spec :
    mulCoeffTwo GData X4NRC3Data 22 24 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 24 0 := by
  decide

private theorem x4NRGRow22Coeff25_spec :
    mulCoeffTwo GData X4NRC3Data 22 25 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 25 0 := by
  decide

private theorem x4NRGRow22Coeff26_spec :
    mulCoeffTwo GData X4NRC3Data 22 26 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 26 0 := by
  decide

private theorem x4NRGRow22Coeff27_spec :
    mulCoeffTwo GData X4NRC3Data 22 27 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 27 0 := by
  decide

private theorem x4NRGRow22Coeff28_spec :
    mulCoeffTwo GData X4NRC3Data 22 28 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 28 0 := by
  decide

private theorem x4NRGRow22Coeff29_spec :
    mulCoeffTwo GData X4NRC3Data 22 29 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 29 0 := by
  decide

private theorem x4NRGRow22Coeff30_spec :
    mulCoeffTwo GData X4NRC3Data 22 30 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 30 0 := by
  decide

private theorem x4NRGRow22Coeff31_spec :
    mulCoeffTwo GData X4NRC3Data 22 31 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 31 0 := by
  decide

private theorem x4NRGRow22Coeff32_spec :
    mulCoeffTwo GData X4NRC3Data 22 32 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 32 0 := by
  decide

private theorem x4NRGRow22Coeff33_spec :
    mulCoeffTwo GData X4NRC3Data 22 33 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 33 0 := by
  decide

private theorem x4NRGRow22Coeff34_spec :
    mulCoeffTwo GData X4NRC3Data 22 34 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 34 0 := by
  decide

private theorem x4NRGRow22Coeff35_spec :
    mulCoeffTwo GData X4NRC3Data 22 35 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 35 0 := by
  decide

private theorem x4NRGRow22Coeff36_spec :
    mulCoeffTwo GData X4NRC3Data 22 36 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 36 0 := by
  decide

private theorem x4NRGRow22Coeff37_spec :
    mulCoeffTwo GData X4NRC3Data 22 37 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 37 0 := by
  decide

private theorem x4NRGRow22Coeff38_spec :
    mulCoeffTwo GData X4NRC3Data 22 38 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 38 0 := by
  decide

private theorem x4NRGRow22Coeff39_spec :
    mulCoeffTwo GData X4NRC3Data 22 39 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 39 0 := by
  decide

private theorem x4NRGRow22Coeff40_spec :
    mulCoeffTwo GData X4NRC3Data 22 40 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 40 0 := by
  decide

private theorem x4NRGRow22Coeff41_spec :
    mulCoeffTwo GData X4NRC3Data 22 41 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 41 0 := by
  decide

private theorem x4NRGRow22Coeff42_spec :
    mulCoeffTwo GData X4NRC3Data 22 42 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 42 0 := by
  decide

private theorem x4NRGRow22Coeff43_spec :
    mulCoeffTwo GData X4NRC3Data 22 43 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 43 0 := by
  decide

private theorem x4NRGRow22Coeff44_spec :
    mulCoeffTwo GData X4NRC3Data 22 44 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 44 0 := by
  decide

private theorem x4NRGRow22Coeff45_spec :
    mulCoeffTwo GData X4NRC3Data 22 45 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 45 0 := by
  decide

private theorem x4NRGRow22Coeff46_spec :
    mulCoeffTwo GData X4NRC3Data 22 46 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 46 0 := by
  decide

private theorem x4NRGRow22Coeff47_spec :
    mulCoeffTwo GData X4NRC3Data 22 47 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 47 0 := by
  decide

private theorem x4NRGRow22Coeff48_spec :
    mulCoeffTwo GData X4NRC3Data 22 48 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 48 0 := by
  decide

private theorem x4NRGRow22Coeff49_spec :
    mulCoeffTwo GData X4NRC3Data 22 49 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 49 0 := by
  decide

private theorem x4NRGRow22Coeff50_spec :
    mulCoeffTwo GData X4NRC3Data 22 50 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 50 0 := by
  decide

private theorem x4NRGRow22Coeff51_spec :
    mulCoeffTwo GData X4NRC3Data 22 51 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 51 0 := by
  decide

private theorem x4NRGRow22Coeff52_spec :
    mulCoeffTwo GData X4NRC3Data 22 52 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 52 0 := by
  decide

private theorem x4NRGRow22Coeff53_spec :
    mulCoeffTwo GData X4NRC3Data 22 53 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 53 0 := by
  decide

private theorem x4NRGRow22Coeff54_spec :
    mulCoeffTwo GData X4NRC3Data 22 54 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 54 0 := by
  decide

private theorem x4NRGRow22Coeff55_spec :
    mulCoeffTwo GData X4NRC3Data 22 55 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 55 0 := by
  decide

private theorem x4NRGRow22Coeff56_spec :
    mulCoeffTwo GData X4NRC3Data 22 56 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 56 0 := by
  decide

private theorem x4NRGRow22Coeff57_spec :
    mulCoeffTwo GData X4NRC3Data 22 57 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 57 0 := by
  decide

private theorem x4NRGRow22Coeff58_spec :
    mulCoeffTwo GData X4NRC3Data 22 58 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 58 0 := by
  decide

private theorem x4NRGRow22Coeff59_spec :
    mulCoeffTwo GData X4NRC3Data 22 59 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 59 0 := by
  decide

private theorem x4NRGRow22Coeff60_spec :
    mulCoeffTwo GData X4NRC3Data 22 60 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 60 0 := by
  decide

private theorem x4NRGRow22Coeff61_spec :
    mulCoeffTwo GData X4NRC3Data 22 61 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 61 0 := by
  decide

private theorem x4NRGRow22Coeff62_spec :
    mulCoeffTwo GData X4NRC3Data 22 62 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 62 0 := by
  decide

private theorem x4NRGRow22Coeff63_spec :
    mulCoeffTwo GData X4NRC3Data 22 63 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 63 0 := by
  decide

private theorem x4NRGRow22Coeff64_spec :
    mulCoeffTwo GData X4NRC3Data 22 64 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 64 0 := by
  decide

private theorem x4NRGRow22Coeff65_spec :
    mulCoeffTwo GData X4NRC3Data 22 65 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 65 0 := by
  decide

private theorem x4NRGRow22Coeff66_spec :
    mulCoeffTwo GData X4NRC3Data 22 66 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 66 0 := by
  decide

private theorem x4NRGRow22Coeff67_spec :
    mulCoeffTwo GData X4NRC3Data 22 67 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 67 0 := by
  decide

private theorem x4NRGRow22Coeff68_spec :
    mulCoeffTwo GData X4NRC3Data 22 68 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 68 0 := by
  decide

private theorem x4NRGRow22Coeff69_spec :
    mulCoeffTwo GData X4NRC3Data 22 69 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 69 0 := by
  decide

private theorem x4NRGRow22Coeff70_spec :
    mulCoeffTwo GData X4NRC3Data 22 70 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 70 0 := by
  decide

private theorem x4NRGRow22Coeff71_spec :
    mulCoeffTwo GData X4NRC3Data 22 71 =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD 71 0 := by
  decide

private theorem x4NRGRow22Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo GData X4NRC3Data 22 j =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow22Coeff0_spec
  · exact x4NRGRow22Coeff1_spec
  · exact x4NRGRow22Coeff2_spec
  · exact x4NRGRow22Coeff3_spec
  · exact x4NRGRow22Coeff4_spec
  · exact x4NRGRow22Coeff5_spec
  · exact x4NRGRow22Coeff6_spec
  · exact x4NRGRow22Coeff7_spec
  · exact x4NRGRow22Coeff8_spec
  · exact x4NRGRow22Coeff9_spec

private theorem x4NRGRow22Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo GData X4NRC3Data 22 j =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow22Coeff10_spec
  · exact x4NRGRow22Coeff11_spec
  · exact x4NRGRow22Coeff12_spec
  · exact x4NRGRow22Coeff13_spec
  · exact x4NRGRow22Coeff14_spec
  · exact x4NRGRow22Coeff15_spec
  · exact x4NRGRow22Coeff16_spec
  · exact x4NRGRow22Coeff17_spec
  · exact x4NRGRow22Coeff18_spec
  · exact x4NRGRow22Coeff19_spec

private theorem x4NRGRow22Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo GData X4NRC3Data 22 j =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow22Coeff20_spec
  · exact x4NRGRow22Coeff21_spec
  · exact x4NRGRow22Coeff22_spec
  · exact x4NRGRow22Coeff23_spec
  · exact x4NRGRow22Coeff24_spec
  · exact x4NRGRow22Coeff25_spec
  · exact x4NRGRow22Coeff26_spec
  · exact x4NRGRow22Coeff27_spec
  · exact x4NRGRow22Coeff28_spec
  · exact x4NRGRow22Coeff29_spec

private theorem x4NRGRow22Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo GData X4NRC3Data 22 j =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow22Coeff30_spec
  · exact x4NRGRow22Coeff31_spec
  · exact x4NRGRow22Coeff32_spec
  · exact x4NRGRow22Coeff33_spec
  · exact x4NRGRow22Coeff34_spec
  · exact x4NRGRow22Coeff35_spec
  · exact x4NRGRow22Coeff36_spec
  · exact x4NRGRow22Coeff37_spec
  · exact x4NRGRow22Coeff38_spec
  · exact x4NRGRow22Coeff39_spec

private theorem x4NRGRow22Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo GData X4NRC3Data 22 j =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow22Coeff40_spec
  · exact x4NRGRow22Coeff41_spec
  · exact x4NRGRow22Coeff42_spec
  · exact x4NRGRow22Coeff43_spec
  · exact x4NRGRow22Coeff44_spec
  · exact x4NRGRow22Coeff45_spec
  · exact x4NRGRow22Coeff46_spec
  · exact x4NRGRow22Coeff47_spec
  · exact x4NRGRow22Coeff48_spec
  · exact x4NRGRow22Coeff49_spec

private theorem x4NRGRow22Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo GData X4NRC3Data 22 j =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow22Coeff50_spec
  · exact x4NRGRow22Coeff51_spec
  · exact x4NRGRow22Coeff52_spec
  · exact x4NRGRow22Coeff53_spec
  · exact x4NRGRow22Coeff54_spec
  · exact x4NRGRow22Coeff55_spec
  · exact x4NRGRow22Coeff56_spec
  · exact x4NRGRow22Coeff57_spec
  · exact x4NRGRow22Coeff58_spec
  · exact x4NRGRow22Coeff59_spec

private theorem x4NRGRow22Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo GData X4NRC3Data 22 j =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow22Coeff60_spec
  · exact x4NRGRow22Coeff61_spec
  · exact x4NRGRow22Coeff62_spec
  · exact x4NRGRow22Coeff63_spec
  · exact x4NRGRow22Coeff64_spec
  · exact x4NRGRow22Coeff65_spec
  · exact x4NRGRow22Coeff66_spec
  · exact x4NRGRow22Coeff67_spec
  · exact x4NRGRow22Coeff68_spec
  · exact x4NRGRow22Coeff69_spec

private theorem x4NRGRow22Coeffs70To71_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 72) :
    mulCoeffTwo GData X4NRC3Data 22 j =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 := by
    omega
  rcases hCases with
    rfl | rfl
  · exact x4NRGRow22Coeff70_spec
  · exact x4NRGRow22Coeff71_spec

private theorem x4NRGRow22_coefficients (j : ℕ) (hj : j < 72) :
    mulCoeffTwo GData X4NRC3Data 22 j =
      ((rectangularize 52 72 X4NRGData).getD 22 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact x4NRGRow22Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact x4NRGRow22Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact x4NRGRow22Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact x4NRGRow22Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact x4NRGRow22Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact x4NRGRow22Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact x4NRGRow22Coeffs60To69_spec j (by omega) h70
  exact x4NRGRow22Coeffs70To71_spec j (by omega) hj

private theorem x4NRGRow22Padded_spec :
    padOne 72 (mulRow GData X4NRC3Data 22) =
      (rectangularize 52 72 X4NRGData).getD 22 [] := by
  apply padOne_mulRow_eq_of_coefficients 72 GData X4NRC3Data 22
    ((rectangularize 52 72 X4NRGData).getD 22 [])
  · decide
  · have hTargetSupport : (X4NRGData.getD 22 []).length ≤ 72 := by
      decide
    rw [getD_rectangularize 52 72 X4NRGData 22 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact x4NRGRow22_coefficients

private theorem x4NRGRow22_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 22 [] =
      (rectangularize 52 72 X4NRGData).getD 22 [] := by
  rw [getD_rectangularize 52 72 (Two.mul GData X4NRC3Data) 22 (by omega),
    ← mulRow_eq_getD]
  exact x4NRGRow22Padded_spec

private theorem x4NRGRow23Coeff0_spec :
    mulCoeffTwo GData X4NRC3Data 23 0 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 0 0 := by
  decide

private theorem x4NRGRow23Coeff1_spec :
    mulCoeffTwo GData X4NRC3Data 23 1 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 1 0 := by
  decide

private theorem x4NRGRow23Coeff2_spec :
    mulCoeffTwo GData X4NRC3Data 23 2 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 2 0 := by
  decide

private theorem x4NRGRow23Coeff3_spec :
    mulCoeffTwo GData X4NRC3Data 23 3 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 3 0 := by
  decide

private theorem x4NRGRow23Coeff4_spec :
    mulCoeffTwo GData X4NRC3Data 23 4 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 4 0 := by
  decide

private theorem x4NRGRow23Coeff5_spec :
    mulCoeffTwo GData X4NRC3Data 23 5 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 5 0 := by
  decide

private theorem x4NRGRow23Coeff6_spec :
    mulCoeffTwo GData X4NRC3Data 23 6 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 6 0 := by
  decide

private theorem x4NRGRow23Coeff7_spec :
    mulCoeffTwo GData X4NRC3Data 23 7 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 7 0 := by
  decide

private theorem x4NRGRow23Coeff8_spec :
    mulCoeffTwo GData X4NRC3Data 23 8 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 8 0 := by
  decide

private theorem x4NRGRow23Coeff9_spec :
    mulCoeffTwo GData X4NRC3Data 23 9 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 9 0 := by
  decide

private theorem x4NRGRow23Coeff10_spec :
    mulCoeffTwo GData X4NRC3Data 23 10 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 10 0 := by
  decide

private theorem x4NRGRow23Coeff11_spec :
    mulCoeffTwo GData X4NRC3Data 23 11 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 11 0 := by
  decide

private theorem x4NRGRow23Coeff12_spec :
    mulCoeffTwo GData X4NRC3Data 23 12 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 12 0 := by
  decide

private theorem x4NRGRow23Coeff13_spec :
    mulCoeffTwo GData X4NRC3Data 23 13 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 13 0 := by
  decide

private theorem x4NRGRow23Coeff14_spec :
    mulCoeffTwo GData X4NRC3Data 23 14 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 14 0 := by
  decide

private theorem x4NRGRow23Coeff15_spec :
    mulCoeffTwo GData X4NRC3Data 23 15 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 15 0 := by
  decide

private theorem x4NRGRow23Coeff16_spec :
    mulCoeffTwo GData X4NRC3Data 23 16 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 16 0 := by
  decide

private theorem x4NRGRow23Coeff17_spec :
    mulCoeffTwo GData X4NRC3Data 23 17 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 17 0 := by
  decide

private theorem x4NRGRow23Coeff18_spec :
    mulCoeffTwo GData X4NRC3Data 23 18 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 18 0 := by
  decide

private theorem x4NRGRow23Coeff19_spec :
    mulCoeffTwo GData X4NRC3Data 23 19 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 19 0 := by
  decide

private theorem x4NRGRow23Coeff20_spec :
    mulCoeffTwo GData X4NRC3Data 23 20 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 20 0 := by
  decide

private theorem x4NRGRow23Coeff21_spec :
    mulCoeffTwo GData X4NRC3Data 23 21 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 21 0 := by
  decide

private theorem x4NRGRow23Coeff22_spec :
    mulCoeffTwo GData X4NRC3Data 23 22 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 22 0 := by
  decide

private theorem x4NRGRow23Coeff23_spec :
    mulCoeffTwo GData X4NRC3Data 23 23 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 23 0 := by
  decide

private theorem x4NRGRow23Coeff24_spec :
    mulCoeffTwo GData X4NRC3Data 23 24 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 24 0 := by
  decide

private theorem x4NRGRow23Coeff25_spec :
    mulCoeffTwo GData X4NRC3Data 23 25 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 25 0 := by
  decide

private theorem x4NRGRow23Coeff26_spec :
    mulCoeffTwo GData X4NRC3Data 23 26 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 26 0 := by
  decide

private theorem x4NRGRow23Coeff27_spec :
    mulCoeffTwo GData X4NRC3Data 23 27 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 27 0 := by
  decide

private theorem x4NRGRow23Coeff28_spec :
    mulCoeffTwo GData X4NRC3Data 23 28 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 28 0 := by
  decide

private theorem x4NRGRow23Coeff29_spec :
    mulCoeffTwo GData X4NRC3Data 23 29 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 29 0 := by
  decide

private theorem x4NRGRow23Coeff30_spec :
    mulCoeffTwo GData X4NRC3Data 23 30 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 30 0 := by
  decide

private theorem x4NRGRow23Coeff31_spec :
    mulCoeffTwo GData X4NRC3Data 23 31 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 31 0 := by
  decide

private theorem x4NRGRow23Coeff32_spec :
    mulCoeffTwo GData X4NRC3Data 23 32 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 32 0 := by
  decide

private theorem x4NRGRow23Coeff33_spec :
    mulCoeffTwo GData X4NRC3Data 23 33 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 33 0 := by
  decide

private theorem x4NRGRow23Coeff34_spec :
    mulCoeffTwo GData X4NRC3Data 23 34 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 34 0 := by
  decide

private theorem x4NRGRow23Coeff35_spec :
    mulCoeffTwo GData X4NRC3Data 23 35 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 35 0 := by
  decide

private theorem x4NRGRow23Coeff36_spec :
    mulCoeffTwo GData X4NRC3Data 23 36 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 36 0 := by
  decide

private theorem x4NRGRow23Coeff37_spec :
    mulCoeffTwo GData X4NRC3Data 23 37 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 37 0 := by
  decide

private theorem x4NRGRow23Coeff38_spec :
    mulCoeffTwo GData X4NRC3Data 23 38 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 38 0 := by
  decide

private theorem x4NRGRow23Coeff39_spec :
    mulCoeffTwo GData X4NRC3Data 23 39 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 39 0 := by
  decide

private theorem x4NRGRow23Coeff40_spec :
    mulCoeffTwo GData X4NRC3Data 23 40 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 40 0 := by
  decide

private theorem x4NRGRow23Coeff41_spec :
    mulCoeffTwo GData X4NRC3Data 23 41 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 41 0 := by
  decide

private theorem x4NRGRow23Coeff42_spec :
    mulCoeffTwo GData X4NRC3Data 23 42 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 42 0 := by
  decide

private theorem x4NRGRow23Coeff43_spec :
    mulCoeffTwo GData X4NRC3Data 23 43 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 43 0 := by
  decide

private theorem x4NRGRow23Coeff44_spec :
    mulCoeffTwo GData X4NRC3Data 23 44 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 44 0 := by
  decide

private theorem x4NRGRow23Coeff45_spec :
    mulCoeffTwo GData X4NRC3Data 23 45 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 45 0 := by
  decide

private theorem x4NRGRow23Coeff46_spec :
    mulCoeffTwo GData X4NRC3Data 23 46 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 46 0 := by
  decide

private theorem x4NRGRow23Coeff47_spec :
    mulCoeffTwo GData X4NRC3Data 23 47 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 47 0 := by
  decide

private theorem x4NRGRow23Coeff48_spec :
    mulCoeffTwo GData X4NRC3Data 23 48 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 48 0 := by
  decide

private theorem x4NRGRow23Coeff49_spec :
    mulCoeffTwo GData X4NRC3Data 23 49 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 49 0 := by
  decide

private theorem x4NRGRow23Coeff50_spec :
    mulCoeffTwo GData X4NRC3Data 23 50 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 50 0 := by
  decide

private theorem x4NRGRow23Coeff51_spec :
    mulCoeffTwo GData X4NRC3Data 23 51 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 51 0 := by
  decide

private theorem x4NRGRow23Coeff52_spec :
    mulCoeffTwo GData X4NRC3Data 23 52 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 52 0 := by
  decide

private theorem x4NRGRow23Coeff53_spec :
    mulCoeffTwo GData X4NRC3Data 23 53 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 53 0 := by
  decide

private theorem x4NRGRow23Coeff54_spec :
    mulCoeffTwo GData X4NRC3Data 23 54 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 54 0 := by
  decide

private theorem x4NRGRow23Coeff55_spec :
    mulCoeffTwo GData X4NRC3Data 23 55 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 55 0 := by
  decide

private theorem x4NRGRow23Coeff56_spec :
    mulCoeffTwo GData X4NRC3Data 23 56 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 56 0 := by
  decide

private theorem x4NRGRow23Coeff57_spec :
    mulCoeffTwo GData X4NRC3Data 23 57 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 57 0 := by
  decide

private theorem x4NRGRow23Coeff58_spec :
    mulCoeffTwo GData X4NRC3Data 23 58 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 58 0 := by
  decide

private theorem x4NRGRow23Coeff59_spec :
    mulCoeffTwo GData X4NRC3Data 23 59 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 59 0 := by
  decide

private theorem x4NRGRow23Coeff60_spec :
    mulCoeffTwo GData X4NRC3Data 23 60 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 60 0 := by
  decide

private theorem x4NRGRow23Coeff61_spec :
    mulCoeffTwo GData X4NRC3Data 23 61 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 61 0 := by
  decide

private theorem x4NRGRow23Coeff62_spec :
    mulCoeffTwo GData X4NRC3Data 23 62 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 62 0 := by
  decide

private theorem x4NRGRow23Coeff63_spec :
    mulCoeffTwo GData X4NRC3Data 23 63 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 63 0 := by
  decide

private theorem x4NRGRow23Coeff64_spec :
    mulCoeffTwo GData X4NRC3Data 23 64 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 64 0 := by
  decide

private theorem x4NRGRow23Coeff65_spec :
    mulCoeffTwo GData X4NRC3Data 23 65 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 65 0 := by
  decide

private theorem x4NRGRow23Coeff66_spec :
    mulCoeffTwo GData X4NRC3Data 23 66 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 66 0 := by
  decide

private theorem x4NRGRow23Coeff67_spec :
    mulCoeffTwo GData X4NRC3Data 23 67 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 67 0 := by
  decide

private theorem x4NRGRow23Coeff68_spec :
    mulCoeffTwo GData X4NRC3Data 23 68 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 68 0 := by
  decide

private theorem x4NRGRow23Coeff69_spec :
    mulCoeffTwo GData X4NRC3Data 23 69 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 69 0 := by
  decide

private theorem x4NRGRow23Coeff70_spec :
    mulCoeffTwo GData X4NRC3Data 23 70 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 70 0 := by
  decide

private theorem x4NRGRow23Coeff71_spec :
    mulCoeffTwo GData X4NRC3Data 23 71 =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD 71 0 := by
  decide

private theorem x4NRGRow23Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo GData X4NRC3Data 23 j =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow23Coeff0_spec
  · exact x4NRGRow23Coeff1_spec
  · exact x4NRGRow23Coeff2_spec
  · exact x4NRGRow23Coeff3_spec
  · exact x4NRGRow23Coeff4_spec
  · exact x4NRGRow23Coeff5_spec
  · exact x4NRGRow23Coeff6_spec
  · exact x4NRGRow23Coeff7_spec
  · exact x4NRGRow23Coeff8_spec
  · exact x4NRGRow23Coeff9_spec

private theorem x4NRGRow23Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo GData X4NRC3Data 23 j =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow23Coeff10_spec
  · exact x4NRGRow23Coeff11_spec
  · exact x4NRGRow23Coeff12_spec
  · exact x4NRGRow23Coeff13_spec
  · exact x4NRGRow23Coeff14_spec
  · exact x4NRGRow23Coeff15_spec
  · exact x4NRGRow23Coeff16_spec
  · exact x4NRGRow23Coeff17_spec
  · exact x4NRGRow23Coeff18_spec
  · exact x4NRGRow23Coeff19_spec

private theorem x4NRGRow23Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo GData X4NRC3Data 23 j =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow23Coeff20_spec
  · exact x4NRGRow23Coeff21_spec
  · exact x4NRGRow23Coeff22_spec
  · exact x4NRGRow23Coeff23_spec
  · exact x4NRGRow23Coeff24_spec
  · exact x4NRGRow23Coeff25_spec
  · exact x4NRGRow23Coeff26_spec
  · exact x4NRGRow23Coeff27_spec
  · exact x4NRGRow23Coeff28_spec
  · exact x4NRGRow23Coeff29_spec

private theorem x4NRGRow23Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo GData X4NRC3Data 23 j =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow23Coeff30_spec
  · exact x4NRGRow23Coeff31_spec
  · exact x4NRGRow23Coeff32_spec
  · exact x4NRGRow23Coeff33_spec
  · exact x4NRGRow23Coeff34_spec
  · exact x4NRGRow23Coeff35_spec
  · exact x4NRGRow23Coeff36_spec
  · exact x4NRGRow23Coeff37_spec
  · exact x4NRGRow23Coeff38_spec
  · exact x4NRGRow23Coeff39_spec

private theorem x4NRGRow23Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo GData X4NRC3Data 23 j =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow23Coeff40_spec
  · exact x4NRGRow23Coeff41_spec
  · exact x4NRGRow23Coeff42_spec
  · exact x4NRGRow23Coeff43_spec
  · exact x4NRGRow23Coeff44_spec
  · exact x4NRGRow23Coeff45_spec
  · exact x4NRGRow23Coeff46_spec
  · exact x4NRGRow23Coeff47_spec
  · exact x4NRGRow23Coeff48_spec
  · exact x4NRGRow23Coeff49_spec

private theorem x4NRGRow23Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo GData X4NRC3Data 23 j =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow23Coeff50_spec
  · exact x4NRGRow23Coeff51_spec
  · exact x4NRGRow23Coeff52_spec
  · exact x4NRGRow23Coeff53_spec
  · exact x4NRGRow23Coeff54_spec
  · exact x4NRGRow23Coeff55_spec
  · exact x4NRGRow23Coeff56_spec
  · exact x4NRGRow23Coeff57_spec
  · exact x4NRGRow23Coeff58_spec
  · exact x4NRGRow23Coeff59_spec

private theorem x4NRGRow23Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo GData X4NRC3Data 23 j =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow23Coeff60_spec
  · exact x4NRGRow23Coeff61_spec
  · exact x4NRGRow23Coeff62_spec
  · exact x4NRGRow23Coeff63_spec
  · exact x4NRGRow23Coeff64_spec
  · exact x4NRGRow23Coeff65_spec
  · exact x4NRGRow23Coeff66_spec
  · exact x4NRGRow23Coeff67_spec
  · exact x4NRGRow23Coeff68_spec
  · exact x4NRGRow23Coeff69_spec

private theorem x4NRGRow23Coeffs70To71_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 72) :
    mulCoeffTwo GData X4NRC3Data 23 j =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 := by
    omega
  rcases hCases with
    rfl | rfl
  · exact x4NRGRow23Coeff70_spec
  · exact x4NRGRow23Coeff71_spec

private theorem x4NRGRow23_coefficients (j : ℕ) (hj : j < 72) :
    mulCoeffTwo GData X4NRC3Data 23 j =
      ((rectangularize 52 72 X4NRGData).getD 23 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact x4NRGRow23Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact x4NRGRow23Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact x4NRGRow23Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact x4NRGRow23Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact x4NRGRow23Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact x4NRGRow23Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact x4NRGRow23Coeffs60To69_spec j (by omega) h70
  exact x4NRGRow23Coeffs70To71_spec j (by omega) hj

private theorem x4NRGRow23Padded_spec :
    padOne 72 (mulRow GData X4NRC3Data 23) =
      (rectangularize 52 72 X4NRGData).getD 23 [] := by
  apply padOne_mulRow_eq_of_coefficients 72 GData X4NRC3Data 23
    ((rectangularize 52 72 X4NRGData).getD 23 [])
  · decide
  · have hTargetSupport : (X4NRGData.getD 23 []).length ≤ 72 := by
      decide
    rw [getD_rectangularize 52 72 X4NRGData 23 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact x4NRGRow23_coefficients

private theorem x4NRGRow23_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 23 [] =
      (rectangularize 52 72 X4NRGData).getD 23 [] := by
  rw [getD_rectangularize 52 72 (Two.mul GData X4NRC3Data) 23 (by omega),
    ← mulRow_eq_getD]
  exact x4NRGRow23Padded_spec

private theorem x4NRGRow24Coeff0_spec :
    mulCoeffTwo GData X4NRC3Data 24 0 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 0 0 := by
  decide

private theorem x4NRGRow24Coeff1_spec :
    mulCoeffTwo GData X4NRC3Data 24 1 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 1 0 := by
  decide

private theorem x4NRGRow24Coeff2_spec :
    mulCoeffTwo GData X4NRC3Data 24 2 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 2 0 := by
  decide

private theorem x4NRGRow24Coeff3_spec :
    mulCoeffTwo GData X4NRC3Data 24 3 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 3 0 := by
  decide

private theorem x4NRGRow24Coeff4_spec :
    mulCoeffTwo GData X4NRC3Data 24 4 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 4 0 := by
  decide

private theorem x4NRGRow24Coeff5_spec :
    mulCoeffTwo GData X4NRC3Data 24 5 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 5 0 := by
  decide

private theorem x4NRGRow24Coeff6_spec :
    mulCoeffTwo GData X4NRC3Data 24 6 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 6 0 := by
  decide

private theorem x4NRGRow24Coeff7_spec :
    mulCoeffTwo GData X4NRC3Data 24 7 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 7 0 := by
  decide

private theorem x4NRGRow24Coeff8_spec :
    mulCoeffTwo GData X4NRC3Data 24 8 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 8 0 := by
  decide

private theorem x4NRGRow24Coeff9_spec :
    mulCoeffTwo GData X4NRC3Data 24 9 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 9 0 := by
  decide

private theorem x4NRGRow24Coeff10_spec :
    mulCoeffTwo GData X4NRC3Data 24 10 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 10 0 := by
  decide

private theorem x4NRGRow24Coeff11_spec :
    mulCoeffTwo GData X4NRC3Data 24 11 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 11 0 := by
  decide

private theorem x4NRGRow24Coeff12_spec :
    mulCoeffTwo GData X4NRC3Data 24 12 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 12 0 := by
  decide

private theorem x4NRGRow24Coeff13_spec :
    mulCoeffTwo GData X4NRC3Data 24 13 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 13 0 := by
  decide

private theorem x4NRGRow24Coeff14_spec :
    mulCoeffTwo GData X4NRC3Data 24 14 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 14 0 := by
  decide

private theorem x4NRGRow24Coeff15_spec :
    mulCoeffTwo GData X4NRC3Data 24 15 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 15 0 := by
  decide

private theorem x4NRGRow24Coeff16_spec :
    mulCoeffTwo GData X4NRC3Data 24 16 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 16 0 := by
  decide

private theorem x4NRGRow24Coeff17_spec :
    mulCoeffTwo GData X4NRC3Data 24 17 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 17 0 := by
  decide

private theorem x4NRGRow24Coeff18_spec :
    mulCoeffTwo GData X4NRC3Data 24 18 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 18 0 := by
  decide

private theorem x4NRGRow24Coeff19_spec :
    mulCoeffTwo GData X4NRC3Data 24 19 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 19 0 := by
  decide

private theorem x4NRGRow24Coeff20_spec :
    mulCoeffTwo GData X4NRC3Data 24 20 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 20 0 := by
  decide

private theorem x4NRGRow24Coeff21_spec :
    mulCoeffTwo GData X4NRC3Data 24 21 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 21 0 := by
  decide

private theorem x4NRGRow24Coeff22_spec :
    mulCoeffTwo GData X4NRC3Data 24 22 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 22 0 := by
  decide

private theorem x4NRGRow24Coeff23_spec :
    mulCoeffTwo GData X4NRC3Data 24 23 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 23 0 := by
  decide

private theorem x4NRGRow24Coeff24_spec :
    mulCoeffTwo GData X4NRC3Data 24 24 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 24 0 := by
  decide

private theorem x4NRGRow24Coeff25_spec :
    mulCoeffTwo GData X4NRC3Data 24 25 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 25 0 := by
  decide

private theorem x4NRGRow24Coeff26_spec :
    mulCoeffTwo GData X4NRC3Data 24 26 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 26 0 := by
  decide

private theorem x4NRGRow24Coeff27_spec :
    mulCoeffTwo GData X4NRC3Data 24 27 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 27 0 := by
  decide

private theorem x4NRGRow24Coeff28_spec :
    mulCoeffTwo GData X4NRC3Data 24 28 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 28 0 := by
  decide

private theorem x4NRGRow24Coeff29_spec :
    mulCoeffTwo GData X4NRC3Data 24 29 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 29 0 := by
  decide

private theorem x4NRGRow24Coeff30_spec :
    mulCoeffTwo GData X4NRC3Data 24 30 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 30 0 := by
  decide

private theorem x4NRGRow24Coeff31_spec :
    mulCoeffTwo GData X4NRC3Data 24 31 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 31 0 := by
  decide

private theorem x4NRGRow24Coeff32_spec :
    mulCoeffTwo GData X4NRC3Data 24 32 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 32 0 := by
  decide

private theorem x4NRGRow24Coeff33_spec :
    mulCoeffTwo GData X4NRC3Data 24 33 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 33 0 := by
  decide

private theorem x4NRGRow24Coeff34_spec :
    mulCoeffTwo GData X4NRC3Data 24 34 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 34 0 := by
  decide

private theorem x4NRGRow24Coeff35_spec :
    mulCoeffTwo GData X4NRC3Data 24 35 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 35 0 := by
  decide

private theorem x4NRGRow24Coeff36_spec :
    mulCoeffTwo GData X4NRC3Data 24 36 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 36 0 := by
  decide

private theorem x4NRGRow24Coeff37_spec :
    mulCoeffTwo GData X4NRC3Data 24 37 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 37 0 := by
  decide

private theorem x4NRGRow24Coeff38_spec :
    mulCoeffTwo GData X4NRC3Data 24 38 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 38 0 := by
  decide

private theorem x4NRGRow24Coeff39_spec :
    mulCoeffTwo GData X4NRC3Data 24 39 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 39 0 := by
  decide

private theorem x4NRGRow24Coeff40_spec :
    mulCoeffTwo GData X4NRC3Data 24 40 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 40 0 := by
  decide

private theorem x4NRGRow24Coeff41_spec :
    mulCoeffTwo GData X4NRC3Data 24 41 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 41 0 := by
  decide

private theorem x4NRGRow24Coeff42_spec :
    mulCoeffTwo GData X4NRC3Data 24 42 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 42 0 := by
  decide

private theorem x4NRGRow24Coeff43_spec :
    mulCoeffTwo GData X4NRC3Data 24 43 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 43 0 := by
  decide

private theorem x4NRGRow24Coeff44_spec :
    mulCoeffTwo GData X4NRC3Data 24 44 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 44 0 := by
  decide

private theorem x4NRGRow24Coeff45_spec :
    mulCoeffTwo GData X4NRC3Data 24 45 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 45 0 := by
  decide

private theorem x4NRGRow24Coeff46_spec :
    mulCoeffTwo GData X4NRC3Data 24 46 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 46 0 := by
  decide

private theorem x4NRGRow24Coeff47_spec :
    mulCoeffTwo GData X4NRC3Data 24 47 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 47 0 := by
  decide

private theorem x4NRGRow24Coeff48_spec :
    mulCoeffTwo GData X4NRC3Data 24 48 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 48 0 := by
  decide

private theorem x4NRGRow24Coeff49_spec :
    mulCoeffTwo GData X4NRC3Data 24 49 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 49 0 := by
  decide

private theorem x4NRGRow24Coeff50_spec :
    mulCoeffTwo GData X4NRC3Data 24 50 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 50 0 := by
  decide

private theorem x4NRGRow24Coeff51_spec :
    mulCoeffTwo GData X4NRC3Data 24 51 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 51 0 := by
  decide

private theorem x4NRGRow24Coeff52_spec :
    mulCoeffTwo GData X4NRC3Data 24 52 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 52 0 := by
  decide

private theorem x4NRGRow24Coeff53_spec :
    mulCoeffTwo GData X4NRC3Data 24 53 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 53 0 := by
  decide

private theorem x4NRGRow24Coeff54_spec :
    mulCoeffTwo GData X4NRC3Data 24 54 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 54 0 := by
  decide

private theorem x4NRGRow24Coeff55_spec :
    mulCoeffTwo GData X4NRC3Data 24 55 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 55 0 := by
  decide

private theorem x4NRGRow24Coeff56_spec :
    mulCoeffTwo GData X4NRC3Data 24 56 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 56 0 := by
  decide

private theorem x4NRGRow24Coeff57_spec :
    mulCoeffTwo GData X4NRC3Data 24 57 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 57 0 := by
  decide

private theorem x4NRGRow24Coeff58_spec :
    mulCoeffTwo GData X4NRC3Data 24 58 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 58 0 := by
  decide

private theorem x4NRGRow24Coeff59_spec :
    mulCoeffTwo GData X4NRC3Data 24 59 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 59 0 := by
  decide

private theorem x4NRGRow24Coeff60_spec :
    mulCoeffTwo GData X4NRC3Data 24 60 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 60 0 := by
  decide

private theorem x4NRGRow24Coeff61_spec :
    mulCoeffTwo GData X4NRC3Data 24 61 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 61 0 := by
  decide

private theorem x4NRGRow24Coeff62_spec :
    mulCoeffTwo GData X4NRC3Data 24 62 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 62 0 := by
  decide

private theorem x4NRGRow24Coeff63_spec :
    mulCoeffTwo GData X4NRC3Data 24 63 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 63 0 := by
  decide

private theorem x4NRGRow24Coeff64_spec :
    mulCoeffTwo GData X4NRC3Data 24 64 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 64 0 := by
  decide

private theorem x4NRGRow24Coeff65_spec :
    mulCoeffTwo GData X4NRC3Data 24 65 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 65 0 := by
  decide

private theorem x4NRGRow24Coeff66_spec :
    mulCoeffTwo GData X4NRC3Data 24 66 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 66 0 := by
  decide

private theorem x4NRGRow24Coeff67_spec :
    mulCoeffTwo GData X4NRC3Data 24 67 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 67 0 := by
  decide

private theorem x4NRGRow24Coeff68_spec :
    mulCoeffTwo GData X4NRC3Data 24 68 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 68 0 := by
  decide

private theorem x4NRGRow24Coeff69_spec :
    mulCoeffTwo GData X4NRC3Data 24 69 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 69 0 := by
  decide

private theorem x4NRGRow24Coeff70_spec :
    mulCoeffTwo GData X4NRC3Data 24 70 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 70 0 := by
  decide

private theorem x4NRGRow24Coeff71_spec :
    mulCoeffTwo GData X4NRC3Data 24 71 =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD 71 0 := by
  decide

private theorem x4NRGRow24Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo GData X4NRC3Data 24 j =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow24Coeff0_spec
  · exact x4NRGRow24Coeff1_spec
  · exact x4NRGRow24Coeff2_spec
  · exact x4NRGRow24Coeff3_spec
  · exact x4NRGRow24Coeff4_spec
  · exact x4NRGRow24Coeff5_spec
  · exact x4NRGRow24Coeff6_spec
  · exact x4NRGRow24Coeff7_spec
  · exact x4NRGRow24Coeff8_spec
  · exact x4NRGRow24Coeff9_spec

private theorem x4NRGRow24Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo GData X4NRC3Data 24 j =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow24Coeff10_spec
  · exact x4NRGRow24Coeff11_spec
  · exact x4NRGRow24Coeff12_spec
  · exact x4NRGRow24Coeff13_spec
  · exact x4NRGRow24Coeff14_spec
  · exact x4NRGRow24Coeff15_spec
  · exact x4NRGRow24Coeff16_spec
  · exact x4NRGRow24Coeff17_spec
  · exact x4NRGRow24Coeff18_spec
  · exact x4NRGRow24Coeff19_spec

private theorem x4NRGRow24Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo GData X4NRC3Data 24 j =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow24Coeff20_spec
  · exact x4NRGRow24Coeff21_spec
  · exact x4NRGRow24Coeff22_spec
  · exact x4NRGRow24Coeff23_spec
  · exact x4NRGRow24Coeff24_spec
  · exact x4NRGRow24Coeff25_spec
  · exact x4NRGRow24Coeff26_spec
  · exact x4NRGRow24Coeff27_spec
  · exact x4NRGRow24Coeff28_spec
  · exact x4NRGRow24Coeff29_spec

private theorem x4NRGRow24Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo GData X4NRC3Data 24 j =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow24Coeff30_spec
  · exact x4NRGRow24Coeff31_spec
  · exact x4NRGRow24Coeff32_spec
  · exact x4NRGRow24Coeff33_spec
  · exact x4NRGRow24Coeff34_spec
  · exact x4NRGRow24Coeff35_spec
  · exact x4NRGRow24Coeff36_spec
  · exact x4NRGRow24Coeff37_spec
  · exact x4NRGRow24Coeff38_spec
  · exact x4NRGRow24Coeff39_spec

private theorem x4NRGRow24Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo GData X4NRC3Data 24 j =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow24Coeff40_spec
  · exact x4NRGRow24Coeff41_spec
  · exact x4NRGRow24Coeff42_spec
  · exact x4NRGRow24Coeff43_spec
  · exact x4NRGRow24Coeff44_spec
  · exact x4NRGRow24Coeff45_spec
  · exact x4NRGRow24Coeff46_spec
  · exact x4NRGRow24Coeff47_spec
  · exact x4NRGRow24Coeff48_spec
  · exact x4NRGRow24Coeff49_spec

private theorem x4NRGRow24Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo GData X4NRC3Data 24 j =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow24Coeff50_spec
  · exact x4NRGRow24Coeff51_spec
  · exact x4NRGRow24Coeff52_spec
  · exact x4NRGRow24Coeff53_spec
  · exact x4NRGRow24Coeff54_spec
  · exact x4NRGRow24Coeff55_spec
  · exact x4NRGRow24Coeff56_spec
  · exact x4NRGRow24Coeff57_spec
  · exact x4NRGRow24Coeff58_spec
  · exact x4NRGRow24Coeff59_spec

private theorem x4NRGRow24Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo GData X4NRC3Data 24 j =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow24Coeff60_spec
  · exact x4NRGRow24Coeff61_spec
  · exact x4NRGRow24Coeff62_spec
  · exact x4NRGRow24Coeff63_spec
  · exact x4NRGRow24Coeff64_spec
  · exact x4NRGRow24Coeff65_spec
  · exact x4NRGRow24Coeff66_spec
  · exact x4NRGRow24Coeff67_spec
  · exact x4NRGRow24Coeff68_spec
  · exact x4NRGRow24Coeff69_spec

private theorem x4NRGRow24Coeffs70To71_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 72) :
    mulCoeffTwo GData X4NRC3Data 24 j =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 := by
    omega
  rcases hCases with
    rfl | rfl
  · exact x4NRGRow24Coeff70_spec
  · exact x4NRGRow24Coeff71_spec

private theorem x4NRGRow24_coefficients (j : ℕ) (hj : j < 72) :
    mulCoeffTwo GData X4NRC3Data 24 j =
      ((rectangularize 52 72 X4NRGData).getD 24 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact x4NRGRow24Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact x4NRGRow24Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact x4NRGRow24Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact x4NRGRow24Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact x4NRGRow24Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact x4NRGRow24Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact x4NRGRow24Coeffs60To69_spec j (by omega) h70
  exact x4NRGRow24Coeffs70To71_spec j (by omega) hj

private theorem x4NRGRow24Padded_spec :
    padOne 72 (mulRow GData X4NRC3Data 24) =
      (rectangularize 52 72 X4NRGData).getD 24 [] := by
  apply padOne_mulRow_eq_of_coefficients 72 GData X4NRC3Data 24
    ((rectangularize 52 72 X4NRGData).getD 24 [])
  · decide
  · have hTargetSupport : (X4NRGData.getD 24 []).length ≤ 72 := by
      decide
    rw [getD_rectangularize 52 72 X4NRGData 24 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact x4NRGRow24_coefficients

private theorem x4NRGRow24_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 24 [] =
      (rectangularize 52 72 X4NRGData).getD 24 [] := by
  rw [getD_rectangularize 52 72 (Two.mul GData X4NRC3Data) 24 (by omega),
    ← mulRow_eq_getD]
  exact x4NRGRow24Padded_spec

private theorem x4NRGRow25Coeff0_spec :
    mulCoeffTwo GData X4NRC3Data 25 0 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 0 0 := by
  decide

private theorem x4NRGRow25Coeff1_spec :
    mulCoeffTwo GData X4NRC3Data 25 1 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 1 0 := by
  decide

private theorem x4NRGRow25Coeff2_spec :
    mulCoeffTwo GData X4NRC3Data 25 2 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 2 0 := by
  decide

private theorem x4NRGRow25Coeff3_spec :
    mulCoeffTwo GData X4NRC3Data 25 3 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 3 0 := by
  decide

private theorem x4NRGRow25Coeff4_spec :
    mulCoeffTwo GData X4NRC3Data 25 4 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 4 0 := by
  decide

private theorem x4NRGRow25Coeff5_spec :
    mulCoeffTwo GData X4NRC3Data 25 5 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 5 0 := by
  decide

private theorem x4NRGRow25Coeff6_spec :
    mulCoeffTwo GData X4NRC3Data 25 6 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 6 0 := by
  decide

private theorem x4NRGRow25Coeff7_spec :
    mulCoeffTwo GData X4NRC3Data 25 7 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 7 0 := by
  decide

private theorem x4NRGRow25Coeff8_spec :
    mulCoeffTwo GData X4NRC3Data 25 8 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 8 0 := by
  decide

private theorem x4NRGRow25Coeff9_spec :
    mulCoeffTwo GData X4NRC3Data 25 9 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 9 0 := by
  decide

private theorem x4NRGRow25Coeff10_spec :
    mulCoeffTwo GData X4NRC3Data 25 10 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 10 0 := by
  decide

private theorem x4NRGRow25Coeff11_spec :
    mulCoeffTwo GData X4NRC3Data 25 11 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 11 0 := by
  decide

private theorem x4NRGRow25Coeff12_spec :
    mulCoeffTwo GData X4NRC3Data 25 12 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 12 0 := by
  decide

private theorem x4NRGRow25Coeff13_spec :
    mulCoeffTwo GData X4NRC3Data 25 13 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 13 0 := by
  decide

private theorem x4NRGRow25Coeff14_spec :
    mulCoeffTwo GData X4NRC3Data 25 14 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 14 0 := by
  decide

private theorem x4NRGRow25Coeff15_spec :
    mulCoeffTwo GData X4NRC3Data 25 15 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 15 0 := by
  decide

private theorem x4NRGRow25Coeff16_spec :
    mulCoeffTwo GData X4NRC3Data 25 16 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 16 0 := by
  decide

private theorem x4NRGRow25Coeff17_spec :
    mulCoeffTwo GData X4NRC3Data 25 17 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 17 0 := by
  decide

private theorem x4NRGRow25Coeff18_spec :
    mulCoeffTwo GData X4NRC3Data 25 18 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 18 0 := by
  decide

private theorem x4NRGRow25Coeff19_spec :
    mulCoeffTwo GData X4NRC3Data 25 19 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 19 0 := by
  decide

private theorem x4NRGRow25Coeff20_spec :
    mulCoeffTwo GData X4NRC3Data 25 20 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 20 0 := by
  decide

private theorem x4NRGRow25Coeff21_spec :
    mulCoeffTwo GData X4NRC3Data 25 21 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 21 0 := by
  decide

private theorem x4NRGRow25Coeff22_spec :
    mulCoeffTwo GData X4NRC3Data 25 22 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 22 0 := by
  decide

private theorem x4NRGRow25Coeff23_spec :
    mulCoeffTwo GData X4NRC3Data 25 23 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 23 0 := by
  decide

private theorem x4NRGRow25Coeff24_spec :
    mulCoeffTwo GData X4NRC3Data 25 24 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 24 0 := by
  decide

private theorem x4NRGRow25Coeff25_spec :
    mulCoeffTwo GData X4NRC3Data 25 25 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 25 0 := by
  decide

private theorem x4NRGRow25Coeff26_spec :
    mulCoeffTwo GData X4NRC3Data 25 26 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 26 0 := by
  decide

private theorem x4NRGRow25Coeff27_spec :
    mulCoeffTwo GData X4NRC3Data 25 27 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 27 0 := by
  decide

private theorem x4NRGRow25Coeff28_spec :
    mulCoeffTwo GData X4NRC3Data 25 28 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 28 0 := by
  decide

private theorem x4NRGRow25Coeff29_spec :
    mulCoeffTwo GData X4NRC3Data 25 29 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 29 0 := by
  decide

private theorem x4NRGRow25Coeff30_spec :
    mulCoeffTwo GData X4NRC3Data 25 30 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 30 0 := by
  decide

private theorem x4NRGRow25Coeff31_spec :
    mulCoeffTwo GData X4NRC3Data 25 31 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 31 0 := by
  decide

private theorem x4NRGRow25Coeff32_spec :
    mulCoeffTwo GData X4NRC3Data 25 32 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 32 0 := by
  decide

private theorem x4NRGRow25Coeff33_spec :
    mulCoeffTwo GData X4NRC3Data 25 33 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 33 0 := by
  decide

private theorem x4NRGRow25Coeff34_spec :
    mulCoeffTwo GData X4NRC3Data 25 34 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 34 0 := by
  decide

private theorem x4NRGRow25Coeff35_spec :
    mulCoeffTwo GData X4NRC3Data 25 35 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 35 0 := by
  decide

private theorem x4NRGRow25Coeff36_spec :
    mulCoeffTwo GData X4NRC3Data 25 36 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 36 0 := by
  decide

private theorem x4NRGRow25Coeff37_spec :
    mulCoeffTwo GData X4NRC3Data 25 37 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 37 0 := by
  decide

private theorem x4NRGRow25Coeff38_spec :
    mulCoeffTwo GData X4NRC3Data 25 38 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 38 0 := by
  decide

private theorem x4NRGRow25Coeff39_spec :
    mulCoeffTwo GData X4NRC3Data 25 39 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 39 0 := by
  decide

private theorem x4NRGRow25Coeff40_spec :
    mulCoeffTwo GData X4NRC3Data 25 40 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 40 0 := by
  decide

private theorem x4NRGRow25Coeff41_spec :
    mulCoeffTwo GData X4NRC3Data 25 41 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 41 0 := by
  decide

private theorem x4NRGRow25Coeff42_spec :
    mulCoeffTwo GData X4NRC3Data 25 42 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 42 0 := by
  decide

private theorem x4NRGRow25Coeff43_spec :
    mulCoeffTwo GData X4NRC3Data 25 43 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 43 0 := by
  decide

private theorem x4NRGRow25Coeff44_spec :
    mulCoeffTwo GData X4NRC3Data 25 44 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 44 0 := by
  decide

private theorem x4NRGRow25Coeff45_spec :
    mulCoeffTwo GData X4NRC3Data 25 45 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 45 0 := by
  decide

private theorem x4NRGRow25Coeff46_spec :
    mulCoeffTwo GData X4NRC3Data 25 46 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 46 0 := by
  decide

private theorem x4NRGRow25Coeff47_spec :
    mulCoeffTwo GData X4NRC3Data 25 47 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 47 0 := by
  decide

private theorem x4NRGRow25Coeff48_spec :
    mulCoeffTwo GData X4NRC3Data 25 48 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 48 0 := by
  decide

private theorem x4NRGRow25Coeff49_spec :
    mulCoeffTwo GData X4NRC3Data 25 49 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 49 0 := by
  decide

private theorem x4NRGRow25Coeff50_spec :
    mulCoeffTwo GData X4NRC3Data 25 50 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 50 0 := by
  decide

private theorem x4NRGRow25Coeff51_spec :
    mulCoeffTwo GData X4NRC3Data 25 51 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 51 0 := by
  decide

private theorem x4NRGRow25Coeff52_spec :
    mulCoeffTwo GData X4NRC3Data 25 52 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 52 0 := by
  decide

private theorem x4NRGRow25Coeff53_spec :
    mulCoeffTwo GData X4NRC3Data 25 53 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 53 0 := by
  decide

private theorem x4NRGRow25Coeff54_spec :
    mulCoeffTwo GData X4NRC3Data 25 54 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 54 0 := by
  decide

private theorem x4NRGRow25Coeff55_spec :
    mulCoeffTwo GData X4NRC3Data 25 55 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 55 0 := by
  decide

private theorem x4NRGRow25Coeff56_spec :
    mulCoeffTwo GData X4NRC3Data 25 56 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 56 0 := by
  decide

private theorem x4NRGRow25Coeff57_spec :
    mulCoeffTwo GData X4NRC3Data 25 57 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 57 0 := by
  decide

private theorem x4NRGRow25Coeff58_spec :
    mulCoeffTwo GData X4NRC3Data 25 58 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 58 0 := by
  decide

private theorem x4NRGRow25Coeff59_spec :
    mulCoeffTwo GData X4NRC3Data 25 59 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 59 0 := by
  decide

private theorem x4NRGRow25Coeff60_spec :
    mulCoeffTwo GData X4NRC3Data 25 60 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 60 0 := by
  decide

private theorem x4NRGRow25Coeff61_spec :
    mulCoeffTwo GData X4NRC3Data 25 61 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 61 0 := by
  decide

private theorem x4NRGRow25Coeff62_spec :
    mulCoeffTwo GData X4NRC3Data 25 62 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 62 0 := by
  decide

private theorem x4NRGRow25Coeff63_spec :
    mulCoeffTwo GData X4NRC3Data 25 63 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 63 0 := by
  decide

private theorem x4NRGRow25Coeff64_spec :
    mulCoeffTwo GData X4NRC3Data 25 64 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 64 0 := by
  decide

private theorem x4NRGRow25Coeff65_spec :
    mulCoeffTwo GData X4NRC3Data 25 65 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 65 0 := by
  decide

private theorem x4NRGRow25Coeff66_spec :
    mulCoeffTwo GData X4NRC3Data 25 66 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 66 0 := by
  decide

private theorem x4NRGRow25Coeff67_spec :
    mulCoeffTwo GData X4NRC3Data 25 67 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 67 0 := by
  decide

private theorem x4NRGRow25Coeff68_spec :
    mulCoeffTwo GData X4NRC3Data 25 68 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 68 0 := by
  decide

private theorem x4NRGRow25Coeff69_spec :
    mulCoeffTwo GData X4NRC3Data 25 69 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 69 0 := by
  decide

private theorem x4NRGRow25Coeff70_spec :
    mulCoeffTwo GData X4NRC3Data 25 70 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 70 0 := by
  decide

private theorem x4NRGRow25Coeff71_spec :
    mulCoeffTwo GData X4NRC3Data 25 71 =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD 71 0 := by
  decide

private theorem x4NRGRow25Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo GData X4NRC3Data 25 j =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow25Coeff0_spec
  · exact x4NRGRow25Coeff1_spec
  · exact x4NRGRow25Coeff2_spec
  · exact x4NRGRow25Coeff3_spec
  · exact x4NRGRow25Coeff4_spec
  · exact x4NRGRow25Coeff5_spec
  · exact x4NRGRow25Coeff6_spec
  · exact x4NRGRow25Coeff7_spec
  · exact x4NRGRow25Coeff8_spec
  · exact x4NRGRow25Coeff9_spec

private theorem x4NRGRow25Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo GData X4NRC3Data 25 j =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow25Coeff10_spec
  · exact x4NRGRow25Coeff11_spec
  · exact x4NRGRow25Coeff12_spec
  · exact x4NRGRow25Coeff13_spec
  · exact x4NRGRow25Coeff14_spec
  · exact x4NRGRow25Coeff15_spec
  · exact x4NRGRow25Coeff16_spec
  · exact x4NRGRow25Coeff17_spec
  · exact x4NRGRow25Coeff18_spec
  · exact x4NRGRow25Coeff19_spec

private theorem x4NRGRow25Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo GData X4NRC3Data 25 j =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow25Coeff20_spec
  · exact x4NRGRow25Coeff21_spec
  · exact x4NRGRow25Coeff22_spec
  · exact x4NRGRow25Coeff23_spec
  · exact x4NRGRow25Coeff24_spec
  · exact x4NRGRow25Coeff25_spec
  · exact x4NRGRow25Coeff26_spec
  · exact x4NRGRow25Coeff27_spec
  · exact x4NRGRow25Coeff28_spec
  · exact x4NRGRow25Coeff29_spec

private theorem x4NRGRow25Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo GData X4NRC3Data 25 j =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow25Coeff30_spec
  · exact x4NRGRow25Coeff31_spec
  · exact x4NRGRow25Coeff32_spec
  · exact x4NRGRow25Coeff33_spec
  · exact x4NRGRow25Coeff34_spec
  · exact x4NRGRow25Coeff35_spec
  · exact x4NRGRow25Coeff36_spec
  · exact x4NRGRow25Coeff37_spec
  · exact x4NRGRow25Coeff38_spec
  · exact x4NRGRow25Coeff39_spec

private theorem x4NRGRow25Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo GData X4NRC3Data 25 j =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow25Coeff40_spec
  · exact x4NRGRow25Coeff41_spec
  · exact x4NRGRow25Coeff42_spec
  · exact x4NRGRow25Coeff43_spec
  · exact x4NRGRow25Coeff44_spec
  · exact x4NRGRow25Coeff45_spec
  · exact x4NRGRow25Coeff46_spec
  · exact x4NRGRow25Coeff47_spec
  · exact x4NRGRow25Coeff48_spec
  · exact x4NRGRow25Coeff49_spec

private theorem x4NRGRow25Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo GData X4NRC3Data 25 j =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow25Coeff50_spec
  · exact x4NRGRow25Coeff51_spec
  · exact x4NRGRow25Coeff52_spec
  · exact x4NRGRow25Coeff53_spec
  · exact x4NRGRow25Coeff54_spec
  · exact x4NRGRow25Coeff55_spec
  · exact x4NRGRow25Coeff56_spec
  · exact x4NRGRow25Coeff57_spec
  · exact x4NRGRow25Coeff58_spec
  · exact x4NRGRow25Coeff59_spec

private theorem x4NRGRow25Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo GData X4NRC3Data 25 j =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow25Coeff60_spec
  · exact x4NRGRow25Coeff61_spec
  · exact x4NRGRow25Coeff62_spec
  · exact x4NRGRow25Coeff63_spec
  · exact x4NRGRow25Coeff64_spec
  · exact x4NRGRow25Coeff65_spec
  · exact x4NRGRow25Coeff66_spec
  · exact x4NRGRow25Coeff67_spec
  · exact x4NRGRow25Coeff68_spec
  · exact x4NRGRow25Coeff69_spec

private theorem x4NRGRow25Coeffs70To71_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 72) :
    mulCoeffTwo GData X4NRC3Data 25 j =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 := by
    omega
  rcases hCases with
    rfl | rfl
  · exact x4NRGRow25Coeff70_spec
  · exact x4NRGRow25Coeff71_spec

private theorem x4NRGRow25_coefficients (j : ℕ) (hj : j < 72) :
    mulCoeffTwo GData X4NRC3Data 25 j =
      ((rectangularize 52 72 X4NRGData).getD 25 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact x4NRGRow25Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact x4NRGRow25Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact x4NRGRow25Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact x4NRGRow25Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact x4NRGRow25Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact x4NRGRow25Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact x4NRGRow25Coeffs60To69_spec j (by omega) h70
  exact x4NRGRow25Coeffs70To71_spec j (by omega) hj

private theorem x4NRGRow25Padded_spec :
    padOne 72 (mulRow GData X4NRC3Data 25) =
      (rectangularize 52 72 X4NRGData).getD 25 [] := by
  apply padOne_mulRow_eq_of_coefficients 72 GData X4NRC3Data 25
    ((rectangularize 52 72 X4NRGData).getD 25 [])
  · decide
  · have hTargetSupport : (X4NRGData.getD 25 []).length ≤ 72 := by
      decide
    rw [getD_rectangularize 52 72 X4NRGData 25 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact x4NRGRow25_coefficients

private theorem x4NRGRow25_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 25 [] =
      (rectangularize 52 72 X4NRGData).getD 25 [] := by
  rw [getD_rectangularize 52 72 (Two.mul GData X4NRC3Data) 25 (by omega),
    ← mulRow_eq_getD]
  exact x4NRGRow25Padded_spec

private theorem x4NRGRow26Coeff0_spec :
    mulCoeffTwo GData X4NRC3Data 26 0 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 0 0 := by
  decide

private theorem x4NRGRow26Coeff1_spec :
    mulCoeffTwo GData X4NRC3Data 26 1 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 1 0 := by
  decide

private theorem x4NRGRow26Coeff2_spec :
    mulCoeffTwo GData X4NRC3Data 26 2 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 2 0 := by
  decide

private theorem x4NRGRow26Coeff3_spec :
    mulCoeffTwo GData X4NRC3Data 26 3 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 3 0 := by
  decide

private theorem x4NRGRow26Coeff4_spec :
    mulCoeffTwo GData X4NRC3Data 26 4 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 4 0 := by
  decide

private theorem x4NRGRow26Coeff5_spec :
    mulCoeffTwo GData X4NRC3Data 26 5 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 5 0 := by
  decide

private theorem x4NRGRow26Coeff6_spec :
    mulCoeffTwo GData X4NRC3Data 26 6 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 6 0 := by
  decide

private theorem x4NRGRow26Coeff7_spec :
    mulCoeffTwo GData X4NRC3Data 26 7 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 7 0 := by
  decide

private theorem x4NRGRow26Coeff8_spec :
    mulCoeffTwo GData X4NRC3Data 26 8 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 8 0 := by
  decide

private theorem x4NRGRow26Coeff9_spec :
    mulCoeffTwo GData X4NRC3Data 26 9 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 9 0 := by
  decide

private theorem x4NRGRow26Coeff10_spec :
    mulCoeffTwo GData X4NRC3Data 26 10 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 10 0 := by
  decide

private theorem x4NRGRow26Coeff11_spec :
    mulCoeffTwo GData X4NRC3Data 26 11 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 11 0 := by
  decide

private theorem x4NRGRow26Coeff12_spec :
    mulCoeffTwo GData X4NRC3Data 26 12 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 12 0 := by
  decide

private theorem x4NRGRow26Coeff13_spec :
    mulCoeffTwo GData X4NRC3Data 26 13 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 13 0 := by
  decide

private theorem x4NRGRow26Coeff14_spec :
    mulCoeffTwo GData X4NRC3Data 26 14 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 14 0 := by
  decide

private theorem x4NRGRow26Coeff15_spec :
    mulCoeffTwo GData X4NRC3Data 26 15 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 15 0 := by
  decide

private theorem x4NRGRow26Coeff16_spec :
    mulCoeffTwo GData X4NRC3Data 26 16 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 16 0 := by
  decide

private theorem x4NRGRow26Coeff17_spec :
    mulCoeffTwo GData X4NRC3Data 26 17 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 17 0 := by
  decide

private theorem x4NRGRow26Coeff18_spec :
    mulCoeffTwo GData X4NRC3Data 26 18 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 18 0 := by
  decide

private theorem x4NRGRow26Coeff19_spec :
    mulCoeffTwo GData X4NRC3Data 26 19 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 19 0 := by
  decide

private theorem x4NRGRow26Coeff20_spec :
    mulCoeffTwo GData X4NRC3Data 26 20 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 20 0 := by
  decide

private theorem x4NRGRow26Coeff21_spec :
    mulCoeffTwo GData X4NRC3Data 26 21 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 21 0 := by
  decide

private theorem x4NRGRow26Coeff22_spec :
    mulCoeffTwo GData X4NRC3Data 26 22 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 22 0 := by
  decide

private theorem x4NRGRow26Coeff23_spec :
    mulCoeffTwo GData X4NRC3Data 26 23 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 23 0 := by
  decide

private theorem x4NRGRow26Coeff24_spec :
    mulCoeffTwo GData X4NRC3Data 26 24 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 24 0 := by
  decide

private theorem x4NRGRow26Coeff25_spec :
    mulCoeffTwo GData X4NRC3Data 26 25 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 25 0 := by
  decide

private theorem x4NRGRow26Coeff26_spec :
    mulCoeffTwo GData X4NRC3Data 26 26 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 26 0 := by
  decide

private theorem x4NRGRow26Coeff27_spec :
    mulCoeffTwo GData X4NRC3Data 26 27 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 27 0 := by
  decide

private theorem x4NRGRow26Coeff28_spec :
    mulCoeffTwo GData X4NRC3Data 26 28 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 28 0 := by
  decide

private theorem x4NRGRow26Coeff29_spec :
    mulCoeffTwo GData X4NRC3Data 26 29 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 29 0 := by
  decide

private theorem x4NRGRow26Coeff30_spec :
    mulCoeffTwo GData X4NRC3Data 26 30 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 30 0 := by
  decide

private theorem x4NRGRow26Coeff31_spec :
    mulCoeffTwo GData X4NRC3Data 26 31 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 31 0 := by
  decide

private theorem x4NRGRow26Coeff32_spec :
    mulCoeffTwo GData X4NRC3Data 26 32 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 32 0 := by
  decide

private theorem x4NRGRow26Coeff33_spec :
    mulCoeffTwo GData X4NRC3Data 26 33 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 33 0 := by
  decide

private theorem x4NRGRow26Coeff34_spec :
    mulCoeffTwo GData X4NRC3Data 26 34 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 34 0 := by
  decide

private theorem x4NRGRow26Coeff35_spec :
    mulCoeffTwo GData X4NRC3Data 26 35 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 35 0 := by
  decide

private theorem x4NRGRow26Coeff36_spec :
    mulCoeffTwo GData X4NRC3Data 26 36 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 36 0 := by
  decide

private theorem x4NRGRow26Coeff37_spec :
    mulCoeffTwo GData X4NRC3Data 26 37 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 37 0 := by
  decide

private theorem x4NRGRow26Coeff38_spec :
    mulCoeffTwo GData X4NRC3Data 26 38 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 38 0 := by
  decide

private theorem x4NRGRow26Coeff39_spec :
    mulCoeffTwo GData X4NRC3Data 26 39 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 39 0 := by
  decide

private theorem x4NRGRow26Coeff40_spec :
    mulCoeffTwo GData X4NRC3Data 26 40 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 40 0 := by
  decide

private theorem x4NRGRow26Coeff41_spec :
    mulCoeffTwo GData X4NRC3Data 26 41 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 41 0 := by
  decide

private theorem x4NRGRow26Coeff42_spec :
    mulCoeffTwo GData X4NRC3Data 26 42 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 42 0 := by
  decide

private theorem x4NRGRow26Coeff43_spec :
    mulCoeffTwo GData X4NRC3Data 26 43 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 43 0 := by
  decide

private theorem x4NRGRow26Coeff44_spec :
    mulCoeffTwo GData X4NRC3Data 26 44 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 44 0 := by
  decide

private theorem x4NRGRow26Coeff45_spec :
    mulCoeffTwo GData X4NRC3Data 26 45 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 45 0 := by
  decide

private theorem x4NRGRow26Coeff46_spec :
    mulCoeffTwo GData X4NRC3Data 26 46 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 46 0 := by
  decide

private theorem x4NRGRow26Coeff47_spec :
    mulCoeffTwo GData X4NRC3Data 26 47 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 47 0 := by
  decide

private theorem x4NRGRow26Coeff48_spec :
    mulCoeffTwo GData X4NRC3Data 26 48 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 48 0 := by
  decide

private theorem x4NRGRow26Coeff49_spec :
    mulCoeffTwo GData X4NRC3Data 26 49 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 49 0 := by
  decide

private theorem x4NRGRow26Coeff50_spec :
    mulCoeffTwo GData X4NRC3Data 26 50 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 50 0 := by
  decide

private theorem x4NRGRow26Coeff51_spec :
    mulCoeffTwo GData X4NRC3Data 26 51 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 51 0 := by
  decide

private theorem x4NRGRow26Coeff52_spec :
    mulCoeffTwo GData X4NRC3Data 26 52 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 52 0 := by
  decide

private theorem x4NRGRow26Coeff53_spec :
    mulCoeffTwo GData X4NRC3Data 26 53 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 53 0 := by
  decide

private theorem x4NRGRow26Coeff54_spec :
    mulCoeffTwo GData X4NRC3Data 26 54 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 54 0 := by
  decide

private theorem x4NRGRow26Coeff55_spec :
    mulCoeffTwo GData X4NRC3Data 26 55 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 55 0 := by
  decide

private theorem x4NRGRow26Coeff56_spec :
    mulCoeffTwo GData X4NRC3Data 26 56 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 56 0 := by
  decide

private theorem x4NRGRow26Coeff57_spec :
    mulCoeffTwo GData X4NRC3Data 26 57 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 57 0 := by
  decide

private theorem x4NRGRow26Coeff58_spec :
    mulCoeffTwo GData X4NRC3Data 26 58 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 58 0 := by
  decide

private theorem x4NRGRow26Coeff59_spec :
    mulCoeffTwo GData X4NRC3Data 26 59 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 59 0 := by
  decide

private theorem x4NRGRow26Coeff60_spec :
    mulCoeffTwo GData X4NRC3Data 26 60 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 60 0 := by
  decide

private theorem x4NRGRow26Coeff61_spec :
    mulCoeffTwo GData X4NRC3Data 26 61 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 61 0 := by
  decide

private theorem x4NRGRow26Coeff62_spec :
    mulCoeffTwo GData X4NRC3Data 26 62 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 62 0 := by
  decide

private theorem x4NRGRow26Coeff63_spec :
    mulCoeffTwo GData X4NRC3Data 26 63 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 63 0 := by
  decide

private theorem x4NRGRow26Coeff64_spec :
    mulCoeffTwo GData X4NRC3Data 26 64 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 64 0 := by
  decide

private theorem x4NRGRow26Coeff65_spec :
    mulCoeffTwo GData X4NRC3Data 26 65 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 65 0 := by
  decide

private theorem x4NRGRow26Coeff66_spec :
    mulCoeffTwo GData X4NRC3Data 26 66 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 66 0 := by
  decide

private theorem x4NRGRow26Coeff67_spec :
    mulCoeffTwo GData X4NRC3Data 26 67 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 67 0 := by
  decide

private theorem x4NRGRow26Coeff68_spec :
    mulCoeffTwo GData X4NRC3Data 26 68 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 68 0 := by
  decide

private theorem x4NRGRow26Coeff69_spec :
    mulCoeffTwo GData X4NRC3Data 26 69 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 69 0 := by
  decide

private theorem x4NRGRow26Coeff70_spec :
    mulCoeffTwo GData X4NRC3Data 26 70 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 70 0 := by
  decide

private theorem x4NRGRow26Coeff71_spec :
    mulCoeffTwo GData X4NRC3Data 26 71 =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD 71 0 := by
  decide

private theorem x4NRGRow26Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo GData X4NRC3Data 26 j =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow26Coeff0_spec
  · exact x4NRGRow26Coeff1_spec
  · exact x4NRGRow26Coeff2_spec
  · exact x4NRGRow26Coeff3_spec
  · exact x4NRGRow26Coeff4_spec
  · exact x4NRGRow26Coeff5_spec
  · exact x4NRGRow26Coeff6_spec
  · exact x4NRGRow26Coeff7_spec
  · exact x4NRGRow26Coeff8_spec
  · exact x4NRGRow26Coeff9_spec

private theorem x4NRGRow26Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo GData X4NRC3Data 26 j =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow26Coeff10_spec
  · exact x4NRGRow26Coeff11_spec
  · exact x4NRGRow26Coeff12_spec
  · exact x4NRGRow26Coeff13_spec
  · exact x4NRGRow26Coeff14_spec
  · exact x4NRGRow26Coeff15_spec
  · exact x4NRGRow26Coeff16_spec
  · exact x4NRGRow26Coeff17_spec
  · exact x4NRGRow26Coeff18_spec
  · exact x4NRGRow26Coeff19_spec

private theorem x4NRGRow26Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo GData X4NRC3Data 26 j =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow26Coeff20_spec
  · exact x4NRGRow26Coeff21_spec
  · exact x4NRGRow26Coeff22_spec
  · exact x4NRGRow26Coeff23_spec
  · exact x4NRGRow26Coeff24_spec
  · exact x4NRGRow26Coeff25_spec
  · exact x4NRGRow26Coeff26_spec
  · exact x4NRGRow26Coeff27_spec
  · exact x4NRGRow26Coeff28_spec
  · exact x4NRGRow26Coeff29_spec

private theorem x4NRGRow26Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo GData X4NRC3Data 26 j =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow26Coeff30_spec
  · exact x4NRGRow26Coeff31_spec
  · exact x4NRGRow26Coeff32_spec
  · exact x4NRGRow26Coeff33_spec
  · exact x4NRGRow26Coeff34_spec
  · exact x4NRGRow26Coeff35_spec
  · exact x4NRGRow26Coeff36_spec
  · exact x4NRGRow26Coeff37_spec
  · exact x4NRGRow26Coeff38_spec
  · exact x4NRGRow26Coeff39_spec

private theorem x4NRGRow26Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo GData X4NRC3Data 26 j =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow26Coeff40_spec
  · exact x4NRGRow26Coeff41_spec
  · exact x4NRGRow26Coeff42_spec
  · exact x4NRGRow26Coeff43_spec
  · exact x4NRGRow26Coeff44_spec
  · exact x4NRGRow26Coeff45_spec
  · exact x4NRGRow26Coeff46_spec
  · exact x4NRGRow26Coeff47_spec
  · exact x4NRGRow26Coeff48_spec
  · exact x4NRGRow26Coeff49_spec

private theorem x4NRGRow26Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo GData X4NRC3Data 26 j =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow26Coeff50_spec
  · exact x4NRGRow26Coeff51_spec
  · exact x4NRGRow26Coeff52_spec
  · exact x4NRGRow26Coeff53_spec
  · exact x4NRGRow26Coeff54_spec
  · exact x4NRGRow26Coeff55_spec
  · exact x4NRGRow26Coeff56_spec
  · exact x4NRGRow26Coeff57_spec
  · exact x4NRGRow26Coeff58_spec
  · exact x4NRGRow26Coeff59_spec

private theorem x4NRGRow26Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo GData X4NRC3Data 26 j =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NRGRow26Coeff60_spec
  · exact x4NRGRow26Coeff61_spec
  · exact x4NRGRow26Coeff62_spec
  · exact x4NRGRow26Coeff63_spec
  · exact x4NRGRow26Coeff64_spec
  · exact x4NRGRow26Coeff65_spec
  · exact x4NRGRow26Coeff66_spec
  · exact x4NRGRow26Coeff67_spec
  · exact x4NRGRow26Coeff68_spec
  · exact x4NRGRow26Coeff69_spec

private theorem x4NRGRow26Coeffs70To71_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 72) :
    mulCoeffTwo GData X4NRC3Data 26 j =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 := by
    omega
  rcases hCases with
    rfl | rfl
  · exact x4NRGRow26Coeff70_spec
  · exact x4NRGRow26Coeff71_spec

private theorem x4NRGRow26_coefficients (j : ℕ) (hj : j < 72) :
    mulCoeffTwo GData X4NRC3Data 26 j =
      ((rectangularize 52 72 X4NRGData).getD 26 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact x4NRGRow26Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact x4NRGRow26Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact x4NRGRow26Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact x4NRGRow26Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact x4NRGRow26Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact x4NRGRow26Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact x4NRGRow26Coeffs60To69_spec j (by omega) h70
  exact x4NRGRow26Coeffs70To71_spec j (by omega) hj

private theorem x4NRGRow26Padded_spec :
    padOne 72 (mulRow GData X4NRC3Data 26) =
      (rectangularize 52 72 X4NRGData).getD 26 [] := by
  apply padOne_mulRow_eq_of_coefficients 72 GData X4NRC3Data 26
    ((rectangularize 52 72 X4NRGData).getD 26 [])
  · decide
  · have hTargetSupport : (X4NRGData.getD 26 []).length ≤ 72 := by
      decide
    rw [getD_rectangularize 52 72 X4NRGData 26 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact x4NRGRow26_coefficients

private theorem x4NRGRow26_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 26 [] =
      (rectangularize 52 72 X4NRGData).getD 26 [] := by
  rw [getD_rectangularize 52 72 (Two.mul GData X4NRC3Data) 26 (by omega),
    ← mulRow_eq_getD]
  exact x4NRGRow26Padded_spec

private theorem x4NRGRow27_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 27 [] =
      (rectangularize 52 72 X4NRGData).getD 27 [] := by
  decide

private theorem x4NRGRow28_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 28 [] =
      (rectangularize 52 72 X4NRGData).getD 28 [] := by
  decide

private theorem x4NRGRow29_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 29 [] =
      (rectangularize 52 72 X4NRGData).getD 29 [] := by
  decide

private theorem x4NRGRow30_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 30 [] =
      (rectangularize 52 72 X4NRGData).getD 30 [] := by
  decide

private theorem x4NRGRow31_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 31 [] =
      (rectangularize 52 72 X4NRGData).getD 31 [] := by
  decide

private theorem x4NRGRow32_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 32 [] =
      (rectangularize 52 72 X4NRGData).getD 32 [] := by
  decide

private theorem x4NRGRow33_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 33 [] =
      (rectangularize 52 72 X4NRGData).getD 33 [] := by
  decide

private theorem x4NRGRow34_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 34 [] =
      (rectangularize 52 72 X4NRGData).getD 34 [] := by
  decide

private theorem x4NRGRow35_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 35 [] =
      (rectangularize 52 72 X4NRGData).getD 35 [] := by
  decide

private theorem x4NRGRow36_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 36 [] =
      (rectangularize 52 72 X4NRGData).getD 36 [] := by
  decide

private theorem x4NRGRow37_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 37 [] =
      (rectangularize 52 72 X4NRGData).getD 37 [] := by
  decide

private theorem x4NRGRow38_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 38 [] =
      (rectangularize 52 72 X4NRGData).getD 38 [] := by
  decide

private theorem x4NRGRow39_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 39 [] =
      (rectangularize 52 72 X4NRGData).getD 39 [] := by
  decide

private theorem x4NRGRow40_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 40 [] =
      (rectangularize 52 72 X4NRGData).getD 40 [] := by
  decide

private theorem x4NRGRow41_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 41 [] =
      (rectangularize 52 72 X4NRGData).getD 41 [] := by
  decide

private theorem x4NRGRow42_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 42 [] =
      (rectangularize 52 72 X4NRGData).getD 42 [] := by
  decide

private theorem x4NRGRow43_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 43 [] =
      (rectangularize 52 72 X4NRGData).getD 43 [] := by
  decide

private theorem x4NRGRow44_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 44 [] =
      (rectangularize 52 72 X4NRGData).getD 44 [] := by
  decide

private theorem x4NRGRow45_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 45 [] =
      (rectangularize 52 72 X4NRGData).getD 45 [] := by
  decide

private theorem x4NRGRow46_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 46 [] =
      (rectangularize 52 72 X4NRGData).getD 46 [] := by
  decide

private theorem x4NRGRow47_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 47 [] =
      (rectangularize 52 72 X4NRGData).getD 47 [] := by
  decide

private theorem x4NRGRow48_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 48 [] =
      (rectangularize 52 72 X4NRGData).getD 48 [] := by
  decide

private theorem x4NRGRow49_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 49 [] =
      (rectangularize 52 72 X4NRGData).getD 49 [] := by
  decide

private theorem x4NRGRow50_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 50 [] =
      (rectangularize 52 72 X4NRGData).getD 50 [] := by
  decide

private theorem x4NRGRow51_spec :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD 51 [] =
      (rectangularize 52 72 X4NRGData).getD 51 [] := by
  decide

private theorem x4NRGRows_spec (n : ℕ) (hn : n < 52) :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).getD n [] =
      (rectangularize 52 72 X4NRGData).getD n [] := by
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
    n = 50 ∨ n = 51 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact x4NRGRow0_spec
  · exact x4NRGRow1_spec
  · exact x4NRGRow2_spec
  · exact x4NRGRow3_spec
  · exact x4NRGRow4_spec
  · exact x4NRGRow5_spec
  · exact x4NRGRow6_spec
  · exact x4NRGRow7_spec
  · exact x4NRGRow8_spec
  · exact x4NRGRow9_spec
  · exact x4NRGRow10_spec
  · exact x4NRGRow11_spec
  · exact x4NRGRow12_spec
  · exact x4NRGRow13_spec
  · exact x4NRGRow14_spec
  · exact x4NRGRow15_spec
  · exact x4NRGRow16_spec
  · exact x4NRGRow17_spec
  · exact x4NRGRow18_spec
  · exact x4NRGRow19_spec
  · exact x4NRGRow20_spec
  · exact x4NRGRow21_spec
  · exact x4NRGRow22_spec
  · exact x4NRGRow23_spec
  · exact x4NRGRow24_spec
  · exact x4NRGRow25_spec
  · exact x4NRGRow26_spec
  · exact x4NRGRow27_spec
  · exact x4NRGRow28_spec
  · exact x4NRGRow29_spec
  · exact x4NRGRow30_spec
  · exact x4NRGRow31_spec
  · exact x4NRGRow32_spec
  · exact x4NRGRow33_spec
  · exact x4NRGRow34_spec
  · exact x4NRGRow35_spec
  · exact x4NRGRow36_spec
  · exact x4NRGRow37_spec
  · exact x4NRGRow38_spec
  · exact x4NRGRow39_spec
  · exact x4NRGRow40_spec
  · exact x4NRGRow41_spec
  · exact x4NRGRow42_spec
  · exact x4NRGRow43_spec
  · exact x4NRGRow44_spec
  · exact x4NRGRow45_spec
  · exact x4NRGRow46_spec
  · exact x4NRGRow47_spec
  · exact x4NRGRow48_spec
  · exact x4NRGRow49_spec
  · exact x4NRGRow50_spec
  · exact x4NRGRow51_spec

private theorem x4NRGLeft_length :
    (rectangularize 52 72 (Two.mul GData X4NRC3Data)).length = 52 := by
  decide

private theorem x4NRGRight_length :
    (rectangularize 52 72 X4NRGData).length = 52 := by
  decide

-- Exact bidegree bound (51, 71); no row or column is discarded.
private theorem x4NRGData_spec :
    rectangularize 52 72 (Two.mul GData X4NRC3Data) =
      rectangularize 52 72 X4NRGData := by
  apply List.ext_getElem (x4NRGLeft_length.trans x4NRGRight_length.symm)
  intro n hn _
  rw [List.getElem_eq_getD [], List.getElem_eq_getD []]
  rw [x4NRGLeft_length] at hn
  exact x4NRGRows_spec n hn

/-- Evaluation of the checked `S * C^3 * G` branch of the canonical `N`. -/
theorem eval_x4NRightData (r s : ℚ) :
    Two.eval X4NRGData r s =
      Two.eval SData r s * Two.eval CData r s ^ 3 *
        OrderTwentyFiveRawOrbitFactorCertificate.G r s *
          Two.eval X4MData r s := by
  have hS := congrArg (fun p => Two.eval p r s) x4NRSData_spec
  have hC1 := congrArg (fun p => Two.eval p r s) x4NRC1Data_spec
  have hC2 := congrArg (fun p => Two.eval p r s) x4NRC2Data_spec
  have hC3 := congrArg (fun p => Two.eval p r s) x4NRC3Data_spec
  have hG := congrArg (fun p => Two.eval p r s) x4NRGData_spec
  simp only [eval_rectangularize, Two.eval_mul] at hS hC1 hC2 hC3 hG
  calc
    Two.eval X4NRGData r s =
        Two.eval GData r s * Two.eval X4NRC3Data r s := hG.symm
    _ = Two.eval GData r s *
        (Two.eval CData r s * Two.eval X4NRC2Data r s) := by rw [← hC3]
    _ = Two.eval GData r s *
        (Two.eval CData r s *
          (Two.eval CData r s * Two.eval X4NRC1Data r s)) := by rw [← hC2]
    _ = Two.eval GData r s *
        (Two.eval CData r s *
          (Two.eval CData r s *
            (Two.eval CData r s * Two.eval X4NRSData r s))) := by rw [← hC1]
    _ = Two.eval SData r s * Two.eval CData r s ^ 3 *
        OrderTwentyFiveRawOrbitFactorCertificate.G r s *
          Two.eval X4MData r s := by rw [← hS, eval_GData]; ring

end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
