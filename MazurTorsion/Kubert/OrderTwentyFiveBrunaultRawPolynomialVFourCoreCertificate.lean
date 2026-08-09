/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroDenseFactors
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialVThreeCertificate
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialVFourSData
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialVFourCOneData
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialVFourCTwoData
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialVFourCThreeData
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialVFourJData
import MazurTorsion.Kubert.OrderTwentyFiveDensePolynomialRowCertificate

/-!
# Checked primitive core of the raw V fourth-power table

Every stated rectangle is an exact bidegree bound, and rectangularization only
appends zeros. The row-local equalities therefore check every coefficient and
every possible tail.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveRelationZeroCertificate.Dense
open OrderTwentyFiveDensePolynomialRectangular
open OrderTwentyFiveDensePolynomialRowCertificate

private theorem v4SRow0_spec :
    padOne 68 (mulRow SData V3Data 0) =
      (rectangularize 46 68 V4SData).getD 0 [] := by
  decide

private theorem v4SRow1_spec :
    padOne 68 (mulRow SData V3Data 1) =
      (rectangularize 46 68 V4SData).getD 1 [] := by
  decide

private theorem v4SRow2_spec :
    padOne 68 (mulRow SData V3Data 2) =
      (rectangularize 46 68 V4SData).getD 2 [] := by
  decide

private theorem v4SRow3_spec :
    padOne 68 (mulRow SData V3Data 3) =
      (rectangularize 46 68 V4SData).getD 3 [] := by
  decide

private theorem v4SRow4_spec :
    padOne 68 (mulRow SData V3Data 4) =
      (rectangularize 46 68 V4SData).getD 4 [] := by
  decide

private theorem v4SRow5_spec :
    padOne 68 (mulRow SData V3Data 5) =
      (rectangularize 46 68 V4SData).getD 5 [] := by
  decide

private theorem v4SRow6_spec :
    padOne 68 (mulRow SData V3Data 6) =
      (rectangularize 46 68 V4SData).getD 6 [] := by
  decide

private theorem v4SRow7_spec :
    padOne 68 (mulRow SData V3Data 7) =
      (rectangularize 46 68 V4SData).getD 7 [] := by
  decide

private theorem v4SRow8_spec :
    padOne 68 (mulRow SData V3Data 8) =
      (rectangularize 46 68 V4SData).getD 8 [] := by
  decide

private theorem v4SRow9_spec :
    padOne 68 (mulRow SData V3Data 9) =
      (rectangularize 46 68 V4SData).getD 9 [] := by
  decide

private theorem v4SRow10_spec :
    padOne 68 (mulRow SData V3Data 10) =
      (rectangularize 46 68 V4SData).getD 10 [] := by
  decide

private theorem v4SRow11_spec :
    padOne 68 (mulRow SData V3Data 11) =
      (rectangularize 46 68 V4SData).getD 11 [] := by
  decide

private theorem v4SRow12_spec :
    padOne 68 (mulRow SData V3Data 12) =
      (rectangularize 46 68 V4SData).getD 12 [] := by
  decide

private theorem v4SRow13_spec :
    padOne 68 (mulRow SData V3Data 13) =
      (rectangularize 46 68 V4SData).getD 13 [] := by
  decide

private theorem v4SRow14_spec :
    padOne 68 (mulRow SData V3Data 14) =
      (rectangularize 46 68 V4SData).getD 14 [] := by
  decide

private theorem v4SRow15_spec :
    padOne 68 (mulRow SData V3Data 15) =
      (rectangularize 46 68 V4SData).getD 15 [] := by
  decide

private theorem v4SRow16_spec :
    padOne 68 (mulRow SData V3Data 16) =
      (rectangularize 46 68 V4SData).getD 16 [] := by
  decide

private theorem v4SRow17_spec :
    padOne 68 (mulRow SData V3Data 17) =
      (rectangularize 46 68 V4SData).getD 17 [] := by
  decide

private theorem v4SRow18_spec :
    padOne 68 (mulRow SData V3Data 18) =
      (rectangularize 46 68 V4SData).getD 18 [] := by
  decide

private theorem v4SRow19_spec :
    padOne 68 (mulRow SData V3Data 19) =
      (rectangularize 46 68 V4SData).getD 19 [] := by
  decide

private theorem v4SRow20_spec :
    padOne 68 (mulRow SData V3Data 20) =
      (rectangularize 46 68 V4SData).getD 20 [] := by
  decide

private theorem v4SRow21_spec :
    padOne 68 (mulRow SData V3Data 21) =
      (rectangularize 46 68 V4SData).getD 21 [] := by
  decide

private theorem v4SRow22_spec :
    padOne 68 (mulRow SData V3Data 22) =
      (rectangularize 46 68 V4SData).getD 22 [] := by
  decide

private theorem v4SRow23_spec :
    padOne 68 (mulRow SData V3Data 23) =
      (rectangularize 46 68 V4SData).getD 23 [] := by
  decide

private theorem v4SRow24_spec :
    padOne 68 (mulRow SData V3Data 24) =
      (rectangularize 46 68 V4SData).getD 24 [] := by
  decide

private theorem v4SRow25_spec :
    padOne 68 (mulRow SData V3Data 25) =
      (rectangularize 46 68 V4SData).getD 25 [] := by
  decide

private theorem v4SRow26_spec :
    padOne 68 (mulRow SData V3Data 26) =
      (rectangularize 46 68 V4SData).getD 26 [] := by
  decide

private theorem v4SRow27_spec :
    padOne 68 (mulRow SData V3Data 27) =
      (rectangularize 46 68 V4SData).getD 27 [] := by
  decide

private theorem v4SRow28_spec :
    padOne 68 (mulRow SData V3Data 28) =
      (rectangularize 46 68 V4SData).getD 28 [] := by
  decide

private theorem v4SRow29_spec :
    padOne 68 (mulRow SData V3Data 29) =
      (rectangularize 46 68 V4SData).getD 29 [] := by
  decide

private theorem v4SRow30_spec :
    padOne 68 (mulRow SData V3Data 30) =
      (rectangularize 46 68 V4SData).getD 30 [] := by
  decide

private theorem v4SRow31_spec :
    padOne 68 (mulRow SData V3Data 31) =
      (rectangularize 46 68 V4SData).getD 31 [] := by
  decide

private theorem v4SRow32_spec :
    padOne 68 (mulRow SData V3Data 32) =
      (rectangularize 46 68 V4SData).getD 32 [] := by
  decide

private theorem v4SRow33_spec :
    padOne 68 (mulRow SData V3Data 33) =
      (rectangularize 46 68 V4SData).getD 33 [] := by
  decide

private theorem v4SRow34_spec :
    padOne 68 (mulRow SData V3Data 34) =
      (rectangularize 46 68 V4SData).getD 34 [] := by
  decide

private theorem v4SRow35_spec :
    padOne 68 (mulRow SData V3Data 35) =
      (rectangularize 46 68 V4SData).getD 35 [] := by
  decide

private theorem v4SRow36_spec :
    padOne 68 (mulRow SData V3Data 36) =
      (rectangularize 46 68 V4SData).getD 36 [] := by
  decide

private theorem v4SRow37_spec :
    padOne 68 (mulRow SData V3Data 37) =
      (rectangularize 46 68 V4SData).getD 37 [] := by
  decide

private theorem v4SRow38_spec :
    padOne 68 (mulRow SData V3Data 38) =
      (rectangularize 46 68 V4SData).getD 38 [] := by
  decide

private theorem v4SRow39_spec :
    padOne 68 (mulRow SData V3Data 39) =
      (rectangularize 46 68 V4SData).getD 39 [] := by
  decide

private theorem v4SRow40_spec :
    padOne 68 (mulRow SData V3Data 40) =
      (rectangularize 46 68 V4SData).getD 40 [] := by
  decide

private theorem v4SRow41_spec :
    padOne 68 (mulRow SData V3Data 41) =
      (rectangularize 46 68 V4SData).getD 41 [] := by
  decide

private theorem v4SRow42_spec :
    padOne 68 (mulRow SData V3Data 42) =
      (rectangularize 46 68 V4SData).getD 42 [] := by
  decide

private theorem v4SRow43_spec :
    padOne 68 (mulRow SData V3Data 43) =
      (rectangularize 46 68 V4SData).getD 43 [] := by
  decide

private theorem v4SRow44_spec :
    padOne 68 (mulRow SData V3Data 44) =
      (rectangularize 46 68 V4SData).getD 44 [] := by
  decide

private theorem v4SRow45_spec :
    padOne 68 (mulRow SData V3Data 45) =
      (rectangularize 46 68 V4SData).getD 45 [] := by
  decide

private theorem v4SRows_spec (n : ℕ) (hn : n < 46) :
    padOne 68 (mulRow SData V3Data n) =
      (rectangularize 46 68 V4SData).getD n [] := by
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
    n = 45 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact v4SRow0_spec
  · exact v4SRow1_spec
  · exact v4SRow2_spec
  · exact v4SRow3_spec
  · exact v4SRow4_spec
  · exact v4SRow5_spec
  · exact v4SRow6_spec
  · exact v4SRow7_spec
  · exact v4SRow8_spec
  · exact v4SRow9_spec
  · exact v4SRow10_spec
  · exact v4SRow11_spec
  · exact v4SRow12_spec
  · exact v4SRow13_spec
  · exact v4SRow14_spec
  · exact v4SRow15_spec
  · exact v4SRow16_spec
  · exact v4SRow17_spec
  · exact v4SRow18_spec
  · exact v4SRow19_spec
  · exact v4SRow20_spec
  · exact v4SRow21_spec
  · exact v4SRow22_spec
  · exact v4SRow23_spec
  · exact v4SRow24_spec
  · exact v4SRow25_spec
  · exact v4SRow26_spec
  · exact v4SRow27_spec
  · exact v4SRow28_spec
  · exact v4SRow29_spec
  · exact v4SRow30_spec
  · exact v4SRow31_spec
  · exact v4SRow32_spec
  · exact v4SRow33_spec
  · exact v4SRow34_spec
  · exact v4SRow35_spec
  · exact v4SRow36_spec
  · exact v4SRow37_spec
  · exact v4SRow38_spec
  · exact v4SRow39_spec
  · exact v4SRow40_spec
  · exact v4SRow41_spec
  · exact v4SRow42_spec
  · exact v4SRow43_spec
  · exact v4SRow44_spec
  · exact v4SRow45_spec

private theorem v4SLeft_length :
    (rectangularize 46 68 (Two.mul SData V3Data)).length = 46 := by
  decide

private theorem v4SRight_length :
    (rectangularize 46 68 V4SData).length = 46 := by
  decide

-- Exact bidegree bound (45, 67); no row or column is discarded.
private theorem v4SData_spec :
    rectangularize 46 68 (Two.mul SData V3Data) =
      rectangularize 46 68 V4SData := by
  apply List.ext_getElem (v4SLeft_length.trans v4SRight_length.symm)
  intro n hn _
  rw [List.getElem_eq_getD [], List.getElem_eq_getD []]
  rw [v4SLeft_length] at hn
  rw [getD_rectangularize 46 68 (Two.mul SData V3Data) n hn,
    ← mulRow_eq_getD]
  exact v4SRows_spec n hn

private theorem v4C1Row0_spec :
    padOne 69 (mulRow CData V4SData 0) =
      (rectangularize 47 69 V4C1Data).getD 0 [] := by
  decide

private theorem v4C1Row1_spec :
    padOne 69 (mulRow CData V4SData 1) =
      (rectangularize 47 69 V4C1Data).getD 1 [] := by
  decide

private theorem v4C1Row2_spec :
    padOne 69 (mulRow CData V4SData 2) =
      (rectangularize 47 69 V4C1Data).getD 2 [] := by
  decide

private theorem v4C1Row3_spec :
    padOne 69 (mulRow CData V4SData 3) =
      (rectangularize 47 69 V4C1Data).getD 3 [] := by
  decide

private theorem v4C1Row4_spec :
    padOne 69 (mulRow CData V4SData 4) =
      (rectangularize 47 69 V4C1Data).getD 4 [] := by
  decide

private theorem v4C1Row5_spec :
    padOne 69 (mulRow CData V4SData 5) =
      (rectangularize 47 69 V4C1Data).getD 5 [] := by
  decide

private theorem v4C1Row6_spec :
    padOne 69 (mulRow CData V4SData 6) =
      (rectangularize 47 69 V4C1Data).getD 6 [] := by
  decide

private theorem v4C1Row7_spec :
    padOne 69 (mulRow CData V4SData 7) =
      (rectangularize 47 69 V4C1Data).getD 7 [] := by
  decide

private theorem v4C1Row8_spec :
    padOne 69 (mulRow CData V4SData 8) =
      (rectangularize 47 69 V4C1Data).getD 8 [] := by
  decide

private theorem v4C1Row9_spec :
    padOne 69 (mulRow CData V4SData 9) =
      (rectangularize 47 69 V4C1Data).getD 9 [] := by
  decide

private theorem v4C1Row10_spec :
    padOne 69 (mulRow CData V4SData 10) =
      (rectangularize 47 69 V4C1Data).getD 10 [] := by
  decide

private theorem v4C1Row11_spec :
    padOne 69 (mulRow CData V4SData 11) =
      (rectangularize 47 69 V4C1Data).getD 11 [] := by
  decide

private theorem v4C1Row12_spec :
    padOne 69 (mulRow CData V4SData 12) =
      (rectangularize 47 69 V4C1Data).getD 12 [] := by
  decide

private theorem v4C1Row13_spec :
    padOne 69 (mulRow CData V4SData 13) =
      (rectangularize 47 69 V4C1Data).getD 13 [] := by
  decide

private theorem v4C1Row14_spec :
    padOne 69 (mulRow CData V4SData 14) =
      (rectangularize 47 69 V4C1Data).getD 14 [] := by
  decide

private theorem v4C1Row15_spec :
    padOne 69 (mulRow CData V4SData 15) =
      (rectangularize 47 69 V4C1Data).getD 15 [] := by
  decide

private theorem v4C1Row16_spec :
    padOne 69 (mulRow CData V4SData 16) =
      (rectangularize 47 69 V4C1Data).getD 16 [] := by
  decide

private theorem v4C1Row17_spec :
    padOne 69 (mulRow CData V4SData 17) =
      (rectangularize 47 69 V4C1Data).getD 17 [] := by
  decide

private theorem v4C1Row18_spec :
    padOne 69 (mulRow CData V4SData 18) =
      (rectangularize 47 69 V4C1Data).getD 18 [] := by
  decide

private theorem v4C1Row19_spec :
    padOne 69 (mulRow CData V4SData 19) =
      (rectangularize 47 69 V4C1Data).getD 19 [] := by
  decide

private theorem v4C1Row20_spec :
    padOne 69 (mulRow CData V4SData 20) =
      (rectangularize 47 69 V4C1Data).getD 20 [] := by
  decide

private theorem v4C1Row21_spec :
    padOne 69 (mulRow CData V4SData 21) =
      (rectangularize 47 69 V4C1Data).getD 21 [] := by
  decide

private theorem v4C1Row22_spec :
    padOne 69 (mulRow CData V4SData 22) =
      (rectangularize 47 69 V4C1Data).getD 22 [] := by
  decide

private theorem v4C1Row23_spec :
    padOne 69 (mulRow CData V4SData 23) =
      (rectangularize 47 69 V4C1Data).getD 23 [] := by
  decide

private theorem v4C1Row24_spec :
    padOne 69 (mulRow CData V4SData 24) =
      (rectangularize 47 69 V4C1Data).getD 24 [] := by
  decide

private theorem v4C1Row25_spec :
    padOne 69 (mulRow CData V4SData 25) =
      (rectangularize 47 69 V4C1Data).getD 25 [] := by
  decide

private theorem v4C1Row26_spec :
    padOne 69 (mulRow CData V4SData 26) =
      (rectangularize 47 69 V4C1Data).getD 26 [] := by
  decide

private theorem v4C1Row27_spec :
    padOne 69 (mulRow CData V4SData 27) =
      (rectangularize 47 69 V4C1Data).getD 27 [] := by
  decide

private theorem v4C1Row28_spec :
    padOne 69 (mulRow CData V4SData 28) =
      (rectangularize 47 69 V4C1Data).getD 28 [] := by
  decide

private theorem v4C1Row29_spec :
    padOne 69 (mulRow CData V4SData 29) =
      (rectangularize 47 69 V4C1Data).getD 29 [] := by
  decide

private theorem v4C1Row30_spec :
    padOne 69 (mulRow CData V4SData 30) =
      (rectangularize 47 69 V4C1Data).getD 30 [] := by
  decide

private theorem v4C1Row31_spec :
    padOne 69 (mulRow CData V4SData 31) =
      (rectangularize 47 69 V4C1Data).getD 31 [] := by
  decide

private theorem v4C1Row32_spec :
    padOne 69 (mulRow CData V4SData 32) =
      (rectangularize 47 69 V4C1Data).getD 32 [] := by
  decide

private theorem v4C1Row33_spec :
    padOne 69 (mulRow CData V4SData 33) =
      (rectangularize 47 69 V4C1Data).getD 33 [] := by
  decide

private theorem v4C1Row34_spec :
    padOne 69 (mulRow CData V4SData 34) =
      (rectangularize 47 69 V4C1Data).getD 34 [] := by
  decide

private theorem v4C1Row35_spec :
    padOne 69 (mulRow CData V4SData 35) =
      (rectangularize 47 69 V4C1Data).getD 35 [] := by
  decide

private theorem v4C1Row36_spec :
    padOne 69 (mulRow CData V4SData 36) =
      (rectangularize 47 69 V4C1Data).getD 36 [] := by
  decide

private theorem v4C1Row37_spec :
    padOne 69 (mulRow CData V4SData 37) =
      (rectangularize 47 69 V4C1Data).getD 37 [] := by
  decide

private theorem v4C1Row38_spec :
    padOne 69 (mulRow CData V4SData 38) =
      (rectangularize 47 69 V4C1Data).getD 38 [] := by
  decide

private theorem v4C1Row39_spec :
    padOne 69 (mulRow CData V4SData 39) =
      (rectangularize 47 69 V4C1Data).getD 39 [] := by
  decide

private theorem v4C1Row40_spec :
    padOne 69 (mulRow CData V4SData 40) =
      (rectangularize 47 69 V4C1Data).getD 40 [] := by
  decide

private theorem v4C1Row41_spec :
    padOne 69 (mulRow CData V4SData 41) =
      (rectangularize 47 69 V4C1Data).getD 41 [] := by
  decide

private theorem v4C1Row42_spec :
    padOne 69 (mulRow CData V4SData 42) =
      (rectangularize 47 69 V4C1Data).getD 42 [] := by
  decide

private theorem v4C1Row43_spec :
    padOne 69 (mulRow CData V4SData 43) =
      (rectangularize 47 69 V4C1Data).getD 43 [] := by
  decide

private theorem v4C1Row44_spec :
    padOne 69 (mulRow CData V4SData 44) =
      (rectangularize 47 69 V4C1Data).getD 44 [] := by
  decide

private theorem v4C1Row45_spec :
    padOne 69 (mulRow CData V4SData 45) =
      (rectangularize 47 69 V4C1Data).getD 45 [] := by
  decide

private theorem v4C1Row46_spec :
    padOne 69 (mulRow CData V4SData 46) =
      (rectangularize 47 69 V4C1Data).getD 46 [] := by
  decide

private theorem v4C1Rows_spec (n : ℕ) (hn : n < 47) :
    padOne 69 (mulRow CData V4SData n) =
      (rectangularize 47 69 V4C1Data).getD n [] := by
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
    n = 45 ∨ n = 46 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact v4C1Row0_spec
  · exact v4C1Row1_spec
  · exact v4C1Row2_spec
  · exact v4C1Row3_spec
  · exact v4C1Row4_spec
  · exact v4C1Row5_spec
  · exact v4C1Row6_spec
  · exact v4C1Row7_spec
  · exact v4C1Row8_spec
  · exact v4C1Row9_spec
  · exact v4C1Row10_spec
  · exact v4C1Row11_spec
  · exact v4C1Row12_spec
  · exact v4C1Row13_spec
  · exact v4C1Row14_spec
  · exact v4C1Row15_spec
  · exact v4C1Row16_spec
  · exact v4C1Row17_spec
  · exact v4C1Row18_spec
  · exact v4C1Row19_spec
  · exact v4C1Row20_spec
  · exact v4C1Row21_spec
  · exact v4C1Row22_spec
  · exact v4C1Row23_spec
  · exact v4C1Row24_spec
  · exact v4C1Row25_spec
  · exact v4C1Row26_spec
  · exact v4C1Row27_spec
  · exact v4C1Row28_spec
  · exact v4C1Row29_spec
  · exact v4C1Row30_spec
  · exact v4C1Row31_spec
  · exact v4C1Row32_spec
  · exact v4C1Row33_spec
  · exact v4C1Row34_spec
  · exact v4C1Row35_spec
  · exact v4C1Row36_spec
  · exact v4C1Row37_spec
  · exact v4C1Row38_spec
  · exact v4C1Row39_spec
  · exact v4C1Row40_spec
  · exact v4C1Row41_spec
  · exact v4C1Row42_spec
  · exact v4C1Row43_spec
  · exact v4C1Row44_spec
  · exact v4C1Row45_spec
  · exact v4C1Row46_spec

private theorem v4C1Left_length :
    (rectangularize 47 69 (Two.mul CData V4SData)).length = 47 := by
  decide

private theorem v4C1Right_length :
    (rectangularize 47 69 V4C1Data).length = 47 := by
  decide

-- Exact bidegree bound (46, 68); no row or column is discarded.
private theorem v4C1Data_spec :
    rectangularize 47 69 (Two.mul CData V4SData) =
      rectangularize 47 69 V4C1Data := by
  apply List.ext_getElem (v4C1Left_length.trans v4C1Right_length.symm)
  intro n hn _
  rw [List.getElem_eq_getD [], List.getElem_eq_getD []]
  rw [v4C1Left_length] at hn
  rw [getD_rectangularize 47 69 (Two.mul CData V4SData) n hn,
    ← mulRow_eq_getD]
  exact v4C1Rows_spec n hn

private theorem v4C2Row0_spec :
    padOne 70 (mulRow CData V4C1Data 0) =
      (rectangularize 48 70 V4C2Data).getD 0 [] := by
  decide

private theorem v4C2Row1_spec :
    padOne 70 (mulRow CData V4C1Data 1) =
      (rectangularize 48 70 V4C2Data).getD 1 [] := by
  decide

private theorem v4C2Row2_spec :
    padOne 70 (mulRow CData V4C1Data 2) =
      (rectangularize 48 70 V4C2Data).getD 2 [] := by
  decide

private theorem v4C2Row3_spec :
    padOne 70 (mulRow CData V4C1Data 3) =
      (rectangularize 48 70 V4C2Data).getD 3 [] := by
  decide

private theorem v4C2Row4_spec :
    padOne 70 (mulRow CData V4C1Data 4) =
      (rectangularize 48 70 V4C2Data).getD 4 [] := by
  decide

private theorem v4C2Row5_spec :
    padOne 70 (mulRow CData V4C1Data 5) =
      (rectangularize 48 70 V4C2Data).getD 5 [] := by
  decide

private theorem v4C2Row6_spec :
    padOne 70 (mulRow CData V4C1Data 6) =
      (rectangularize 48 70 V4C2Data).getD 6 [] := by
  decide

private theorem v4C2Row7_spec :
    padOne 70 (mulRow CData V4C1Data 7) =
      (rectangularize 48 70 V4C2Data).getD 7 [] := by
  decide

private theorem v4C2Row8_spec :
    padOne 70 (mulRow CData V4C1Data 8) =
      (rectangularize 48 70 V4C2Data).getD 8 [] := by
  decide

private theorem v4C2Row9_spec :
    padOne 70 (mulRow CData V4C1Data 9) =
      (rectangularize 48 70 V4C2Data).getD 9 [] := by
  decide

private theorem v4C2Row10_spec :
    padOne 70 (mulRow CData V4C1Data 10) =
      (rectangularize 48 70 V4C2Data).getD 10 [] := by
  decide

private theorem v4C2Row11_spec :
    padOne 70 (mulRow CData V4C1Data 11) =
      (rectangularize 48 70 V4C2Data).getD 11 [] := by
  decide

private theorem v4C2Row12_spec :
    padOne 70 (mulRow CData V4C1Data 12) =
      (rectangularize 48 70 V4C2Data).getD 12 [] := by
  decide

private theorem v4C2Row13_spec :
    padOne 70 (mulRow CData V4C1Data 13) =
      (rectangularize 48 70 V4C2Data).getD 13 [] := by
  decide

private theorem v4C2Row14_spec :
    padOne 70 (mulRow CData V4C1Data 14) =
      (rectangularize 48 70 V4C2Data).getD 14 [] := by
  decide

private theorem v4C2Row15_spec :
    padOne 70 (mulRow CData V4C1Data 15) =
      (rectangularize 48 70 V4C2Data).getD 15 [] := by
  decide

private theorem v4C2Row16_spec :
    padOne 70 (mulRow CData V4C1Data 16) =
      (rectangularize 48 70 V4C2Data).getD 16 [] := by
  decide

private theorem v4C2Row17_spec :
    padOne 70 (mulRow CData V4C1Data 17) =
      (rectangularize 48 70 V4C2Data).getD 17 [] := by
  decide

private theorem v4C2Row18_spec :
    padOne 70 (mulRow CData V4C1Data 18) =
      (rectangularize 48 70 V4C2Data).getD 18 [] := by
  decide

private theorem v4C2Row19_spec :
    padOne 70 (mulRow CData V4C1Data 19) =
      (rectangularize 48 70 V4C2Data).getD 19 [] := by
  decide

private theorem v4C2Row20_spec :
    padOne 70 (mulRow CData V4C1Data 20) =
      (rectangularize 48 70 V4C2Data).getD 20 [] := by
  decide

private theorem v4C2Row21_spec :
    padOne 70 (mulRow CData V4C1Data 21) =
      (rectangularize 48 70 V4C2Data).getD 21 [] := by
  decide

private theorem v4C2Row22_spec :
    padOne 70 (mulRow CData V4C1Data 22) =
      (rectangularize 48 70 V4C2Data).getD 22 [] := by
  decide

private theorem v4C2Row23_spec :
    padOne 70 (mulRow CData V4C1Data 23) =
      (rectangularize 48 70 V4C2Data).getD 23 [] := by
  decide

private theorem v4C2Row24_spec :
    padOne 70 (mulRow CData V4C1Data 24) =
      (rectangularize 48 70 V4C2Data).getD 24 [] := by
  decide

private theorem v4C2Row25_spec :
    padOne 70 (mulRow CData V4C1Data 25) =
      (rectangularize 48 70 V4C2Data).getD 25 [] := by
  decide

private theorem v4C2Row26_spec :
    padOne 70 (mulRow CData V4C1Data 26) =
      (rectangularize 48 70 V4C2Data).getD 26 [] := by
  decide

private theorem v4C2Row27_spec :
    padOne 70 (mulRow CData V4C1Data 27) =
      (rectangularize 48 70 V4C2Data).getD 27 [] := by
  decide

private theorem v4C2Row28_spec :
    padOne 70 (mulRow CData V4C1Data 28) =
      (rectangularize 48 70 V4C2Data).getD 28 [] := by
  decide

private theorem v4C2Row29_spec :
    padOne 70 (mulRow CData V4C1Data 29) =
      (rectangularize 48 70 V4C2Data).getD 29 [] := by
  decide

private theorem v4C2Row30_spec :
    padOne 70 (mulRow CData V4C1Data 30) =
      (rectangularize 48 70 V4C2Data).getD 30 [] := by
  decide

private theorem v4C2Row31_spec :
    padOne 70 (mulRow CData V4C1Data 31) =
      (rectangularize 48 70 V4C2Data).getD 31 [] := by
  decide

private theorem v4C2Row32_spec :
    padOne 70 (mulRow CData V4C1Data 32) =
      (rectangularize 48 70 V4C2Data).getD 32 [] := by
  decide

private theorem v4C2Row33_spec :
    padOne 70 (mulRow CData V4C1Data 33) =
      (rectangularize 48 70 V4C2Data).getD 33 [] := by
  decide

private theorem v4C2Row34_spec :
    padOne 70 (mulRow CData V4C1Data 34) =
      (rectangularize 48 70 V4C2Data).getD 34 [] := by
  decide

private theorem v4C2Row35_spec :
    padOne 70 (mulRow CData V4C1Data 35) =
      (rectangularize 48 70 V4C2Data).getD 35 [] := by
  decide

private theorem v4C2Row36_spec :
    padOne 70 (mulRow CData V4C1Data 36) =
      (rectangularize 48 70 V4C2Data).getD 36 [] := by
  decide

private theorem v4C2Row37_spec :
    padOne 70 (mulRow CData V4C1Data 37) =
      (rectangularize 48 70 V4C2Data).getD 37 [] := by
  decide

private theorem v4C2Row38_spec :
    padOne 70 (mulRow CData V4C1Data 38) =
      (rectangularize 48 70 V4C2Data).getD 38 [] := by
  decide

private theorem v4C2Row39_spec :
    padOne 70 (mulRow CData V4C1Data 39) =
      (rectangularize 48 70 V4C2Data).getD 39 [] := by
  decide

private theorem v4C2Row40_spec :
    padOne 70 (mulRow CData V4C1Data 40) =
      (rectangularize 48 70 V4C2Data).getD 40 [] := by
  decide

private theorem v4C2Row41_spec :
    padOne 70 (mulRow CData V4C1Data 41) =
      (rectangularize 48 70 V4C2Data).getD 41 [] := by
  decide

private theorem v4C2Row42_spec :
    padOne 70 (mulRow CData V4C1Data 42) =
      (rectangularize 48 70 V4C2Data).getD 42 [] := by
  decide

private theorem v4C2Row43_spec :
    padOne 70 (mulRow CData V4C1Data 43) =
      (rectangularize 48 70 V4C2Data).getD 43 [] := by
  decide

private theorem v4C2Row44_spec :
    padOne 70 (mulRow CData V4C1Data 44) =
      (rectangularize 48 70 V4C2Data).getD 44 [] := by
  decide

private theorem v4C2Row45_spec :
    padOne 70 (mulRow CData V4C1Data 45) =
      (rectangularize 48 70 V4C2Data).getD 45 [] := by
  decide

private theorem v4C2Row46_spec :
    padOne 70 (mulRow CData V4C1Data 46) =
      (rectangularize 48 70 V4C2Data).getD 46 [] := by
  decide

private theorem v4C2Row47_spec :
    padOne 70 (mulRow CData V4C1Data 47) =
      (rectangularize 48 70 V4C2Data).getD 47 [] := by
  decide

private theorem v4C2Rows_spec (n : ℕ) (hn : n < 48) :
    padOne 70 (mulRow CData V4C1Data n) =
      (rectangularize 48 70 V4C2Data).getD n [] := by
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
  · exact v4C2Row0_spec
  · exact v4C2Row1_spec
  · exact v4C2Row2_spec
  · exact v4C2Row3_spec
  · exact v4C2Row4_spec
  · exact v4C2Row5_spec
  · exact v4C2Row6_spec
  · exact v4C2Row7_spec
  · exact v4C2Row8_spec
  · exact v4C2Row9_spec
  · exact v4C2Row10_spec
  · exact v4C2Row11_spec
  · exact v4C2Row12_spec
  · exact v4C2Row13_spec
  · exact v4C2Row14_spec
  · exact v4C2Row15_spec
  · exact v4C2Row16_spec
  · exact v4C2Row17_spec
  · exact v4C2Row18_spec
  · exact v4C2Row19_spec
  · exact v4C2Row20_spec
  · exact v4C2Row21_spec
  · exact v4C2Row22_spec
  · exact v4C2Row23_spec
  · exact v4C2Row24_spec
  · exact v4C2Row25_spec
  · exact v4C2Row26_spec
  · exact v4C2Row27_spec
  · exact v4C2Row28_spec
  · exact v4C2Row29_spec
  · exact v4C2Row30_spec
  · exact v4C2Row31_spec
  · exact v4C2Row32_spec
  · exact v4C2Row33_spec
  · exact v4C2Row34_spec
  · exact v4C2Row35_spec
  · exact v4C2Row36_spec
  · exact v4C2Row37_spec
  · exact v4C2Row38_spec
  · exact v4C2Row39_spec
  · exact v4C2Row40_spec
  · exact v4C2Row41_spec
  · exact v4C2Row42_spec
  · exact v4C2Row43_spec
  · exact v4C2Row44_spec
  · exact v4C2Row45_spec
  · exact v4C2Row46_spec
  · exact v4C2Row47_spec

private theorem v4C2Left_length :
    (rectangularize 48 70 (Two.mul CData V4C1Data)).length = 48 := by
  decide

private theorem v4C2Right_length :
    (rectangularize 48 70 V4C2Data).length = 48 := by
  decide

-- Exact bidegree bound (47, 69); no row or column is discarded.
private theorem v4C2Data_spec :
    rectangularize 48 70 (Two.mul CData V4C1Data) =
      rectangularize 48 70 V4C2Data := by
  apply List.ext_getElem (v4C2Left_length.trans v4C2Right_length.symm)
  intro n hn _
  rw [List.getElem_eq_getD [], List.getElem_eq_getD []]
  rw [v4C2Left_length] at hn
  rw [getD_rectangularize 48 70 (Two.mul CData V4C1Data) n hn,
    ← mulRow_eq_getD]
  exact v4C2Rows_spec n hn

private theorem v4C3Row0_spec :
    padOne 71 (mulRow CData V4C2Data 0) =
      (rectangularize 49 71 V4C3Data).getD 0 [] := by
  decide

private theorem v4C3Row1_spec :
    padOne 71 (mulRow CData V4C2Data 1) =
      (rectangularize 49 71 V4C3Data).getD 1 [] := by
  decide

private theorem v4C3Row2_spec :
    padOne 71 (mulRow CData V4C2Data 2) =
      (rectangularize 49 71 V4C3Data).getD 2 [] := by
  decide

private theorem v4C3Row3_spec :
    padOne 71 (mulRow CData V4C2Data 3) =
      (rectangularize 49 71 V4C3Data).getD 3 [] := by
  decide

private theorem v4C3Row4_spec :
    padOne 71 (mulRow CData V4C2Data 4) =
      (rectangularize 49 71 V4C3Data).getD 4 [] := by
  decide

private theorem v4C3Row5_spec :
    padOne 71 (mulRow CData V4C2Data 5) =
      (rectangularize 49 71 V4C3Data).getD 5 [] := by
  decide

private theorem v4C3Row6_spec :
    padOne 71 (mulRow CData V4C2Data 6) =
      (rectangularize 49 71 V4C3Data).getD 6 [] := by
  decide

private theorem v4C3Row7_spec :
    padOne 71 (mulRow CData V4C2Data 7) =
      (rectangularize 49 71 V4C3Data).getD 7 [] := by
  decide

private theorem v4C3Row8_spec :
    padOne 71 (mulRow CData V4C2Data 8) =
      (rectangularize 49 71 V4C3Data).getD 8 [] := by
  decide

private theorem v4C3Row9_spec :
    padOne 71 (mulRow CData V4C2Data 9) =
      (rectangularize 49 71 V4C3Data).getD 9 [] := by
  decide

private theorem v4C3Row10_spec :
    padOne 71 (mulRow CData V4C2Data 10) =
      (rectangularize 49 71 V4C3Data).getD 10 [] := by
  decide

private theorem v4C3Row11_spec :
    padOne 71 (mulRow CData V4C2Data 11) =
      (rectangularize 49 71 V4C3Data).getD 11 [] := by
  decide

private theorem v4C3Row12_spec :
    padOne 71 (mulRow CData V4C2Data 12) =
      (rectangularize 49 71 V4C3Data).getD 12 [] := by
  decide

private theorem v4C3Row13_spec :
    padOne 71 (mulRow CData V4C2Data 13) =
      (rectangularize 49 71 V4C3Data).getD 13 [] := by
  decide

private theorem v4C3Row14_spec :
    padOne 71 (mulRow CData V4C2Data 14) =
      (rectangularize 49 71 V4C3Data).getD 14 [] := by
  decide

private theorem v4C3Row15_spec :
    padOne 71 (mulRow CData V4C2Data 15) =
      (rectangularize 49 71 V4C3Data).getD 15 [] := by
  decide

private theorem v4C3Row16_spec :
    padOne 71 (mulRow CData V4C2Data 16) =
      (rectangularize 49 71 V4C3Data).getD 16 [] := by
  decide

private theorem v4C3Row17_spec :
    padOne 71 (mulRow CData V4C2Data 17) =
      (rectangularize 49 71 V4C3Data).getD 17 [] := by
  decide

private theorem v4C3Row18_spec :
    padOne 71 (mulRow CData V4C2Data 18) =
      (rectangularize 49 71 V4C3Data).getD 18 [] := by
  decide

private theorem v4C3Row19_spec :
    padOne 71 (mulRow CData V4C2Data 19) =
      (rectangularize 49 71 V4C3Data).getD 19 [] := by
  decide

private theorem v4C3Row20_spec :
    padOne 71 (mulRow CData V4C2Data 20) =
      (rectangularize 49 71 V4C3Data).getD 20 [] := by
  decide

private theorem v4C3Row21_spec :
    padOne 71 (mulRow CData V4C2Data 21) =
      (rectangularize 49 71 V4C3Data).getD 21 [] := by
  decide

private theorem v4C3Row22_spec :
    padOne 71 (mulRow CData V4C2Data 22) =
      (rectangularize 49 71 V4C3Data).getD 22 [] := by
  decide

private theorem v4C3Row23_spec :
    padOne 71 (mulRow CData V4C2Data 23) =
      (rectangularize 49 71 V4C3Data).getD 23 [] := by
  decide

private theorem v4C3Row24_spec :
    padOne 71 (mulRow CData V4C2Data 24) =
      (rectangularize 49 71 V4C3Data).getD 24 [] := by
  decide

private theorem v4C3Row25_spec :
    padOne 71 (mulRow CData V4C2Data 25) =
      (rectangularize 49 71 V4C3Data).getD 25 [] := by
  decide

private theorem v4C3Row26_spec :
    padOne 71 (mulRow CData V4C2Data 26) =
      (rectangularize 49 71 V4C3Data).getD 26 [] := by
  decide

private theorem v4C3Row27_spec :
    padOne 71 (mulRow CData V4C2Data 27) =
      (rectangularize 49 71 V4C3Data).getD 27 [] := by
  decide

private theorem v4C3Row28_spec :
    padOne 71 (mulRow CData V4C2Data 28) =
      (rectangularize 49 71 V4C3Data).getD 28 [] := by
  decide

private theorem v4C3Row29_spec :
    padOne 71 (mulRow CData V4C2Data 29) =
      (rectangularize 49 71 V4C3Data).getD 29 [] := by
  decide

private theorem v4C3Row30Coeff0_spec :
    mulCoeffTwo CData V4C2Data 30 0 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 0 0 := by
  decide

private theorem v4C3Row30Coeff1_spec :
    mulCoeffTwo CData V4C2Data 30 1 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 1 0 := by
  decide

private theorem v4C3Row30Coeff2_spec :
    mulCoeffTwo CData V4C2Data 30 2 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 2 0 := by
  decide

private theorem v4C3Row30Coeff3_spec :
    mulCoeffTwo CData V4C2Data 30 3 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 3 0 := by
  decide

private theorem v4C3Row30Coeff4_spec :
    mulCoeffTwo CData V4C2Data 30 4 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 4 0 := by
  decide

private theorem v4C3Row30Coeff5_spec :
    mulCoeffTwo CData V4C2Data 30 5 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 5 0 := by
  decide

private theorem v4C3Row30Coeff6_spec :
    mulCoeffTwo CData V4C2Data 30 6 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 6 0 := by
  decide

private theorem v4C3Row30Coeff7_spec :
    mulCoeffTwo CData V4C2Data 30 7 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 7 0 := by
  decide

private theorem v4C3Row30Coeff8_spec :
    mulCoeffTwo CData V4C2Data 30 8 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 8 0 := by
  decide

private theorem v4C3Row30Coeff9_spec :
    mulCoeffTwo CData V4C2Data 30 9 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 9 0 := by
  decide

private theorem v4C3Row30Coeff10_spec :
    mulCoeffTwo CData V4C2Data 30 10 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 10 0 := by
  decide

private theorem v4C3Row30Coeff11_spec :
    mulCoeffTwo CData V4C2Data 30 11 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 11 0 := by
  decide

private theorem v4C3Row30Coeff12_spec :
    mulCoeffTwo CData V4C2Data 30 12 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 12 0 := by
  decide

private theorem v4C3Row30Coeff13_spec :
    mulCoeffTwo CData V4C2Data 30 13 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 13 0 := by
  decide

private theorem v4C3Row30Coeff14_spec :
    mulCoeffTwo CData V4C2Data 30 14 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 14 0 := by
  decide

private theorem v4C3Row30Coeff15_spec :
    mulCoeffTwo CData V4C2Data 30 15 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 15 0 := by
  decide

private theorem v4C3Row30Coeff16_spec :
    mulCoeffTwo CData V4C2Data 30 16 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 16 0 := by
  decide

private theorem v4C3Row30Coeff17_spec :
    mulCoeffTwo CData V4C2Data 30 17 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 17 0 := by
  decide

private theorem v4C3Row30Coeff18_spec :
    mulCoeffTwo CData V4C2Data 30 18 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 18 0 := by
  decide

private theorem v4C3Row30Coeff19_spec :
    mulCoeffTwo CData V4C2Data 30 19 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 19 0 := by
  decide

private theorem v4C3Row30Coeff20_spec :
    mulCoeffTwo CData V4C2Data 30 20 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 20 0 := by
  decide

private theorem v4C3Row30Coeff21_spec :
    mulCoeffTwo CData V4C2Data 30 21 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 21 0 := by
  decide

private theorem v4C3Row30Coeff22_spec :
    mulCoeffTwo CData V4C2Data 30 22 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 22 0 := by
  decide

private theorem v4C3Row30Coeff23_spec :
    mulCoeffTwo CData V4C2Data 30 23 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 23 0 := by
  decide

private theorem v4C3Row30Coeff24_spec :
    mulCoeffTwo CData V4C2Data 30 24 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 24 0 := by
  decide

private theorem v4C3Row30Coeff25_spec :
    mulCoeffTwo CData V4C2Data 30 25 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 25 0 := by
  decide

private theorem v4C3Row30Coeff26_spec :
    mulCoeffTwo CData V4C2Data 30 26 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 26 0 := by
  decide

private theorem v4C3Row30Coeff27_spec :
    mulCoeffTwo CData V4C2Data 30 27 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 27 0 := by
  decide

private theorem v4C3Row30Coeff28_spec :
    mulCoeffTwo CData V4C2Data 30 28 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 28 0 := by
  decide

private theorem v4C3Row30Coeff29_spec :
    mulCoeffTwo CData V4C2Data 30 29 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 29 0 := by
  decide

private theorem v4C3Row30Coeff30_spec :
    mulCoeffTwo CData V4C2Data 30 30 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 30 0 := by
  decide

private theorem v4C3Row30Coeff31_spec :
    mulCoeffTwo CData V4C2Data 30 31 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 31 0 := by
  decide

private theorem v4C3Row30Coeff32_spec :
    mulCoeffTwo CData V4C2Data 30 32 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 32 0 := by
  decide

private theorem v4C3Row30Coeff33_spec :
    mulCoeffTwo CData V4C2Data 30 33 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 33 0 := by
  decide

private theorem v4C3Row30Coeff34_spec :
    mulCoeffTwo CData V4C2Data 30 34 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 34 0 := by
  decide

private theorem v4C3Row30Coeff35_spec :
    mulCoeffTwo CData V4C2Data 30 35 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 35 0 := by
  decide

private theorem v4C3Row30Coeff36_spec :
    mulCoeffTwo CData V4C2Data 30 36 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 36 0 := by
  decide

private theorem v4C3Row30Coeff37_spec :
    mulCoeffTwo CData V4C2Data 30 37 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 37 0 := by
  decide

private theorem v4C3Row30Coeff38_spec :
    mulCoeffTwo CData V4C2Data 30 38 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 38 0 := by
  decide

private theorem v4C3Row30Coeff39_spec :
    mulCoeffTwo CData V4C2Data 30 39 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 39 0 := by
  decide

private theorem v4C3Row30Coeff40_spec :
    mulCoeffTwo CData V4C2Data 30 40 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 40 0 := by
  decide

private theorem v4C3Row30Coeff41_spec :
    mulCoeffTwo CData V4C2Data 30 41 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 41 0 := by
  decide

private theorem v4C3Row30Coeff42_spec :
    mulCoeffTwo CData V4C2Data 30 42 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 42 0 := by
  decide

private theorem v4C3Row30Coeff43_spec :
    mulCoeffTwo CData V4C2Data 30 43 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 43 0 := by
  decide

private theorem v4C3Row30Coeff44_spec :
    mulCoeffTwo CData V4C2Data 30 44 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 44 0 := by
  decide

private theorem v4C3Row30Coeff45_spec :
    mulCoeffTwo CData V4C2Data 30 45 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 45 0 := by
  decide

private theorem v4C3Row30Coeff46_spec :
    mulCoeffTwo CData V4C2Data 30 46 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 46 0 := by
  decide

private theorem v4C3Row30Coeff47_spec :
    mulCoeffTwo CData V4C2Data 30 47 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 47 0 := by
  decide

private theorem v4C3Row30Coeff48_spec :
    mulCoeffTwo CData V4C2Data 30 48 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 48 0 := by
  decide

private theorem v4C3Row30Coeff49_spec :
    mulCoeffTwo CData V4C2Data 30 49 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 49 0 := by
  decide

private theorem v4C3Row30Coeff50_spec :
    mulCoeffTwo CData V4C2Data 30 50 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 50 0 := by
  decide

private theorem v4C3Row30Coeff51_spec :
    mulCoeffTwo CData V4C2Data 30 51 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 51 0 := by
  decide

private theorem v4C3Row30Coeff52_spec :
    mulCoeffTwo CData V4C2Data 30 52 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 52 0 := by
  decide

private theorem v4C3Row30Coeff53_spec :
    mulCoeffTwo CData V4C2Data 30 53 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 53 0 := by
  decide

private theorem v4C3Row30Coeff54_spec :
    mulCoeffTwo CData V4C2Data 30 54 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 54 0 := by
  decide

private theorem v4C3Row30Coeff55_spec :
    mulCoeffTwo CData V4C2Data 30 55 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 55 0 := by
  decide

private theorem v4C3Row30Coeff56_spec :
    mulCoeffTwo CData V4C2Data 30 56 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 56 0 := by
  decide

private theorem v4C3Row30Coeff57_spec :
    mulCoeffTwo CData V4C2Data 30 57 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 57 0 := by
  decide

private theorem v4C3Row30Coeff58_spec :
    mulCoeffTwo CData V4C2Data 30 58 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 58 0 := by
  decide

private theorem v4C3Row30Coeff59_spec :
    mulCoeffTwo CData V4C2Data 30 59 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 59 0 := by
  decide

private theorem v4C3Row30Coeff60_spec :
    mulCoeffTwo CData V4C2Data 30 60 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 60 0 := by
  decide

private theorem v4C3Row30Coeff61_spec :
    mulCoeffTwo CData V4C2Data 30 61 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 61 0 := by
  decide

private theorem v4C3Row30Coeff62_spec :
    mulCoeffTwo CData V4C2Data 30 62 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 62 0 := by
  decide

private theorem v4C3Row30Coeff63_spec :
    mulCoeffTwo CData V4C2Data 30 63 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 63 0 := by
  decide

private theorem v4C3Row30Coeff64_spec :
    mulCoeffTwo CData V4C2Data 30 64 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 64 0 := by
  decide

private theorem v4C3Row30Coeff65_spec :
    mulCoeffTwo CData V4C2Data 30 65 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 65 0 := by
  decide

private theorem v4C3Row30Coeff66_spec :
    mulCoeffTwo CData V4C2Data 30 66 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 66 0 := by
  decide

private theorem v4C3Row30Coeff67_spec :
    mulCoeffTwo CData V4C2Data 30 67 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 67 0 := by
  decide

private theorem v4C3Row30Coeff68_spec :
    mulCoeffTwo CData V4C2Data 30 68 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 68 0 := by
  decide

private theorem v4C3Row30Coeff69_spec :
    mulCoeffTwo CData V4C2Data 30 69 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 69 0 := by
  decide

private theorem v4C3Row30Coeff70_spec :
    mulCoeffTwo CData V4C2Data 30 70 =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD 70 0 := by
  decide

private theorem v4C3Row30Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo CData V4C2Data 30 j =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4C3Row30Coeff0_spec
  · exact v4C3Row30Coeff1_spec
  · exact v4C3Row30Coeff2_spec
  · exact v4C3Row30Coeff3_spec
  · exact v4C3Row30Coeff4_spec
  · exact v4C3Row30Coeff5_spec
  · exact v4C3Row30Coeff6_spec
  · exact v4C3Row30Coeff7_spec
  · exact v4C3Row30Coeff8_spec
  · exact v4C3Row30Coeff9_spec

private theorem v4C3Row30Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo CData V4C2Data 30 j =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4C3Row30Coeff10_spec
  · exact v4C3Row30Coeff11_spec
  · exact v4C3Row30Coeff12_spec
  · exact v4C3Row30Coeff13_spec
  · exact v4C3Row30Coeff14_spec
  · exact v4C3Row30Coeff15_spec
  · exact v4C3Row30Coeff16_spec
  · exact v4C3Row30Coeff17_spec
  · exact v4C3Row30Coeff18_spec
  · exact v4C3Row30Coeff19_spec

private theorem v4C3Row30Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo CData V4C2Data 30 j =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4C3Row30Coeff20_spec
  · exact v4C3Row30Coeff21_spec
  · exact v4C3Row30Coeff22_spec
  · exact v4C3Row30Coeff23_spec
  · exact v4C3Row30Coeff24_spec
  · exact v4C3Row30Coeff25_spec
  · exact v4C3Row30Coeff26_spec
  · exact v4C3Row30Coeff27_spec
  · exact v4C3Row30Coeff28_spec
  · exact v4C3Row30Coeff29_spec

private theorem v4C3Row30Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo CData V4C2Data 30 j =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4C3Row30Coeff30_spec
  · exact v4C3Row30Coeff31_spec
  · exact v4C3Row30Coeff32_spec
  · exact v4C3Row30Coeff33_spec
  · exact v4C3Row30Coeff34_spec
  · exact v4C3Row30Coeff35_spec
  · exact v4C3Row30Coeff36_spec
  · exact v4C3Row30Coeff37_spec
  · exact v4C3Row30Coeff38_spec
  · exact v4C3Row30Coeff39_spec

private theorem v4C3Row30Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo CData V4C2Data 30 j =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4C3Row30Coeff40_spec
  · exact v4C3Row30Coeff41_spec
  · exact v4C3Row30Coeff42_spec
  · exact v4C3Row30Coeff43_spec
  · exact v4C3Row30Coeff44_spec
  · exact v4C3Row30Coeff45_spec
  · exact v4C3Row30Coeff46_spec
  · exact v4C3Row30Coeff47_spec
  · exact v4C3Row30Coeff48_spec
  · exact v4C3Row30Coeff49_spec

private theorem v4C3Row30Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo CData V4C2Data 30 j =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4C3Row30Coeff50_spec
  · exact v4C3Row30Coeff51_spec
  · exact v4C3Row30Coeff52_spec
  · exact v4C3Row30Coeff53_spec
  · exact v4C3Row30Coeff54_spec
  · exact v4C3Row30Coeff55_spec
  · exact v4C3Row30Coeff56_spec
  · exact v4C3Row30Coeff57_spec
  · exact v4C3Row30Coeff58_spec
  · exact v4C3Row30Coeff59_spec

private theorem v4C3Row30Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo CData V4C2Data 30 j =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4C3Row30Coeff60_spec
  · exact v4C3Row30Coeff61_spec
  · exact v4C3Row30Coeff62_spec
  · exact v4C3Row30Coeff63_spec
  · exact v4C3Row30Coeff64_spec
  · exact v4C3Row30Coeff65_spec
  · exact v4C3Row30Coeff66_spec
  · exact v4C3Row30Coeff67_spec
  · exact v4C3Row30Coeff68_spec
  · exact v4C3Row30Coeff69_spec

private theorem v4C3Row30Coeffs70To70_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 71) :
    mulCoeffTwo CData V4C2Data 30 j =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD j 0 := by
  have hCases :
    j = 70 := by
    omega
  rcases hCases with
    rfl
  · exact v4C3Row30Coeff70_spec

private theorem v4C3Row30_coefficients (j : ℕ) (hj : j < 71) :
    mulCoeffTwo CData V4C2Data 30 j =
      ((rectangularize 49 71 V4C3Data).getD 30 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4C3Row30Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4C3Row30Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4C3Row30Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4C3Row30Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4C3Row30Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4C3Row30Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4C3Row30Coeffs60To69_spec j (by omega) h70
  exact v4C3Row30Coeffs70To70_spec j (by omega) hj

private theorem v4C3Row30_spec :
    padOne 71 (mulRow CData V4C2Data 30) =
      (rectangularize 49 71 V4C3Data).getD 30 [] := by
  apply padOne_mulRow_eq_of_coefficients 71 CData V4C2Data 30
    ((rectangularize 49 71 V4C3Data).getD 30 [])
  · decide
  · have hTargetSupport : (V4C3Data.getD 30 []).length ≤ 71 := by
      decide
    rw [getD_rectangularize 49 71 V4C3Data 30 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4C3Row30_coefficients

private theorem v4C3Row31_spec :
    padOne 71 (mulRow CData V4C2Data 31) =
      (rectangularize 49 71 V4C3Data).getD 31 [] := by
  decide

private theorem v4C3Row32_spec :
    padOne 71 (mulRow CData V4C2Data 32) =
      (rectangularize 49 71 V4C3Data).getD 32 [] := by
  decide

private theorem v4C3Row33_spec :
    padOne 71 (mulRow CData V4C2Data 33) =
      (rectangularize 49 71 V4C3Data).getD 33 [] := by
  decide

private theorem v4C3Row34_spec :
    padOne 71 (mulRow CData V4C2Data 34) =
      (rectangularize 49 71 V4C3Data).getD 34 [] := by
  decide

private theorem v4C3Row35_spec :
    padOne 71 (mulRow CData V4C2Data 35) =
      (rectangularize 49 71 V4C3Data).getD 35 [] := by
  decide

private theorem v4C3Row36_spec :
    padOne 71 (mulRow CData V4C2Data 36) =
      (rectangularize 49 71 V4C3Data).getD 36 [] := by
  decide

private theorem v4C3Row37_spec :
    padOne 71 (mulRow CData V4C2Data 37) =
      (rectangularize 49 71 V4C3Data).getD 37 [] := by
  decide

private theorem v4C3Row38_spec :
    padOne 71 (mulRow CData V4C2Data 38) =
      (rectangularize 49 71 V4C3Data).getD 38 [] := by
  decide

private theorem v4C3Row39_spec :
    padOne 71 (mulRow CData V4C2Data 39) =
      (rectangularize 49 71 V4C3Data).getD 39 [] := by
  decide

private theorem v4C3Row40_spec :
    padOne 71 (mulRow CData V4C2Data 40) =
      (rectangularize 49 71 V4C3Data).getD 40 [] := by
  decide

private theorem v4C3Row41_spec :
    padOne 71 (mulRow CData V4C2Data 41) =
      (rectangularize 49 71 V4C3Data).getD 41 [] := by
  decide

private theorem v4C3Row42_spec :
    padOne 71 (mulRow CData V4C2Data 42) =
      (rectangularize 49 71 V4C3Data).getD 42 [] := by
  decide

private theorem v4C3Row43_spec :
    padOne 71 (mulRow CData V4C2Data 43) =
      (rectangularize 49 71 V4C3Data).getD 43 [] := by
  decide

private theorem v4C3Row44_spec :
    padOne 71 (mulRow CData V4C2Data 44) =
      (rectangularize 49 71 V4C3Data).getD 44 [] := by
  decide

private theorem v4C3Row45_spec :
    padOne 71 (mulRow CData V4C2Data 45) =
      (rectangularize 49 71 V4C3Data).getD 45 [] := by
  decide

private theorem v4C3Row46_spec :
    padOne 71 (mulRow CData V4C2Data 46) =
      (rectangularize 49 71 V4C3Data).getD 46 [] := by
  decide

private theorem v4C3Row47_spec :
    padOne 71 (mulRow CData V4C2Data 47) =
      (rectangularize 49 71 V4C3Data).getD 47 [] := by
  decide

private theorem v4C3Row48_spec :
    padOne 71 (mulRow CData V4C2Data 48) =
      (rectangularize 49 71 V4C3Data).getD 48 [] := by
  decide

private theorem v4C3Rows_spec (n : ℕ) (hn : n < 49) :
    padOne 71 (mulRow CData V4C2Data n) =
      (rectangularize 49 71 V4C3Data).getD n [] := by
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
  · exact v4C3Row0_spec
  · exact v4C3Row1_spec
  · exact v4C3Row2_spec
  · exact v4C3Row3_spec
  · exact v4C3Row4_spec
  · exact v4C3Row5_spec
  · exact v4C3Row6_spec
  · exact v4C3Row7_spec
  · exact v4C3Row8_spec
  · exact v4C3Row9_spec
  · exact v4C3Row10_spec
  · exact v4C3Row11_spec
  · exact v4C3Row12_spec
  · exact v4C3Row13_spec
  · exact v4C3Row14_spec
  · exact v4C3Row15_spec
  · exact v4C3Row16_spec
  · exact v4C3Row17_spec
  · exact v4C3Row18_spec
  · exact v4C3Row19_spec
  · exact v4C3Row20_spec
  · exact v4C3Row21_spec
  · exact v4C3Row22_spec
  · exact v4C3Row23_spec
  · exact v4C3Row24_spec
  · exact v4C3Row25_spec
  · exact v4C3Row26_spec
  · exact v4C3Row27_spec
  · exact v4C3Row28_spec
  · exact v4C3Row29_spec
  · exact v4C3Row30_spec
  · exact v4C3Row31_spec
  · exact v4C3Row32_spec
  · exact v4C3Row33_spec
  · exact v4C3Row34_spec
  · exact v4C3Row35_spec
  · exact v4C3Row36_spec
  · exact v4C3Row37_spec
  · exact v4C3Row38_spec
  · exact v4C3Row39_spec
  · exact v4C3Row40_spec
  · exact v4C3Row41_spec
  · exact v4C3Row42_spec
  · exact v4C3Row43_spec
  · exact v4C3Row44_spec
  · exact v4C3Row45_spec
  · exact v4C3Row46_spec
  · exact v4C3Row47_spec
  · exact v4C3Row48_spec

private theorem v4C3Left_length :
    (rectangularize 49 71 (Two.mul CData V4C2Data)).length = 49 := by
  decide

private theorem v4C3Right_length :
    (rectangularize 49 71 V4C3Data).length = 49 := by
  decide

-- Exact bidegree bound (48, 70); no row or column is discarded.
private theorem v4C3Data_spec :
    rectangularize 49 71 (Two.mul CData V4C2Data) =
      rectangularize 49 71 V4C3Data := by
  apply List.ext_getElem (v4C3Left_length.trans v4C3Right_length.symm)
  intro n hn _
  rw [List.getElem_eq_getD [], List.getElem_eq_getD []]
  rw [v4C3Left_length] at hn
  rw [getD_rectangularize 49 71 (Two.mul CData V4C2Data) n hn,
    ← mulRow_eq_getD]
  exact v4C3Rows_spec n hn

private theorem v4JRow0_spec :
    padOne 76 (mulRow JData V4C3Data 0) =
      (rectangularize 52 76 V4JData).getD 0 [] := by
  decide

private theorem v4JRow1_spec :
    padOne 76 (mulRow JData V4C3Data 1) =
      (rectangularize 52 76 V4JData).getD 1 [] := by
  decide

private theorem v4JRow2_spec :
    padOne 76 (mulRow JData V4C3Data 2) =
      (rectangularize 52 76 V4JData).getD 2 [] := by
  decide

private theorem v4JRow3_spec :
    padOne 76 (mulRow JData V4C3Data 3) =
      (rectangularize 52 76 V4JData).getD 3 [] := by
  decide

private theorem v4JRow4_spec :
    padOne 76 (mulRow JData V4C3Data 4) =
      (rectangularize 52 76 V4JData).getD 4 [] := by
  decide

private theorem v4JRow5_spec :
    padOne 76 (mulRow JData V4C3Data 5) =
      (rectangularize 52 76 V4JData).getD 5 [] := by
  decide

private theorem v4JRow6_spec :
    padOne 76 (mulRow JData V4C3Data 6) =
      (rectangularize 52 76 V4JData).getD 6 [] := by
  decide

private theorem v4JRow7_spec :
    padOne 76 (mulRow JData V4C3Data 7) =
      (rectangularize 52 76 V4JData).getD 7 [] := by
  decide

private theorem v4JRow8_spec :
    padOne 76 (mulRow JData V4C3Data 8) =
      (rectangularize 52 76 V4JData).getD 8 [] := by
  decide

private theorem v4JRow9_spec :
    padOne 76 (mulRow JData V4C3Data 9) =
      (rectangularize 52 76 V4JData).getD 9 [] := by
  decide

private theorem v4JRow10_spec :
    padOne 76 (mulRow JData V4C3Data 10) =
      (rectangularize 52 76 V4JData).getD 10 [] := by
  decide

private theorem v4JRow11_spec :
    padOne 76 (mulRow JData V4C3Data 11) =
      (rectangularize 52 76 V4JData).getD 11 [] := by
  decide

private theorem v4JRow12_spec :
    padOne 76 (mulRow JData V4C3Data 12) =
      (rectangularize 52 76 V4JData).getD 12 [] := by
  decide

private theorem v4JRow13_spec :
    padOne 76 (mulRow JData V4C3Data 13) =
      (rectangularize 52 76 V4JData).getD 13 [] := by
  decide

private theorem v4JRow14_spec :
    padOne 76 (mulRow JData V4C3Data 14) =
      (rectangularize 52 76 V4JData).getD 14 [] := by
  decide

private theorem v4JRow15_spec :
    padOne 76 (mulRow JData V4C3Data 15) =
      (rectangularize 52 76 V4JData).getD 15 [] := by
  decide

private theorem v4JRow16_spec :
    padOne 76 (mulRow JData V4C3Data 16) =
      (rectangularize 52 76 V4JData).getD 16 [] := by
  decide

private theorem v4JRow17Coeff0_spec :
    mulCoeffTwo JData V4C3Data 17 0 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 0 0 := by
  decide

private theorem v4JRow17Coeff1_spec :
    mulCoeffTwo JData V4C3Data 17 1 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 1 0 := by
  decide

private theorem v4JRow17Coeff2_spec :
    mulCoeffTwo JData V4C3Data 17 2 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 2 0 := by
  decide

private theorem v4JRow17Coeff3_spec :
    mulCoeffTwo JData V4C3Data 17 3 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 3 0 := by
  decide

private theorem v4JRow17Coeff4_spec :
    mulCoeffTwo JData V4C3Data 17 4 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 4 0 := by
  decide

private theorem v4JRow17Coeff5_spec :
    mulCoeffTwo JData V4C3Data 17 5 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 5 0 := by
  decide

private theorem v4JRow17Coeff6_spec :
    mulCoeffTwo JData V4C3Data 17 6 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 6 0 := by
  decide

private theorem v4JRow17Coeff7_spec :
    mulCoeffTwo JData V4C3Data 17 7 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 7 0 := by
  decide

private theorem v4JRow17Coeff8_spec :
    mulCoeffTwo JData V4C3Data 17 8 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 8 0 := by
  decide

private theorem v4JRow17Coeff9_spec :
    mulCoeffTwo JData V4C3Data 17 9 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 9 0 := by
  decide

private theorem v4JRow17Coeff10_spec :
    mulCoeffTwo JData V4C3Data 17 10 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 10 0 := by
  decide

private theorem v4JRow17Coeff11_spec :
    mulCoeffTwo JData V4C3Data 17 11 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 11 0 := by
  decide

private theorem v4JRow17Coeff12_spec :
    mulCoeffTwo JData V4C3Data 17 12 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 12 0 := by
  decide

private theorem v4JRow17Coeff13_spec :
    mulCoeffTwo JData V4C3Data 17 13 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 13 0 := by
  decide

private theorem v4JRow17Coeff14_spec :
    mulCoeffTwo JData V4C3Data 17 14 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 14 0 := by
  decide

private theorem v4JRow17Coeff15_spec :
    mulCoeffTwo JData V4C3Data 17 15 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 15 0 := by
  decide

private theorem v4JRow17Coeff16_spec :
    mulCoeffTwo JData V4C3Data 17 16 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 16 0 := by
  decide

private theorem v4JRow17Coeff17_spec :
    mulCoeffTwo JData V4C3Data 17 17 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 17 0 := by
  decide

private theorem v4JRow17Coeff18_spec :
    mulCoeffTwo JData V4C3Data 17 18 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 18 0 := by
  decide

private theorem v4JRow17Coeff19_spec :
    mulCoeffTwo JData V4C3Data 17 19 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 19 0 := by
  decide

private theorem v4JRow17Coeff20_spec :
    mulCoeffTwo JData V4C3Data 17 20 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 20 0 := by
  decide

private theorem v4JRow17Coeff21_spec :
    mulCoeffTwo JData V4C3Data 17 21 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 21 0 := by
  decide

private theorem v4JRow17Coeff22_spec :
    mulCoeffTwo JData V4C3Data 17 22 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 22 0 := by
  decide

private theorem v4JRow17Coeff23_spec :
    mulCoeffTwo JData V4C3Data 17 23 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 23 0 := by
  decide

private theorem v4JRow17Coeff24_spec :
    mulCoeffTwo JData V4C3Data 17 24 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 24 0 := by
  decide

private theorem v4JRow17Coeff25_spec :
    mulCoeffTwo JData V4C3Data 17 25 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 25 0 := by
  decide

private theorem v4JRow17Coeff26_spec :
    mulCoeffTwo JData V4C3Data 17 26 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 26 0 := by
  decide

private theorem v4JRow17Coeff27_spec :
    mulCoeffTwo JData V4C3Data 17 27 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 27 0 := by
  decide

private theorem v4JRow17Coeff28_spec :
    mulCoeffTwo JData V4C3Data 17 28 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 28 0 := by
  decide

private theorem v4JRow17Coeff29_spec :
    mulCoeffTwo JData V4C3Data 17 29 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 29 0 := by
  decide

private theorem v4JRow17Coeff30_spec :
    mulCoeffTwo JData V4C3Data 17 30 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 30 0 := by
  decide

private theorem v4JRow17Coeff31_spec :
    mulCoeffTwo JData V4C3Data 17 31 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 31 0 := by
  decide

private theorem v4JRow17Coeff32_spec :
    mulCoeffTwo JData V4C3Data 17 32 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 32 0 := by
  decide

private theorem v4JRow17Coeff33_spec :
    mulCoeffTwo JData V4C3Data 17 33 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 33 0 := by
  decide

private theorem v4JRow17Coeff34_spec :
    mulCoeffTwo JData V4C3Data 17 34 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 34 0 := by
  decide

private theorem v4JRow17Coeff35_spec :
    mulCoeffTwo JData V4C3Data 17 35 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 35 0 := by
  decide

private theorem v4JRow17Coeff36_spec :
    mulCoeffTwo JData V4C3Data 17 36 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 36 0 := by
  decide

private theorem v4JRow17Coeff37_spec :
    mulCoeffTwo JData V4C3Data 17 37 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 37 0 := by
  decide

private theorem v4JRow17Coeff38_spec :
    mulCoeffTwo JData V4C3Data 17 38 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 38 0 := by
  decide

private theorem v4JRow17Coeff39_spec :
    mulCoeffTwo JData V4C3Data 17 39 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 39 0 := by
  decide

private theorem v4JRow17Coeff40_spec :
    mulCoeffTwo JData V4C3Data 17 40 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 40 0 := by
  decide

private theorem v4JRow17Coeff41_spec :
    mulCoeffTwo JData V4C3Data 17 41 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 41 0 := by
  decide

private theorem v4JRow17Coeff42_spec :
    mulCoeffTwo JData V4C3Data 17 42 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 42 0 := by
  decide

private theorem v4JRow17Coeff43_spec :
    mulCoeffTwo JData V4C3Data 17 43 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 43 0 := by
  decide

private theorem v4JRow17Coeff44_spec :
    mulCoeffTwo JData V4C3Data 17 44 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 44 0 := by
  decide

private theorem v4JRow17Coeff45_spec :
    mulCoeffTwo JData V4C3Data 17 45 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 45 0 := by
  decide

private theorem v4JRow17Coeff46_spec :
    mulCoeffTwo JData V4C3Data 17 46 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 46 0 := by
  decide

private theorem v4JRow17Coeff47_spec :
    mulCoeffTwo JData V4C3Data 17 47 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 47 0 := by
  decide

private theorem v4JRow17Coeff48_spec :
    mulCoeffTwo JData V4C3Data 17 48 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 48 0 := by
  decide

private theorem v4JRow17Coeff49_spec :
    mulCoeffTwo JData V4C3Data 17 49 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 49 0 := by
  decide

private theorem v4JRow17Coeff50_spec :
    mulCoeffTwo JData V4C3Data 17 50 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 50 0 := by
  decide

private theorem v4JRow17Coeff51_spec :
    mulCoeffTwo JData V4C3Data 17 51 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 51 0 := by
  decide

private theorem v4JRow17Coeff52_spec :
    mulCoeffTwo JData V4C3Data 17 52 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 52 0 := by
  decide

private theorem v4JRow17Coeff53_spec :
    mulCoeffTwo JData V4C3Data 17 53 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 53 0 := by
  decide

private theorem v4JRow17Coeff54_spec :
    mulCoeffTwo JData V4C3Data 17 54 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 54 0 := by
  decide

private theorem v4JRow17Coeff55_spec :
    mulCoeffTwo JData V4C3Data 17 55 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 55 0 := by
  decide

private theorem v4JRow17Coeff56_spec :
    mulCoeffTwo JData V4C3Data 17 56 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 56 0 := by
  decide

private theorem v4JRow17Coeff57_spec :
    mulCoeffTwo JData V4C3Data 17 57 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 57 0 := by
  decide

private theorem v4JRow17Coeff58_spec :
    mulCoeffTwo JData V4C3Data 17 58 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 58 0 := by
  decide

private theorem v4JRow17Coeff59_spec :
    mulCoeffTwo JData V4C3Data 17 59 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 59 0 := by
  decide

private theorem v4JRow17Coeff60_spec :
    mulCoeffTwo JData V4C3Data 17 60 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 60 0 := by
  decide

private theorem v4JRow17Coeff61_spec :
    mulCoeffTwo JData V4C3Data 17 61 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 61 0 := by
  decide

private theorem v4JRow17Coeff62_spec :
    mulCoeffTwo JData V4C3Data 17 62 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 62 0 := by
  decide

private theorem v4JRow17Coeff63_spec :
    mulCoeffTwo JData V4C3Data 17 63 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 63 0 := by
  decide

private theorem v4JRow17Coeff64_spec :
    mulCoeffTwo JData V4C3Data 17 64 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 64 0 := by
  decide

private theorem v4JRow17Coeff65_spec :
    mulCoeffTwo JData V4C3Data 17 65 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 65 0 := by
  decide

private theorem v4JRow17Coeff66_spec :
    mulCoeffTwo JData V4C3Data 17 66 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 66 0 := by
  decide

private theorem v4JRow17Coeff67_spec :
    mulCoeffTwo JData V4C3Data 17 67 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 67 0 := by
  decide

private theorem v4JRow17Coeff68_spec :
    mulCoeffTwo JData V4C3Data 17 68 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 68 0 := by
  decide

private theorem v4JRow17Coeff69_spec :
    mulCoeffTwo JData V4C3Data 17 69 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 69 0 := by
  decide

private theorem v4JRow17Coeff70_spec :
    mulCoeffTwo JData V4C3Data 17 70 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 70 0 := by
  decide

private theorem v4JRow17Coeff71_spec :
    mulCoeffTwo JData V4C3Data 17 71 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 71 0 := by
  decide

private theorem v4JRow17Coeff72_spec :
    mulCoeffTwo JData V4C3Data 17 72 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 72 0 := by
  decide

private theorem v4JRow17Coeff73_spec :
    mulCoeffTwo JData V4C3Data 17 73 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 73 0 := by
  decide

private theorem v4JRow17Coeff74_spec :
    mulCoeffTwo JData V4C3Data 17 74 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 74 0 := by
  decide

private theorem v4JRow17Coeff75_spec :
    mulCoeffTwo JData V4C3Data 17 75 =
      ((rectangularize 52 76 V4JData).getD 17 []).getD 75 0 := by
  decide

private theorem v4JRow17Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo JData V4C3Data 17 j =
      ((rectangularize 52 76 V4JData).getD 17 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow17Coeff0_spec
  · exact v4JRow17Coeff1_spec
  · exact v4JRow17Coeff2_spec
  · exact v4JRow17Coeff3_spec
  · exact v4JRow17Coeff4_spec
  · exact v4JRow17Coeff5_spec
  · exact v4JRow17Coeff6_spec
  · exact v4JRow17Coeff7_spec
  · exact v4JRow17Coeff8_spec
  · exact v4JRow17Coeff9_spec

private theorem v4JRow17Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo JData V4C3Data 17 j =
      ((rectangularize 52 76 V4JData).getD 17 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow17Coeff10_spec
  · exact v4JRow17Coeff11_spec
  · exact v4JRow17Coeff12_spec
  · exact v4JRow17Coeff13_spec
  · exact v4JRow17Coeff14_spec
  · exact v4JRow17Coeff15_spec
  · exact v4JRow17Coeff16_spec
  · exact v4JRow17Coeff17_spec
  · exact v4JRow17Coeff18_spec
  · exact v4JRow17Coeff19_spec

private theorem v4JRow17Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo JData V4C3Data 17 j =
      ((rectangularize 52 76 V4JData).getD 17 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow17Coeff20_spec
  · exact v4JRow17Coeff21_spec
  · exact v4JRow17Coeff22_spec
  · exact v4JRow17Coeff23_spec
  · exact v4JRow17Coeff24_spec
  · exact v4JRow17Coeff25_spec
  · exact v4JRow17Coeff26_spec
  · exact v4JRow17Coeff27_spec
  · exact v4JRow17Coeff28_spec
  · exact v4JRow17Coeff29_spec

private theorem v4JRow17Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo JData V4C3Data 17 j =
      ((rectangularize 52 76 V4JData).getD 17 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow17Coeff30_spec
  · exact v4JRow17Coeff31_spec
  · exact v4JRow17Coeff32_spec
  · exact v4JRow17Coeff33_spec
  · exact v4JRow17Coeff34_spec
  · exact v4JRow17Coeff35_spec
  · exact v4JRow17Coeff36_spec
  · exact v4JRow17Coeff37_spec
  · exact v4JRow17Coeff38_spec
  · exact v4JRow17Coeff39_spec

private theorem v4JRow17Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo JData V4C3Data 17 j =
      ((rectangularize 52 76 V4JData).getD 17 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow17Coeff40_spec
  · exact v4JRow17Coeff41_spec
  · exact v4JRow17Coeff42_spec
  · exact v4JRow17Coeff43_spec
  · exact v4JRow17Coeff44_spec
  · exact v4JRow17Coeff45_spec
  · exact v4JRow17Coeff46_spec
  · exact v4JRow17Coeff47_spec
  · exact v4JRow17Coeff48_spec
  · exact v4JRow17Coeff49_spec

private theorem v4JRow17Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo JData V4C3Data 17 j =
      ((rectangularize 52 76 V4JData).getD 17 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow17Coeff50_spec
  · exact v4JRow17Coeff51_spec
  · exact v4JRow17Coeff52_spec
  · exact v4JRow17Coeff53_spec
  · exact v4JRow17Coeff54_spec
  · exact v4JRow17Coeff55_spec
  · exact v4JRow17Coeff56_spec
  · exact v4JRow17Coeff57_spec
  · exact v4JRow17Coeff58_spec
  · exact v4JRow17Coeff59_spec

private theorem v4JRow17Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo JData V4C3Data 17 j =
      ((rectangularize 52 76 V4JData).getD 17 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow17Coeff60_spec
  · exact v4JRow17Coeff61_spec
  · exact v4JRow17Coeff62_spec
  · exact v4JRow17Coeff63_spec
  · exact v4JRow17Coeff64_spec
  · exact v4JRow17Coeff65_spec
  · exact v4JRow17Coeff66_spec
  · exact v4JRow17Coeff67_spec
  · exact v4JRow17Coeff68_spec
  · exact v4JRow17Coeff69_spec

private theorem v4JRow17Coeffs70To75_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 76) :
    mulCoeffTwo JData V4C3Data 17 j =
      ((rectangularize 52 76 V4JData).getD 17 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact v4JRow17Coeff70_spec
  · exact v4JRow17Coeff71_spec
  · exact v4JRow17Coeff72_spec
  · exact v4JRow17Coeff73_spec
  · exact v4JRow17Coeff74_spec
  · exact v4JRow17Coeff75_spec

private theorem v4JRow17_coefficients (j : ℕ) (hj : j < 76) :
    mulCoeffTwo JData V4C3Data 17 j =
      ((rectangularize 52 76 V4JData).getD 17 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4JRow17Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4JRow17Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4JRow17Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4JRow17Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4JRow17Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4JRow17Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4JRow17Coeffs60To69_spec j (by omega) h70
  exact v4JRow17Coeffs70To75_spec j (by omega) hj

private theorem v4JRow17_spec :
    padOne 76 (mulRow JData V4C3Data 17) =
      (rectangularize 52 76 V4JData).getD 17 [] := by
  apply padOne_mulRow_eq_of_coefficients 76 JData V4C3Data 17
    ((rectangularize 52 76 V4JData).getD 17 [])
  · decide
  · have hTargetSupport : (V4JData.getD 17 []).length ≤ 76 := by
      decide
    rw [getD_rectangularize 52 76 V4JData 17 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4JRow17_coefficients

private theorem v4JRow18Coeff0_spec :
    mulCoeffTwo JData V4C3Data 18 0 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 0 0 := by
  decide

private theorem v4JRow18Coeff1_spec :
    mulCoeffTwo JData V4C3Data 18 1 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 1 0 := by
  decide

private theorem v4JRow18Coeff2_spec :
    mulCoeffTwo JData V4C3Data 18 2 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 2 0 := by
  decide

private theorem v4JRow18Coeff3_spec :
    mulCoeffTwo JData V4C3Data 18 3 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 3 0 := by
  decide

private theorem v4JRow18Coeff4_spec :
    mulCoeffTwo JData V4C3Data 18 4 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 4 0 := by
  decide

private theorem v4JRow18Coeff5_spec :
    mulCoeffTwo JData V4C3Data 18 5 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 5 0 := by
  decide

private theorem v4JRow18Coeff6_spec :
    mulCoeffTwo JData V4C3Data 18 6 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 6 0 := by
  decide

private theorem v4JRow18Coeff7_spec :
    mulCoeffTwo JData V4C3Data 18 7 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 7 0 := by
  decide

private theorem v4JRow18Coeff8_spec :
    mulCoeffTwo JData V4C3Data 18 8 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 8 0 := by
  decide

private theorem v4JRow18Coeff9_spec :
    mulCoeffTwo JData V4C3Data 18 9 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 9 0 := by
  decide

private theorem v4JRow18Coeff10_spec :
    mulCoeffTwo JData V4C3Data 18 10 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 10 0 := by
  decide

private theorem v4JRow18Coeff11_spec :
    mulCoeffTwo JData V4C3Data 18 11 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 11 0 := by
  decide

private theorem v4JRow18Coeff12_spec :
    mulCoeffTwo JData V4C3Data 18 12 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 12 0 := by
  decide

private theorem v4JRow18Coeff13_spec :
    mulCoeffTwo JData V4C3Data 18 13 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 13 0 := by
  decide

private theorem v4JRow18Coeff14_spec :
    mulCoeffTwo JData V4C3Data 18 14 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 14 0 := by
  decide

private theorem v4JRow18Coeff15_spec :
    mulCoeffTwo JData V4C3Data 18 15 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 15 0 := by
  decide

private theorem v4JRow18Coeff16_spec :
    mulCoeffTwo JData V4C3Data 18 16 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 16 0 := by
  decide

private theorem v4JRow18Coeff17_spec :
    mulCoeffTwo JData V4C3Data 18 17 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 17 0 := by
  decide

private theorem v4JRow18Coeff18_spec :
    mulCoeffTwo JData V4C3Data 18 18 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 18 0 := by
  decide

private theorem v4JRow18Coeff19_spec :
    mulCoeffTwo JData V4C3Data 18 19 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 19 0 := by
  decide

private theorem v4JRow18Coeff20_spec :
    mulCoeffTwo JData V4C3Data 18 20 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 20 0 := by
  decide

private theorem v4JRow18Coeff21_spec :
    mulCoeffTwo JData V4C3Data 18 21 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 21 0 := by
  decide

private theorem v4JRow18Coeff22_spec :
    mulCoeffTwo JData V4C3Data 18 22 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 22 0 := by
  decide

private theorem v4JRow18Coeff23_spec :
    mulCoeffTwo JData V4C3Data 18 23 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 23 0 := by
  decide

private theorem v4JRow18Coeff24_spec :
    mulCoeffTwo JData V4C3Data 18 24 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 24 0 := by
  decide

private theorem v4JRow18Coeff25_spec :
    mulCoeffTwo JData V4C3Data 18 25 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 25 0 := by
  decide

private theorem v4JRow18Coeff26_spec :
    mulCoeffTwo JData V4C3Data 18 26 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 26 0 := by
  decide

private theorem v4JRow18Coeff27_spec :
    mulCoeffTwo JData V4C3Data 18 27 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 27 0 := by
  decide

private theorem v4JRow18Coeff28_spec :
    mulCoeffTwo JData V4C3Data 18 28 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 28 0 := by
  decide

private theorem v4JRow18Coeff29_spec :
    mulCoeffTwo JData V4C3Data 18 29 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 29 0 := by
  decide

private theorem v4JRow18Coeff30_spec :
    mulCoeffTwo JData V4C3Data 18 30 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 30 0 := by
  decide

private theorem v4JRow18Coeff31_spec :
    mulCoeffTwo JData V4C3Data 18 31 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 31 0 := by
  decide

private theorem v4JRow18Coeff32_spec :
    mulCoeffTwo JData V4C3Data 18 32 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 32 0 := by
  decide

private theorem v4JRow18Coeff33_spec :
    mulCoeffTwo JData V4C3Data 18 33 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 33 0 := by
  decide

private theorem v4JRow18Coeff34_spec :
    mulCoeffTwo JData V4C3Data 18 34 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 34 0 := by
  decide

private theorem v4JRow18Coeff35_spec :
    mulCoeffTwo JData V4C3Data 18 35 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 35 0 := by
  decide

private theorem v4JRow18Coeff36_spec :
    mulCoeffTwo JData V4C3Data 18 36 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 36 0 := by
  decide

private theorem v4JRow18Coeff37_spec :
    mulCoeffTwo JData V4C3Data 18 37 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 37 0 := by
  decide

private theorem v4JRow18Coeff38_spec :
    mulCoeffTwo JData V4C3Data 18 38 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 38 0 := by
  decide

private theorem v4JRow18Coeff39_spec :
    mulCoeffTwo JData V4C3Data 18 39 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 39 0 := by
  decide

private theorem v4JRow18Coeff40_spec :
    mulCoeffTwo JData V4C3Data 18 40 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 40 0 := by
  decide

private theorem v4JRow18Coeff41_spec :
    mulCoeffTwo JData V4C3Data 18 41 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 41 0 := by
  decide

private theorem v4JRow18Coeff42_spec :
    mulCoeffTwo JData V4C3Data 18 42 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 42 0 := by
  decide

private theorem v4JRow18Coeff43_spec :
    mulCoeffTwo JData V4C3Data 18 43 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 43 0 := by
  decide

private theorem v4JRow18Coeff44_spec :
    mulCoeffTwo JData V4C3Data 18 44 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 44 0 := by
  decide

private theorem v4JRow18Coeff45_spec :
    mulCoeffTwo JData V4C3Data 18 45 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 45 0 := by
  decide

private theorem v4JRow18Coeff46_spec :
    mulCoeffTwo JData V4C3Data 18 46 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 46 0 := by
  decide

private theorem v4JRow18Coeff47_spec :
    mulCoeffTwo JData V4C3Data 18 47 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 47 0 := by
  decide

private theorem v4JRow18Coeff48_spec :
    mulCoeffTwo JData V4C3Data 18 48 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 48 0 := by
  decide

private theorem v4JRow18Coeff49_spec :
    mulCoeffTwo JData V4C3Data 18 49 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 49 0 := by
  decide

private theorem v4JRow18Coeff50_spec :
    mulCoeffTwo JData V4C3Data 18 50 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 50 0 := by
  decide

private theorem v4JRow18Coeff51_spec :
    mulCoeffTwo JData V4C3Data 18 51 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 51 0 := by
  decide

private theorem v4JRow18Coeff52_spec :
    mulCoeffTwo JData V4C3Data 18 52 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 52 0 := by
  decide

private theorem v4JRow18Coeff53_spec :
    mulCoeffTwo JData V4C3Data 18 53 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 53 0 := by
  decide

private theorem v4JRow18Coeff54_spec :
    mulCoeffTwo JData V4C3Data 18 54 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 54 0 := by
  decide

private theorem v4JRow18Coeff55_spec :
    mulCoeffTwo JData V4C3Data 18 55 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 55 0 := by
  decide

private theorem v4JRow18Coeff56_spec :
    mulCoeffTwo JData V4C3Data 18 56 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 56 0 := by
  decide

private theorem v4JRow18Coeff57_spec :
    mulCoeffTwo JData V4C3Data 18 57 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 57 0 := by
  decide

private theorem v4JRow18Coeff58_spec :
    mulCoeffTwo JData V4C3Data 18 58 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 58 0 := by
  decide

private theorem v4JRow18Coeff59_spec :
    mulCoeffTwo JData V4C3Data 18 59 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 59 0 := by
  decide

private theorem v4JRow18Coeff60_spec :
    mulCoeffTwo JData V4C3Data 18 60 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 60 0 := by
  decide

private theorem v4JRow18Coeff61_spec :
    mulCoeffTwo JData V4C3Data 18 61 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 61 0 := by
  decide

private theorem v4JRow18Coeff62_spec :
    mulCoeffTwo JData V4C3Data 18 62 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 62 0 := by
  decide

private theorem v4JRow18Coeff63_spec :
    mulCoeffTwo JData V4C3Data 18 63 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 63 0 := by
  decide

private theorem v4JRow18Coeff64_spec :
    mulCoeffTwo JData V4C3Data 18 64 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 64 0 := by
  decide

private theorem v4JRow18Coeff65_spec :
    mulCoeffTwo JData V4C3Data 18 65 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 65 0 := by
  decide

private theorem v4JRow18Coeff66_spec :
    mulCoeffTwo JData V4C3Data 18 66 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 66 0 := by
  decide

private theorem v4JRow18Coeff67_spec :
    mulCoeffTwo JData V4C3Data 18 67 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 67 0 := by
  decide

private theorem v4JRow18Coeff68_spec :
    mulCoeffTwo JData V4C3Data 18 68 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 68 0 := by
  decide

private theorem v4JRow18Coeff69_spec :
    mulCoeffTwo JData V4C3Data 18 69 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 69 0 := by
  decide

private theorem v4JRow18Coeff70_spec :
    mulCoeffTwo JData V4C3Data 18 70 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 70 0 := by
  decide

private theorem v4JRow18Coeff71_spec :
    mulCoeffTwo JData V4C3Data 18 71 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 71 0 := by
  decide

private theorem v4JRow18Coeff72_spec :
    mulCoeffTwo JData V4C3Data 18 72 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 72 0 := by
  decide

private theorem v4JRow18Coeff73_spec :
    mulCoeffTwo JData V4C3Data 18 73 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 73 0 := by
  decide

private theorem v4JRow18Coeff74_spec :
    mulCoeffTwo JData V4C3Data 18 74 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 74 0 := by
  decide

private theorem v4JRow18Coeff75_spec :
    mulCoeffTwo JData V4C3Data 18 75 =
      ((rectangularize 52 76 V4JData).getD 18 []).getD 75 0 := by
  decide

private theorem v4JRow18Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo JData V4C3Data 18 j =
      ((rectangularize 52 76 V4JData).getD 18 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow18Coeff0_spec
  · exact v4JRow18Coeff1_spec
  · exact v4JRow18Coeff2_spec
  · exact v4JRow18Coeff3_spec
  · exact v4JRow18Coeff4_spec
  · exact v4JRow18Coeff5_spec
  · exact v4JRow18Coeff6_spec
  · exact v4JRow18Coeff7_spec
  · exact v4JRow18Coeff8_spec
  · exact v4JRow18Coeff9_spec

private theorem v4JRow18Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo JData V4C3Data 18 j =
      ((rectangularize 52 76 V4JData).getD 18 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow18Coeff10_spec
  · exact v4JRow18Coeff11_spec
  · exact v4JRow18Coeff12_spec
  · exact v4JRow18Coeff13_spec
  · exact v4JRow18Coeff14_spec
  · exact v4JRow18Coeff15_spec
  · exact v4JRow18Coeff16_spec
  · exact v4JRow18Coeff17_spec
  · exact v4JRow18Coeff18_spec
  · exact v4JRow18Coeff19_spec

private theorem v4JRow18Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo JData V4C3Data 18 j =
      ((rectangularize 52 76 V4JData).getD 18 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow18Coeff20_spec
  · exact v4JRow18Coeff21_spec
  · exact v4JRow18Coeff22_spec
  · exact v4JRow18Coeff23_spec
  · exact v4JRow18Coeff24_spec
  · exact v4JRow18Coeff25_spec
  · exact v4JRow18Coeff26_spec
  · exact v4JRow18Coeff27_spec
  · exact v4JRow18Coeff28_spec
  · exact v4JRow18Coeff29_spec

private theorem v4JRow18Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo JData V4C3Data 18 j =
      ((rectangularize 52 76 V4JData).getD 18 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow18Coeff30_spec
  · exact v4JRow18Coeff31_spec
  · exact v4JRow18Coeff32_spec
  · exact v4JRow18Coeff33_spec
  · exact v4JRow18Coeff34_spec
  · exact v4JRow18Coeff35_spec
  · exact v4JRow18Coeff36_spec
  · exact v4JRow18Coeff37_spec
  · exact v4JRow18Coeff38_spec
  · exact v4JRow18Coeff39_spec

private theorem v4JRow18Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo JData V4C3Data 18 j =
      ((rectangularize 52 76 V4JData).getD 18 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow18Coeff40_spec
  · exact v4JRow18Coeff41_spec
  · exact v4JRow18Coeff42_spec
  · exact v4JRow18Coeff43_spec
  · exact v4JRow18Coeff44_spec
  · exact v4JRow18Coeff45_spec
  · exact v4JRow18Coeff46_spec
  · exact v4JRow18Coeff47_spec
  · exact v4JRow18Coeff48_spec
  · exact v4JRow18Coeff49_spec

private theorem v4JRow18Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo JData V4C3Data 18 j =
      ((rectangularize 52 76 V4JData).getD 18 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow18Coeff50_spec
  · exact v4JRow18Coeff51_spec
  · exact v4JRow18Coeff52_spec
  · exact v4JRow18Coeff53_spec
  · exact v4JRow18Coeff54_spec
  · exact v4JRow18Coeff55_spec
  · exact v4JRow18Coeff56_spec
  · exact v4JRow18Coeff57_spec
  · exact v4JRow18Coeff58_spec
  · exact v4JRow18Coeff59_spec

private theorem v4JRow18Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo JData V4C3Data 18 j =
      ((rectangularize 52 76 V4JData).getD 18 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow18Coeff60_spec
  · exact v4JRow18Coeff61_spec
  · exact v4JRow18Coeff62_spec
  · exact v4JRow18Coeff63_spec
  · exact v4JRow18Coeff64_spec
  · exact v4JRow18Coeff65_spec
  · exact v4JRow18Coeff66_spec
  · exact v4JRow18Coeff67_spec
  · exact v4JRow18Coeff68_spec
  · exact v4JRow18Coeff69_spec

private theorem v4JRow18Coeffs70To75_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 76) :
    mulCoeffTwo JData V4C3Data 18 j =
      ((rectangularize 52 76 V4JData).getD 18 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact v4JRow18Coeff70_spec
  · exact v4JRow18Coeff71_spec
  · exact v4JRow18Coeff72_spec
  · exact v4JRow18Coeff73_spec
  · exact v4JRow18Coeff74_spec
  · exact v4JRow18Coeff75_spec

private theorem v4JRow18_coefficients (j : ℕ) (hj : j < 76) :
    mulCoeffTwo JData V4C3Data 18 j =
      ((rectangularize 52 76 V4JData).getD 18 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4JRow18Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4JRow18Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4JRow18Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4JRow18Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4JRow18Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4JRow18Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4JRow18Coeffs60To69_spec j (by omega) h70
  exact v4JRow18Coeffs70To75_spec j (by omega) hj

private theorem v4JRow18_spec :
    padOne 76 (mulRow JData V4C3Data 18) =
      (rectangularize 52 76 V4JData).getD 18 [] := by
  apply padOne_mulRow_eq_of_coefficients 76 JData V4C3Data 18
    ((rectangularize 52 76 V4JData).getD 18 [])
  · decide
  · have hTargetSupport : (V4JData.getD 18 []).length ≤ 76 := by
      decide
    rw [getD_rectangularize 52 76 V4JData 18 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4JRow18_coefficients

private theorem v4JRow19Coeff0_spec :
    mulCoeffTwo JData V4C3Data 19 0 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 0 0 := by
  decide

private theorem v4JRow19Coeff1_spec :
    mulCoeffTwo JData V4C3Data 19 1 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 1 0 := by
  decide

private theorem v4JRow19Coeff2_spec :
    mulCoeffTwo JData V4C3Data 19 2 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 2 0 := by
  decide

private theorem v4JRow19Coeff3_spec :
    mulCoeffTwo JData V4C3Data 19 3 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 3 0 := by
  decide

private theorem v4JRow19Coeff4_spec :
    mulCoeffTwo JData V4C3Data 19 4 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 4 0 := by
  decide

private theorem v4JRow19Coeff5_spec :
    mulCoeffTwo JData V4C3Data 19 5 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 5 0 := by
  decide

private theorem v4JRow19Coeff6_spec :
    mulCoeffTwo JData V4C3Data 19 6 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 6 0 := by
  decide

private theorem v4JRow19Coeff7_spec :
    mulCoeffTwo JData V4C3Data 19 7 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 7 0 := by
  decide

private theorem v4JRow19Coeff8_spec :
    mulCoeffTwo JData V4C3Data 19 8 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 8 0 := by
  decide

private theorem v4JRow19Coeff9_spec :
    mulCoeffTwo JData V4C3Data 19 9 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 9 0 := by
  decide

private theorem v4JRow19Coeff10_spec :
    mulCoeffTwo JData V4C3Data 19 10 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 10 0 := by
  decide

private theorem v4JRow19Coeff11_spec :
    mulCoeffTwo JData V4C3Data 19 11 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 11 0 := by
  decide

private theorem v4JRow19Coeff12_spec :
    mulCoeffTwo JData V4C3Data 19 12 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 12 0 := by
  decide

private theorem v4JRow19Coeff13_spec :
    mulCoeffTwo JData V4C3Data 19 13 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 13 0 := by
  decide

private theorem v4JRow19Coeff14_spec :
    mulCoeffTwo JData V4C3Data 19 14 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 14 0 := by
  decide

private theorem v4JRow19Coeff15_spec :
    mulCoeffTwo JData V4C3Data 19 15 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 15 0 := by
  decide

private theorem v4JRow19Coeff16_spec :
    mulCoeffTwo JData V4C3Data 19 16 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 16 0 := by
  decide

private theorem v4JRow19Coeff17_spec :
    mulCoeffTwo JData V4C3Data 19 17 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 17 0 := by
  decide

private theorem v4JRow19Coeff18_spec :
    mulCoeffTwo JData V4C3Data 19 18 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 18 0 := by
  decide

private theorem v4JRow19Coeff19_spec :
    mulCoeffTwo JData V4C3Data 19 19 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 19 0 := by
  decide

private theorem v4JRow19Coeff20_spec :
    mulCoeffTwo JData V4C3Data 19 20 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 20 0 := by
  decide

private theorem v4JRow19Coeff21_spec :
    mulCoeffTwo JData V4C3Data 19 21 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 21 0 := by
  decide

private theorem v4JRow19Coeff22_spec :
    mulCoeffTwo JData V4C3Data 19 22 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 22 0 := by
  decide

private theorem v4JRow19Coeff23_spec :
    mulCoeffTwo JData V4C3Data 19 23 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 23 0 := by
  decide

private theorem v4JRow19Coeff24_spec :
    mulCoeffTwo JData V4C3Data 19 24 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 24 0 := by
  decide

private theorem v4JRow19Coeff25_spec :
    mulCoeffTwo JData V4C3Data 19 25 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 25 0 := by
  decide

private theorem v4JRow19Coeff26_spec :
    mulCoeffTwo JData V4C3Data 19 26 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 26 0 := by
  decide

private theorem v4JRow19Coeff27_spec :
    mulCoeffTwo JData V4C3Data 19 27 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 27 0 := by
  decide

private theorem v4JRow19Coeff28_spec :
    mulCoeffTwo JData V4C3Data 19 28 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 28 0 := by
  decide

private theorem v4JRow19Coeff29_spec :
    mulCoeffTwo JData V4C3Data 19 29 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 29 0 := by
  decide

private theorem v4JRow19Coeff30_spec :
    mulCoeffTwo JData V4C3Data 19 30 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 30 0 := by
  decide

private theorem v4JRow19Coeff31_spec :
    mulCoeffTwo JData V4C3Data 19 31 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 31 0 := by
  decide

private theorem v4JRow19Coeff32_spec :
    mulCoeffTwo JData V4C3Data 19 32 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 32 0 := by
  decide

private theorem v4JRow19Coeff33_spec :
    mulCoeffTwo JData V4C3Data 19 33 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 33 0 := by
  decide

private theorem v4JRow19Coeff34_spec :
    mulCoeffTwo JData V4C3Data 19 34 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 34 0 := by
  decide

private theorem v4JRow19Coeff35_spec :
    mulCoeffTwo JData V4C3Data 19 35 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 35 0 := by
  decide

private theorem v4JRow19Coeff36_spec :
    mulCoeffTwo JData V4C3Data 19 36 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 36 0 := by
  decide

private theorem v4JRow19Coeff37_spec :
    mulCoeffTwo JData V4C3Data 19 37 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 37 0 := by
  decide

private theorem v4JRow19Coeff38_spec :
    mulCoeffTwo JData V4C3Data 19 38 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 38 0 := by
  decide

private theorem v4JRow19Coeff39_spec :
    mulCoeffTwo JData V4C3Data 19 39 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 39 0 := by
  decide

private theorem v4JRow19Coeff40_spec :
    mulCoeffTwo JData V4C3Data 19 40 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 40 0 := by
  decide

private theorem v4JRow19Coeff41_spec :
    mulCoeffTwo JData V4C3Data 19 41 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 41 0 := by
  decide

private theorem v4JRow19Coeff42_spec :
    mulCoeffTwo JData V4C3Data 19 42 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 42 0 := by
  decide

private theorem v4JRow19Coeff43_spec :
    mulCoeffTwo JData V4C3Data 19 43 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 43 0 := by
  decide

private theorem v4JRow19Coeff44_spec :
    mulCoeffTwo JData V4C3Data 19 44 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 44 0 := by
  decide

private theorem v4JRow19Coeff45_spec :
    mulCoeffTwo JData V4C3Data 19 45 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 45 0 := by
  decide

private theorem v4JRow19Coeff46_spec :
    mulCoeffTwo JData V4C3Data 19 46 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 46 0 := by
  decide

private theorem v4JRow19Coeff47_spec :
    mulCoeffTwo JData V4C3Data 19 47 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 47 0 := by
  decide

private theorem v4JRow19Coeff48_spec :
    mulCoeffTwo JData V4C3Data 19 48 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 48 0 := by
  decide

private theorem v4JRow19Coeff49_spec :
    mulCoeffTwo JData V4C3Data 19 49 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 49 0 := by
  decide

private theorem v4JRow19Coeff50_spec :
    mulCoeffTwo JData V4C3Data 19 50 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 50 0 := by
  decide

private theorem v4JRow19Coeff51_spec :
    mulCoeffTwo JData V4C3Data 19 51 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 51 0 := by
  decide

private theorem v4JRow19Coeff52_spec :
    mulCoeffTwo JData V4C3Data 19 52 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 52 0 := by
  decide

private theorem v4JRow19Coeff53_spec :
    mulCoeffTwo JData V4C3Data 19 53 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 53 0 := by
  decide

private theorem v4JRow19Coeff54_spec :
    mulCoeffTwo JData V4C3Data 19 54 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 54 0 := by
  decide

private theorem v4JRow19Coeff55_spec :
    mulCoeffTwo JData V4C3Data 19 55 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 55 0 := by
  decide

private theorem v4JRow19Coeff56_spec :
    mulCoeffTwo JData V4C3Data 19 56 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 56 0 := by
  decide

private theorem v4JRow19Coeff57_spec :
    mulCoeffTwo JData V4C3Data 19 57 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 57 0 := by
  decide

private theorem v4JRow19Coeff58_spec :
    mulCoeffTwo JData V4C3Data 19 58 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 58 0 := by
  decide

private theorem v4JRow19Coeff59_spec :
    mulCoeffTwo JData V4C3Data 19 59 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 59 0 := by
  decide

private theorem v4JRow19Coeff60_spec :
    mulCoeffTwo JData V4C3Data 19 60 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 60 0 := by
  decide

private theorem v4JRow19Coeff61_spec :
    mulCoeffTwo JData V4C3Data 19 61 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 61 0 := by
  decide

private theorem v4JRow19Coeff62_spec :
    mulCoeffTwo JData V4C3Data 19 62 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 62 0 := by
  decide

private theorem v4JRow19Coeff63_spec :
    mulCoeffTwo JData V4C3Data 19 63 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 63 0 := by
  decide

private theorem v4JRow19Coeff64_spec :
    mulCoeffTwo JData V4C3Data 19 64 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 64 0 := by
  decide

private theorem v4JRow19Coeff65_spec :
    mulCoeffTwo JData V4C3Data 19 65 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 65 0 := by
  decide

private theorem v4JRow19Coeff66_spec :
    mulCoeffTwo JData V4C3Data 19 66 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 66 0 := by
  decide

private theorem v4JRow19Coeff67_spec :
    mulCoeffTwo JData V4C3Data 19 67 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 67 0 := by
  decide

private theorem v4JRow19Coeff68_spec :
    mulCoeffTwo JData V4C3Data 19 68 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 68 0 := by
  decide

private theorem v4JRow19Coeff69_spec :
    mulCoeffTwo JData V4C3Data 19 69 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 69 0 := by
  decide

private theorem v4JRow19Coeff70_spec :
    mulCoeffTwo JData V4C3Data 19 70 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 70 0 := by
  decide

private theorem v4JRow19Coeff71_spec :
    mulCoeffTwo JData V4C3Data 19 71 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 71 0 := by
  decide

private theorem v4JRow19Coeff72_spec :
    mulCoeffTwo JData V4C3Data 19 72 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 72 0 := by
  decide

private theorem v4JRow19Coeff73_spec :
    mulCoeffTwo JData V4C3Data 19 73 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 73 0 := by
  decide

private theorem v4JRow19Coeff74_spec :
    mulCoeffTwo JData V4C3Data 19 74 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 74 0 := by
  decide

private theorem v4JRow19Coeff75_spec :
    mulCoeffTwo JData V4C3Data 19 75 =
      ((rectangularize 52 76 V4JData).getD 19 []).getD 75 0 := by
  decide

private theorem v4JRow19Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo JData V4C3Data 19 j =
      ((rectangularize 52 76 V4JData).getD 19 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow19Coeff0_spec
  · exact v4JRow19Coeff1_spec
  · exact v4JRow19Coeff2_spec
  · exact v4JRow19Coeff3_spec
  · exact v4JRow19Coeff4_spec
  · exact v4JRow19Coeff5_spec
  · exact v4JRow19Coeff6_spec
  · exact v4JRow19Coeff7_spec
  · exact v4JRow19Coeff8_spec
  · exact v4JRow19Coeff9_spec

private theorem v4JRow19Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo JData V4C3Data 19 j =
      ((rectangularize 52 76 V4JData).getD 19 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow19Coeff10_spec
  · exact v4JRow19Coeff11_spec
  · exact v4JRow19Coeff12_spec
  · exact v4JRow19Coeff13_spec
  · exact v4JRow19Coeff14_spec
  · exact v4JRow19Coeff15_spec
  · exact v4JRow19Coeff16_spec
  · exact v4JRow19Coeff17_spec
  · exact v4JRow19Coeff18_spec
  · exact v4JRow19Coeff19_spec

private theorem v4JRow19Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo JData V4C3Data 19 j =
      ((rectangularize 52 76 V4JData).getD 19 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow19Coeff20_spec
  · exact v4JRow19Coeff21_spec
  · exact v4JRow19Coeff22_spec
  · exact v4JRow19Coeff23_spec
  · exact v4JRow19Coeff24_spec
  · exact v4JRow19Coeff25_spec
  · exact v4JRow19Coeff26_spec
  · exact v4JRow19Coeff27_spec
  · exact v4JRow19Coeff28_spec
  · exact v4JRow19Coeff29_spec

private theorem v4JRow19Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo JData V4C3Data 19 j =
      ((rectangularize 52 76 V4JData).getD 19 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow19Coeff30_spec
  · exact v4JRow19Coeff31_spec
  · exact v4JRow19Coeff32_spec
  · exact v4JRow19Coeff33_spec
  · exact v4JRow19Coeff34_spec
  · exact v4JRow19Coeff35_spec
  · exact v4JRow19Coeff36_spec
  · exact v4JRow19Coeff37_spec
  · exact v4JRow19Coeff38_spec
  · exact v4JRow19Coeff39_spec

private theorem v4JRow19Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo JData V4C3Data 19 j =
      ((rectangularize 52 76 V4JData).getD 19 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow19Coeff40_spec
  · exact v4JRow19Coeff41_spec
  · exact v4JRow19Coeff42_spec
  · exact v4JRow19Coeff43_spec
  · exact v4JRow19Coeff44_spec
  · exact v4JRow19Coeff45_spec
  · exact v4JRow19Coeff46_spec
  · exact v4JRow19Coeff47_spec
  · exact v4JRow19Coeff48_spec
  · exact v4JRow19Coeff49_spec

private theorem v4JRow19Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo JData V4C3Data 19 j =
      ((rectangularize 52 76 V4JData).getD 19 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow19Coeff50_spec
  · exact v4JRow19Coeff51_spec
  · exact v4JRow19Coeff52_spec
  · exact v4JRow19Coeff53_spec
  · exact v4JRow19Coeff54_spec
  · exact v4JRow19Coeff55_spec
  · exact v4JRow19Coeff56_spec
  · exact v4JRow19Coeff57_spec
  · exact v4JRow19Coeff58_spec
  · exact v4JRow19Coeff59_spec

private theorem v4JRow19Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo JData V4C3Data 19 j =
      ((rectangularize 52 76 V4JData).getD 19 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow19Coeff60_spec
  · exact v4JRow19Coeff61_spec
  · exact v4JRow19Coeff62_spec
  · exact v4JRow19Coeff63_spec
  · exact v4JRow19Coeff64_spec
  · exact v4JRow19Coeff65_spec
  · exact v4JRow19Coeff66_spec
  · exact v4JRow19Coeff67_spec
  · exact v4JRow19Coeff68_spec
  · exact v4JRow19Coeff69_spec

private theorem v4JRow19Coeffs70To75_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 76) :
    mulCoeffTwo JData V4C3Data 19 j =
      ((rectangularize 52 76 V4JData).getD 19 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact v4JRow19Coeff70_spec
  · exact v4JRow19Coeff71_spec
  · exact v4JRow19Coeff72_spec
  · exact v4JRow19Coeff73_spec
  · exact v4JRow19Coeff74_spec
  · exact v4JRow19Coeff75_spec

private theorem v4JRow19_coefficients (j : ℕ) (hj : j < 76) :
    mulCoeffTwo JData V4C3Data 19 j =
      ((rectangularize 52 76 V4JData).getD 19 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4JRow19Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4JRow19Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4JRow19Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4JRow19Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4JRow19Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4JRow19Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4JRow19Coeffs60To69_spec j (by omega) h70
  exact v4JRow19Coeffs70To75_spec j (by omega) hj

private theorem v4JRow19_spec :
    padOne 76 (mulRow JData V4C3Data 19) =
      (rectangularize 52 76 V4JData).getD 19 [] := by
  apply padOne_mulRow_eq_of_coefficients 76 JData V4C3Data 19
    ((rectangularize 52 76 V4JData).getD 19 [])
  · decide
  · have hTargetSupport : (V4JData.getD 19 []).length ≤ 76 := by
      decide
    rw [getD_rectangularize 52 76 V4JData 19 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4JRow19_coefficients

private theorem v4JRow20Coeff0_spec :
    mulCoeffTwo JData V4C3Data 20 0 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 0 0 := by
  decide

private theorem v4JRow20Coeff1_spec :
    mulCoeffTwo JData V4C3Data 20 1 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 1 0 := by
  decide

private theorem v4JRow20Coeff2_spec :
    mulCoeffTwo JData V4C3Data 20 2 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 2 0 := by
  decide

private theorem v4JRow20Coeff3_spec :
    mulCoeffTwo JData V4C3Data 20 3 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 3 0 := by
  decide

private theorem v4JRow20Coeff4_spec :
    mulCoeffTwo JData V4C3Data 20 4 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 4 0 := by
  decide

private theorem v4JRow20Coeff5_spec :
    mulCoeffTwo JData V4C3Data 20 5 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 5 0 := by
  decide

private theorem v4JRow20Coeff6_spec :
    mulCoeffTwo JData V4C3Data 20 6 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 6 0 := by
  decide

private theorem v4JRow20Coeff7_spec :
    mulCoeffTwo JData V4C3Data 20 7 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 7 0 := by
  decide

private theorem v4JRow20Coeff8_spec :
    mulCoeffTwo JData V4C3Data 20 8 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 8 0 := by
  decide

private theorem v4JRow20Coeff9_spec :
    mulCoeffTwo JData V4C3Data 20 9 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 9 0 := by
  decide

private theorem v4JRow20Coeff10_spec :
    mulCoeffTwo JData V4C3Data 20 10 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 10 0 := by
  decide

private theorem v4JRow20Coeff11_spec :
    mulCoeffTwo JData V4C3Data 20 11 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 11 0 := by
  decide

private theorem v4JRow20Coeff12_spec :
    mulCoeffTwo JData V4C3Data 20 12 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 12 0 := by
  decide

private theorem v4JRow20Coeff13_spec :
    mulCoeffTwo JData V4C3Data 20 13 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 13 0 := by
  decide

private theorem v4JRow20Coeff14_spec :
    mulCoeffTwo JData V4C3Data 20 14 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 14 0 := by
  decide

private theorem v4JRow20Coeff15_spec :
    mulCoeffTwo JData V4C3Data 20 15 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 15 0 := by
  decide

private theorem v4JRow20Coeff16_spec :
    mulCoeffTwo JData V4C3Data 20 16 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 16 0 := by
  decide

private theorem v4JRow20Coeff17_spec :
    mulCoeffTwo JData V4C3Data 20 17 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 17 0 := by
  decide

private theorem v4JRow20Coeff18_spec :
    mulCoeffTwo JData V4C3Data 20 18 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 18 0 := by
  decide

private theorem v4JRow20Coeff19_spec :
    mulCoeffTwo JData V4C3Data 20 19 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 19 0 := by
  decide

private theorem v4JRow20Coeff20_spec :
    mulCoeffTwo JData V4C3Data 20 20 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 20 0 := by
  decide

private theorem v4JRow20Coeff21_spec :
    mulCoeffTwo JData V4C3Data 20 21 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 21 0 := by
  decide

private theorem v4JRow20Coeff22_spec :
    mulCoeffTwo JData V4C3Data 20 22 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 22 0 := by
  decide

private theorem v4JRow20Coeff23_spec :
    mulCoeffTwo JData V4C3Data 20 23 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 23 0 := by
  decide

private theorem v4JRow20Coeff24_spec :
    mulCoeffTwo JData V4C3Data 20 24 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 24 0 := by
  decide

private theorem v4JRow20Coeff25_spec :
    mulCoeffTwo JData V4C3Data 20 25 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 25 0 := by
  decide

private theorem v4JRow20Coeff26_spec :
    mulCoeffTwo JData V4C3Data 20 26 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 26 0 := by
  decide

private theorem v4JRow20Coeff27_spec :
    mulCoeffTwo JData V4C3Data 20 27 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 27 0 := by
  decide

private theorem v4JRow20Coeff28_spec :
    mulCoeffTwo JData V4C3Data 20 28 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 28 0 := by
  decide

private theorem v4JRow20Coeff29_spec :
    mulCoeffTwo JData V4C3Data 20 29 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 29 0 := by
  decide

private theorem v4JRow20Coeff30_spec :
    mulCoeffTwo JData V4C3Data 20 30 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 30 0 := by
  decide

private theorem v4JRow20Coeff31_spec :
    mulCoeffTwo JData V4C3Data 20 31 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 31 0 := by
  decide

private theorem v4JRow20Coeff32_spec :
    mulCoeffTwo JData V4C3Data 20 32 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 32 0 := by
  decide

private theorem v4JRow20Coeff33_spec :
    mulCoeffTwo JData V4C3Data 20 33 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 33 0 := by
  decide

private theorem v4JRow20Coeff34_spec :
    mulCoeffTwo JData V4C3Data 20 34 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 34 0 := by
  decide

private theorem v4JRow20Coeff35_spec :
    mulCoeffTwo JData V4C3Data 20 35 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 35 0 := by
  decide

private theorem v4JRow20Coeff36_spec :
    mulCoeffTwo JData V4C3Data 20 36 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 36 0 := by
  decide

private theorem v4JRow20Coeff37_spec :
    mulCoeffTwo JData V4C3Data 20 37 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 37 0 := by
  decide

private theorem v4JRow20Coeff38_spec :
    mulCoeffTwo JData V4C3Data 20 38 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 38 0 := by
  decide

private theorem v4JRow20Coeff39_spec :
    mulCoeffTwo JData V4C3Data 20 39 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 39 0 := by
  decide

private theorem v4JRow20Coeff40_spec :
    mulCoeffTwo JData V4C3Data 20 40 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 40 0 := by
  decide

private theorem v4JRow20Coeff41_spec :
    mulCoeffTwo JData V4C3Data 20 41 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 41 0 := by
  decide

private theorem v4JRow20Coeff42_spec :
    mulCoeffTwo JData V4C3Data 20 42 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 42 0 := by
  decide

private theorem v4JRow20Coeff43_spec :
    mulCoeffTwo JData V4C3Data 20 43 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 43 0 := by
  decide

private theorem v4JRow20Coeff44_spec :
    mulCoeffTwo JData V4C3Data 20 44 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 44 0 := by
  decide

private theorem v4JRow20Coeff45_spec :
    mulCoeffTwo JData V4C3Data 20 45 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 45 0 := by
  decide

private theorem v4JRow20Coeff46_spec :
    mulCoeffTwo JData V4C3Data 20 46 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 46 0 := by
  decide

private theorem v4JRow20Coeff47_spec :
    mulCoeffTwo JData V4C3Data 20 47 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 47 0 := by
  decide

private theorem v4JRow20Coeff48_spec :
    mulCoeffTwo JData V4C3Data 20 48 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 48 0 := by
  decide

private theorem v4JRow20Coeff49_spec :
    mulCoeffTwo JData V4C3Data 20 49 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 49 0 := by
  decide

private theorem v4JRow20Coeff50_spec :
    mulCoeffTwo JData V4C3Data 20 50 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 50 0 := by
  decide

private theorem v4JRow20Coeff51_spec :
    mulCoeffTwo JData V4C3Data 20 51 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 51 0 := by
  decide

private theorem v4JRow20Coeff52_spec :
    mulCoeffTwo JData V4C3Data 20 52 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 52 0 := by
  decide

private theorem v4JRow20Coeff53_spec :
    mulCoeffTwo JData V4C3Data 20 53 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 53 0 := by
  decide

private theorem v4JRow20Coeff54_spec :
    mulCoeffTwo JData V4C3Data 20 54 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 54 0 := by
  decide

private theorem v4JRow20Coeff55_spec :
    mulCoeffTwo JData V4C3Data 20 55 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 55 0 := by
  decide

private theorem v4JRow20Coeff56_spec :
    mulCoeffTwo JData V4C3Data 20 56 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 56 0 := by
  decide

private theorem v4JRow20Coeff57_spec :
    mulCoeffTwo JData V4C3Data 20 57 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 57 0 := by
  decide

private theorem v4JRow20Coeff58_spec :
    mulCoeffTwo JData V4C3Data 20 58 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 58 0 := by
  decide

private theorem v4JRow20Coeff59_spec :
    mulCoeffTwo JData V4C3Data 20 59 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 59 0 := by
  decide

private theorem v4JRow20Coeff60_spec :
    mulCoeffTwo JData V4C3Data 20 60 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 60 0 := by
  decide

private theorem v4JRow20Coeff61_spec :
    mulCoeffTwo JData V4C3Data 20 61 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 61 0 := by
  decide

private theorem v4JRow20Coeff62_spec :
    mulCoeffTwo JData V4C3Data 20 62 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 62 0 := by
  decide

private theorem v4JRow20Coeff63_spec :
    mulCoeffTwo JData V4C3Data 20 63 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 63 0 := by
  decide

private theorem v4JRow20Coeff64_spec :
    mulCoeffTwo JData V4C3Data 20 64 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 64 0 := by
  decide

private theorem v4JRow20Coeff65_spec :
    mulCoeffTwo JData V4C3Data 20 65 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 65 0 := by
  decide

private theorem v4JRow20Coeff66_spec :
    mulCoeffTwo JData V4C3Data 20 66 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 66 0 := by
  decide

private theorem v4JRow20Coeff67_spec :
    mulCoeffTwo JData V4C3Data 20 67 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 67 0 := by
  decide

private theorem v4JRow20Coeff68_spec :
    mulCoeffTwo JData V4C3Data 20 68 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 68 0 := by
  decide

private theorem v4JRow20Coeff69_spec :
    mulCoeffTwo JData V4C3Data 20 69 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 69 0 := by
  decide

private theorem v4JRow20Coeff70_spec :
    mulCoeffTwo JData V4C3Data 20 70 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 70 0 := by
  decide

private theorem v4JRow20Coeff71_spec :
    mulCoeffTwo JData V4C3Data 20 71 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 71 0 := by
  decide

private theorem v4JRow20Coeff72_spec :
    mulCoeffTwo JData V4C3Data 20 72 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 72 0 := by
  decide

private theorem v4JRow20Coeff73_spec :
    mulCoeffTwo JData V4C3Data 20 73 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 73 0 := by
  decide

private theorem v4JRow20Coeff74_spec :
    mulCoeffTwo JData V4C3Data 20 74 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 74 0 := by
  decide

private theorem v4JRow20Coeff75_spec :
    mulCoeffTwo JData V4C3Data 20 75 =
      ((rectangularize 52 76 V4JData).getD 20 []).getD 75 0 := by
  decide

private theorem v4JRow20Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo JData V4C3Data 20 j =
      ((rectangularize 52 76 V4JData).getD 20 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow20Coeff0_spec
  · exact v4JRow20Coeff1_spec
  · exact v4JRow20Coeff2_spec
  · exact v4JRow20Coeff3_spec
  · exact v4JRow20Coeff4_spec
  · exact v4JRow20Coeff5_spec
  · exact v4JRow20Coeff6_spec
  · exact v4JRow20Coeff7_spec
  · exact v4JRow20Coeff8_spec
  · exact v4JRow20Coeff9_spec

private theorem v4JRow20Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo JData V4C3Data 20 j =
      ((rectangularize 52 76 V4JData).getD 20 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow20Coeff10_spec
  · exact v4JRow20Coeff11_spec
  · exact v4JRow20Coeff12_spec
  · exact v4JRow20Coeff13_spec
  · exact v4JRow20Coeff14_spec
  · exact v4JRow20Coeff15_spec
  · exact v4JRow20Coeff16_spec
  · exact v4JRow20Coeff17_spec
  · exact v4JRow20Coeff18_spec
  · exact v4JRow20Coeff19_spec

private theorem v4JRow20Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo JData V4C3Data 20 j =
      ((rectangularize 52 76 V4JData).getD 20 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow20Coeff20_spec
  · exact v4JRow20Coeff21_spec
  · exact v4JRow20Coeff22_spec
  · exact v4JRow20Coeff23_spec
  · exact v4JRow20Coeff24_spec
  · exact v4JRow20Coeff25_spec
  · exact v4JRow20Coeff26_spec
  · exact v4JRow20Coeff27_spec
  · exact v4JRow20Coeff28_spec
  · exact v4JRow20Coeff29_spec

private theorem v4JRow20Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo JData V4C3Data 20 j =
      ((rectangularize 52 76 V4JData).getD 20 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow20Coeff30_spec
  · exact v4JRow20Coeff31_spec
  · exact v4JRow20Coeff32_spec
  · exact v4JRow20Coeff33_spec
  · exact v4JRow20Coeff34_spec
  · exact v4JRow20Coeff35_spec
  · exact v4JRow20Coeff36_spec
  · exact v4JRow20Coeff37_spec
  · exact v4JRow20Coeff38_spec
  · exact v4JRow20Coeff39_spec

private theorem v4JRow20Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo JData V4C3Data 20 j =
      ((rectangularize 52 76 V4JData).getD 20 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow20Coeff40_spec
  · exact v4JRow20Coeff41_spec
  · exact v4JRow20Coeff42_spec
  · exact v4JRow20Coeff43_spec
  · exact v4JRow20Coeff44_spec
  · exact v4JRow20Coeff45_spec
  · exact v4JRow20Coeff46_spec
  · exact v4JRow20Coeff47_spec
  · exact v4JRow20Coeff48_spec
  · exact v4JRow20Coeff49_spec

private theorem v4JRow20Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo JData V4C3Data 20 j =
      ((rectangularize 52 76 V4JData).getD 20 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow20Coeff50_spec
  · exact v4JRow20Coeff51_spec
  · exact v4JRow20Coeff52_spec
  · exact v4JRow20Coeff53_spec
  · exact v4JRow20Coeff54_spec
  · exact v4JRow20Coeff55_spec
  · exact v4JRow20Coeff56_spec
  · exact v4JRow20Coeff57_spec
  · exact v4JRow20Coeff58_spec
  · exact v4JRow20Coeff59_spec

private theorem v4JRow20Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo JData V4C3Data 20 j =
      ((rectangularize 52 76 V4JData).getD 20 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow20Coeff60_spec
  · exact v4JRow20Coeff61_spec
  · exact v4JRow20Coeff62_spec
  · exact v4JRow20Coeff63_spec
  · exact v4JRow20Coeff64_spec
  · exact v4JRow20Coeff65_spec
  · exact v4JRow20Coeff66_spec
  · exact v4JRow20Coeff67_spec
  · exact v4JRow20Coeff68_spec
  · exact v4JRow20Coeff69_spec

private theorem v4JRow20Coeffs70To75_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 76) :
    mulCoeffTwo JData V4C3Data 20 j =
      ((rectangularize 52 76 V4JData).getD 20 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact v4JRow20Coeff70_spec
  · exact v4JRow20Coeff71_spec
  · exact v4JRow20Coeff72_spec
  · exact v4JRow20Coeff73_spec
  · exact v4JRow20Coeff74_spec
  · exact v4JRow20Coeff75_spec

private theorem v4JRow20_coefficients (j : ℕ) (hj : j < 76) :
    mulCoeffTwo JData V4C3Data 20 j =
      ((rectangularize 52 76 V4JData).getD 20 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4JRow20Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4JRow20Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4JRow20Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4JRow20Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4JRow20Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4JRow20Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4JRow20Coeffs60To69_spec j (by omega) h70
  exact v4JRow20Coeffs70To75_spec j (by omega) hj

private theorem v4JRow20_spec :
    padOne 76 (mulRow JData V4C3Data 20) =
      (rectangularize 52 76 V4JData).getD 20 [] := by
  apply padOne_mulRow_eq_of_coefficients 76 JData V4C3Data 20
    ((rectangularize 52 76 V4JData).getD 20 [])
  · decide
  · have hTargetSupport : (V4JData.getD 20 []).length ≤ 76 := by
      decide
    rw [getD_rectangularize 52 76 V4JData 20 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4JRow20_coefficients

private theorem v4JRow21Coeff0_spec :
    mulCoeffTwo JData V4C3Data 21 0 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 0 0 := by
  decide

private theorem v4JRow21Coeff1_spec :
    mulCoeffTwo JData V4C3Data 21 1 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 1 0 := by
  decide

private theorem v4JRow21Coeff2_spec :
    mulCoeffTwo JData V4C3Data 21 2 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 2 0 := by
  decide

private theorem v4JRow21Coeff3_spec :
    mulCoeffTwo JData V4C3Data 21 3 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 3 0 := by
  decide

private theorem v4JRow21Coeff4_spec :
    mulCoeffTwo JData V4C3Data 21 4 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 4 0 := by
  decide

private theorem v4JRow21Coeff5_spec :
    mulCoeffTwo JData V4C3Data 21 5 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 5 0 := by
  decide

private theorem v4JRow21Coeff6_spec :
    mulCoeffTwo JData V4C3Data 21 6 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 6 0 := by
  decide

private theorem v4JRow21Coeff7_spec :
    mulCoeffTwo JData V4C3Data 21 7 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 7 0 := by
  decide

private theorem v4JRow21Coeff8_spec :
    mulCoeffTwo JData V4C3Data 21 8 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 8 0 := by
  decide

private theorem v4JRow21Coeff9_spec :
    mulCoeffTwo JData V4C3Data 21 9 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 9 0 := by
  decide

private theorem v4JRow21Coeff10_spec :
    mulCoeffTwo JData V4C3Data 21 10 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 10 0 := by
  decide

private theorem v4JRow21Coeff11_spec :
    mulCoeffTwo JData V4C3Data 21 11 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 11 0 := by
  decide

private theorem v4JRow21Coeff12_spec :
    mulCoeffTwo JData V4C3Data 21 12 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 12 0 := by
  decide

private theorem v4JRow21Coeff13_spec :
    mulCoeffTwo JData V4C3Data 21 13 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 13 0 := by
  decide

private theorem v4JRow21Coeff14_spec :
    mulCoeffTwo JData V4C3Data 21 14 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 14 0 := by
  decide

private theorem v4JRow21Coeff15_spec :
    mulCoeffTwo JData V4C3Data 21 15 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 15 0 := by
  decide

private theorem v4JRow21Coeff16_spec :
    mulCoeffTwo JData V4C3Data 21 16 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 16 0 := by
  decide

private theorem v4JRow21Coeff17_spec :
    mulCoeffTwo JData V4C3Data 21 17 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 17 0 := by
  decide

private theorem v4JRow21Coeff18_spec :
    mulCoeffTwo JData V4C3Data 21 18 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 18 0 := by
  decide

private theorem v4JRow21Coeff19_spec :
    mulCoeffTwo JData V4C3Data 21 19 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 19 0 := by
  decide

private theorem v4JRow21Coeff20_spec :
    mulCoeffTwo JData V4C3Data 21 20 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 20 0 := by
  decide

private theorem v4JRow21Coeff21_spec :
    mulCoeffTwo JData V4C3Data 21 21 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 21 0 := by
  decide

private theorem v4JRow21Coeff22_spec :
    mulCoeffTwo JData V4C3Data 21 22 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 22 0 := by
  decide

private theorem v4JRow21Coeff23_spec :
    mulCoeffTwo JData V4C3Data 21 23 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 23 0 := by
  decide

private theorem v4JRow21Coeff24_spec :
    mulCoeffTwo JData V4C3Data 21 24 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 24 0 := by
  decide

private theorem v4JRow21Coeff25_spec :
    mulCoeffTwo JData V4C3Data 21 25 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 25 0 := by
  decide

private theorem v4JRow21Coeff26_spec :
    mulCoeffTwo JData V4C3Data 21 26 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 26 0 := by
  decide

private theorem v4JRow21Coeff27_spec :
    mulCoeffTwo JData V4C3Data 21 27 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 27 0 := by
  decide

private theorem v4JRow21Coeff28_spec :
    mulCoeffTwo JData V4C3Data 21 28 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 28 0 := by
  decide

private theorem v4JRow21Coeff29_spec :
    mulCoeffTwo JData V4C3Data 21 29 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 29 0 := by
  decide

private theorem v4JRow21Coeff30_spec :
    mulCoeffTwo JData V4C3Data 21 30 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 30 0 := by
  decide

private theorem v4JRow21Coeff31_spec :
    mulCoeffTwo JData V4C3Data 21 31 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 31 0 := by
  decide

private theorem v4JRow21Coeff32_spec :
    mulCoeffTwo JData V4C3Data 21 32 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 32 0 := by
  decide

private theorem v4JRow21Coeff33_spec :
    mulCoeffTwo JData V4C3Data 21 33 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 33 0 := by
  decide

private theorem v4JRow21Coeff34_spec :
    mulCoeffTwo JData V4C3Data 21 34 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 34 0 := by
  decide

private theorem v4JRow21Coeff35_spec :
    mulCoeffTwo JData V4C3Data 21 35 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 35 0 := by
  decide

private theorem v4JRow21Coeff36_spec :
    mulCoeffTwo JData V4C3Data 21 36 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 36 0 := by
  decide

private theorem v4JRow21Coeff37_spec :
    mulCoeffTwo JData V4C3Data 21 37 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 37 0 := by
  decide

private theorem v4JRow21Coeff38_spec :
    mulCoeffTwo JData V4C3Data 21 38 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 38 0 := by
  decide

private theorem v4JRow21Coeff39_spec :
    mulCoeffTwo JData V4C3Data 21 39 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 39 0 := by
  decide

private theorem v4JRow21Coeff40_spec :
    mulCoeffTwo JData V4C3Data 21 40 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 40 0 := by
  decide

private theorem v4JRow21Coeff41_spec :
    mulCoeffTwo JData V4C3Data 21 41 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 41 0 := by
  decide

private theorem v4JRow21Coeff42_spec :
    mulCoeffTwo JData V4C3Data 21 42 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 42 0 := by
  decide

private theorem v4JRow21Coeff43_spec :
    mulCoeffTwo JData V4C3Data 21 43 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 43 0 := by
  decide

private theorem v4JRow21Coeff44_spec :
    mulCoeffTwo JData V4C3Data 21 44 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 44 0 := by
  decide

private theorem v4JRow21Coeff45_spec :
    mulCoeffTwo JData V4C3Data 21 45 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 45 0 := by
  decide

private theorem v4JRow21Coeff46_spec :
    mulCoeffTwo JData V4C3Data 21 46 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 46 0 := by
  decide

private theorem v4JRow21Coeff47_spec :
    mulCoeffTwo JData V4C3Data 21 47 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 47 0 := by
  decide

private theorem v4JRow21Coeff48_spec :
    mulCoeffTwo JData V4C3Data 21 48 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 48 0 := by
  decide

private theorem v4JRow21Coeff49_spec :
    mulCoeffTwo JData V4C3Data 21 49 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 49 0 := by
  decide

private theorem v4JRow21Coeff50_spec :
    mulCoeffTwo JData V4C3Data 21 50 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 50 0 := by
  decide

private theorem v4JRow21Coeff51_spec :
    mulCoeffTwo JData V4C3Data 21 51 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 51 0 := by
  decide

private theorem v4JRow21Coeff52_spec :
    mulCoeffTwo JData V4C3Data 21 52 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 52 0 := by
  decide

private theorem v4JRow21Coeff53_spec :
    mulCoeffTwo JData V4C3Data 21 53 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 53 0 := by
  decide

private theorem v4JRow21Coeff54_spec :
    mulCoeffTwo JData V4C3Data 21 54 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 54 0 := by
  decide

private theorem v4JRow21Coeff55_spec :
    mulCoeffTwo JData V4C3Data 21 55 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 55 0 := by
  decide

private theorem v4JRow21Coeff56_spec :
    mulCoeffTwo JData V4C3Data 21 56 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 56 0 := by
  decide

private theorem v4JRow21Coeff57_spec :
    mulCoeffTwo JData V4C3Data 21 57 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 57 0 := by
  decide

private theorem v4JRow21Coeff58_spec :
    mulCoeffTwo JData V4C3Data 21 58 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 58 0 := by
  decide

private theorem v4JRow21Coeff59_spec :
    mulCoeffTwo JData V4C3Data 21 59 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 59 0 := by
  decide

private theorem v4JRow21Coeff60_spec :
    mulCoeffTwo JData V4C3Data 21 60 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 60 0 := by
  decide

private theorem v4JRow21Coeff61_spec :
    mulCoeffTwo JData V4C3Data 21 61 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 61 0 := by
  decide

private theorem v4JRow21Coeff62_spec :
    mulCoeffTwo JData V4C3Data 21 62 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 62 0 := by
  decide

private theorem v4JRow21Coeff63_spec :
    mulCoeffTwo JData V4C3Data 21 63 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 63 0 := by
  decide

private theorem v4JRow21Coeff64_spec :
    mulCoeffTwo JData V4C3Data 21 64 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 64 0 := by
  decide

private theorem v4JRow21Coeff65_spec :
    mulCoeffTwo JData V4C3Data 21 65 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 65 0 := by
  decide

private theorem v4JRow21Coeff66_spec :
    mulCoeffTwo JData V4C3Data 21 66 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 66 0 := by
  decide

private theorem v4JRow21Coeff67_spec :
    mulCoeffTwo JData V4C3Data 21 67 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 67 0 := by
  decide

private theorem v4JRow21Coeff68_spec :
    mulCoeffTwo JData V4C3Data 21 68 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 68 0 := by
  decide

private theorem v4JRow21Coeff69_spec :
    mulCoeffTwo JData V4C3Data 21 69 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 69 0 := by
  decide

private theorem v4JRow21Coeff70_spec :
    mulCoeffTwo JData V4C3Data 21 70 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 70 0 := by
  decide

private theorem v4JRow21Coeff71_spec :
    mulCoeffTwo JData V4C3Data 21 71 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 71 0 := by
  decide

private theorem v4JRow21Coeff72_spec :
    mulCoeffTwo JData V4C3Data 21 72 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 72 0 := by
  decide

private theorem v4JRow21Coeff73_spec :
    mulCoeffTwo JData V4C3Data 21 73 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 73 0 := by
  decide

private theorem v4JRow21Coeff74_spec :
    mulCoeffTwo JData V4C3Data 21 74 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 74 0 := by
  decide

private theorem v4JRow21Coeff75_spec :
    mulCoeffTwo JData V4C3Data 21 75 =
      ((rectangularize 52 76 V4JData).getD 21 []).getD 75 0 := by
  decide

private theorem v4JRow21Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo JData V4C3Data 21 j =
      ((rectangularize 52 76 V4JData).getD 21 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow21Coeff0_spec
  · exact v4JRow21Coeff1_spec
  · exact v4JRow21Coeff2_spec
  · exact v4JRow21Coeff3_spec
  · exact v4JRow21Coeff4_spec
  · exact v4JRow21Coeff5_spec
  · exact v4JRow21Coeff6_spec
  · exact v4JRow21Coeff7_spec
  · exact v4JRow21Coeff8_spec
  · exact v4JRow21Coeff9_spec

private theorem v4JRow21Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo JData V4C3Data 21 j =
      ((rectangularize 52 76 V4JData).getD 21 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow21Coeff10_spec
  · exact v4JRow21Coeff11_spec
  · exact v4JRow21Coeff12_spec
  · exact v4JRow21Coeff13_spec
  · exact v4JRow21Coeff14_spec
  · exact v4JRow21Coeff15_spec
  · exact v4JRow21Coeff16_spec
  · exact v4JRow21Coeff17_spec
  · exact v4JRow21Coeff18_spec
  · exact v4JRow21Coeff19_spec

private theorem v4JRow21Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo JData V4C3Data 21 j =
      ((rectangularize 52 76 V4JData).getD 21 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow21Coeff20_spec
  · exact v4JRow21Coeff21_spec
  · exact v4JRow21Coeff22_spec
  · exact v4JRow21Coeff23_spec
  · exact v4JRow21Coeff24_spec
  · exact v4JRow21Coeff25_spec
  · exact v4JRow21Coeff26_spec
  · exact v4JRow21Coeff27_spec
  · exact v4JRow21Coeff28_spec
  · exact v4JRow21Coeff29_spec

private theorem v4JRow21Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo JData V4C3Data 21 j =
      ((rectangularize 52 76 V4JData).getD 21 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow21Coeff30_spec
  · exact v4JRow21Coeff31_spec
  · exact v4JRow21Coeff32_spec
  · exact v4JRow21Coeff33_spec
  · exact v4JRow21Coeff34_spec
  · exact v4JRow21Coeff35_spec
  · exact v4JRow21Coeff36_spec
  · exact v4JRow21Coeff37_spec
  · exact v4JRow21Coeff38_spec
  · exact v4JRow21Coeff39_spec

private theorem v4JRow21Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo JData V4C3Data 21 j =
      ((rectangularize 52 76 V4JData).getD 21 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow21Coeff40_spec
  · exact v4JRow21Coeff41_spec
  · exact v4JRow21Coeff42_spec
  · exact v4JRow21Coeff43_spec
  · exact v4JRow21Coeff44_spec
  · exact v4JRow21Coeff45_spec
  · exact v4JRow21Coeff46_spec
  · exact v4JRow21Coeff47_spec
  · exact v4JRow21Coeff48_spec
  · exact v4JRow21Coeff49_spec

private theorem v4JRow21Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo JData V4C3Data 21 j =
      ((rectangularize 52 76 V4JData).getD 21 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow21Coeff50_spec
  · exact v4JRow21Coeff51_spec
  · exact v4JRow21Coeff52_spec
  · exact v4JRow21Coeff53_spec
  · exact v4JRow21Coeff54_spec
  · exact v4JRow21Coeff55_spec
  · exact v4JRow21Coeff56_spec
  · exact v4JRow21Coeff57_spec
  · exact v4JRow21Coeff58_spec
  · exact v4JRow21Coeff59_spec

private theorem v4JRow21Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo JData V4C3Data 21 j =
      ((rectangularize 52 76 V4JData).getD 21 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow21Coeff60_spec
  · exact v4JRow21Coeff61_spec
  · exact v4JRow21Coeff62_spec
  · exact v4JRow21Coeff63_spec
  · exact v4JRow21Coeff64_spec
  · exact v4JRow21Coeff65_spec
  · exact v4JRow21Coeff66_spec
  · exact v4JRow21Coeff67_spec
  · exact v4JRow21Coeff68_spec
  · exact v4JRow21Coeff69_spec

private theorem v4JRow21Coeffs70To75_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 76) :
    mulCoeffTwo JData V4C3Data 21 j =
      ((rectangularize 52 76 V4JData).getD 21 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact v4JRow21Coeff70_spec
  · exact v4JRow21Coeff71_spec
  · exact v4JRow21Coeff72_spec
  · exact v4JRow21Coeff73_spec
  · exact v4JRow21Coeff74_spec
  · exact v4JRow21Coeff75_spec

private theorem v4JRow21_coefficients (j : ℕ) (hj : j < 76) :
    mulCoeffTwo JData V4C3Data 21 j =
      ((rectangularize 52 76 V4JData).getD 21 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4JRow21Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4JRow21Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4JRow21Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4JRow21Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4JRow21Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4JRow21Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4JRow21Coeffs60To69_spec j (by omega) h70
  exact v4JRow21Coeffs70To75_spec j (by omega) hj

private theorem v4JRow21_spec :
    padOne 76 (mulRow JData V4C3Data 21) =
      (rectangularize 52 76 V4JData).getD 21 [] := by
  apply padOne_mulRow_eq_of_coefficients 76 JData V4C3Data 21
    ((rectangularize 52 76 V4JData).getD 21 [])
  · decide
  · have hTargetSupport : (V4JData.getD 21 []).length ≤ 76 := by
      decide
    rw [getD_rectangularize 52 76 V4JData 21 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4JRow21_coefficients

private theorem v4JRow22Coeff0_spec :
    mulCoeffTwo JData V4C3Data 22 0 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 0 0 := by
  decide

private theorem v4JRow22Coeff1_spec :
    mulCoeffTwo JData V4C3Data 22 1 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 1 0 := by
  decide

private theorem v4JRow22Coeff2_spec :
    mulCoeffTwo JData V4C3Data 22 2 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 2 0 := by
  decide

private theorem v4JRow22Coeff3_spec :
    mulCoeffTwo JData V4C3Data 22 3 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 3 0 := by
  decide

private theorem v4JRow22Coeff4_spec :
    mulCoeffTwo JData V4C3Data 22 4 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 4 0 := by
  decide

private theorem v4JRow22Coeff5_spec :
    mulCoeffTwo JData V4C3Data 22 5 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 5 0 := by
  decide

private theorem v4JRow22Coeff6_spec :
    mulCoeffTwo JData V4C3Data 22 6 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 6 0 := by
  decide

private theorem v4JRow22Coeff7_spec :
    mulCoeffTwo JData V4C3Data 22 7 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 7 0 := by
  decide

private theorem v4JRow22Coeff8_spec :
    mulCoeffTwo JData V4C3Data 22 8 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 8 0 := by
  decide

private theorem v4JRow22Coeff9_spec :
    mulCoeffTwo JData V4C3Data 22 9 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 9 0 := by
  decide

private theorem v4JRow22Coeff10_spec :
    mulCoeffTwo JData V4C3Data 22 10 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 10 0 := by
  decide

private theorem v4JRow22Coeff11_spec :
    mulCoeffTwo JData V4C3Data 22 11 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 11 0 := by
  decide

private theorem v4JRow22Coeff12_spec :
    mulCoeffTwo JData V4C3Data 22 12 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 12 0 := by
  decide

private theorem v4JRow22Coeff13_spec :
    mulCoeffTwo JData V4C3Data 22 13 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 13 0 := by
  decide

private theorem v4JRow22Coeff14_spec :
    mulCoeffTwo JData V4C3Data 22 14 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 14 0 := by
  decide

private theorem v4JRow22Coeff15_spec :
    mulCoeffTwo JData V4C3Data 22 15 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 15 0 := by
  decide

private theorem v4JRow22Coeff16_spec :
    mulCoeffTwo JData V4C3Data 22 16 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 16 0 := by
  decide

private theorem v4JRow22Coeff17_spec :
    mulCoeffTwo JData V4C3Data 22 17 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 17 0 := by
  decide

private theorem v4JRow22Coeff18_spec :
    mulCoeffTwo JData V4C3Data 22 18 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 18 0 := by
  decide

private theorem v4JRow22Coeff19_spec :
    mulCoeffTwo JData V4C3Data 22 19 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 19 0 := by
  decide

private theorem v4JRow22Coeff20_spec :
    mulCoeffTwo JData V4C3Data 22 20 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 20 0 := by
  decide

private theorem v4JRow22Coeff21_spec :
    mulCoeffTwo JData V4C3Data 22 21 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 21 0 := by
  decide

private theorem v4JRow22Coeff22_spec :
    mulCoeffTwo JData V4C3Data 22 22 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 22 0 := by
  decide

private theorem v4JRow22Coeff23_spec :
    mulCoeffTwo JData V4C3Data 22 23 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 23 0 := by
  decide

private theorem v4JRow22Coeff24_spec :
    mulCoeffTwo JData V4C3Data 22 24 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 24 0 := by
  decide

private theorem v4JRow22Coeff25_spec :
    mulCoeffTwo JData V4C3Data 22 25 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 25 0 := by
  decide

private theorem v4JRow22Coeff26_spec :
    mulCoeffTwo JData V4C3Data 22 26 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 26 0 := by
  decide

private theorem v4JRow22Coeff27_spec :
    mulCoeffTwo JData V4C3Data 22 27 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 27 0 := by
  decide

private theorem v4JRow22Coeff28_spec :
    mulCoeffTwo JData V4C3Data 22 28 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 28 0 := by
  decide

private theorem v4JRow22Coeff29_spec :
    mulCoeffTwo JData V4C3Data 22 29 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 29 0 := by
  decide

private theorem v4JRow22Coeff30_spec :
    mulCoeffTwo JData V4C3Data 22 30 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 30 0 := by
  decide

private theorem v4JRow22Coeff31_spec :
    mulCoeffTwo JData V4C3Data 22 31 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 31 0 := by
  decide

private theorem v4JRow22Coeff32_spec :
    mulCoeffTwo JData V4C3Data 22 32 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 32 0 := by
  decide

private theorem v4JRow22Coeff33_spec :
    mulCoeffTwo JData V4C3Data 22 33 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 33 0 := by
  decide

private theorem v4JRow22Coeff34_spec :
    mulCoeffTwo JData V4C3Data 22 34 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 34 0 := by
  decide

private theorem v4JRow22Coeff35_spec :
    mulCoeffTwo JData V4C3Data 22 35 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 35 0 := by
  decide

private theorem v4JRow22Coeff36_spec :
    mulCoeffTwo JData V4C3Data 22 36 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 36 0 := by
  decide

private theorem v4JRow22Coeff37_spec :
    mulCoeffTwo JData V4C3Data 22 37 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 37 0 := by
  decide

private theorem v4JRow22Coeff38_spec :
    mulCoeffTwo JData V4C3Data 22 38 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 38 0 := by
  decide

private theorem v4JRow22Coeff39_spec :
    mulCoeffTwo JData V4C3Data 22 39 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 39 0 := by
  decide

private theorem v4JRow22Coeff40_spec :
    mulCoeffTwo JData V4C3Data 22 40 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 40 0 := by
  decide

private theorem v4JRow22Coeff41_spec :
    mulCoeffTwo JData V4C3Data 22 41 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 41 0 := by
  decide

private theorem v4JRow22Coeff42_spec :
    mulCoeffTwo JData V4C3Data 22 42 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 42 0 := by
  decide

private theorem v4JRow22Coeff43_spec :
    mulCoeffTwo JData V4C3Data 22 43 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 43 0 := by
  decide

private theorem v4JRow22Coeff44_spec :
    mulCoeffTwo JData V4C3Data 22 44 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 44 0 := by
  decide

private theorem v4JRow22Coeff45_spec :
    mulCoeffTwo JData V4C3Data 22 45 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 45 0 := by
  decide

private theorem v4JRow22Coeff46_spec :
    mulCoeffTwo JData V4C3Data 22 46 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 46 0 := by
  decide

private theorem v4JRow22Coeff47_spec :
    mulCoeffTwo JData V4C3Data 22 47 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 47 0 := by
  decide

private theorem v4JRow22Coeff48_spec :
    mulCoeffTwo JData V4C3Data 22 48 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 48 0 := by
  decide

private theorem v4JRow22Coeff49_spec :
    mulCoeffTwo JData V4C3Data 22 49 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 49 0 := by
  decide

private theorem v4JRow22Coeff50_spec :
    mulCoeffTwo JData V4C3Data 22 50 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 50 0 := by
  decide

private theorem v4JRow22Coeff51_spec :
    mulCoeffTwo JData V4C3Data 22 51 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 51 0 := by
  decide

private theorem v4JRow22Coeff52_spec :
    mulCoeffTwo JData V4C3Data 22 52 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 52 0 := by
  decide

private theorem v4JRow22Coeff53_spec :
    mulCoeffTwo JData V4C3Data 22 53 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 53 0 := by
  decide

private theorem v4JRow22Coeff54_spec :
    mulCoeffTwo JData V4C3Data 22 54 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 54 0 := by
  decide

private theorem v4JRow22Coeff55_spec :
    mulCoeffTwo JData V4C3Data 22 55 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 55 0 := by
  decide

private theorem v4JRow22Coeff56_spec :
    mulCoeffTwo JData V4C3Data 22 56 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 56 0 := by
  decide

private theorem v4JRow22Coeff57_spec :
    mulCoeffTwo JData V4C3Data 22 57 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 57 0 := by
  decide

private theorem v4JRow22Coeff58_spec :
    mulCoeffTwo JData V4C3Data 22 58 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 58 0 := by
  decide

private theorem v4JRow22Coeff59_spec :
    mulCoeffTwo JData V4C3Data 22 59 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 59 0 := by
  decide

private theorem v4JRow22Coeff60_spec :
    mulCoeffTwo JData V4C3Data 22 60 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 60 0 := by
  decide

private theorem v4JRow22Coeff61_spec :
    mulCoeffTwo JData V4C3Data 22 61 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 61 0 := by
  decide

private theorem v4JRow22Coeff62_spec :
    mulCoeffTwo JData V4C3Data 22 62 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 62 0 := by
  decide

private theorem v4JRow22Coeff63_spec :
    mulCoeffTwo JData V4C3Data 22 63 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 63 0 := by
  decide

private theorem v4JRow22Coeff64_spec :
    mulCoeffTwo JData V4C3Data 22 64 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 64 0 := by
  decide

private theorem v4JRow22Coeff65_spec :
    mulCoeffTwo JData V4C3Data 22 65 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 65 0 := by
  decide

private theorem v4JRow22Coeff66_spec :
    mulCoeffTwo JData V4C3Data 22 66 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 66 0 := by
  decide

private theorem v4JRow22Coeff67_spec :
    mulCoeffTwo JData V4C3Data 22 67 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 67 0 := by
  decide

private theorem v4JRow22Coeff68_spec :
    mulCoeffTwo JData V4C3Data 22 68 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 68 0 := by
  decide

private theorem v4JRow22Coeff69_spec :
    mulCoeffTwo JData V4C3Data 22 69 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 69 0 := by
  decide

private theorem v4JRow22Coeff70_spec :
    mulCoeffTwo JData V4C3Data 22 70 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 70 0 := by
  decide

private theorem v4JRow22Coeff71_spec :
    mulCoeffTwo JData V4C3Data 22 71 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 71 0 := by
  decide

private theorem v4JRow22Coeff72_spec :
    mulCoeffTwo JData V4C3Data 22 72 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 72 0 := by
  decide

private theorem v4JRow22Coeff73_spec :
    mulCoeffTwo JData V4C3Data 22 73 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 73 0 := by
  decide

private theorem v4JRow22Coeff74_spec :
    mulCoeffTwo JData V4C3Data 22 74 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 74 0 := by
  decide

private theorem v4JRow22Coeff75_spec :
    mulCoeffTwo JData V4C3Data 22 75 =
      ((rectangularize 52 76 V4JData).getD 22 []).getD 75 0 := by
  decide

private theorem v4JRow22Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo JData V4C3Data 22 j =
      ((rectangularize 52 76 V4JData).getD 22 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow22Coeff0_spec
  · exact v4JRow22Coeff1_spec
  · exact v4JRow22Coeff2_spec
  · exact v4JRow22Coeff3_spec
  · exact v4JRow22Coeff4_spec
  · exact v4JRow22Coeff5_spec
  · exact v4JRow22Coeff6_spec
  · exact v4JRow22Coeff7_spec
  · exact v4JRow22Coeff8_spec
  · exact v4JRow22Coeff9_spec

private theorem v4JRow22Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo JData V4C3Data 22 j =
      ((rectangularize 52 76 V4JData).getD 22 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow22Coeff10_spec
  · exact v4JRow22Coeff11_spec
  · exact v4JRow22Coeff12_spec
  · exact v4JRow22Coeff13_spec
  · exact v4JRow22Coeff14_spec
  · exact v4JRow22Coeff15_spec
  · exact v4JRow22Coeff16_spec
  · exact v4JRow22Coeff17_spec
  · exact v4JRow22Coeff18_spec
  · exact v4JRow22Coeff19_spec

private theorem v4JRow22Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo JData V4C3Data 22 j =
      ((rectangularize 52 76 V4JData).getD 22 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow22Coeff20_spec
  · exact v4JRow22Coeff21_spec
  · exact v4JRow22Coeff22_spec
  · exact v4JRow22Coeff23_spec
  · exact v4JRow22Coeff24_spec
  · exact v4JRow22Coeff25_spec
  · exact v4JRow22Coeff26_spec
  · exact v4JRow22Coeff27_spec
  · exact v4JRow22Coeff28_spec
  · exact v4JRow22Coeff29_spec

private theorem v4JRow22Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo JData V4C3Data 22 j =
      ((rectangularize 52 76 V4JData).getD 22 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow22Coeff30_spec
  · exact v4JRow22Coeff31_spec
  · exact v4JRow22Coeff32_spec
  · exact v4JRow22Coeff33_spec
  · exact v4JRow22Coeff34_spec
  · exact v4JRow22Coeff35_spec
  · exact v4JRow22Coeff36_spec
  · exact v4JRow22Coeff37_spec
  · exact v4JRow22Coeff38_spec
  · exact v4JRow22Coeff39_spec

private theorem v4JRow22Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo JData V4C3Data 22 j =
      ((rectangularize 52 76 V4JData).getD 22 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow22Coeff40_spec
  · exact v4JRow22Coeff41_spec
  · exact v4JRow22Coeff42_spec
  · exact v4JRow22Coeff43_spec
  · exact v4JRow22Coeff44_spec
  · exact v4JRow22Coeff45_spec
  · exact v4JRow22Coeff46_spec
  · exact v4JRow22Coeff47_spec
  · exact v4JRow22Coeff48_spec
  · exact v4JRow22Coeff49_spec

private theorem v4JRow22Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo JData V4C3Data 22 j =
      ((rectangularize 52 76 V4JData).getD 22 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow22Coeff50_spec
  · exact v4JRow22Coeff51_spec
  · exact v4JRow22Coeff52_spec
  · exact v4JRow22Coeff53_spec
  · exact v4JRow22Coeff54_spec
  · exact v4JRow22Coeff55_spec
  · exact v4JRow22Coeff56_spec
  · exact v4JRow22Coeff57_spec
  · exact v4JRow22Coeff58_spec
  · exact v4JRow22Coeff59_spec

private theorem v4JRow22Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo JData V4C3Data 22 j =
      ((rectangularize 52 76 V4JData).getD 22 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow22Coeff60_spec
  · exact v4JRow22Coeff61_spec
  · exact v4JRow22Coeff62_spec
  · exact v4JRow22Coeff63_spec
  · exact v4JRow22Coeff64_spec
  · exact v4JRow22Coeff65_spec
  · exact v4JRow22Coeff66_spec
  · exact v4JRow22Coeff67_spec
  · exact v4JRow22Coeff68_spec
  · exact v4JRow22Coeff69_spec

private theorem v4JRow22Coeffs70To75_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 76) :
    mulCoeffTwo JData V4C3Data 22 j =
      ((rectangularize 52 76 V4JData).getD 22 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact v4JRow22Coeff70_spec
  · exact v4JRow22Coeff71_spec
  · exact v4JRow22Coeff72_spec
  · exact v4JRow22Coeff73_spec
  · exact v4JRow22Coeff74_spec
  · exact v4JRow22Coeff75_spec

private theorem v4JRow22_coefficients (j : ℕ) (hj : j < 76) :
    mulCoeffTwo JData V4C3Data 22 j =
      ((rectangularize 52 76 V4JData).getD 22 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4JRow22Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4JRow22Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4JRow22Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4JRow22Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4JRow22Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4JRow22Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4JRow22Coeffs60To69_spec j (by omega) h70
  exact v4JRow22Coeffs70To75_spec j (by omega) hj

private theorem v4JRow22_spec :
    padOne 76 (mulRow JData V4C3Data 22) =
      (rectangularize 52 76 V4JData).getD 22 [] := by
  apply padOne_mulRow_eq_of_coefficients 76 JData V4C3Data 22
    ((rectangularize 52 76 V4JData).getD 22 [])
  · decide
  · have hTargetSupport : (V4JData.getD 22 []).length ≤ 76 := by
      decide
    rw [getD_rectangularize 52 76 V4JData 22 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4JRow22_coefficients

private theorem v4JRow23Coeff0_spec :
    mulCoeffTwo JData V4C3Data 23 0 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 0 0 := by
  decide

private theorem v4JRow23Coeff1_spec :
    mulCoeffTwo JData V4C3Data 23 1 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 1 0 := by
  decide

private theorem v4JRow23Coeff2_spec :
    mulCoeffTwo JData V4C3Data 23 2 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 2 0 := by
  decide

private theorem v4JRow23Coeff3_spec :
    mulCoeffTwo JData V4C3Data 23 3 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 3 0 := by
  decide

private theorem v4JRow23Coeff4_spec :
    mulCoeffTwo JData V4C3Data 23 4 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 4 0 := by
  decide

private theorem v4JRow23Coeff5_spec :
    mulCoeffTwo JData V4C3Data 23 5 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 5 0 := by
  decide

private theorem v4JRow23Coeff6_spec :
    mulCoeffTwo JData V4C3Data 23 6 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 6 0 := by
  decide

private theorem v4JRow23Coeff7_spec :
    mulCoeffTwo JData V4C3Data 23 7 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 7 0 := by
  decide

private theorem v4JRow23Coeff8_spec :
    mulCoeffTwo JData V4C3Data 23 8 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 8 0 := by
  decide

private theorem v4JRow23Coeff9_spec :
    mulCoeffTwo JData V4C3Data 23 9 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 9 0 := by
  decide

private theorem v4JRow23Coeff10_spec :
    mulCoeffTwo JData V4C3Data 23 10 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 10 0 := by
  decide

private theorem v4JRow23Coeff11_spec :
    mulCoeffTwo JData V4C3Data 23 11 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 11 0 := by
  decide

private theorem v4JRow23Coeff12_spec :
    mulCoeffTwo JData V4C3Data 23 12 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 12 0 := by
  decide

private theorem v4JRow23Coeff13_spec :
    mulCoeffTwo JData V4C3Data 23 13 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 13 0 := by
  decide

private theorem v4JRow23Coeff14_spec :
    mulCoeffTwo JData V4C3Data 23 14 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 14 0 := by
  decide

private theorem v4JRow23Coeff15_spec :
    mulCoeffTwo JData V4C3Data 23 15 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 15 0 := by
  decide

private theorem v4JRow23Coeff16_spec :
    mulCoeffTwo JData V4C3Data 23 16 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 16 0 := by
  decide

private theorem v4JRow23Coeff17_spec :
    mulCoeffTwo JData V4C3Data 23 17 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 17 0 := by
  decide

private theorem v4JRow23Coeff18_spec :
    mulCoeffTwo JData V4C3Data 23 18 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 18 0 := by
  decide

private theorem v4JRow23Coeff19_spec :
    mulCoeffTwo JData V4C3Data 23 19 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 19 0 := by
  decide

private theorem v4JRow23Coeff20_spec :
    mulCoeffTwo JData V4C3Data 23 20 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 20 0 := by
  decide

private theorem v4JRow23Coeff21_spec :
    mulCoeffTwo JData V4C3Data 23 21 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 21 0 := by
  decide

private theorem v4JRow23Coeff22_spec :
    mulCoeffTwo JData V4C3Data 23 22 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 22 0 := by
  decide

private theorem v4JRow23Coeff23_spec :
    mulCoeffTwo JData V4C3Data 23 23 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 23 0 := by
  decide

private theorem v4JRow23Coeff24_spec :
    mulCoeffTwo JData V4C3Data 23 24 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 24 0 := by
  decide

private theorem v4JRow23Coeff25_spec :
    mulCoeffTwo JData V4C3Data 23 25 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 25 0 := by
  decide

private theorem v4JRow23Coeff26_spec :
    mulCoeffTwo JData V4C3Data 23 26 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 26 0 := by
  decide

private theorem v4JRow23Coeff27_spec :
    mulCoeffTwo JData V4C3Data 23 27 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 27 0 := by
  decide

private theorem v4JRow23Coeff28_spec :
    mulCoeffTwo JData V4C3Data 23 28 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 28 0 := by
  decide

private theorem v4JRow23Coeff29_spec :
    mulCoeffTwo JData V4C3Data 23 29 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 29 0 := by
  decide

private theorem v4JRow23Coeff30_spec :
    mulCoeffTwo JData V4C3Data 23 30 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 30 0 := by
  decide

private theorem v4JRow23Coeff31_spec :
    mulCoeffTwo JData V4C3Data 23 31 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 31 0 := by
  decide

private theorem v4JRow23Coeff32_spec :
    mulCoeffTwo JData V4C3Data 23 32 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 32 0 := by
  decide

private theorem v4JRow23Coeff33_spec :
    mulCoeffTwo JData V4C3Data 23 33 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 33 0 := by
  decide

private theorem v4JRow23Coeff34_spec :
    mulCoeffTwo JData V4C3Data 23 34 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 34 0 := by
  decide

private theorem v4JRow23Coeff35_spec :
    mulCoeffTwo JData V4C3Data 23 35 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 35 0 := by
  decide

private theorem v4JRow23Coeff36_spec :
    mulCoeffTwo JData V4C3Data 23 36 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 36 0 := by
  decide

private theorem v4JRow23Coeff37_spec :
    mulCoeffTwo JData V4C3Data 23 37 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 37 0 := by
  decide

private theorem v4JRow23Coeff38_spec :
    mulCoeffTwo JData V4C3Data 23 38 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 38 0 := by
  decide

private theorem v4JRow23Coeff39_spec :
    mulCoeffTwo JData V4C3Data 23 39 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 39 0 := by
  decide

private theorem v4JRow23Coeff40_spec :
    mulCoeffTwo JData V4C3Data 23 40 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 40 0 := by
  decide

private theorem v4JRow23Coeff41_spec :
    mulCoeffTwo JData V4C3Data 23 41 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 41 0 := by
  decide

private theorem v4JRow23Coeff42_spec :
    mulCoeffTwo JData V4C3Data 23 42 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 42 0 := by
  decide

private theorem v4JRow23Coeff43_spec :
    mulCoeffTwo JData V4C3Data 23 43 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 43 0 := by
  decide

private theorem v4JRow23Coeff44_spec :
    mulCoeffTwo JData V4C3Data 23 44 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 44 0 := by
  decide

private theorem v4JRow23Coeff45_spec :
    mulCoeffTwo JData V4C3Data 23 45 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 45 0 := by
  decide

private theorem v4JRow23Coeff46_spec :
    mulCoeffTwo JData V4C3Data 23 46 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 46 0 := by
  decide

private theorem v4JRow23Coeff47_spec :
    mulCoeffTwo JData V4C3Data 23 47 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 47 0 := by
  decide

private theorem v4JRow23Coeff48_spec :
    mulCoeffTwo JData V4C3Data 23 48 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 48 0 := by
  decide

private theorem v4JRow23Coeff49_spec :
    mulCoeffTwo JData V4C3Data 23 49 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 49 0 := by
  decide

private theorem v4JRow23Coeff50_spec :
    mulCoeffTwo JData V4C3Data 23 50 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 50 0 := by
  decide

private theorem v4JRow23Coeff51_spec :
    mulCoeffTwo JData V4C3Data 23 51 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 51 0 := by
  decide

private theorem v4JRow23Coeff52_spec :
    mulCoeffTwo JData V4C3Data 23 52 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 52 0 := by
  decide

private theorem v4JRow23Coeff53_spec :
    mulCoeffTwo JData V4C3Data 23 53 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 53 0 := by
  decide

private theorem v4JRow23Coeff54_spec :
    mulCoeffTwo JData V4C3Data 23 54 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 54 0 := by
  decide

private theorem v4JRow23Coeff55_spec :
    mulCoeffTwo JData V4C3Data 23 55 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 55 0 := by
  decide

private theorem v4JRow23Coeff56_spec :
    mulCoeffTwo JData V4C3Data 23 56 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 56 0 := by
  decide

private theorem v4JRow23Coeff57_spec :
    mulCoeffTwo JData V4C3Data 23 57 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 57 0 := by
  decide

private theorem v4JRow23Coeff58_spec :
    mulCoeffTwo JData V4C3Data 23 58 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 58 0 := by
  decide

private theorem v4JRow23Coeff59_spec :
    mulCoeffTwo JData V4C3Data 23 59 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 59 0 := by
  decide

private theorem v4JRow23Coeff60_spec :
    mulCoeffTwo JData V4C3Data 23 60 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 60 0 := by
  decide

private theorem v4JRow23Coeff61_spec :
    mulCoeffTwo JData V4C3Data 23 61 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 61 0 := by
  decide

private theorem v4JRow23Coeff62_spec :
    mulCoeffTwo JData V4C3Data 23 62 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 62 0 := by
  decide

private theorem v4JRow23Coeff63_spec :
    mulCoeffTwo JData V4C3Data 23 63 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 63 0 := by
  decide

private theorem v4JRow23Coeff64_spec :
    mulCoeffTwo JData V4C3Data 23 64 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 64 0 := by
  decide

private theorem v4JRow23Coeff65_spec :
    mulCoeffTwo JData V4C3Data 23 65 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 65 0 := by
  decide

private theorem v4JRow23Coeff66_spec :
    mulCoeffTwo JData V4C3Data 23 66 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 66 0 := by
  decide

private theorem v4JRow23Coeff67_spec :
    mulCoeffTwo JData V4C3Data 23 67 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 67 0 := by
  decide

private theorem v4JRow23Coeff68_spec :
    mulCoeffTwo JData V4C3Data 23 68 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 68 0 := by
  decide

private theorem v4JRow23Coeff69_spec :
    mulCoeffTwo JData V4C3Data 23 69 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 69 0 := by
  decide

private theorem v4JRow23Coeff70_spec :
    mulCoeffTwo JData V4C3Data 23 70 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 70 0 := by
  decide

private theorem v4JRow23Coeff71_spec :
    mulCoeffTwo JData V4C3Data 23 71 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 71 0 := by
  decide

private theorem v4JRow23Coeff72_spec :
    mulCoeffTwo JData V4C3Data 23 72 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 72 0 := by
  decide

private theorem v4JRow23Coeff73_spec :
    mulCoeffTwo JData V4C3Data 23 73 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 73 0 := by
  decide

private theorem v4JRow23Coeff74_spec :
    mulCoeffTwo JData V4C3Data 23 74 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 74 0 := by
  decide

private theorem v4JRow23Coeff75_spec :
    mulCoeffTwo JData V4C3Data 23 75 =
      ((rectangularize 52 76 V4JData).getD 23 []).getD 75 0 := by
  decide

private theorem v4JRow23Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo JData V4C3Data 23 j =
      ((rectangularize 52 76 V4JData).getD 23 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow23Coeff0_spec
  · exact v4JRow23Coeff1_spec
  · exact v4JRow23Coeff2_spec
  · exact v4JRow23Coeff3_spec
  · exact v4JRow23Coeff4_spec
  · exact v4JRow23Coeff5_spec
  · exact v4JRow23Coeff6_spec
  · exact v4JRow23Coeff7_spec
  · exact v4JRow23Coeff8_spec
  · exact v4JRow23Coeff9_spec

private theorem v4JRow23Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo JData V4C3Data 23 j =
      ((rectangularize 52 76 V4JData).getD 23 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow23Coeff10_spec
  · exact v4JRow23Coeff11_spec
  · exact v4JRow23Coeff12_spec
  · exact v4JRow23Coeff13_spec
  · exact v4JRow23Coeff14_spec
  · exact v4JRow23Coeff15_spec
  · exact v4JRow23Coeff16_spec
  · exact v4JRow23Coeff17_spec
  · exact v4JRow23Coeff18_spec
  · exact v4JRow23Coeff19_spec

private theorem v4JRow23Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo JData V4C3Data 23 j =
      ((rectangularize 52 76 V4JData).getD 23 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow23Coeff20_spec
  · exact v4JRow23Coeff21_spec
  · exact v4JRow23Coeff22_spec
  · exact v4JRow23Coeff23_spec
  · exact v4JRow23Coeff24_spec
  · exact v4JRow23Coeff25_spec
  · exact v4JRow23Coeff26_spec
  · exact v4JRow23Coeff27_spec
  · exact v4JRow23Coeff28_spec
  · exact v4JRow23Coeff29_spec

private theorem v4JRow23Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo JData V4C3Data 23 j =
      ((rectangularize 52 76 V4JData).getD 23 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow23Coeff30_spec
  · exact v4JRow23Coeff31_spec
  · exact v4JRow23Coeff32_spec
  · exact v4JRow23Coeff33_spec
  · exact v4JRow23Coeff34_spec
  · exact v4JRow23Coeff35_spec
  · exact v4JRow23Coeff36_spec
  · exact v4JRow23Coeff37_spec
  · exact v4JRow23Coeff38_spec
  · exact v4JRow23Coeff39_spec

private theorem v4JRow23Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo JData V4C3Data 23 j =
      ((rectangularize 52 76 V4JData).getD 23 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow23Coeff40_spec
  · exact v4JRow23Coeff41_spec
  · exact v4JRow23Coeff42_spec
  · exact v4JRow23Coeff43_spec
  · exact v4JRow23Coeff44_spec
  · exact v4JRow23Coeff45_spec
  · exact v4JRow23Coeff46_spec
  · exact v4JRow23Coeff47_spec
  · exact v4JRow23Coeff48_spec
  · exact v4JRow23Coeff49_spec

private theorem v4JRow23Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo JData V4C3Data 23 j =
      ((rectangularize 52 76 V4JData).getD 23 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow23Coeff50_spec
  · exact v4JRow23Coeff51_spec
  · exact v4JRow23Coeff52_spec
  · exact v4JRow23Coeff53_spec
  · exact v4JRow23Coeff54_spec
  · exact v4JRow23Coeff55_spec
  · exact v4JRow23Coeff56_spec
  · exact v4JRow23Coeff57_spec
  · exact v4JRow23Coeff58_spec
  · exact v4JRow23Coeff59_spec

private theorem v4JRow23Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo JData V4C3Data 23 j =
      ((rectangularize 52 76 V4JData).getD 23 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow23Coeff60_spec
  · exact v4JRow23Coeff61_spec
  · exact v4JRow23Coeff62_spec
  · exact v4JRow23Coeff63_spec
  · exact v4JRow23Coeff64_spec
  · exact v4JRow23Coeff65_spec
  · exact v4JRow23Coeff66_spec
  · exact v4JRow23Coeff67_spec
  · exact v4JRow23Coeff68_spec
  · exact v4JRow23Coeff69_spec

private theorem v4JRow23Coeffs70To75_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 76) :
    mulCoeffTwo JData V4C3Data 23 j =
      ((rectangularize 52 76 V4JData).getD 23 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact v4JRow23Coeff70_spec
  · exact v4JRow23Coeff71_spec
  · exact v4JRow23Coeff72_spec
  · exact v4JRow23Coeff73_spec
  · exact v4JRow23Coeff74_spec
  · exact v4JRow23Coeff75_spec

private theorem v4JRow23_coefficients (j : ℕ) (hj : j < 76) :
    mulCoeffTwo JData V4C3Data 23 j =
      ((rectangularize 52 76 V4JData).getD 23 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4JRow23Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4JRow23Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4JRow23Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4JRow23Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4JRow23Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4JRow23Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4JRow23Coeffs60To69_spec j (by omega) h70
  exact v4JRow23Coeffs70To75_spec j (by omega) hj

private theorem v4JRow23_spec :
    padOne 76 (mulRow JData V4C3Data 23) =
      (rectangularize 52 76 V4JData).getD 23 [] := by
  apply padOne_mulRow_eq_of_coefficients 76 JData V4C3Data 23
    ((rectangularize 52 76 V4JData).getD 23 [])
  · decide
  · have hTargetSupport : (V4JData.getD 23 []).length ≤ 76 := by
      decide
    rw [getD_rectangularize 52 76 V4JData 23 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4JRow23_coefficients

private theorem v4JRow24Coeff0_spec :
    mulCoeffTwo JData V4C3Data 24 0 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 0 0 := by
  decide

private theorem v4JRow24Coeff1_spec :
    mulCoeffTwo JData V4C3Data 24 1 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 1 0 := by
  decide

private theorem v4JRow24Coeff2_spec :
    mulCoeffTwo JData V4C3Data 24 2 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 2 0 := by
  decide

private theorem v4JRow24Coeff3_spec :
    mulCoeffTwo JData V4C3Data 24 3 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 3 0 := by
  decide

private theorem v4JRow24Coeff4_spec :
    mulCoeffTwo JData V4C3Data 24 4 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 4 0 := by
  decide

private theorem v4JRow24Coeff5_spec :
    mulCoeffTwo JData V4C3Data 24 5 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 5 0 := by
  decide

private theorem v4JRow24Coeff6_spec :
    mulCoeffTwo JData V4C3Data 24 6 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 6 0 := by
  decide

private theorem v4JRow24Coeff7_spec :
    mulCoeffTwo JData V4C3Data 24 7 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 7 0 := by
  decide

private theorem v4JRow24Coeff8_spec :
    mulCoeffTwo JData V4C3Data 24 8 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 8 0 := by
  decide

private theorem v4JRow24Coeff9_spec :
    mulCoeffTwo JData V4C3Data 24 9 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 9 0 := by
  decide

private theorem v4JRow24Coeff10_spec :
    mulCoeffTwo JData V4C3Data 24 10 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 10 0 := by
  decide

private theorem v4JRow24Coeff11_spec :
    mulCoeffTwo JData V4C3Data 24 11 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 11 0 := by
  decide

private theorem v4JRow24Coeff12_spec :
    mulCoeffTwo JData V4C3Data 24 12 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 12 0 := by
  decide

private theorem v4JRow24Coeff13_spec :
    mulCoeffTwo JData V4C3Data 24 13 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 13 0 := by
  decide

private theorem v4JRow24Coeff14_spec :
    mulCoeffTwo JData V4C3Data 24 14 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 14 0 := by
  decide

private theorem v4JRow24Coeff15_spec :
    mulCoeffTwo JData V4C3Data 24 15 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 15 0 := by
  decide

private theorem v4JRow24Coeff16_spec :
    mulCoeffTwo JData V4C3Data 24 16 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 16 0 := by
  decide

private theorem v4JRow24Coeff17_spec :
    mulCoeffTwo JData V4C3Data 24 17 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 17 0 := by
  decide

private theorem v4JRow24Coeff18_spec :
    mulCoeffTwo JData V4C3Data 24 18 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 18 0 := by
  decide

private theorem v4JRow24Coeff19_spec :
    mulCoeffTwo JData V4C3Data 24 19 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 19 0 := by
  decide

private theorem v4JRow24Coeff20_spec :
    mulCoeffTwo JData V4C3Data 24 20 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 20 0 := by
  decide

private theorem v4JRow24Coeff21_spec :
    mulCoeffTwo JData V4C3Data 24 21 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 21 0 := by
  decide

private theorem v4JRow24Coeff22_spec :
    mulCoeffTwo JData V4C3Data 24 22 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 22 0 := by
  decide

private theorem v4JRow24Coeff23_spec :
    mulCoeffTwo JData V4C3Data 24 23 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 23 0 := by
  decide

private theorem v4JRow24Coeff24_spec :
    mulCoeffTwo JData V4C3Data 24 24 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 24 0 := by
  decide

private theorem v4JRow24Coeff25_spec :
    mulCoeffTwo JData V4C3Data 24 25 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 25 0 := by
  decide

private theorem v4JRow24Coeff26_spec :
    mulCoeffTwo JData V4C3Data 24 26 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 26 0 := by
  decide

private theorem v4JRow24Coeff27_spec :
    mulCoeffTwo JData V4C3Data 24 27 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 27 0 := by
  decide

private theorem v4JRow24Coeff28_spec :
    mulCoeffTwo JData V4C3Data 24 28 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 28 0 := by
  decide

private theorem v4JRow24Coeff29_spec :
    mulCoeffTwo JData V4C3Data 24 29 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 29 0 := by
  decide

private theorem v4JRow24Coeff30_spec :
    mulCoeffTwo JData V4C3Data 24 30 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 30 0 := by
  decide

private theorem v4JRow24Coeff31_spec :
    mulCoeffTwo JData V4C3Data 24 31 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 31 0 := by
  decide

private theorem v4JRow24Coeff32_spec :
    mulCoeffTwo JData V4C3Data 24 32 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 32 0 := by
  decide

private theorem v4JRow24Coeff33_spec :
    mulCoeffTwo JData V4C3Data 24 33 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 33 0 := by
  decide

private theorem v4JRow24Coeff34_spec :
    mulCoeffTwo JData V4C3Data 24 34 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 34 0 := by
  decide

private theorem v4JRow24Coeff35_spec :
    mulCoeffTwo JData V4C3Data 24 35 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 35 0 := by
  decide

private theorem v4JRow24Coeff36_spec :
    mulCoeffTwo JData V4C3Data 24 36 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 36 0 := by
  decide

private theorem v4JRow24Coeff37_spec :
    mulCoeffTwo JData V4C3Data 24 37 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 37 0 := by
  decide

private theorem v4JRow24Coeff38_spec :
    mulCoeffTwo JData V4C3Data 24 38 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 38 0 := by
  decide

private theorem v4JRow24Coeff39_spec :
    mulCoeffTwo JData V4C3Data 24 39 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 39 0 := by
  decide

private theorem v4JRow24Coeff40_spec :
    mulCoeffTwo JData V4C3Data 24 40 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 40 0 := by
  decide

private theorem v4JRow24Coeff41_spec :
    mulCoeffTwo JData V4C3Data 24 41 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 41 0 := by
  decide

private theorem v4JRow24Coeff42_spec :
    mulCoeffTwo JData V4C3Data 24 42 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 42 0 := by
  decide

private theorem v4JRow24Coeff43_spec :
    mulCoeffTwo JData V4C3Data 24 43 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 43 0 := by
  decide

private theorem v4JRow24Coeff44_spec :
    mulCoeffTwo JData V4C3Data 24 44 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 44 0 := by
  decide

private theorem v4JRow24Coeff45_spec :
    mulCoeffTwo JData V4C3Data 24 45 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 45 0 := by
  decide

private theorem v4JRow24Coeff46_spec :
    mulCoeffTwo JData V4C3Data 24 46 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 46 0 := by
  decide

private theorem v4JRow24Coeff47_spec :
    mulCoeffTwo JData V4C3Data 24 47 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 47 0 := by
  decide

private theorem v4JRow24Coeff48_spec :
    mulCoeffTwo JData V4C3Data 24 48 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 48 0 := by
  decide

private theorem v4JRow24Coeff49_spec :
    mulCoeffTwo JData V4C3Data 24 49 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 49 0 := by
  decide

private theorem v4JRow24Coeff50_spec :
    mulCoeffTwo JData V4C3Data 24 50 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 50 0 := by
  decide

private theorem v4JRow24Coeff51_spec :
    mulCoeffTwo JData V4C3Data 24 51 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 51 0 := by
  decide

private theorem v4JRow24Coeff52_spec :
    mulCoeffTwo JData V4C3Data 24 52 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 52 0 := by
  decide

private theorem v4JRow24Coeff53_spec :
    mulCoeffTwo JData V4C3Data 24 53 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 53 0 := by
  decide

private theorem v4JRow24Coeff54_spec :
    mulCoeffTwo JData V4C3Data 24 54 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 54 0 := by
  decide

private theorem v4JRow24Coeff55_spec :
    mulCoeffTwo JData V4C3Data 24 55 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 55 0 := by
  decide

private theorem v4JRow24Coeff56_spec :
    mulCoeffTwo JData V4C3Data 24 56 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 56 0 := by
  decide

private theorem v4JRow24Coeff57_spec :
    mulCoeffTwo JData V4C3Data 24 57 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 57 0 := by
  decide

private theorem v4JRow24Coeff58_spec :
    mulCoeffTwo JData V4C3Data 24 58 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 58 0 := by
  decide

private theorem v4JRow24Coeff59_spec :
    mulCoeffTwo JData V4C3Data 24 59 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 59 0 := by
  decide

private theorem v4JRow24Coeff60_spec :
    mulCoeffTwo JData V4C3Data 24 60 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 60 0 := by
  decide

private theorem v4JRow24Coeff61_spec :
    mulCoeffTwo JData V4C3Data 24 61 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 61 0 := by
  decide

private theorem v4JRow24Coeff62_spec :
    mulCoeffTwo JData V4C3Data 24 62 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 62 0 := by
  decide

private theorem v4JRow24Coeff63_spec :
    mulCoeffTwo JData V4C3Data 24 63 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 63 0 := by
  decide

private theorem v4JRow24Coeff64_spec :
    mulCoeffTwo JData V4C3Data 24 64 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 64 0 := by
  decide

private theorem v4JRow24Coeff65_spec :
    mulCoeffTwo JData V4C3Data 24 65 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 65 0 := by
  decide

private theorem v4JRow24Coeff66_spec :
    mulCoeffTwo JData V4C3Data 24 66 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 66 0 := by
  decide

private theorem v4JRow24Coeff67_spec :
    mulCoeffTwo JData V4C3Data 24 67 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 67 0 := by
  decide

private theorem v4JRow24Coeff68_spec :
    mulCoeffTwo JData V4C3Data 24 68 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 68 0 := by
  decide

private theorem v4JRow24Coeff69_spec :
    mulCoeffTwo JData V4C3Data 24 69 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 69 0 := by
  decide

private theorem v4JRow24Coeff70_spec :
    mulCoeffTwo JData V4C3Data 24 70 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 70 0 := by
  decide

private theorem v4JRow24Coeff71_spec :
    mulCoeffTwo JData V4C3Data 24 71 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 71 0 := by
  decide

private theorem v4JRow24Coeff72_spec :
    mulCoeffTwo JData V4C3Data 24 72 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 72 0 := by
  decide

private theorem v4JRow24Coeff73_spec :
    mulCoeffTwo JData V4C3Data 24 73 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 73 0 := by
  decide

private theorem v4JRow24Coeff74_spec :
    mulCoeffTwo JData V4C3Data 24 74 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 74 0 := by
  decide

private theorem v4JRow24Coeff75_spec :
    mulCoeffTwo JData V4C3Data 24 75 =
      ((rectangularize 52 76 V4JData).getD 24 []).getD 75 0 := by
  decide

private theorem v4JRow24Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo JData V4C3Data 24 j =
      ((rectangularize 52 76 V4JData).getD 24 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow24Coeff0_spec
  · exact v4JRow24Coeff1_spec
  · exact v4JRow24Coeff2_spec
  · exact v4JRow24Coeff3_spec
  · exact v4JRow24Coeff4_spec
  · exact v4JRow24Coeff5_spec
  · exact v4JRow24Coeff6_spec
  · exact v4JRow24Coeff7_spec
  · exact v4JRow24Coeff8_spec
  · exact v4JRow24Coeff9_spec

private theorem v4JRow24Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo JData V4C3Data 24 j =
      ((rectangularize 52 76 V4JData).getD 24 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow24Coeff10_spec
  · exact v4JRow24Coeff11_spec
  · exact v4JRow24Coeff12_spec
  · exact v4JRow24Coeff13_spec
  · exact v4JRow24Coeff14_spec
  · exact v4JRow24Coeff15_spec
  · exact v4JRow24Coeff16_spec
  · exact v4JRow24Coeff17_spec
  · exact v4JRow24Coeff18_spec
  · exact v4JRow24Coeff19_spec

private theorem v4JRow24Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo JData V4C3Data 24 j =
      ((rectangularize 52 76 V4JData).getD 24 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow24Coeff20_spec
  · exact v4JRow24Coeff21_spec
  · exact v4JRow24Coeff22_spec
  · exact v4JRow24Coeff23_spec
  · exact v4JRow24Coeff24_spec
  · exact v4JRow24Coeff25_spec
  · exact v4JRow24Coeff26_spec
  · exact v4JRow24Coeff27_spec
  · exact v4JRow24Coeff28_spec
  · exact v4JRow24Coeff29_spec

private theorem v4JRow24Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo JData V4C3Data 24 j =
      ((rectangularize 52 76 V4JData).getD 24 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow24Coeff30_spec
  · exact v4JRow24Coeff31_spec
  · exact v4JRow24Coeff32_spec
  · exact v4JRow24Coeff33_spec
  · exact v4JRow24Coeff34_spec
  · exact v4JRow24Coeff35_spec
  · exact v4JRow24Coeff36_spec
  · exact v4JRow24Coeff37_spec
  · exact v4JRow24Coeff38_spec
  · exact v4JRow24Coeff39_spec

private theorem v4JRow24Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo JData V4C3Data 24 j =
      ((rectangularize 52 76 V4JData).getD 24 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow24Coeff40_spec
  · exact v4JRow24Coeff41_spec
  · exact v4JRow24Coeff42_spec
  · exact v4JRow24Coeff43_spec
  · exact v4JRow24Coeff44_spec
  · exact v4JRow24Coeff45_spec
  · exact v4JRow24Coeff46_spec
  · exact v4JRow24Coeff47_spec
  · exact v4JRow24Coeff48_spec
  · exact v4JRow24Coeff49_spec

private theorem v4JRow24Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo JData V4C3Data 24 j =
      ((rectangularize 52 76 V4JData).getD 24 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow24Coeff50_spec
  · exact v4JRow24Coeff51_spec
  · exact v4JRow24Coeff52_spec
  · exact v4JRow24Coeff53_spec
  · exact v4JRow24Coeff54_spec
  · exact v4JRow24Coeff55_spec
  · exact v4JRow24Coeff56_spec
  · exact v4JRow24Coeff57_spec
  · exact v4JRow24Coeff58_spec
  · exact v4JRow24Coeff59_spec

private theorem v4JRow24Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo JData V4C3Data 24 j =
      ((rectangularize 52 76 V4JData).getD 24 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow24Coeff60_spec
  · exact v4JRow24Coeff61_spec
  · exact v4JRow24Coeff62_spec
  · exact v4JRow24Coeff63_spec
  · exact v4JRow24Coeff64_spec
  · exact v4JRow24Coeff65_spec
  · exact v4JRow24Coeff66_spec
  · exact v4JRow24Coeff67_spec
  · exact v4JRow24Coeff68_spec
  · exact v4JRow24Coeff69_spec

private theorem v4JRow24Coeffs70To75_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 76) :
    mulCoeffTwo JData V4C3Data 24 j =
      ((rectangularize 52 76 V4JData).getD 24 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact v4JRow24Coeff70_spec
  · exact v4JRow24Coeff71_spec
  · exact v4JRow24Coeff72_spec
  · exact v4JRow24Coeff73_spec
  · exact v4JRow24Coeff74_spec
  · exact v4JRow24Coeff75_spec

private theorem v4JRow24_coefficients (j : ℕ) (hj : j < 76) :
    mulCoeffTwo JData V4C3Data 24 j =
      ((rectangularize 52 76 V4JData).getD 24 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4JRow24Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4JRow24Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4JRow24Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4JRow24Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4JRow24Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4JRow24Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4JRow24Coeffs60To69_spec j (by omega) h70
  exact v4JRow24Coeffs70To75_spec j (by omega) hj

private theorem v4JRow24_spec :
    padOne 76 (mulRow JData V4C3Data 24) =
      (rectangularize 52 76 V4JData).getD 24 [] := by
  apply padOne_mulRow_eq_of_coefficients 76 JData V4C3Data 24
    ((rectangularize 52 76 V4JData).getD 24 [])
  · decide
  · have hTargetSupport : (V4JData.getD 24 []).length ≤ 76 := by
      decide
    rw [getD_rectangularize 52 76 V4JData 24 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4JRow24_coefficients

private theorem v4JRow25Coeff0_spec :
    mulCoeffTwo JData V4C3Data 25 0 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 0 0 := by
  decide

private theorem v4JRow25Coeff1_spec :
    mulCoeffTwo JData V4C3Data 25 1 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 1 0 := by
  decide

private theorem v4JRow25Coeff2_spec :
    mulCoeffTwo JData V4C3Data 25 2 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 2 0 := by
  decide

private theorem v4JRow25Coeff3_spec :
    mulCoeffTwo JData V4C3Data 25 3 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 3 0 := by
  decide

private theorem v4JRow25Coeff4_spec :
    mulCoeffTwo JData V4C3Data 25 4 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 4 0 := by
  decide

private theorem v4JRow25Coeff5_spec :
    mulCoeffTwo JData V4C3Data 25 5 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 5 0 := by
  decide

private theorem v4JRow25Coeff6_spec :
    mulCoeffTwo JData V4C3Data 25 6 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 6 0 := by
  decide

private theorem v4JRow25Coeff7_spec :
    mulCoeffTwo JData V4C3Data 25 7 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 7 0 := by
  decide

private theorem v4JRow25Coeff8_spec :
    mulCoeffTwo JData V4C3Data 25 8 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 8 0 := by
  decide

private theorem v4JRow25Coeff9_spec :
    mulCoeffTwo JData V4C3Data 25 9 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 9 0 := by
  decide

private theorem v4JRow25Coeff10_spec :
    mulCoeffTwo JData V4C3Data 25 10 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 10 0 := by
  decide

private theorem v4JRow25Coeff11_spec :
    mulCoeffTwo JData V4C3Data 25 11 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 11 0 := by
  decide

private theorem v4JRow25Coeff12_spec :
    mulCoeffTwo JData V4C3Data 25 12 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 12 0 := by
  decide

private theorem v4JRow25Coeff13_spec :
    mulCoeffTwo JData V4C3Data 25 13 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 13 0 := by
  decide

private theorem v4JRow25Coeff14_spec :
    mulCoeffTwo JData V4C3Data 25 14 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 14 0 := by
  decide

private theorem v4JRow25Coeff15_spec :
    mulCoeffTwo JData V4C3Data 25 15 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 15 0 := by
  decide

private theorem v4JRow25Coeff16_spec :
    mulCoeffTwo JData V4C3Data 25 16 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 16 0 := by
  decide

private theorem v4JRow25Coeff17_spec :
    mulCoeffTwo JData V4C3Data 25 17 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 17 0 := by
  decide

private theorem v4JRow25Coeff18_spec :
    mulCoeffTwo JData V4C3Data 25 18 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 18 0 := by
  decide

private theorem v4JRow25Coeff19_spec :
    mulCoeffTwo JData V4C3Data 25 19 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 19 0 := by
  decide

private theorem v4JRow25Coeff20_spec :
    mulCoeffTwo JData V4C3Data 25 20 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 20 0 := by
  decide

private theorem v4JRow25Coeff21_spec :
    mulCoeffTwo JData V4C3Data 25 21 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 21 0 := by
  decide

private theorem v4JRow25Coeff22_spec :
    mulCoeffTwo JData V4C3Data 25 22 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 22 0 := by
  decide

private theorem v4JRow25Coeff23_spec :
    mulCoeffTwo JData V4C3Data 25 23 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 23 0 := by
  decide

private theorem v4JRow25Coeff24_spec :
    mulCoeffTwo JData V4C3Data 25 24 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 24 0 := by
  decide

private theorem v4JRow25Coeff25_spec :
    mulCoeffTwo JData V4C3Data 25 25 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 25 0 := by
  decide

private theorem v4JRow25Coeff26_spec :
    mulCoeffTwo JData V4C3Data 25 26 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 26 0 := by
  decide

private theorem v4JRow25Coeff27_spec :
    mulCoeffTwo JData V4C3Data 25 27 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 27 0 := by
  decide

private theorem v4JRow25Coeff28_spec :
    mulCoeffTwo JData V4C3Data 25 28 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 28 0 := by
  decide

private theorem v4JRow25Coeff29_spec :
    mulCoeffTwo JData V4C3Data 25 29 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 29 0 := by
  decide

private theorem v4JRow25Coeff30_spec :
    mulCoeffTwo JData V4C3Data 25 30 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 30 0 := by
  decide

private theorem v4JRow25Coeff31_spec :
    mulCoeffTwo JData V4C3Data 25 31 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 31 0 := by
  decide

private theorem v4JRow25Coeff32_spec :
    mulCoeffTwo JData V4C3Data 25 32 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 32 0 := by
  decide

private theorem v4JRow25Coeff33_spec :
    mulCoeffTwo JData V4C3Data 25 33 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 33 0 := by
  decide

private theorem v4JRow25Coeff34_spec :
    mulCoeffTwo JData V4C3Data 25 34 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 34 0 := by
  decide

private theorem v4JRow25Coeff35_spec :
    mulCoeffTwo JData V4C3Data 25 35 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 35 0 := by
  decide

private theorem v4JRow25Coeff36_spec :
    mulCoeffTwo JData V4C3Data 25 36 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 36 0 := by
  decide

private theorem v4JRow25Coeff37_spec :
    mulCoeffTwo JData V4C3Data 25 37 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 37 0 := by
  decide

private theorem v4JRow25Coeff38_spec :
    mulCoeffTwo JData V4C3Data 25 38 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 38 0 := by
  decide

private theorem v4JRow25Coeff39_spec :
    mulCoeffTwo JData V4C3Data 25 39 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 39 0 := by
  decide

private theorem v4JRow25Coeff40_spec :
    mulCoeffTwo JData V4C3Data 25 40 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 40 0 := by
  decide

private theorem v4JRow25Coeff41_spec :
    mulCoeffTwo JData V4C3Data 25 41 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 41 0 := by
  decide

private theorem v4JRow25Coeff42_spec :
    mulCoeffTwo JData V4C3Data 25 42 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 42 0 := by
  decide

private theorem v4JRow25Coeff43_spec :
    mulCoeffTwo JData V4C3Data 25 43 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 43 0 := by
  decide

private theorem v4JRow25Coeff44_spec :
    mulCoeffTwo JData V4C3Data 25 44 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 44 0 := by
  decide

private theorem v4JRow25Coeff45_spec :
    mulCoeffTwo JData V4C3Data 25 45 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 45 0 := by
  decide

private theorem v4JRow25Coeff46_spec :
    mulCoeffTwo JData V4C3Data 25 46 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 46 0 := by
  decide

private theorem v4JRow25Coeff47_spec :
    mulCoeffTwo JData V4C3Data 25 47 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 47 0 := by
  decide

private theorem v4JRow25Coeff48_spec :
    mulCoeffTwo JData V4C3Data 25 48 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 48 0 := by
  decide

private theorem v4JRow25Coeff49_spec :
    mulCoeffTwo JData V4C3Data 25 49 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 49 0 := by
  decide

private theorem v4JRow25Coeff50_spec :
    mulCoeffTwo JData V4C3Data 25 50 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 50 0 := by
  decide

private theorem v4JRow25Coeff51_spec :
    mulCoeffTwo JData V4C3Data 25 51 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 51 0 := by
  decide

private theorem v4JRow25Coeff52_spec :
    mulCoeffTwo JData V4C3Data 25 52 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 52 0 := by
  decide

private theorem v4JRow25Coeff53_spec :
    mulCoeffTwo JData V4C3Data 25 53 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 53 0 := by
  decide

private theorem v4JRow25Coeff54_spec :
    mulCoeffTwo JData V4C3Data 25 54 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 54 0 := by
  decide

private theorem v4JRow25Coeff55_spec :
    mulCoeffTwo JData V4C3Data 25 55 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 55 0 := by
  decide

private theorem v4JRow25Coeff56_spec :
    mulCoeffTwo JData V4C3Data 25 56 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 56 0 := by
  decide

private theorem v4JRow25Coeff57_spec :
    mulCoeffTwo JData V4C3Data 25 57 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 57 0 := by
  decide

private theorem v4JRow25Coeff58_spec :
    mulCoeffTwo JData V4C3Data 25 58 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 58 0 := by
  decide

private theorem v4JRow25Coeff59_spec :
    mulCoeffTwo JData V4C3Data 25 59 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 59 0 := by
  decide

private theorem v4JRow25Coeff60_spec :
    mulCoeffTwo JData V4C3Data 25 60 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 60 0 := by
  decide

private theorem v4JRow25Coeff61_spec :
    mulCoeffTwo JData V4C3Data 25 61 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 61 0 := by
  decide

private theorem v4JRow25Coeff62_spec :
    mulCoeffTwo JData V4C3Data 25 62 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 62 0 := by
  decide

private theorem v4JRow25Coeff63_spec :
    mulCoeffTwo JData V4C3Data 25 63 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 63 0 := by
  decide

private theorem v4JRow25Coeff64_spec :
    mulCoeffTwo JData V4C3Data 25 64 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 64 0 := by
  decide

private theorem v4JRow25Coeff65_spec :
    mulCoeffTwo JData V4C3Data 25 65 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 65 0 := by
  decide

private theorem v4JRow25Coeff66_spec :
    mulCoeffTwo JData V4C3Data 25 66 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 66 0 := by
  decide

private theorem v4JRow25Coeff67_spec :
    mulCoeffTwo JData V4C3Data 25 67 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 67 0 := by
  decide

private theorem v4JRow25Coeff68_spec :
    mulCoeffTwo JData V4C3Data 25 68 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 68 0 := by
  decide

private theorem v4JRow25Coeff69_spec :
    mulCoeffTwo JData V4C3Data 25 69 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 69 0 := by
  decide

private theorem v4JRow25Coeff70_spec :
    mulCoeffTwo JData V4C3Data 25 70 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 70 0 := by
  decide

private theorem v4JRow25Coeff71_spec :
    mulCoeffTwo JData V4C3Data 25 71 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 71 0 := by
  decide

private theorem v4JRow25Coeff72_spec :
    mulCoeffTwo JData V4C3Data 25 72 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 72 0 := by
  decide

private theorem v4JRow25Coeff73_spec :
    mulCoeffTwo JData V4C3Data 25 73 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 73 0 := by
  decide

private theorem v4JRow25Coeff74_spec :
    mulCoeffTwo JData V4C3Data 25 74 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 74 0 := by
  decide

private theorem v4JRow25Coeff75_spec :
    mulCoeffTwo JData V4C3Data 25 75 =
      ((rectangularize 52 76 V4JData).getD 25 []).getD 75 0 := by
  decide

private theorem v4JRow25Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo JData V4C3Data 25 j =
      ((rectangularize 52 76 V4JData).getD 25 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow25Coeff0_spec
  · exact v4JRow25Coeff1_spec
  · exact v4JRow25Coeff2_spec
  · exact v4JRow25Coeff3_spec
  · exact v4JRow25Coeff4_spec
  · exact v4JRow25Coeff5_spec
  · exact v4JRow25Coeff6_spec
  · exact v4JRow25Coeff7_spec
  · exact v4JRow25Coeff8_spec
  · exact v4JRow25Coeff9_spec

private theorem v4JRow25Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo JData V4C3Data 25 j =
      ((rectangularize 52 76 V4JData).getD 25 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow25Coeff10_spec
  · exact v4JRow25Coeff11_spec
  · exact v4JRow25Coeff12_spec
  · exact v4JRow25Coeff13_spec
  · exact v4JRow25Coeff14_spec
  · exact v4JRow25Coeff15_spec
  · exact v4JRow25Coeff16_spec
  · exact v4JRow25Coeff17_spec
  · exact v4JRow25Coeff18_spec
  · exact v4JRow25Coeff19_spec

private theorem v4JRow25Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo JData V4C3Data 25 j =
      ((rectangularize 52 76 V4JData).getD 25 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow25Coeff20_spec
  · exact v4JRow25Coeff21_spec
  · exact v4JRow25Coeff22_spec
  · exact v4JRow25Coeff23_spec
  · exact v4JRow25Coeff24_spec
  · exact v4JRow25Coeff25_spec
  · exact v4JRow25Coeff26_spec
  · exact v4JRow25Coeff27_spec
  · exact v4JRow25Coeff28_spec
  · exact v4JRow25Coeff29_spec

private theorem v4JRow25Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo JData V4C3Data 25 j =
      ((rectangularize 52 76 V4JData).getD 25 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow25Coeff30_spec
  · exact v4JRow25Coeff31_spec
  · exact v4JRow25Coeff32_spec
  · exact v4JRow25Coeff33_spec
  · exact v4JRow25Coeff34_spec
  · exact v4JRow25Coeff35_spec
  · exact v4JRow25Coeff36_spec
  · exact v4JRow25Coeff37_spec
  · exact v4JRow25Coeff38_spec
  · exact v4JRow25Coeff39_spec

private theorem v4JRow25Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo JData V4C3Data 25 j =
      ((rectangularize 52 76 V4JData).getD 25 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow25Coeff40_spec
  · exact v4JRow25Coeff41_spec
  · exact v4JRow25Coeff42_spec
  · exact v4JRow25Coeff43_spec
  · exact v4JRow25Coeff44_spec
  · exact v4JRow25Coeff45_spec
  · exact v4JRow25Coeff46_spec
  · exact v4JRow25Coeff47_spec
  · exact v4JRow25Coeff48_spec
  · exact v4JRow25Coeff49_spec

private theorem v4JRow25Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo JData V4C3Data 25 j =
      ((rectangularize 52 76 V4JData).getD 25 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow25Coeff50_spec
  · exact v4JRow25Coeff51_spec
  · exact v4JRow25Coeff52_spec
  · exact v4JRow25Coeff53_spec
  · exact v4JRow25Coeff54_spec
  · exact v4JRow25Coeff55_spec
  · exact v4JRow25Coeff56_spec
  · exact v4JRow25Coeff57_spec
  · exact v4JRow25Coeff58_spec
  · exact v4JRow25Coeff59_spec

private theorem v4JRow25Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo JData V4C3Data 25 j =
      ((rectangularize 52 76 V4JData).getD 25 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow25Coeff60_spec
  · exact v4JRow25Coeff61_spec
  · exact v4JRow25Coeff62_spec
  · exact v4JRow25Coeff63_spec
  · exact v4JRow25Coeff64_spec
  · exact v4JRow25Coeff65_spec
  · exact v4JRow25Coeff66_spec
  · exact v4JRow25Coeff67_spec
  · exact v4JRow25Coeff68_spec
  · exact v4JRow25Coeff69_spec

private theorem v4JRow25Coeffs70To75_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 76) :
    mulCoeffTwo JData V4C3Data 25 j =
      ((rectangularize 52 76 V4JData).getD 25 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact v4JRow25Coeff70_spec
  · exact v4JRow25Coeff71_spec
  · exact v4JRow25Coeff72_spec
  · exact v4JRow25Coeff73_spec
  · exact v4JRow25Coeff74_spec
  · exact v4JRow25Coeff75_spec

private theorem v4JRow25_coefficients (j : ℕ) (hj : j < 76) :
    mulCoeffTwo JData V4C3Data 25 j =
      ((rectangularize 52 76 V4JData).getD 25 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4JRow25Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4JRow25Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4JRow25Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4JRow25Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4JRow25Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4JRow25Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4JRow25Coeffs60To69_spec j (by omega) h70
  exact v4JRow25Coeffs70To75_spec j (by omega) hj

private theorem v4JRow25_spec :
    padOne 76 (mulRow JData V4C3Data 25) =
      (rectangularize 52 76 V4JData).getD 25 [] := by
  apply padOne_mulRow_eq_of_coefficients 76 JData V4C3Data 25
    ((rectangularize 52 76 V4JData).getD 25 [])
  · decide
  · have hTargetSupport : (V4JData.getD 25 []).length ≤ 76 := by
      decide
    rw [getD_rectangularize 52 76 V4JData 25 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4JRow25_coefficients

private theorem v4JRow26Coeff0_spec :
    mulCoeffTwo JData V4C3Data 26 0 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 0 0 := by
  decide

private theorem v4JRow26Coeff1_spec :
    mulCoeffTwo JData V4C3Data 26 1 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 1 0 := by
  decide

private theorem v4JRow26Coeff2_spec :
    mulCoeffTwo JData V4C3Data 26 2 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 2 0 := by
  decide

private theorem v4JRow26Coeff3_spec :
    mulCoeffTwo JData V4C3Data 26 3 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 3 0 := by
  decide

private theorem v4JRow26Coeff4_spec :
    mulCoeffTwo JData V4C3Data 26 4 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 4 0 := by
  decide

private theorem v4JRow26Coeff5_spec :
    mulCoeffTwo JData V4C3Data 26 5 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 5 0 := by
  decide

private theorem v4JRow26Coeff6_spec :
    mulCoeffTwo JData V4C3Data 26 6 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 6 0 := by
  decide

private theorem v4JRow26Coeff7_spec :
    mulCoeffTwo JData V4C3Data 26 7 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 7 0 := by
  decide

private theorem v4JRow26Coeff8_spec :
    mulCoeffTwo JData V4C3Data 26 8 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 8 0 := by
  decide

private theorem v4JRow26Coeff9_spec :
    mulCoeffTwo JData V4C3Data 26 9 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 9 0 := by
  decide

private theorem v4JRow26Coeff10_spec :
    mulCoeffTwo JData V4C3Data 26 10 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 10 0 := by
  decide

private theorem v4JRow26Coeff11_spec :
    mulCoeffTwo JData V4C3Data 26 11 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 11 0 := by
  decide

private theorem v4JRow26Coeff12_spec :
    mulCoeffTwo JData V4C3Data 26 12 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 12 0 := by
  decide

private theorem v4JRow26Coeff13_spec :
    mulCoeffTwo JData V4C3Data 26 13 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 13 0 := by
  decide

private theorem v4JRow26Coeff14_spec :
    mulCoeffTwo JData V4C3Data 26 14 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 14 0 := by
  decide

private theorem v4JRow26Coeff15_spec :
    mulCoeffTwo JData V4C3Data 26 15 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 15 0 := by
  decide

private theorem v4JRow26Coeff16_spec :
    mulCoeffTwo JData V4C3Data 26 16 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 16 0 := by
  decide

private theorem v4JRow26Coeff17_spec :
    mulCoeffTwo JData V4C3Data 26 17 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 17 0 := by
  decide

private theorem v4JRow26Coeff18_spec :
    mulCoeffTwo JData V4C3Data 26 18 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 18 0 := by
  decide

private theorem v4JRow26Coeff19_spec :
    mulCoeffTwo JData V4C3Data 26 19 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 19 0 := by
  decide

private theorem v4JRow26Coeff20_spec :
    mulCoeffTwo JData V4C3Data 26 20 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 20 0 := by
  decide

private theorem v4JRow26Coeff21_spec :
    mulCoeffTwo JData V4C3Data 26 21 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 21 0 := by
  decide

private theorem v4JRow26Coeff22_spec :
    mulCoeffTwo JData V4C3Data 26 22 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 22 0 := by
  decide

private theorem v4JRow26Coeff23_spec :
    mulCoeffTwo JData V4C3Data 26 23 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 23 0 := by
  decide

private theorem v4JRow26Coeff24_spec :
    mulCoeffTwo JData V4C3Data 26 24 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 24 0 := by
  decide

private theorem v4JRow26Coeff25_spec :
    mulCoeffTwo JData V4C3Data 26 25 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 25 0 := by
  decide

private theorem v4JRow26Coeff26_spec :
    mulCoeffTwo JData V4C3Data 26 26 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 26 0 := by
  decide

private theorem v4JRow26Coeff27_spec :
    mulCoeffTwo JData V4C3Data 26 27 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 27 0 := by
  decide

private theorem v4JRow26Coeff28_spec :
    mulCoeffTwo JData V4C3Data 26 28 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 28 0 := by
  decide

private theorem v4JRow26Coeff29_spec :
    mulCoeffTwo JData V4C3Data 26 29 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 29 0 := by
  decide

private theorem v4JRow26Coeff30_spec :
    mulCoeffTwo JData V4C3Data 26 30 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 30 0 := by
  decide

private theorem v4JRow26Coeff31_spec :
    mulCoeffTwo JData V4C3Data 26 31 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 31 0 := by
  decide

private theorem v4JRow26Coeff32_spec :
    mulCoeffTwo JData V4C3Data 26 32 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 32 0 := by
  decide

private theorem v4JRow26Coeff33_spec :
    mulCoeffTwo JData V4C3Data 26 33 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 33 0 := by
  decide

private theorem v4JRow26Coeff34_spec :
    mulCoeffTwo JData V4C3Data 26 34 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 34 0 := by
  decide

private theorem v4JRow26Coeff35_spec :
    mulCoeffTwo JData V4C3Data 26 35 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 35 0 := by
  decide

private theorem v4JRow26Coeff36_spec :
    mulCoeffTwo JData V4C3Data 26 36 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 36 0 := by
  decide

private theorem v4JRow26Coeff37_spec :
    mulCoeffTwo JData V4C3Data 26 37 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 37 0 := by
  decide

private theorem v4JRow26Coeff38_spec :
    mulCoeffTwo JData V4C3Data 26 38 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 38 0 := by
  decide

private theorem v4JRow26Coeff39_spec :
    mulCoeffTwo JData V4C3Data 26 39 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 39 0 := by
  decide

private theorem v4JRow26Coeff40_spec :
    mulCoeffTwo JData V4C3Data 26 40 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 40 0 := by
  decide

private theorem v4JRow26Coeff41_spec :
    mulCoeffTwo JData V4C3Data 26 41 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 41 0 := by
  decide

private theorem v4JRow26Coeff42_spec :
    mulCoeffTwo JData V4C3Data 26 42 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 42 0 := by
  decide

private theorem v4JRow26Coeff43_spec :
    mulCoeffTwo JData V4C3Data 26 43 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 43 0 := by
  decide

private theorem v4JRow26Coeff44_spec :
    mulCoeffTwo JData V4C3Data 26 44 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 44 0 := by
  decide

private theorem v4JRow26Coeff45_spec :
    mulCoeffTwo JData V4C3Data 26 45 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 45 0 := by
  decide

private theorem v4JRow26Coeff46_spec :
    mulCoeffTwo JData V4C3Data 26 46 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 46 0 := by
  decide

private theorem v4JRow26Coeff47_spec :
    mulCoeffTwo JData V4C3Data 26 47 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 47 0 := by
  decide

private theorem v4JRow26Coeff48_spec :
    mulCoeffTwo JData V4C3Data 26 48 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 48 0 := by
  decide

private theorem v4JRow26Coeff49_spec :
    mulCoeffTwo JData V4C3Data 26 49 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 49 0 := by
  decide

private theorem v4JRow26Coeff50_spec :
    mulCoeffTwo JData V4C3Data 26 50 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 50 0 := by
  decide

private theorem v4JRow26Coeff51_spec :
    mulCoeffTwo JData V4C3Data 26 51 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 51 0 := by
  decide

private theorem v4JRow26Coeff52_spec :
    mulCoeffTwo JData V4C3Data 26 52 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 52 0 := by
  decide

private theorem v4JRow26Coeff53_spec :
    mulCoeffTwo JData V4C3Data 26 53 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 53 0 := by
  decide

private theorem v4JRow26Coeff54_spec :
    mulCoeffTwo JData V4C3Data 26 54 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 54 0 := by
  decide

private theorem v4JRow26Coeff55_spec :
    mulCoeffTwo JData V4C3Data 26 55 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 55 0 := by
  decide

private theorem v4JRow26Coeff56_spec :
    mulCoeffTwo JData V4C3Data 26 56 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 56 0 := by
  decide

private theorem v4JRow26Coeff57_spec :
    mulCoeffTwo JData V4C3Data 26 57 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 57 0 := by
  decide

private theorem v4JRow26Coeff58_spec :
    mulCoeffTwo JData V4C3Data 26 58 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 58 0 := by
  decide

private theorem v4JRow26Coeff59_spec :
    mulCoeffTwo JData V4C3Data 26 59 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 59 0 := by
  decide

private theorem v4JRow26Coeff60_spec :
    mulCoeffTwo JData V4C3Data 26 60 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 60 0 := by
  decide

private theorem v4JRow26Coeff61_spec :
    mulCoeffTwo JData V4C3Data 26 61 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 61 0 := by
  decide

private theorem v4JRow26Coeff62_spec :
    mulCoeffTwo JData V4C3Data 26 62 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 62 0 := by
  decide

private theorem v4JRow26Coeff63_spec :
    mulCoeffTwo JData V4C3Data 26 63 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 63 0 := by
  decide

private theorem v4JRow26Coeff64_spec :
    mulCoeffTwo JData V4C3Data 26 64 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 64 0 := by
  decide

private theorem v4JRow26Coeff65_spec :
    mulCoeffTwo JData V4C3Data 26 65 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 65 0 := by
  decide

private theorem v4JRow26Coeff66_spec :
    mulCoeffTwo JData V4C3Data 26 66 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 66 0 := by
  decide

private theorem v4JRow26Coeff67_spec :
    mulCoeffTwo JData V4C3Data 26 67 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 67 0 := by
  decide

private theorem v4JRow26Coeff68_spec :
    mulCoeffTwo JData V4C3Data 26 68 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 68 0 := by
  decide

private theorem v4JRow26Coeff69_spec :
    mulCoeffTwo JData V4C3Data 26 69 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 69 0 := by
  decide

private theorem v4JRow26Coeff70_spec :
    mulCoeffTwo JData V4C3Data 26 70 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 70 0 := by
  decide

private theorem v4JRow26Coeff71_spec :
    mulCoeffTwo JData V4C3Data 26 71 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 71 0 := by
  decide

private theorem v4JRow26Coeff72_spec :
    mulCoeffTwo JData V4C3Data 26 72 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 72 0 := by
  decide

private theorem v4JRow26Coeff73_spec :
    mulCoeffTwo JData V4C3Data 26 73 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 73 0 := by
  decide

private theorem v4JRow26Coeff74_spec :
    mulCoeffTwo JData V4C3Data 26 74 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 74 0 := by
  decide

private theorem v4JRow26Coeff75_spec :
    mulCoeffTwo JData V4C3Data 26 75 =
      ((rectangularize 52 76 V4JData).getD 26 []).getD 75 0 := by
  decide

private theorem v4JRow26Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo JData V4C3Data 26 j =
      ((rectangularize 52 76 V4JData).getD 26 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow26Coeff0_spec
  · exact v4JRow26Coeff1_spec
  · exact v4JRow26Coeff2_spec
  · exact v4JRow26Coeff3_spec
  · exact v4JRow26Coeff4_spec
  · exact v4JRow26Coeff5_spec
  · exact v4JRow26Coeff6_spec
  · exact v4JRow26Coeff7_spec
  · exact v4JRow26Coeff8_spec
  · exact v4JRow26Coeff9_spec

private theorem v4JRow26Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo JData V4C3Data 26 j =
      ((rectangularize 52 76 V4JData).getD 26 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow26Coeff10_spec
  · exact v4JRow26Coeff11_spec
  · exact v4JRow26Coeff12_spec
  · exact v4JRow26Coeff13_spec
  · exact v4JRow26Coeff14_spec
  · exact v4JRow26Coeff15_spec
  · exact v4JRow26Coeff16_spec
  · exact v4JRow26Coeff17_spec
  · exact v4JRow26Coeff18_spec
  · exact v4JRow26Coeff19_spec

private theorem v4JRow26Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo JData V4C3Data 26 j =
      ((rectangularize 52 76 V4JData).getD 26 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow26Coeff20_spec
  · exact v4JRow26Coeff21_spec
  · exact v4JRow26Coeff22_spec
  · exact v4JRow26Coeff23_spec
  · exact v4JRow26Coeff24_spec
  · exact v4JRow26Coeff25_spec
  · exact v4JRow26Coeff26_spec
  · exact v4JRow26Coeff27_spec
  · exact v4JRow26Coeff28_spec
  · exact v4JRow26Coeff29_spec

private theorem v4JRow26Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo JData V4C3Data 26 j =
      ((rectangularize 52 76 V4JData).getD 26 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow26Coeff30_spec
  · exact v4JRow26Coeff31_spec
  · exact v4JRow26Coeff32_spec
  · exact v4JRow26Coeff33_spec
  · exact v4JRow26Coeff34_spec
  · exact v4JRow26Coeff35_spec
  · exact v4JRow26Coeff36_spec
  · exact v4JRow26Coeff37_spec
  · exact v4JRow26Coeff38_spec
  · exact v4JRow26Coeff39_spec

private theorem v4JRow26Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo JData V4C3Data 26 j =
      ((rectangularize 52 76 V4JData).getD 26 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow26Coeff40_spec
  · exact v4JRow26Coeff41_spec
  · exact v4JRow26Coeff42_spec
  · exact v4JRow26Coeff43_spec
  · exact v4JRow26Coeff44_spec
  · exact v4JRow26Coeff45_spec
  · exact v4JRow26Coeff46_spec
  · exact v4JRow26Coeff47_spec
  · exact v4JRow26Coeff48_spec
  · exact v4JRow26Coeff49_spec

private theorem v4JRow26Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo JData V4C3Data 26 j =
      ((rectangularize 52 76 V4JData).getD 26 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow26Coeff50_spec
  · exact v4JRow26Coeff51_spec
  · exact v4JRow26Coeff52_spec
  · exact v4JRow26Coeff53_spec
  · exact v4JRow26Coeff54_spec
  · exact v4JRow26Coeff55_spec
  · exact v4JRow26Coeff56_spec
  · exact v4JRow26Coeff57_spec
  · exact v4JRow26Coeff58_spec
  · exact v4JRow26Coeff59_spec

private theorem v4JRow26Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo JData V4C3Data 26 j =
      ((rectangularize 52 76 V4JData).getD 26 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow26Coeff60_spec
  · exact v4JRow26Coeff61_spec
  · exact v4JRow26Coeff62_spec
  · exact v4JRow26Coeff63_spec
  · exact v4JRow26Coeff64_spec
  · exact v4JRow26Coeff65_spec
  · exact v4JRow26Coeff66_spec
  · exact v4JRow26Coeff67_spec
  · exact v4JRow26Coeff68_spec
  · exact v4JRow26Coeff69_spec

private theorem v4JRow26Coeffs70To75_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 76) :
    mulCoeffTwo JData V4C3Data 26 j =
      ((rectangularize 52 76 V4JData).getD 26 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact v4JRow26Coeff70_spec
  · exact v4JRow26Coeff71_spec
  · exact v4JRow26Coeff72_spec
  · exact v4JRow26Coeff73_spec
  · exact v4JRow26Coeff74_spec
  · exact v4JRow26Coeff75_spec

private theorem v4JRow26_coefficients (j : ℕ) (hj : j < 76) :
    mulCoeffTwo JData V4C3Data 26 j =
      ((rectangularize 52 76 V4JData).getD 26 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4JRow26Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4JRow26Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4JRow26Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4JRow26Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4JRow26Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4JRow26Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4JRow26Coeffs60To69_spec j (by omega) h70
  exact v4JRow26Coeffs70To75_spec j (by omega) hj

private theorem v4JRow26_spec :
    padOne 76 (mulRow JData V4C3Data 26) =
      (rectangularize 52 76 V4JData).getD 26 [] := by
  apply padOne_mulRow_eq_of_coefficients 76 JData V4C3Data 26
    ((rectangularize 52 76 V4JData).getD 26 [])
  · decide
  · have hTargetSupport : (V4JData.getD 26 []).length ≤ 76 := by
      decide
    rw [getD_rectangularize 52 76 V4JData 26 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4JRow26_coefficients

private theorem v4JRow27Coeff0_spec :
    mulCoeffTwo JData V4C3Data 27 0 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 0 0 := by
  decide

private theorem v4JRow27Coeff1_spec :
    mulCoeffTwo JData V4C3Data 27 1 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 1 0 := by
  decide

private theorem v4JRow27Coeff2_spec :
    mulCoeffTwo JData V4C3Data 27 2 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 2 0 := by
  decide

private theorem v4JRow27Coeff3_spec :
    mulCoeffTwo JData V4C3Data 27 3 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 3 0 := by
  decide

private theorem v4JRow27Coeff4_spec :
    mulCoeffTwo JData V4C3Data 27 4 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 4 0 := by
  decide

private theorem v4JRow27Coeff5_spec :
    mulCoeffTwo JData V4C3Data 27 5 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 5 0 := by
  decide

private theorem v4JRow27Coeff6_spec :
    mulCoeffTwo JData V4C3Data 27 6 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 6 0 := by
  decide

private theorem v4JRow27Coeff7_spec :
    mulCoeffTwo JData V4C3Data 27 7 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 7 0 := by
  decide

private theorem v4JRow27Coeff8_spec :
    mulCoeffTwo JData V4C3Data 27 8 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 8 0 := by
  decide

private theorem v4JRow27Coeff9_spec :
    mulCoeffTwo JData V4C3Data 27 9 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 9 0 := by
  decide

private theorem v4JRow27Coeff10_spec :
    mulCoeffTwo JData V4C3Data 27 10 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 10 0 := by
  decide

private theorem v4JRow27Coeff11_spec :
    mulCoeffTwo JData V4C3Data 27 11 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 11 0 := by
  decide

private theorem v4JRow27Coeff12_spec :
    mulCoeffTwo JData V4C3Data 27 12 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 12 0 := by
  decide

private theorem v4JRow27Coeff13_spec :
    mulCoeffTwo JData V4C3Data 27 13 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 13 0 := by
  decide

private theorem v4JRow27Coeff14_spec :
    mulCoeffTwo JData V4C3Data 27 14 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 14 0 := by
  decide

private theorem v4JRow27Coeff15_spec :
    mulCoeffTwo JData V4C3Data 27 15 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 15 0 := by
  decide

private theorem v4JRow27Coeff16_spec :
    mulCoeffTwo JData V4C3Data 27 16 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 16 0 := by
  decide

private theorem v4JRow27Coeff17_spec :
    mulCoeffTwo JData V4C3Data 27 17 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 17 0 := by
  decide

private theorem v4JRow27Coeff18_spec :
    mulCoeffTwo JData V4C3Data 27 18 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 18 0 := by
  decide

private theorem v4JRow27Coeff19_spec :
    mulCoeffTwo JData V4C3Data 27 19 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 19 0 := by
  decide

private theorem v4JRow27Coeff20_spec :
    mulCoeffTwo JData V4C3Data 27 20 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 20 0 := by
  decide

private theorem v4JRow27Coeff21_spec :
    mulCoeffTwo JData V4C3Data 27 21 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 21 0 := by
  decide

private theorem v4JRow27Coeff22_spec :
    mulCoeffTwo JData V4C3Data 27 22 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 22 0 := by
  decide

private theorem v4JRow27Coeff23_spec :
    mulCoeffTwo JData V4C3Data 27 23 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 23 0 := by
  decide

private theorem v4JRow27Coeff24_spec :
    mulCoeffTwo JData V4C3Data 27 24 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 24 0 := by
  decide

private theorem v4JRow27Coeff25_spec :
    mulCoeffTwo JData V4C3Data 27 25 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 25 0 := by
  decide

private theorem v4JRow27Coeff26_spec :
    mulCoeffTwo JData V4C3Data 27 26 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 26 0 := by
  decide

private theorem v4JRow27Coeff27_spec :
    mulCoeffTwo JData V4C3Data 27 27 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 27 0 := by
  decide

private theorem v4JRow27Coeff28_spec :
    mulCoeffTwo JData V4C3Data 27 28 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 28 0 := by
  decide

private theorem v4JRow27Coeff29_spec :
    mulCoeffTwo JData V4C3Data 27 29 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 29 0 := by
  decide

private theorem v4JRow27Coeff30_spec :
    mulCoeffTwo JData V4C3Data 27 30 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 30 0 := by
  decide

private theorem v4JRow27Coeff31_spec :
    mulCoeffTwo JData V4C3Data 27 31 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 31 0 := by
  decide

private theorem v4JRow27Coeff32_spec :
    mulCoeffTwo JData V4C3Data 27 32 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 32 0 := by
  decide

private theorem v4JRow27Coeff33_spec :
    mulCoeffTwo JData V4C3Data 27 33 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 33 0 := by
  decide

private theorem v4JRow27Coeff34_spec :
    mulCoeffTwo JData V4C3Data 27 34 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 34 0 := by
  decide

private theorem v4JRow27Coeff35_spec :
    mulCoeffTwo JData V4C3Data 27 35 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 35 0 := by
  decide

private theorem v4JRow27Coeff36_spec :
    mulCoeffTwo JData V4C3Data 27 36 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 36 0 := by
  decide

private theorem v4JRow27Coeff37_spec :
    mulCoeffTwo JData V4C3Data 27 37 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 37 0 := by
  decide

private theorem v4JRow27Coeff38_spec :
    mulCoeffTwo JData V4C3Data 27 38 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 38 0 := by
  decide

private theorem v4JRow27Coeff39_spec :
    mulCoeffTwo JData V4C3Data 27 39 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 39 0 := by
  decide

private theorem v4JRow27Coeff40_spec :
    mulCoeffTwo JData V4C3Data 27 40 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 40 0 := by
  decide

private theorem v4JRow27Coeff41_spec :
    mulCoeffTwo JData V4C3Data 27 41 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 41 0 := by
  decide

private theorem v4JRow27Coeff42_spec :
    mulCoeffTwo JData V4C3Data 27 42 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 42 0 := by
  decide

private theorem v4JRow27Coeff43_spec :
    mulCoeffTwo JData V4C3Data 27 43 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 43 0 := by
  decide

private theorem v4JRow27Coeff44_spec :
    mulCoeffTwo JData V4C3Data 27 44 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 44 0 := by
  decide

private theorem v4JRow27Coeff45_spec :
    mulCoeffTwo JData V4C3Data 27 45 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 45 0 := by
  decide

private theorem v4JRow27Coeff46_spec :
    mulCoeffTwo JData V4C3Data 27 46 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 46 0 := by
  decide

private theorem v4JRow27Coeff47_spec :
    mulCoeffTwo JData V4C3Data 27 47 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 47 0 := by
  decide

private theorem v4JRow27Coeff48_spec :
    mulCoeffTwo JData V4C3Data 27 48 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 48 0 := by
  decide

private theorem v4JRow27Coeff49_spec :
    mulCoeffTwo JData V4C3Data 27 49 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 49 0 := by
  decide

private theorem v4JRow27Coeff50_spec :
    mulCoeffTwo JData V4C3Data 27 50 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 50 0 := by
  decide

private theorem v4JRow27Coeff51_spec :
    mulCoeffTwo JData V4C3Data 27 51 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 51 0 := by
  decide

private theorem v4JRow27Coeff52_spec :
    mulCoeffTwo JData V4C3Data 27 52 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 52 0 := by
  decide

private theorem v4JRow27Coeff53_spec :
    mulCoeffTwo JData V4C3Data 27 53 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 53 0 := by
  decide

private theorem v4JRow27Coeff54_spec :
    mulCoeffTwo JData V4C3Data 27 54 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 54 0 := by
  decide

private theorem v4JRow27Coeff55_spec :
    mulCoeffTwo JData V4C3Data 27 55 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 55 0 := by
  decide

private theorem v4JRow27Coeff56_spec :
    mulCoeffTwo JData V4C3Data 27 56 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 56 0 := by
  decide

private theorem v4JRow27Coeff57_spec :
    mulCoeffTwo JData V4C3Data 27 57 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 57 0 := by
  decide

private theorem v4JRow27Coeff58_spec :
    mulCoeffTwo JData V4C3Data 27 58 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 58 0 := by
  decide

private theorem v4JRow27Coeff59_spec :
    mulCoeffTwo JData V4C3Data 27 59 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 59 0 := by
  decide

private theorem v4JRow27Coeff60_spec :
    mulCoeffTwo JData V4C3Data 27 60 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 60 0 := by
  decide

private theorem v4JRow27Coeff61_spec :
    mulCoeffTwo JData V4C3Data 27 61 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 61 0 := by
  decide

private theorem v4JRow27Coeff62_spec :
    mulCoeffTwo JData V4C3Data 27 62 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 62 0 := by
  decide

private theorem v4JRow27Coeff63_spec :
    mulCoeffTwo JData V4C3Data 27 63 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 63 0 := by
  decide

private theorem v4JRow27Coeff64_spec :
    mulCoeffTwo JData V4C3Data 27 64 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 64 0 := by
  decide

private theorem v4JRow27Coeff65_spec :
    mulCoeffTwo JData V4C3Data 27 65 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 65 0 := by
  decide

private theorem v4JRow27Coeff66_spec :
    mulCoeffTwo JData V4C3Data 27 66 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 66 0 := by
  decide

private theorem v4JRow27Coeff67_spec :
    mulCoeffTwo JData V4C3Data 27 67 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 67 0 := by
  decide

private theorem v4JRow27Coeff68_spec :
    mulCoeffTwo JData V4C3Data 27 68 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 68 0 := by
  decide

private theorem v4JRow27Coeff69_spec :
    mulCoeffTwo JData V4C3Data 27 69 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 69 0 := by
  decide

private theorem v4JRow27Coeff70_spec :
    mulCoeffTwo JData V4C3Data 27 70 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 70 0 := by
  decide

private theorem v4JRow27Coeff71_spec :
    mulCoeffTwo JData V4C3Data 27 71 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 71 0 := by
  decide

private theorem v4JRow27Coeff72_spec :
    mulCoeffTwo JData V4C3Data 27 72 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 72 0 := by
  decide

private theorem v4JRow27Coeff73_spec :
    mulCoeffTwo JData V4C3Data 27 73 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 73 0 := by
  decide

private theorem v4JRow27Coeff74_spec :
    mulCoeffTwo JData V4C3Data 27 74 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 74 0 := by
  decide

private theorem v4JRow27Coeff75_spec :
    mulCoeffTwo JData V4C3Data 27 75 =
      ((rectangularize 52 76 V4JData).getD 27 []).getD 75 0 := by
  decide

private theorem v4JRow27Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo JData V4C3Data 27 j =
      ((rectangularize 52 76 V4JData).getD 27 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow27Coeff0_spec
  · exact v4JRow27Coeff1_spec
  · exact v4JRow27Coeff2_spec
  · exact v4JRow27Coeff3_spec
  · exact v4JRow27Coeff4_spec
  · exact v4JRow27Coeff5_spec
  · exact v4JRow27Coeff6_spec
  · exact v4JRow27Coeff7_spec
  · exact v4JRow27Coeff8_spec
  · exact v4JRow27Coeff9_spec

private theorem v4JRow27Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo JData V4C3Data 27 j =
      ((rectangularize 52 76 V4JData).getD 27 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow27Coeff10_spec
  · exact v4JRow27Coeff11_spec
  · exact v4JRow27Coeff12_spec
  · exact v4JRow27Coeff13_spec
  · exact v4JRow27Coeff14_spec
  · exact v4JRow27Coeff15_spec
  · exact v4JRow27Coeff16_spec
  · exact v4JRow27Coeff17_spec
  · exact v4JRow27Coeff18_spec
  · exact v4JRow27Coeff19_spec

private theorem v4JRow27Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo JData V4C3Data 27 j =
      ((rectangularize 52 76 V4JData).getD 27 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow27Coeff20_spec
  · exact v4JRow27Coeff21_spec
  · exact v4JRow27Coeff22_spec
  · exact v4JRow27Coeff23_spec
  · exact v4JRow27Coeff24_spec
  · exact v4JRow27Coeff25_spec
  · exact v4JRow27Coeff26_spec
  · exact v4JRow27Coeff27_spec
  · exact v4JRow27Coeff28_spec
  · exact v4JRow27Coeff29_spec

private theorem v4JRow27Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo JData V4C3Data 27 j =
      ((rectangularize 52 76 V4JData).getD 27 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow27Coeff30_spec
  · exact v4JRow27Coeff31_spec
  · exact v4JRow27Coeff32_spec
  · exact v4JRow27Coeff33_spec
  · exact v4JRow27Coeff34_spec
  · exact v4JRow27Coeff35_spec
  · exact v4JRow27Coeff36_spec
  · exact v4JRow27Coeff37_spec
  · exact v4JRow27Coeff38_spec
  · exact v4JRow27Coeff39_spec

private theorem v4JRow27Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo JData V4C3Data 27 j =
      ((rectangularize 52 76 V4JData).getD 27 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow27Coeff40_spec
  · exact v4JRow27Coeff41_spec
  · exact v4JRow27Coeff42_spec
  · exact v4JRow27Coeff43_spec
  · exact v4JRow27Coeff44_spec
  · exact v4JRow27Coeff45_spec
  · exact v4JRow27Coeff46_spec
  · exact v4JRow27Coeff47_spec
  · exact v4JRow27Coeff48_spec
  · exact v4JRow27Coeff49_spec

private theorem v4JRow27Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo JData V4C3Data 27 j =
      ((rectangularize 52 76 V4JData).getD 27 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow27Coeff50_spec
  · exact v4JRow27Coeff51_spec
  · exact v4JRow27Coeff52_spec
  · exact v4JRow27Coeff53_spec
  · exact v4JRow27Coeff54_spec
  · exact v4JRow27Coeff55_spec
  · exact v4JRow27Coeff56_spec
  · exact v4JRow27Coeff57_spec
  · exact v4JRow27Coeff58_spec
  · exact v4JRow27Coeff59_spec

private theorem v4JRow27Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo JData V4C3Data 27 j =
      ((rectangularize 52 76 V4JData).getD 27 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow27Coeff60_spec
  · exact v4JRow27Coeff61_spec
  · exact v4JRow27Coeff62_spec
  · exact v4JRow27Coeff63_spec
  · exact v4JRow27Coeff64_spec
  · exact v4JRow27Coeff65_spec
  · exact v4JRow27Coeff66_spec
  · exact v4JRow27Coeff67_spec
  · exact v4JRow27Coeff68_spec
  · exact v4JRow27Coeff69_spec

private theorem v4JRow27Coeffs70To75_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 76) :
    mulCoeffTwo JData V4C3Data 27 j =
      ((rectangularize 52 76 V4JData).getD 27 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact v4JRow27Coeff70_spec
  · exact v4JRow27Coeff71_spec
  · exact v4JRow27Coeff72_spec
  · exact v4JRow27Coeff73_spec
  · exact v4JRow27Coeff74_spec
  · exact v4JRow27Coeff75_spec

private theorem v4JRow27_coefficients (j : ℕ) (hj : j < 76) :
    mulCoeffTwo JData V4C3Data 27 j =
      ((rectangularize 52 76 V4JData).getD 27 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4JRow27Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4JRow27Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4JRow27Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4JRow27Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4JRow27Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4JRow27Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4JRow27Coeffs60To69_spec j (by omega) h70
  exact v4JRow27Coeffs70To75_spec j (by omega) hj

private theorem v4JRow27_spec :
    padOne 76 (mulRow JData V4C3Data 27) =
      (rectangularize 52 76 V4JData).getD 27 [] := by
  apply padOne_mulRow_eq_of_coefficients 76 JData V4C3Data 27
    ((rectangularize 52 76 V4JData).getD 27 [])
  · decide
  · have hTargetSupport : (V4JData.getD 27 []).length ≤ 76 := by
      decide
    rw [getD_rectangularize 52 76 V4JData 27 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4JRow27_coefficients

private theorem v4JRow28Coeff0_spec :
    mulCoeffTwo JData V4C3Data 28 0 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 0 0 := by
  decide

private theorem v4JRow28Coeff1_spec :
    mulCoeffTwo JData V4C3Data 28 1 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 1 0 := by
  decide

private theorem v4JRow28Coeff2_spec :
    mulCoeffTwo JData V4C3Data 28 2 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 2 0 := by
  decide

private theorem v4JRow28Coeff3_spec :
    mulCoeffTwo JData V4C3Data 28 3 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 3 0 := by
  decide

private theorem v4JRow28Coeff4_spec :
    mulCoeffTwo JData V4C3Data 28 4 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 4 0 := by
  decide

private theorem v4JRow28Coeff5_spec :
    mulCoeffTwo JData V4C3Data 28 5 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 5 0 := by
  decide

private theorem v4JRow28Coeff6_spec :
    mulCoeffTwo JData V4C3Data 28 6 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 6 0 := by
  decide

private theorem v4JRow28Coeff7_spec :
    mulCoeffTwo JData V4C3Data 28 7 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 7 0 := by
  decide

private theorem v4JRow28Coeff8_spec :
    mulCoeffTwo JData V4C3Data 28 8 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 8 0 := by
  decide

private theorem v4JRow28Coeff9_spec :
    mulCoeffTwo JData V4C3Data 28 9 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 9 0 := by
  decide

private theorem v4JRow28Coeff10_spec :
    mulCoeffTwo JData V4C3Data 28 10 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 10 0 := by
  decide

private theorem v4JRow28Coeff11_spec :
    mulCoeffTwo JData V4C3Data 28 11 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 11 0 := by
  decide

private theorem v4JRow28Coeff12_spec :
    mulCoeffTwo JData V4C3Data 28 12 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 12 0 := by
  decide

private theorem v4JRow28Coeff13_spec :
    mulCoeffTwo JData V4C3Data 28 13 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 13 0 := by
  decide

private theorem v4JRow28Coeff14_spec :
    mulCoeffTwo JData V4C3Data 28 14 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 14 0 := by
  decide

private theorem v4JRow28Coeff15_spec :
    mulCoeffTwo JData V4C3Data 28 15 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 15 0 := by
  decide

private theorem v4JRow28Coeff16_spec :
    mulCoeffTwo JData V4C3Data 28 16 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 16 0 := by
  decide

private theorem v4JRow28Coeff17_spec :
    mulCoeffTwo JData V4C3Data 28 17 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 17 0 := by
  decide

private theorem v4JRow28Coeff18_spec :
    mulCoeffTwo JData V4C3Data 28 18 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 18 0 := by
  decide

private theorem v4JRow28Coeff19_spec :
    mulCoeffTwo JData V4C3Data 28 19 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 19 0 := by
  decide

private theorem v4JRow28Coeff20_spec :
    mulCoeffTwo JData V4C3Data 28 20 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 20 0 := by
  decide

private theorem v4JRow28Coeff21_spec :
    mulCoeffTwo JData V4C3Data 28 21 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 21 0 := by
  decide

private theorem v4JRow28Coeff22_spec :
    mulCoeffTwo JData V4C3Data 28 22 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 22 0 := by
  decide

private theorem v4JRow28Coeff23_spec :
    mulCoeffTwo JData V4C3Data 28 23 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 23 0 := by
  decide

private theorem v4JRow28Coeff24_spec :
    mulCoeffTwo JData V4C3Data 28 24 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 24 0 := by
  decide

private theorem v4JRow28Coeff25_spec :
    mulCoeffTwo JData V4C3Data 28 25 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 25 0 := by
  decide

private theorem v4JRow28Coeff26_spec :
    mulCoeffTwo JData V4C3Data 28 26 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 26 0 := by
  decide

private theorem v4JRow28Coeff27_spec :
    mulCoeffTwo JData V4C3Data 28 27 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 27 0 := by
  decide

private theorem v4JRow28Coeff28_spec :
    mulCoeffTwo JData V4C3Data 28 28 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 28 0 := by
  decide

private theorem v4JRow28Coeff29_spec :
    mulCoeffTwo JData V4C3Data 28 29 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 29 0 := by
  decide

private theorem v4JRow28Coeff30_spec :
    mulCoeffTwo JData V4C3Data 28 30 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 30 0 := by
  decide

private theorem v4JRow28Coeff31_spec :
    mulCoeffTwo JData V4C3Data 28 31 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 31 0 := by
  decide

private theorem v4JRow28Coeff32_spec :
    mulCoeffTwo JData V4C3Data 28 32 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 32 0 := by
  decide

private theorem v4JRow28Coeff33_spec :
    mulCoeffTwo JData V4C3Data 28 33 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 33 0 := by
  decide

private theorem v4JRow28Coeff34_spec :
    mulCoeffTwo JData V4C3Data 28 34 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 34 0 := by
  decide

private theorem v4JRow28Coeff35_spec :
    mulCoeffTwo JData V4C3Data 28 35 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 35 0 := by
  decide

private theorem v4JRow28Coeff36_spec :
    mulCoeffTwo JData V4C3Data 28 36 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 36 0 := by
  decide

private theorem v4JRow28Coeff37_spec :
    mulCoeffTwo JData V4C3Data 28 37 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 37 0 := by
  decide

private theorem v4JRow28Coeff38_spec :
    mulCoeffTwo JData V4C3Data 28 38 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 38 0 := by
  decide

private theorem v4JRow28Coeff39_spec :
    mulCoeffTwo JData V4C3Data 28 39 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 39 0 := by
  decide

private theorem v4JRow28Coeff40_spec :
    mulCoeffTwo JData V4C3Data 28 40 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 40 0 := by
  decide

private theorem v4JRow28Coeff41_spec :
    mulCoeffTwo JData V4C3Data 28 41 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 41 0 := by
  decide

private theorem v4JRow28Coeff42_spec :
    mulCoeffTwo JData V4C3Data 28 42 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 42 0 := by
  decide

private theorem v4JRow28Coeff43_spec :
    mulCoeffTwo JData V4C3Data 28 43 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 43 0 := by
  decide

private theorem v4JRow28Coeff44_spec :
    mulCoeffTwo JData V4C3Data 28 44 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 44 0 := by
  decide

private theorem v4JRow28Coeff45_spec :
    mulCoeffTwo JData V4C3Data 28 45 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 45 0 := by
  decide

private theorem v4JRow28Coeff46_spec :
    mulCoeffTwo JData V4C3Data 28 46 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 46 0 := by
  decide

private theorem v4JRow28Coeff47_spec :
    mulCoeffTwo JData V4C3Data 28 47 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 47 0 := by
  decide

private theorem v4JRow28Coeff48_spec :
    mulCoeffTwo JData V4C3Data 28 48 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 48 0 := by
  decide

private theorem v4JRow28Coeff49_spec :
    mulCoeffTwo JData V4C3Data 28 49 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 49 0 := by
  decide

private theorem v4JRow28Coeff50_spec :
    mulCoeffTwo JData V4C3Data 28 50 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 50 0 := by
  decide

private theorem v4JRow28Coeff51_spec :
    mulCoeffTwo JData V4C3Data 28 51 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 51 0 := by
  decide

private theorem v4JRow28Coeff52_spec :
    mulCoeffTwo JData V4C3Data 28 52 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 52 0 := by
  decide

private theorem v4JRow28Coeff53_spec :
    mulCoeffTwo JData V4C3Data 28 53 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 53 0 := by
  decide

private theorem v4JRow28Coeff54_spec :
    mulCoeffTwo JData V4C3Data 28 54 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 54 0 := by
  decide

private theorem v4JRow28Coeff55_spec :
    mulCoeffTwo JData V4C3Data 28 55 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 55 0 := by
  decide

private theorem v4JRow28Coeff56_spec :
    mulCoeffTwo JData V4C3Data 28 56 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 56 0 := by
  decide

private theorem v4JRow28Coeff57_spec :
    mulCoeffTwo JData V4C3Data 28 57 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 57 0 := by
  decide

private theorem v4JRow28Coeff58_spec :
    mulCoeffTwo JData V4C3Data 28 58 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 58 0 := by
  decide

private theorem v4JRow28Coeff59_spec :
    mulCoeffTwo JData V4C3Data 28 59 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 59 0 := by
  decide

private theorem v4JRow28Coeff60_spec :
    mulCoeffTwo JData V4C3Data 28 60 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 60 0 := by
  decide

private theorem v4JRow28Coeff61_spec :
    mulCoeffTwo JData V4C3Data 28 61 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 61 0 := by
  decide

private theorem v4JRow28Coeff62_spec :
    mulCoeffTwo JData V4C3Data 28 62 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 62 0 := by
  decide

private theorem v4JRow28Coeff63_spec :
    mulCoeffTwo JData V4C3Data 28 63 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 63 0 := by
  decide

private theorem v4JRow28Coeff64_spec :
    mulCoeffTwo JData V4C3Data 28 64 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 64 0 := by
  decide

private theorem v4JRow28Coeff65_spec :
    mulCoeffTwo JData V4C3Data 28 65 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 65 0 := by
  decide

private theorem v4JRow28Coeff66_spec :
    mulCoeffTwo JData V4C3Data 28 66 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 66 0 := by
  decide

private theorem v4JRow28Coeff67_spec :
    mulCoeffTwo JData V4C3Data 28 67 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 67 0 := by
  decide

private theorem v4JRow28Coeff68_spec :
    mulCoeffTwo JData V4C3Data 28 68 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 68 0 := by
  decide

private theorem v4JRow28Coeff69_spec :
    mulCoeffTwo JData V4C3Data 28 69 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 69 0 := by
  decide

private theorem v4JRow28Coeff70_spec :
    mulCoeffTwo JData V4C3Data 28 70 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 70 0 := by
  decide

private theorem v4JRow28Coeff71_spec :
    mulCoeffTwo JData V4C3Data 28 71 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 71 0 := by
  decide

private theorem v4JRow28Coeff72_spec :
    mulCoeffTwo JData V4C3Data 28 72 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 72 0 := by
  decide

private theorem v4JRow28Coeff73_spec :
    mulCoeffTwo JData V4C3Data 28 73 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 73 0 := by
  decide

private theorem v4JRow28Coeff74_spec :
    mulCoeffTwo JData V4C3Data 28 74 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 74 0 := by
  decide

private theorem v4JRow28Coeff75_spec :
    mulCoeffTwo JData V4C3Data 28 75 =
      ((rectangularize 52 76 V4JData).getD 28 []).getD 75 0 := by
  decide

private theorem v4JRow28Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo JData V4C3Data 28 j =
      ((rectangularize 52 76 V4JData).getD 28 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow28Coeff0_spec
  · exact v4JRow28Coeff1_spec
  · exact v4JRow28Coeff2_spec
  · exact v4JRow28Coeff3_spec
  · exact v4JRow28Coeff4_spec
  · exact v4JRow28Coeff5_spec
  · exact v4JRow28Coeff6_spec
  · exact v4JRow28Coeff7_spec
  · exact v4JRow28Coeff8_spec
  · exact v4JRow28Coeff9_spec

private theorem v4JRow28Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo JData V4C3Data 28 j =
      ((rectangularize 52 76 V4JData).getD 28 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow28Coeff10_spec
  · exact v4JRow28Coeff11_spec
  · exact v4JRow28Coeff12_spec
  · exact v4JRow28Coeff13_spec
  · exact v4JRow28Coeff14_spec
  · exact v4JRow28Coeff15_spec
  · exact v4JRow28Coeff16_spec
  · exact v4JRow28Coeff17_spec
  · exact v4JRow28Coeff18_spec
  · exact v4JRow28Coeff19_spec

private theorem v4JRow28Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo JData V4C3Data 28 j =
      ((rectangularize 52 76 V4JData).getD 28 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow28Coeff20_spec
  · exact v4JRow28Coeff21_spec
  · exact v4JRow28Coeff22_spec
  · exact v4JRow28Coeff23_spec
  · exact v4JRow28Coeff24_spec
  · exact v4JRow28Coeff25_spec
  · exact v4JRow28Coeff26_spec
  · exact v4JRow28Coeff27_spec
  · exact v4JRow28Coeff28_spec
  · exact v4JRow28Coeff29_spec

private theorem v4JRow28Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo JData V4C3Data 28 j =
      ((rectangularize 52 76 V4JData).getD 28 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow28Coeff30_spec
  · exact v4JRow28Coeff31_spec
  · exact v4JRow28Coeff32_spec
  · exact v4JRow28Coeff33_spec
  · exact v4JRow28Coeff34_spec
  · exact v4JRow28Coeff35_spec
  · exact v4JRow28Coeff36_spec
  · exact v4JRow28Coeff37_spec
  · exact v4JRow28Coeff38_spec
  · exact v4JRow28Coeff39_spec

private theorem v4JRow28Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo JData V4C3Data 28 j =
      ((rectangularize 52 76 V4JData).getD 28 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow28Coeff40_spec
  · exact v4JRow28Coeff41_spec
  · exact v4JRow28Coeff42_spec
  · exact v4JRow28Coeff43_spec
  · exact v4JRow28Coeff44_spec
  · exact v4JRow28Coeff45_spec
  · exact v4JRow28Coeff46_spec
  · exact v4JRow28Coeff47_spec
  · exact v4JRow28Coeff48_spec
  · exact v4JRow28Coeff49_spec

private theorem v4JRow28Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo JData V4C3Data 28 j =
      ((rectangularize 52 76 V4JData).getD 28 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow28Coeff50_spec
  · exact v4JRow28Coeff51_spec
  · exact v4JRow28Coeff52_spec
  · exact v4JRow28Coeff53_spec
  · exact v4JRow28Coeff54_spec
  · exact v4JRow28Coeff55_spec
  · exact v4JRow28Coeff56_spec
  · exact v4JRow28Coeff57_spec
  · exact v4JRow28Coeff58_spec
  · exact v4JRow28Coeff59_spec

private theorem v4JRow28Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo JData V4C3Data 28 j =
      ((rectangularize 52 76 V4JData).getD 28 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow28Coeff60_spec
  · exact v4JRow28Coeff61_spec
  · exact v4JRow28Coeff62_spec
  · exact v4JRow28Coeff63_spec
  · exact v4JRow28Coeff64_spec
  · exact v4JRow28Coeff65_spec
  · exact v4JRow28Coeff66_spec
  · exact v4JRow28Coeff67_spec
  · exact v4JRow28Coeff68_spec
  · exact v4JRow28Coeff69_spec

private theorem v4JRow28Coeffs70To75_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 76) :
    mulCoeffTwo JData V4C3Data 28 j =
      ((rectangularize 52 76 V4JData).getD 28 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact v4JRow28Coeff70_spec
  · exact v4JRow28Coeff71_spec
  · exact v4JRow28Coeff72_spec
  · exact v4JRow28Coeff73_spec
  · exact v4JRow28Coeff74_spec
  · exact v4JRow28Coeff75_spec

private theorem v4JRow28_coefficients (j : ℕ) (hj : j < 76) :
    mulCoeffTwo JData V4C3Data 28 j =
      ((rectangularize 52 76 V4JData).getD 28 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4JRow28Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4JRow28Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4JRow28Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4JRow28Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4JRow28Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4JRow28Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4JRow28Coeffs60To69_spec j (by omega) h70
  exact v4JRow28Coeffs70To75_spec j (by omega) hj

private theorem v4JRow28_spec :
    padOne 76 (mulRow JData V4C3Data 28) =
      (rectangularize 52 76 V4JData).getD 28 [] := by
  apply padOne_mulRow_eq_of_coefficients 76 JData V4C3Data 28
    ((rectangularize 52 76 V4JData).getD 28 [])
  · decide
  · have hTargetSupport : (V4JData.getD 28 []).length ≤ 76 := by
      decide
    rw [getD_rectangularize 52 76 V4JData 28 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4JRow28_coefficients

private theorem v4JRow29Coeff0_spec :
    mulCoeffTwo JData V4C3Data 29 0 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 0 0 := by
  decide

private theorem v4JRow29Coeff1_spec :
    mulCoeffTwo JData V4C3Data 29 1 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 1 0 := by
  decide

private theorem v4JRow29Coeff2_spec :
    mulCoeffTwo JData V4C3Data 29 2 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 2 0 := by
  decide

private theorem v4JRow29Coeff3_spec :
    mulCoeffTwo JData V4C3Data 29 3 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 3 0 := by
  decide

private theorem v4JRow29Coeff4_spec :
    mulCoeffTwo JData V4C3Data 29 4 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 4 0 := by
  decide

private theorem v4JRow29Coeff5_spec :
    mulCoeffTwo JData V4C3Data 29 5 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 5 0 := by
  decide

private theorem v4JRow29Coeff6_spec :
    mulCoeffTwo JData V4C3Data 29 6 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 6 0 := by
  decide

private theorem v4JRow29Coeff7_spec :
    mulCoeffTwo JData V4C3Data 29 7 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 7 0 := by
  decide

private theorem v4JRow29Coeff8_spec :
    mulCoeffTwo JData V4C3Data 29 8 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 8 0 := by
  decide

private theorem v4JRow29Coeff9_spec :
    mulCoeffTwo JData V4C3Data 29 9 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 9 0 := by
  decide

private theorem v4JRow29Coeff10_spec :
    mulCoeffTwo JData V4C3Data 29 10 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 10 0 := by
  decide

private theorem v4JRow29Coeff11_spec :
    mulCoeffTwo JData V4C3Data 29 11 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 11 0 := by
  decide

private theorem v4JRow29Coeff12_spec :
    mulCoeffTwo JData V4C3Data 29 12 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 12 0 := by
  decide

private theorem v4JRow29Coeff13_spec :
    mulCoeffTwo JData V4C3Data 29 13 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 13 0 := by
  decide

private theorem v4JRow29Coeff14_spec :
    mulCoeffTwo JData V4C3Data 29 14 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 14 0 := by
  decide

private theorem v4JRow29Coeff15_spec :
    mulCoeffTwo JData V4C3Data 29 15 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 15 0 := by
  decide

private theorem v4JRow29Coeff16_spec :
    mulCoeffTwo JData V4C3Data 29 16 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 16 0 := by
  decide

private theorem v4JRow29Coeff17_spec :
    mulCoeffTwo JData V4C3Data 29 17 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 17 0 := by
  decide

private theorem v4JRow29Coeff18_spec :
    mulCoeffTwo JData V4C3Data 29 18 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 18 0 := by
  decide

private theorem v4JRow29Coeff19_spec :
    mulCoeffTwo JData V4C3Data 29 19 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 19 0 := by
  decide

private theorem v4JRow29Coeff20_spec :
    mulCoeffTwo JData V4C3Data 29 20 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 20 0 := by
  decide

private theorem v4JRow29Coeff21_spec :
    mulCoeffTwo JData V4C3Data 29 21 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 21 0 := by
  decide

private theorem v4JRow29Coeff22_spec :
    mulCoeffTwo JData V4C3Data 29 22 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 22 0 := by
  decide

private theorem v4JRow29Coeff23_spec :
    mulCoeffTwo JData V4C3Data 29 23 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 23 0 := by
  decide

private theorem v4JRow29Coeff24_spec :
    mulCoeffTwo JData V4C3Data 29 24 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 24 0 := by
  decide

private theorem v4JRow29Coeff25_spec :
    mulCoeffTwo JData V4C3Data 29 25 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 25 0 := by
  decide

private theorem v4JRow29Coeff26_spec :
    mulCoeffTwo JData V4C3Data 29 26 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 26 0 := by
  decide

private theorem v4JRow29Coeff27_spec :
    mulCoeffTwo JData V4C3Data 29 27 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 27 0 := by
  decide

private theorem v4JRow29Coeff28_spec :
    mulCoeffTwo JData V4C3Data 29 28 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 28 0 := by
  decide

private theorem v4JRow29Coeff29_spec :
    mulCoeffTwo JData V4C3Data 29 29 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 29 0 := by
  decide

private theorem v4JRow29Coeff30_spec :
    mulCoeffTwo JData V4C3Data 29 30 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 30 0 := by
  decide

private theorem v4JRow29Coeff31_spec :
    mulCoeffTwo JData V4C3Data 29 31 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 31 0 := by
  decide

private theorem v4JRow29Coeff32_spec :
    mulCoeffTwo JData V4C3Data 29 32 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 32 0 := by
  decide

private theorem v4JRow29Coeff33_spec :
    mulCoeffTwo JData V4C3Data 29 33 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 33 0 := by
  decide

private theorem v4JRow29Coeff34_spec :
    mulCoeffTwo JData V4C3Data 29 34 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 34 0 := by
  decide

private theorem v4JRow29Coeff35_spec :
    mulCoeffTwo JData V4C3Data 29 35 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 35 0 := by
  decide

private theorem v4JRow29Coeff36_spec :
    mulCoeffTwo JData V4C3Data 29 36 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 36 0 := by
  decide

private theorem v4JRow29Coeff37_spec :
    mulCoeffTwo JData V4C3Data 29 37 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 37 0 := by
  decide

private theorem v4JRow29Coeff38_spec :
    mulCoeffTwo JData V4C3Data 29 38 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 38 0 := by
  decide

private theorem v4JRow29Coeff39_spec :
    mulCoeffTwo JData V4C3Data 29 39 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 39 0 := by
  decide

private theorem v4JRow29Coeff40_spec :
    mulCoeffTwo JData V4C3Data 29 40 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 40 0 := by
  decide

private theorem v4JRow29Coeff41_spec :
    mulCoeffTwo JData V4C3Data 29 41 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 41 0 := by
  decide

private theorem v4JRow29Coeff42_spec :
    mulCoeffTwo JData V4C3Data 29 42 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 42 0 := by
  decide

private theorem v4JRow29Coeff43_spec :
    mulCoeffTwo JData V4C3Data 29 43 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 43 0 := by
  decide

private theorem v4JRow29Coeff44_spec :
    mulCoeffTwo JData V4C3Data 29 44 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 44 0 := by
  decide

private theorem v4JRow29Coeff45_spec :
    mulCoeffTwo JData V4C3Data 29 45 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 45 0 := by
  decide

private theorem v4JRow29Coeff46_spec :
    mulCoeffTwo JData V4C3Data 29 46 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 46 0 := by
  decide

private theorem v4JRow29Coeff47_spec :
    mulCoeffTwo JData V4C3Data 29 47 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 47 0 := by
  decide

private theorem v4JRow29Coeff48_spec :
    mulCoeffTwo JData V4C3Data 29 48 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 48 0 := by
  decide

private theorem v4JRow29Coeff49_spec :
    mulCoeffTwo JData V4C3Data 29 49 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 49 0 := by
  decide

private theorem v4JRow29Coeff50_spec :
    mulCoeffTwo JData V4C3Data 29 50 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 50 0 := by
  decide

private theorem v4JRow29Coeff51_spec :
    mulCoeffTwo JData V4C3Data 29 51 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 51 0 := by
  decide

private theorem v4JRow29Coeff52_spec :
    mulCoeffTwo JData V4C3Data 29 52 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 52 0 := by
  decide

private theorem v4JRow29Coeff53_spec :
    mulCoeffTwo JData V4C3Data 29 53 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 53 0 := by
  decide

private theorem v4JRow29Coeff54_spec :
    mulCoeffTwo JData V4C3Data 29 54 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 54 0 := by
  decide

private theorem v4JRow29Coeff55_spec :
    mulCoeffTwo JData V4C3Data 29 55 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 55 0 := by
  decide

private theorem v4JRow29Coeff56_spec :
    mulCoeffTwo JData V4C3Data 29 56 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 56 0 := by
  decide

private theorem v4JRow29Coeff57_spec :
    mulCoeffTwo JData V4C3Data 29 57 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 57 0 := by
  decide

private theorem v4JRow29Coeff58_spec :
    mulCoeffTwo JData V4C3Data 29 58 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 58 0 := by
  decide

private theorem v4JRow29Coeff59_spec :
    mulCoeffTwo JData V4C3Data 29 59 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 59 0 := by
  decide

private theorem v4JRow29Coeff60_spec :
    mulCoeffTwo JData V4C3Data 29 60 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 60 0 := by
  decide

private theorem v4JRow29Coeff61_spec :
    mulCoeffTwo JData V4C3Data 29 61 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 61 0 := by
  decide

private theorem v4JRow29Coeff62_spec :
    mulCoeffTwo JData V4C3Data 29 62 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 62 0 := by
  decide

private theorem v4JRow29Coeff63_spec :
    mulCoeffTwo JData V4C3Data 29 63 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 63 0 := by
  decide

private theorem v4JRow29Coeff64_spec :
    mulCoeffTwo JData V4C3Data 29 64 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 64 0 := by
  decide

private theorem v4JRow29Coeff65_spec :
    mulCoeffTwo JData V4C3Data 29 65 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 65 0 := by
  decide

private theorem v4JRow29Coeff66_spec :
    mulCoeffTwo JData V4C3Data 29 66 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 66 0 := by
  decide

private theorem v4JRow29Coeff67_spec :
    mulCoeffTwo JData V4C3Data 29 67 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 67 0 := by
  decide

private theorem v4JRow29Coeff68_spec :
    mulCoeffTwo JData V4C3Data 29 68 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 68 0 := by
  decide

private theorem v4JRow29Coeff69_spec :
    mulCoeffTwo JData V4C3Data 29 69 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 69 0 := by
  decide

private theorem v4JRow29Coeff70_spec :
    mulCoeffTwo JData V4C3Data 29 70 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 70 0 := by
  decide

private theorem v4JRow29Coeff71_spec :
    mulCoeffTwo JData V4C3Data 29 71 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 71 0 := by
  decide

private theorem v4JRow29Coeff72_spec :
    mulCoeffTwo JData V4C3Data 29 72 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 72 0 := by
  decide

private theorem v4JRow29Coeff73_spec :
    mulCoeffTwo JData V4C3Data 29 73 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 73 0 := by
  decide

private theorem v4JRow29Coeff74_spec :
    mulCoeffTwo JData V4C3Data 29 74 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 74 0 := by
  decide

private theorem v4JRow29Coeff75_spec :
    mulCoeffTwo JData V4C3Data 29 75 =
      ((rectangularize 52 76 V4JData).getD 29 []).getD 75 0 := by
  decide

private theorem v4JRow29Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo JData V4C3Data 29 j =
      ((rectangularize 52 76 V4JData).getD 29 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow29Coeff0_spec
  · exact v4JRow29Coeff1_spec
  · exact v4JRow29Coeff2_spec
  · exact v4JRow29Coeff3_spec
  · exact v4JRow29Coeff4_spec
  · exact v4JRow29Coeff5_spec
  · exact v4JRow29Coeff6_spec
  · exact v4JRow29Coeff7_spec
  · exact v4JRow29Coeff8_spec
  · exact v4JRow29Coeff9_spec

private theorem v4JRow29Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo JData V4C3Data 29 j =
      ((rectangularize 52 76 V4JData).getD 29 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow29Coeff10_spec
  · exact v4JRow29Coeff11_spec
  · exact v4JRow29Coeff12_spec
  · exact v4JRow29Coeff13_spec
  · exact v4JRow29Coeff14_spec
  · exact v4JRow29Coeff15_spec
  · exact v4JRow29Coeff16_spec
  · exact v4JRow29Coeff17_spec
  · exact v4JRow29Coeff18_spec
  · exact v4JRow29Coeff19_spec

private theorem v4JRow29Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo JData V4C3Data 29 j =
      ((rectangularize 52 76 V4JData).getD 29 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow29Coeff20_spec
  · exact v4JRow29Coeff21_spec
  · exact v4JRow29Coeff22_spec
  · exact v4JRow29Coeff23_spec
  · exact v4JRow29Coeff24_spec
  · exact v4JRow29Coeff25_spec
  · exact v4JRow29Coeff26_spec
  · exact v4JRow29Coeff27_spec
  · exact v4JRow29Coeff28_spec
  · exact v4JRow29Coeff29_spec

private theorem v4JRow29Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo JData V4C3Data 29 j =
      ((rectangularize 52 76 V4JData).getD 29 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow29Coeff30_spec
  · exact v4JRow29Coeff31_spec
  · exact v4JRow29Coeff32_spec
  · exact v4JRow29Coeff33_spec
  · exact v4JRow29Coeff34_spec
  · exact v4JRow29Coeff35_spec
  · exact v4JRow29Coeff36_spec
  · exact v4JRow29Coeff37_spec
  · exact v4JRow29Coeff38_spec
  · exact v4JRow29Coeff39_spec

private theorem v4JRow29Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo JData V4C3Data 29 j =
      ((rectangularize 52 76 V4JData).getD 29 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow29Coeff40_spec
  · exact v4JRow29Coeff41_spec
  · exact v4JRow29Coeff42_spec
  · exact v4JRow29Coeff43_spec
  · exact v4JRow29Coeff44_spec
  · exact v4JRow29Coeff45_spec
  · exact v4JRow29Coeff46_spec
  · exact v4JRow29Coeff47_spec
  · exact v4JRow29Coeff48_spec
  · exact v4JRow29Coeff49_spec

private theorem v4JRow29Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo JData V4C3Data 29 j =
      ((rectangularize 52 76 V4JData).getD 29 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow29Coeff50_spec
  · exact v4JRow29Coeff51_spec
  · exact v4JRow29Coeff52_spec
  · exact v4JRow29Coeff53_spec
  · exact v4JRow29Coeff54_spec
  · exact v4JRow29Coeff55_spec
  · exact v4JRow29Coeff56_spec
  · exact v4JRow29Coeff57_spec
  · exact v4JRow29Coeff58_spec
  · exact v4JRow29Coeff59_spec

private theorem v4JRow29Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo JData V4C3Data 29 j =
      ((rectangularize 52 76 V4JData).getD 29 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow29Coeff60_spec
  · exact v4JRow29Coeff61_spec
  · exact v4JRow29Coeff62_spec
  · exact v4JRow29Coeff63_spec
  · exact v4JRow29Coeff64_spec
  · exact v4JRow29Coeff65_spec
  · exact v4JRow29Coeff66_spec
  · exact v4JRow29Coeff67_spec
  · exact v4JRow29Coeff68_spec
  · exact v4JRow29Coeff69_spec

private theorem v4JRow29Coeffs70To75_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 76) :
    mulCoeffTwo JData V4C3Data 29 j =
      ((rectangularize 52 76 V4JData).getD 29 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact v4JRow29Coeff70_spec
  · exact v4JRow29Coeff71_spec
  · exact v4JRow29Coeff72_spec
  · exact v4JRow29Coeff73_spec
  · exact v4JRow29Coeff74_spec
  · exact v4JRow29Coeff75_spec

private theorem v4JRow29_coefficients (j : ℕ) (hj : j < 76) :
    mulCoeffTwo JData V4C3Data 29 j =
      ((rectangularize 52 76 V4JData).getD 29 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4JRow29Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4JRow29Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4JRow29Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4JRow29Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4JRow29Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4JRow29Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4JRow29Coeffs60To69_spec j (by omega) h70
  exact v4JRow29Coeffs70To75_spec j (by omega) hj

private theorem v4JRow29_spec :
    padOne 76 (mulRow JData V4C3Data 29) =
      (rectangularize 52 76 V4JData).getD 29 [] := by
  apply padOne_mulRow_eq_of_coefficients 76 JData V4C3Data 29
    ((rectangularize 52 76 V4JData).getD 29 [])
  · decide
  · have hTargetSupport : (V4JData.getD 29 []).length ≤ 76 := by
      decide
    rw [getD_rectangularize 52 76 V4JData 29 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4JRow29_coefficients

private theorem v4JRow30Coeff0_spec :
    mulCoeffTwo JData V4C3Data 30 0 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 0 0 := by
  decide

private theorem v4JRow30Coeff1_spec :
    mulCoeffTwo JData V4C3Data 30 1 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 1 0 := by
  decide

private theorem v4JRow30Coeff2_spec :
    mulCoeffTwo JData V4C3Data 30 2 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 2 0 := by
  decide

private theorem v4JRow30Coeff3_spec :
    mulCoeffTwo JData V4C3Data 30 3 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 3 0 := by
  decide

private theorem v4JRow30Coeff4_spec :
    mulCoeffTwo JData V4C3Data 30 4 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 4 0 := by
  decide

private theorem v4JRow30Coeff5_spec :
    mulCoeffTwo JData V4C3Data 30 5 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 5 0 := by
  decide

private theorem v4JRow30Coeff6_spec :
    mulCoeffTwo JData V4C3Data 30 6 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 6 0 := by
  decide

private theorem v4JRow30Coeff7_spec :
    mulCoeffTwo JData V4C3Data 30 7 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 7 0 := by
  decide

private theorem v4JRow30Coeff8_spec :
    mulCoeffTwo JData V4C3Data 30 8 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 8 0 := by
  decide

private theorem v4JRow30Coeff9_spec :
    mulCoeffTwo JData V4C3Data 30 9 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 9 0 := by
  decide

private theorem v4JRow30Coeff10_spec :
    mulCoeffTwo JData V4C3Data 30 10 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 10 0 := by
  decide

private theorem v4JRow30Coeff11_spec :
    mulCoeffTwo JData V4C3Data 30 11 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 11 0 := by
  decide

private theorem v4JRow30Coeff12_spec :
    mulCoeffTwo JData V4C3Data 30 12 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 12 0 := by
  decide

private theorem v4JRow30Coeff13_spec :
    mulCoeffTwo JData V4C3Data 30 13 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 13 0 := by
  decide

private theorem v4JRow30Coeff14_spec :
    mulCoeffTwo JData V4C3Data 30 14 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 14 0 := by
  decide

private theorem v4JRow30Coeff15_spec :
    mulCoeffTwo JData V4C3Data 30 15 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 15 0 := by
  decide

private theorem v4JRow30Coeff16_spec :
    mulCoeffTwo JData V4C3Data 30 16 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 16 0 := by
  decide

private theorem v4JRow30Coeff17_spec :
    mulCoeffTwo JData V4C3Data 30 17 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 17 0 := by
  decide

private theorem v4JRow30Coeff18_spec :
    mulCoeffTwo JData V4C3Data 30 18 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 18 0 := by
  decide

private theorem v4JRow30Coeff19_spec :
    mulCoeffTwo JData V4C3Data 30 19 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 19 0 := by
  decide

private theorem v4JRow30Coeff20_spec :
    mulCoeffTwo JData V4C3Data 30 20 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 20 0 := by
  decide

private theorem v4JRow30Coeff21_spec :
    mulCoeffTwo JData V4C3Data 30 21 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 21 0 := by
  decide

private theorem v4JRow30Coeff22_spec :
    mulCoeffTwo JData V4C3Data 30 22 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 22 0 := by
  decide

private theorem v4JRow30Coeff23_spec :
    mulCoeffTwo JData V4C3Data 30 23 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 23 0 := by
  decide

private theorem v4JRow30Coeff24_spec :
    mulCoeffTwo JData V4C3Data 30 24 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 24 0 := by
  decide

private theorem v4JRow30Coeff25_spec :
    mulCoeffTwo JData V4C3Data 30 25 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 25 0 := by
  decide

private theorem v4JRow30Coeff26_spec :
    mulCoeffTwo JData V4C3Data 30 26 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 26 0 := by
  decide

private theorem v4JRow30Coeff27_spec :
    mulCoeffTwo JData V4C3Data 30 27 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 27 0 := by
  decide

private theorem v4JRow30Coeff28_spec :
    mulCoeffTwo JData V4C3Data 30 28 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 28 0 := by
  decide

private theorem v4JRow30Coeff29_spec :
    mulCoeffTwo JData V4C3Data 30 29 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 29 0 := by
  decide

private theorem v4JRow30Coeff30_spec :
    mulCoeffTwo JData V4C3Data 30 30 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 30 0 := by
  decide

private theorem v4JRow30Coeff31_spec :
    mulCoeffTwo JData V4C3Data 30 31 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 31 0 := by
  decide

private theorem v4JRow30Coeff32_spec :
    mulCoeffTwo JData V4C3Data 30 32 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 32 0 := by
  decide

private theorem v4JRow30Coeff33_spec :
    mulCoeffTwo JData V4C3Data 30 33 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 33 0 := by
  decide

private theorem v4JRow30Coeff34_spec :
    mulCoeffTwo JData V4C3Data 30 34 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 34 0 := by
  decide

private theorem v4JRow30Coeff35_spec :
    mulCoeffTwo JData V4C3Data 30 35 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 35 0 := by
  decide

private theorem v4JRow30Coeff36_spec :
    mulCoeffTwo JData V4C3Data 30 36 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 36 0 := by
  decide

private theorem v4JRow30Coeff37_spec :
    mulCoeffTwo JData V4C3Data 30 37 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 37 0 := by
  decide

private theorem v4JRow30Coeff38_spec :
    mulCoeffTwo JData V4C3Data 30 38 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 38 0 := by
  decide

private theorem v4JRow30Coeff39_spec :
    mulCoeffTwo JData V4C3Data 30 39 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 39 0 := by
  decide

private theorem v4JRow30Coeff40_spec :
    mulCoeffTwo JData V4C3Data 30 40 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 40 0 := by
  decide

private theorem v4JRow30Coeff41_spec :
    mulCoeffTwo JData V4C3Data 30 41 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 41 0 := by
  decide

private theorem v4JRow30Coeff42_spec :
    mulCoeffTwo JData V4C3Data 30 42 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 42 0 := by
  decide

private theorem v4JRow30Coeff43_spec :
    mulCoeffTwo JData V4C3Data 30 43 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 43 0 := by
  decide

private theorem v4JRow30Coeff44_spec :
    mulCoeffTwo JData V4C3Data 30 44 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 44 0 := by
  decide

private theorem v4JRow30Coeff45_spec :
    mulCoeffTwo JData V4C3Data 30 45 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 45 0 := by
  decide

private theorem v4JRow30Coeff46_spec :
    mulCoeffTwo JData V4C3Data 30 46 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 46 0 := by
  decide

private theorem v4JRow30Coeff47_spec :
    mulCoeffTwo JData V4C3Data 30 47 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 47 0 := by
  decide

private theorem v4JRow30Coeff48_spec :
    mulCoeffTwo JData V4C3Data 30 48 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 48 0 := by
  decide

private theorem v4JRow30Coeff49_spec :
    mulCoeffTwo JData V4C3Data 30 49 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 49 0 := by
  decide

private theorem v4JRow30Coeff50_spec :
    mulCoeffTwo JData V4C3Data 30 50 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 50 0 := by
  decide

private theorem v4JRow30Coeff51_spec :
    mulCoeffTwo JData V4C3Data 30 51 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 51 0 := by
  decide

private theorem v4JRow30Coeff52_spec :
    mulCoeffTwo JData V4C3Data 30 52 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 52 0 := by
  decide

private theorem v4JRow30Coeff53_spec :
    mulCoeffTwo JData V4C3Data 30 53 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 53 0 := by
  decide

private theorem v4JRow30Coeff54_spec :
    mulCoeffTwo JData V4C3Data 30 54 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 54 0 := by
  decide

private theorem v4JRow30Coeff55_spec :
    mulCoeffTwo JData V4C3Data 30 55 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 55 0 := by
  decide

private theorem v4JRow30Coeff56_spec :
    mulCoeffTwo JData V4C3Data 30 56 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 56 0 := by
  decide

private theorem v4JRow30Coeff57_spec :
    mulCoeffTwo JData V4C3Data 30 57 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 57 0 := by
  decide

private theorem v4JRow30Coeff58_spec :
    mulCoeffTwo JData V4C3Data 30 58 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 58 0 := by
  decide

private theorem v4JRow30Coeff59_spec :
    mulCoeffTwo JData V4C3Data 30 59 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 59 0 := by
  decide

private theorem v4JRow30Coeff60_spec :
    mulCoeffTwo JData V4C3Data 30 60 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 60 0 := by
  decide

private theorem v4JRow30Coeff61_spec :
    mulCoeffTwo JData V4C3Data 30 61 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 61 0 := by
  decide

private theorem v4JRow30Coeff62_spec :
    mulCoeffTwo JData V4C3Data 30 62 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 62 0 := by
  decide

private theorem v4JRow30Coeff63_spec :
    mulCoeffTwo JData V4C3Data 30 63 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 63 0 := by
  decide

private theorem v4JRow30Coeff64_spec :
    mulCoeffTwo JData V4C3Data 30 64 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 64 0 := by
  decide

private theorem v4JRow30Coeff65_spec :
    mulCoeffTwo JData V4C3Data 30 65 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 65 0 := by
  decide

private theorem v4JRow30Coeff66_spec :
    mulCoeffTwo JData V4C3Data 30 66 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 66 0 := by
  decide

private theorem v4JRow30Coeff67_spec :
    mulCoeffTwo JData V4C3Data 30 67 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 67 0 := by
  decide

private theorem v4JRow30Coeff68_spec :
    mulCoeffTwo JData V4C3Data 30 68 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 68 0 := by
  decide

private theorem v4JRow30Coeff69_spec :
    mulCoeffTwo JData V4C3Data 30 69 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 69 0 := by
  decide

private theorem v4JRow30Coeff70_spec :
    mulCoeffTwo JData V4C3Data 30 70 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 70 0 := by
  decide

private theorem v4JRow30Coeff71_spec :
    mulCoeffTwo JData V4C3Data 30 71 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 71 0 := by
  decide

private theorem v4JRow30Coeff72_spec :
    mulCoeffTwo JData V4C3Data 30 72 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 72 0 := by
  decide

private theorem v4JRow30Coeff73_spec :
    mulCoeffTwo JData V4C3Data 30 73 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 73 0 := by
  decide

private theorem v4JRow30Coeff74_spec :
    mulCoeffTwo JData V4C3Data 30 74 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 74 0 := by
  decide

private theorem v4JRow30Coeff75_spec :
    mulCoeffTwo JData V4C3Data 30 75 =
      ((rectangularize 52 76 V4JData).getD 30 []).getD 75 0 := by
  decide

private theorem v4JRow30Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo JData V4C3Data 30 j =
      ((rectangularize 52 76 V4JData).getD 30 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow30Coeff0_spec
  · exact v4JRow30Coeff1_spec
  · exact v4JRow30Coeff2_spec
  · exact v4JRow30Coeff3_spec
  · exact v4JRow30Coeff4_spec
  · exact v4JRow30Coeff5_spec
  · exact v4JRow30Coeff6_spec
  · exact v4JRow30Coeff7_spec
  · exact v4JRow30Coeff8_spec
  · exact v4JRow30Coeff9_spec

private theorem v4JRow30Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo JData V4C3Data 30 j =
      ((rectangularize 52 76 V4JData).getD 30 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow30Coeff10_spec
  · exact v4JRow30Coeff11_spec
  · exact v4JRow30Coeff12_spec
  · exact v4JRow30Coeff13_spec
  · exact v4JRow30Coeff14_spec
  · exact v4JRow30Coeff15_spec
  · exact v4JRow30Coeff16_spec
  · exact v4JRow30Coeff17_spec
  · exact v4JRow30Coeff18_spec
  · exact v4JRow30Coeff19_spec

private theorem v4JRow30Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo JData V4C3Data 30 j =
      ((rectangularize 52 76 V4JData).getD 30 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow30Coeff20_spec
  · exact v4JRow30Coeff21_spec
  · exact v4JRow30Coeff22_spec
  · exact v4JRow30Coeff23_spec
  · exact v4JRow30Coeff24_spec
  · exact v4JRow30Coeff25_spec
  · exact v4JRow30Coeff26_spec
  · exact v4JRow30Coeff27_spec
  · exact v4JRow30Coeff28_spec
  · exact v4JRow30Coeff29_spec

private theorem v4JRow30Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo JData V4C3Data 30 j =
      ((rectangularize 52 76 V4JData).getD 30 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow30Coeff30_spec
  · exact v4JRow30Coeff31_spec
  · exact v4JRow30Coeff32_spec
  · exact v4JRow30Coeff33_spec
  · exact v4JRow30Coeff34_spec
  · exact v4JRow30Coeff35_spec
  · exact v4JRow30Coeff36_spec
  · exact v4JRow30Coeff37_spec
  · exact v4JRow30Coeff38_spec
  · exact v4JRow30Coeff39_spec

private theorem v4JRow30Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo JData V4C3Data 30 j =
      ((rectangularize 52 76 V4JData).getD 30 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow30Coeff40_spec
  · exact v4JRow30Coeff41_spec
  · exact v4JRow30Coeff42_spec
  · exact v4JRow30Coeff43_spec
  · exact v4JRow30Coeff44_spec
  · exact v4JRow30Coeff45_spec
  · exact v4JRow30Coeff46_spec
  · exact v4JRow30Coeff47_spec
  · exact v4JRow30Coeff48_spec
  · exact v4JRow30Coeff49_spec

private theorem v4JRow30Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo JData V4C3Data 30 j =
      ((rectangularize 52 76 V4JData).getD 30 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow30Coeff50_spec
  · exact v4JRow30Coeff51_spec
  · exact v4JRow30Coeff52_spec
  · exact v4JRow30Coeff53_spec
  · exact v4JRow30Coeff54_spec
  · exact v4JRow30Coeff55_spec
  · exact v4JRow30Coeff56_spec
  · exact v4JRow30Coeff57_spec
  · exact v4JRow30Coeff58_spec
  · exact v4JRow30Coeff59_spec

private theorem v4JRow30Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo JData V4C3Data 30 j =
      ((rectangularize 52 76 V4JData).getD 30 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow30Coeff60_spec
  · exact v4JRow30Coeff61_spec
  · exact v4JRow30Coeff62_spec
  · exact v4JRow30Coeff63_spec
  · exact v4JRow30Coeff64_spec
  · exact v4JRow30Coeff65_spec
  · exact v4JRow30Coeff66_spec
  · exact v4JRow30Coeff67_spec
  · exact v4JRow30Coeff68_spec
  · exact v4JRow30Coeff69_spec

private theorem v4JRow30Coeffs70To75_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 76) :
    mulCoeffTwo JData V4C3Data 30 j =
      ((rectangularize 52 76 V4JData).getD 30 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact v4JRow30Coeff70_spec
  · exact v4JRow30Coeff71_spec
  · exact v4JRow30Coeff72_spec
  · exact v4JRow30Coeff73_spec
  · exact v4JRow30Coeff74_spec
  · exact v4JRow30Coeff75_spec

private theorem v4JRow30_coefficients (j : ℕ) (hj : j < 76) :
    mulCoeffTwo JData V4C3Data 30 j =
      ((rectangularize 52 76 V4JData).getD 30 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4JRow30Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4JRow30Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4JRow30Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4JRow30Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4JRow30Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4JRow30Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4JRow30Coeffs60To69_spec j (by omega) h70
  exact v4JRow30Coeffs70To75_spec j (by omega) hj

private theorem v4JRow30_spec :
    padOne 76 (mulRow JData V4C3Data 30) =
      (rectangularize 52 76 V4JData).getD 30 [] := by
  apply padOne_mulRow_eq_of_coefficients 76 JData V4C3Data 30
    ((rectangularize 52 76 V4JData).getD 30 [])
  · decide
  · have hTargetSupport : (V4JData.getD 30 []).length ≤ 76 := by
      decide
    rw [getD_rectangularize 52 76 V4JData 30 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4JRow30_coefficients

private theorem v4JRow31Coeff0_spec :
    mulCoeffTwo JData V4C3Data 31 0 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 0 0 := by
  decide

private theorem v4JRow31Coeff1_spec :
    mulCoeffTwo JData V4C3Data 31 1 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 1 0 := by
  decide

private theorem v4JRow31Coeff2_spec :
    mulCoeffTwo JData V4C3Data 31 2 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 2 0 := by
  decide

private theorem v4JRow31Coeff3_spec :
    mulCoeffTwo JData V4C3Data 31 3 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 3 0 := by
  decide

private theorem v4JRow31Coeff4_spec :
    mulCoeffTwo JData V4C3Data 31 4 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 4 0 := by
  decide

private theorem v4JRow31Coeff5_spec :
    mulCoeffTwo JData V4C3Data 31 5 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 5 0 := by
  decide

private theorem v4JRow31Coeff6_spec :
    mulCoeffTwo JData V4C3Data 31 6 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 6 0 := by
  decide

private theorem v4JRow31Coeff7_spec :
    mulCoeffTwo JData V4C3Data 31 7 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 7 0 := by
  decide

private theorem v4JRow31Coeff8_spec :
    mulCoeffTwo JData V4C3Data 31 8 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 8 0 := by
  decide

private theorem v4JRow31Coeff9_spec :
    mulCoeffTwo JData V4C3Data 31 9 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 9 0 := by
  decide

private theorem v4JRow31Coeff10_spec :
    mulCoeffTwo JData V4C3Data 31 10 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 10 0 := by
  decide

private theorem v4JRow31Coeff11_spec :
    mulCoeffTwo JData V4C3Data 31 11 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 11 0 := by
  decide

private theorem v4JRow31Coeff12_spec :
    mulCoeffTwo JData V4C3Data 31 12 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 12 0 := by
  decide

private theorem v4JRow31Coeff13_spec :
    mulCoeffTwo JData V4C3Data 31 13 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 13 0 := by
  decide

private theorem v4JRow31Coeff14_spec :
    mulCoeffTwo JData V4C3Data 31 14 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 14 0 := by
  decide

private theorem v4JRow31Coeff15_spec :
    mulCoeffTwo JData V4C3Data 31 15 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 15 0 := by
  decide

private theorem v4JRow31Coeff16_spec :
    mulCoeffTwo JData V4C3Data 31 16 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 16 0 := by
  decide

private theorem v4JRow31Coeff17_spec :
    mulCoeffTwo JData V4C3Data 31 17 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 17 0 := by
  decide

private theorem v4JRow31Coeff18_spec :
    mulCoeffTwo JData V4C3Data 31 18 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 18 0 := by
  decide

private theorem v4JRow31Coeff19_spec :
    mulCoeffTwo JData V4C3Data 31 19 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 19 0 := by
  decide

private theorem v4JRow31Coeff20_spec :
    mulCoeffTwo JData V4C3Data 31 20 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 20 0 := by
  decide

private theorem v4JRow31Coeff21_spec :
    mulCoeffTwo JData V4C3Data 31 21 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 21 0 := by
  decide

private theorem v4JRow31Coeff22_spec :
    mulCoeffTwo JData V4C3Data 31 22 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 22 0 := by
  decide

private theorem v4JRow31Coeff23_spec :
    mulCoeffTwo JData V4C3Data 31 23 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 23 0 := by
  decide

private theorem v4JRow31Coeff24_spec :
    mulCoeffTwo JData V4C3Data 31 24 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 24 0 := by
  decide

private theorem v4JRow31Coeff25_spec :
    mulCoeffTwo JData V4C3Data 31 25 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 25 0 := by
  decide

private theorem v4JRow31Coeff26_spec :
    mulCoeffTwo JData V4C3Data 31 26 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 26 0 := by
  decide

private theorem v4JRow31Coeff27_spec :
    mulCoeffTwo JData V4C3Data 31 27 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 27 0 := by
  decide

private theorem v4JRow31Coeff28_spec :
    mulCoeffTwo JData V4C3Data 31 28 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 28 0 := by
  decide

private theorem v4JRow31Coeff29_spec :
    mulCoeffTwo JData V4C3Data 31 29 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 29 0 := by
  decide

private theorem v4JRow31Coeff30_spec :
    mulCoeffTwo JData V4C3Data 31 30 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 30 0 := by
  decide

private theorem v4JRow31Coeff31_spec :
    mulCoeffTwo JData V4C3Data 31 31 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 31 0 := by
  decide

private theorem v4JRow31Coeff32_spec :
    mulCoeffTwo JData V4C3Data 31 32 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 32 0 := by
  decide

private theorem v4JRow31Coeff33_spec :
    mulCoeffTwo JData V4C3Data 31 33 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 33 0 := by
  decide

private theorem v4JRow31Coeff34_spec :
    mulCoeffTwo JData V4C3Data 31 34 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 34 0 := by
  decide

private theorem v4JRow31Coeff35_spec :
    mulCoeffTwo JData V4C3Data 31 35 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 35 0 := by
  decide

private theorem v4JRow31Coeff36_spec :
    mulCoeffTwo JData V4C3Data 31 36 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 36 0 := by
  decide

private theorem v4JRow31Coeff37_spec :
    mulCoeffTwo JData V4C3Data 31 37 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 37 0 := by
  decide

private theorem v4JRow31Coeff38_spec :
    mulCoeffTwo JData V4C3Data 31 38 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 38 0 := by
  decide

private theorem v4JRow31Coeff39_spec :
    mulCoeffTwo JData V4C3Data 31 39 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 39 0 := by
  decide

private theorem v4JRow31Coeff40_spec :
    mulCoeffTwo JData V4C3Data 31 40 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 40 0 := by
  decide

private theorem v4JRow31Coeff41_spec :
    mulCoeffTwo JData V4C3Data 31 41 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 41 0 := by
  decide

private theorem v4JRow31Coeff42_spec :
    mulCoeffTwo JData V4C3Data 31 42 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 42 0 := by
  decide

private theorem v4JRow31Coeff43_spec :
    mulCoeffTwo JData V4C3Data 31 43 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 43 0 := by
  decide

private theorem v4JRow31Coeff44_spec :
    mulCoeffTwo JData V4C3Data 31 44 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 44 0 := by
  decide

private theorem v4JRow31Coeff45_spec :
    mulCoeffTwo JData V4C3Data 31 45 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 45 0 := by
  decide

private theorem v4JRow31Coeff46_spec :
    mulCoeffTwo JData V4C3Data 31 46 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 46 0 := by
  decide

private theorem v4JRow31Coeff47_spec :
    mulCoeffTwo JData V4C3Data 31 47 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 47 0 := by
  decide

private theorem v4JRow31Coeff48_spec :
    mulCoeffTwo JData V4C3Data 31 48 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 48 0 := by
  decide

private theorem v4JRow31Coeff49_spec :
    mulCoeffTwo JData V4C3Data 31 49 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 49 0 := by
  decide

private theorem v4JRow31Coeff50_spec :
    mulCoeffTwo JData V4C3Data 31 50 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 50 0 := by
  decide

private theorem v4JRow31Coeff51_spec :
    mulCoeffTwo JData V4C3Data 31 51 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 51 0 := by
  decide

private theorem v4JRow31Coeff52_spec :
    mulCoeffTwo JData V4C3Data 31 52 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 52 0 := by
  decide

private theorem v4JRow31Coeff53_spec :
    mulCoeffTwo JData V4C3Data 31 53 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 53 0 := by
  decide

private theorem v4JRow31Coeff54_spec :
    mulCoeffTwo JData V4C3Data 31 54 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 54 0 := by
  decide

private theorem v4JRow31Coeff55_spec :
    mulCoeffTwo JData V4C3Data 31 55 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 55 0 := by
  decide

private theorem v4JRow31Coeff56_spec :
    mulCoeffTwo JData V4C3Data 31 56 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 56 0 := by
  decide

private theorem v4JRow31Coeff57_spec :
    mulCoeffTwo JData V4C3Data 31 57 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 57 0 := by
  decide

private theorem v4JRow31Coeff58_spec :
    mulCoeffTwo JData V4C3Data 31 58 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 58 0 := by
  decide

private theorem v4JRow31Coeff59_spec :
    mulCoeffTwo JData V4C3Data 31 59 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 59 0 := by
  decide

private theorem v4JRow31Coeff60_spec :
    mulCoeffTwo JData V4C3Data 31 60 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 60 0 := by
  decide

private theorem v4JRow31Coeff61_spec :
    mulCoeffTwo JData V4C3Data 31 61 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 61 0 := by
  decide

private theorem v4JRow31Coeff62_spec :
    mulCoeffTwo JData V4C3Data 31 62 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 62 0 := by
  decide

private theorem v4JRow31Coeff63_spec :
    mulCoeffTwo JData V4C3Data 31 63 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 63 0 := by
  decide

private theorem v4JRow31Coeff64_spec :
    mulCoeffTwo JData V4C3Data 31 64 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 64 0 := by
  decide

private theorem v4JRow31Coeff65_spec :
    mulCoeffTwo JData V4C3Data 31 65 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 65 0 := by
  decide

private theorem v4JRow31Coeff66_spec :
    mulCoeffTwo JData V4C3Data 31 66 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 66 0 := by
  decide

private theorem v4JRow31Coeff67_spec :
    mulCoeffTwo JData V4C3Data 31 67 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 67 0 := by
  decide

private theorem v4JRow31Coeff68_spec :
    mulCoeffTwo JData V4C3Data 31 68 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 68 0 := by
  decide

private theorem v4JRow31Coeff69_spec :
    mulCoeffTwo JData V4C3Data 31 69 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 69 0 := by
  decide

private theorem v4JRow31Coeff70_spec :
    mulCoeffTwo JData V4C3Data 31 70 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 70 0 := by
  decide

private theorem v4JRow31Coeff71_spec :
    mulCoeffTwo JData V4C3Data 31 71 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 71 0 := by
  decide

private theorem v4JRow31Coeff72_spec :
    mulCoeffTwo JData V4C3Data 31 72 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 72 0 := by
  decide

private theorem v4JRow31Coeff73_spec :
    mulCoeffTwo JData V4C3Data 31 73 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 73 0 := by
  decide

private theorem v4JRow31Coeff74_spec :
    mulCoeffTwo JData V4C3Data 31 74 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 74 0 := by
  decide

private theorem v4JRow31Coeff75_spec :
    mulCoeffTwo JData V4C3Data 31 75 =
      ((rectangularize 52 76 V4JData).getD 31 []).getD 75 0 := by
  decide

private theorem v4JRow31Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo JData V4C3Data 31 j =
      ((rectangularize 52 76 V4JData).getD 31 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow31Coeff0_spec
  · exact v4JRow31Coeff1_spec
  · exact v4JRow31Coeff2_spec
  · exact v4JRow31Coeff3_spec
  · exact v4JRow31Coeff4_spec
  · exact v4JRow31Coeff5_spec
  · exact v4JRow31Coeff6_spec
  · exact v4JRow31Coeff7_spec
  · exact v4JRow31Coeff8_spec
  · exact v4JRow31Coeff9_spec

private theorem v4JRow31Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo JData V4C3Data 31 j =
      ((rectangularize 52 76 V4JData).getD 31 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow31Coeff10_spec
  · exact v4JRow31Coeff11_spec
  · exact v4JRow31Coeff12_spec
  · exact v4JRow31Coeff13_spec
  · exact v4JRow31Coeff14_spec
  · exact v4JRow31Coeff15_spec
  · exact v4JRow31Coeff16_spec
  · exact v4JRow31Coeff17_spec
  · exact v4JRow31Coeff18_spec
  · exact v4JRow31Coeff19_spec

private theorem v4JRow31Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo JData V4C3Data 31 j =
      ((rectangularize 52 76 V4JData).getD 31 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow31Coeff20_spec
  · exact v4JRow31Coeff21_spec
  · exact v4JRow31Coeff22_spec
  · exact v4JRow31Coeff23_spec
  · exact v4JRow31Coeff24_spec
  · exact v4JRow31Coeff25_spec
  · exact v4JRow31Coeff26_spec
  · exact v4JRow31Coeff27_spec
  · exact v4JRow31Coeff28_spec
  · exact v4JRow31Coeff29_spec

private theorem v4JRow31Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo JData V4C3Data 31 j =
      ((rectangularize 52 76 V4JData).getD 31 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow31Coeff30_spec
  · exact v4JRow31Coeff31_spec
  · exact v4JRow31Coeff32_spec
  · exact v4JRow31Coeff33_spec
  · exact v4JRow31Coeff34_spec
  · exact v4JRow31Coeff35_spec
  · exact v4JRow31Coeff36_spec
  · exact v4JRow31Coeff37_spec
  · exact v4JRow31Coeff38_spec
  · exact v4JRow31Coeff39_spec

private theorem v4JRow31Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo JData V4C3Data 31 j =
      ((rectangularize 52 76 V4JData).getD 31 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow31Coeff40_spec
  · exact v4JRow31Coeff41_spec
  · exact v4JRow31Coeff42_spec
  · exact v4JRow31Coeff43_spec
  · exact v4JRow31Coeff44_spec
  · exact v4JRow31Coeff45_spec
  · exact v4JRow31Coeff46_spec
  · exact v4JRow31Coeff47_spec
  · exact v4JRow31Coeff48_spec
  · exact v4JRow31Coeff49_spec

private theorem v4JRow31Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo JData V4C3Data 31 j =
      ((rectangularize 52 76 V4JData).getD 31 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow31Coeff50_spec
  · exact v4JRow31Coeff51_spec
  · exact v4JRow31Coeff52_spec
  · exact v4JRow31Coeff53_spec
  · exact v4JRow31Coeff54_spec
  · exact v4JRow31Coeff55_spec
  · exact v4JRow31Coeff56_spec
  · exact v4JRow31Coeff57_spec
  · exact v4JRow31Coeff58_spec
  · exact v4JRow31Coeff59_spec

private theorem v4JRow31Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo JData V4C3Data 31 j =
      ((rectangularize 52 76 V4JData).getD 31 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow31Coeff60_spec
  · exact v4JRow31Coeff61_spec
  · exact v4JRow31Coeff62_spec
  · exact v4JRow31Coeff63_spec
  · exact v4JRow31Coeff64_spec
  · exact v4JRow31Coeff65_spec
  · exact v4JRow31Coeff66_spec
  · exact v4JRow31Coeff67_spec
  · exact v4JRow31Coeff68_spec
  · exact v4JRow31Coeff69_spec

private theorem v4JRow31Coeffs70To75_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 76) :
    mulCoeffTwo JData V4C3Data 31 j =
      ((rectangularize 52 76 V4JData).getD 31 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact v4JRow31Coeff70_spec
  · exact v4JRow31Coeff71_spec
  · exact v4JRow31Coeff72_spec
  · exact v4JRow31Coeff73_spec
  · exact v4JRow31Coeff74_spec
  · exact v4JRow31Coeff75_spec

private theorem v4JRow31_coefficients (j : ℕ) (hj : j < 76) :
    mulCoeffTwo JData V4C3Data 31 j =
      ((rectangularize 52 76 V4JData).getD 31 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4JRow31Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4JRow31Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4JRow31Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4JRow31Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4JRow31Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4JRow31Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4JRow31Coeffs60To69_spec j (by omega) h70
  exact v4JRow31Coeffs70To75_spec j (by omega) hj

private theorem v4JRow31_spec :
    padOne 76 (mulRow JData V4C3Data 31) =
      (rectangularize 52 76 V4JData).getD 31 [] := by
  apply padOne_mulRow_eq_of_coefficients 76 JData V4C3Data 31
    ((rectangularize 52 76 V4JData).getD 31 [])
  · decide
  · have hTargetSupport : (V4JData.getD 31 []).length ≤ 76 := by
      decide
    rw [getD_rectangularize 52 76 V4JData 31 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4JRow31_coefficients

private theorem v4JRow32Coeff0_spec :
    mulCoeffTwo JData V4C3Data 32 0 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 0 0 := by
  decide

private theorem v4JRow32Coeff1_spec :
    mulCoeffTwo JData V4C3Data 32 1 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 1 0 := by
  decide

private theorem v4JRow32Coeff2_spec :
    mulCoeffTwo JData V4C3Data 32 2 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 2 0 := by
  decide

private theorem v4JRow32Coeff3_spec :
    mulCoeffTwo JData V4C3Data 32 3 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 3 0 := by
  decide

private theorem v4JRow32Coeff4_spec :
    mulCoeffTwo JData V4C3Data 32 4 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 4 0 := by
  decide

private theorem v4JRow32Coeff5_spec :
    mulCoeffTwo JData V4C3Data 32 5 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 5 0 := by
  decide

private theorem v4JRow32Coeff6_spec :
    mulCoeffTwo JData V4C3Data 32 6 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 6 0 := by
  decide

private theorem v4JRow32Coeff7_spec :
    mulCoeffTwo JData V4C3Data 32 7 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 7 0 := by
  decide

private theorem v4JRow32Coeff8_spec :
    mulCoeffTwo JData V4C3Data 32 8 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 8 0 := by
  decide

private theorem v4JRow32Coeff9_spec :
    mulCoeffTwo JData V4C3Data 32 9 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 9 0 := by
  decide

private theorem v4JRow32Coeff10_spec :
    mulCoeffTwo JData V4C3Data 32 10 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 10 0 := by
  decide

private theorem v4JRow32Coeff11_spec :
    mulCoeffTwo JData V4C3Data 32 11 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 11 0 := by
  decide

private theorem v4JRow32Coeff12_spec :
    mulCoeffTwo JData V4C3Data 32 12 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 12 0 := by
  decide

private theorem v4JRow32Coeff13_spec :
    mulCoeffTwo JData V4C3Data 32 13 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 13 0 := by
  decide

private theorem v4JRow32Coeff14_spec :
    mulCoeffTwo JData V4C3Data 32 14 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 14 0 := by
  decide

private theorem v4JRow32Coeff15_spec :
    mulCoeffTwo JData V4C3Data 32 15 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 15 0 := by
  decide

private theorem v4JRow32Coeff16_spec :
    mulCoeffTwo JData V4C3Data 32 16 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 16 0 := by
  decide

private theorem v4JRow32Coeff17_spec :
    mulCoeffTwo JData V4C3Data 32 17 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 17 0 := by
  decide

private theorem v4JRow32Coeff18_spec :
    mulCoeffTwo JData V4C3Data 32 18 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 18 0 := by
  decide

private theorem v4JRow32Coeff19_spec :
    mulCoeffTwo JData V4C3Data 32 19 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 19 0 := by
  decide

private theorem v4JRow32Coeff20_spec :
    mulCoeffTwo JData V4C3Data 32 20 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 20 0 := by
  decide

private theorem v4JRow32Coeff21_spec :
    mulCoeffTwo JData V4C3Data 32 21 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 21 0 := by
  decide

private theorem v4JRow32Coeff22_spec :
    mulCoeffTwo JData V4C3Data 32 22 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 22 0 := by
  decide

private theorem v4JRow32Coeff23_spec :
    mulCoeffTwo JData V4C3Data 32 23 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 23 0 := by
  decide

private theorem v4JRow32Coeff24_spec :
    mulCoeffTwo JData V4C3Data 32 24 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 24 0 := by
  decide

private theorem v4JRow32Coeff25_spec :
    mulCoeffTwo JData V4C3Data 32 25 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 25 0 := by
  decide

private theorem v4JRow32Coeff26_spec :
    mulCoeffTwo JData V4C3Data 32 26 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 26 0 := by
  decide

private theorem v4JRow32Coeff27_spec :
    mulCoeffTwo JData V4C3Data 32 27 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 27 0 := by
  decide

private theorem v4JRow32Coeff28_spec :
    mulCoeffTwo JData V4C3Data 32 28 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 28 0 := by
  decide

private theorem v4JRow32Coeff29_spec :
    mulCoeffTwo JData V4C3Data 32 29 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 29 0 := by
  decide

private theorem v4JRow32Coeff30_spec :
    mulCoeffTwo JData V4C3Data 32 30 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 30 0 := by
  decide

private theorem v4JRow32Coeff31_spec :
    mulCoeffTwo JData V4C3Data 32 31 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 31 0 := by
  decide

private theorem v4JRow32Coeff32_spec :
    mulCoeffTwo JData V4C3Data 32 32 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 32 0 := by
  decide

private theorem v4JRow32Coeff33_spec :
    mulCoeffTwo JData V4C3Data 32 33 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 33 0 := by
  decide

private theorem v4JRow32Coeff34_spec :
    mulCoeffTwo JData V4C3Data 32 34 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 34 0 := by
  decide

private theorem v4JRow32Coeff35_spec :
    mulCoeffTwo JData V4C3Data 32 35 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 35 0 := by
  decide

private theorem v4JRow32Coeff36_spec :
    mulCoeffTwo JData V4C3Data 32 36 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 36 0 := by
  decide

private theorem v4JRow32Coeff37_spec :
    mulCoeffTwo JData V4C3Data 32 37 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 37 0 := by
  decide

private theorem v4JRow32Coeff38_spec :
    mulCoeffTwo JData V4C3Data 32 38 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 38 0 := by
  decide

private theorem v4JRow32Coeff39_spec :
    mulCoeffTwo JData V4C3Data 32 39 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 39 0 := by
  decide

private theorem v4JRow32Coeff40_spec :
    mulCoeffTwo JData V4C3Data 32 40 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 40 0 := by
  decide

private theorem v4JRow32Coeff41_spec :
    mulCoeffTwo JData V4C3Data 32 41 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 41 0 := by
  decide

private theorem v4JRow32Coeff42_spec :
    mulCoeffTwo JData V4C3Data 32 42 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 42 0 := by
  decide

private theorem v4JRow32Coeff43_spec :
    mulCoeffTwo JData V4C3Data 32 43 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 43 0 := by
  decide

private theorem v4JRow32Coeff44_spec :
    mulCoeffTwo JData V4C3Data 32 44 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 44 0 := by
  decide

private theorem v4JRow32Coeff45_spec :
    mulCoeffTwo JData V4C3Data 32 45 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 45 0 := by
  decide

private theorem v4JRow32Coeff46_spec :
    mulCoeffTwo JData V4C3Data 32 46 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 46 0 := by
  decide

private theorem v4JRow32Coeff47_spec :
    mulCoeffTwo JData V4C3Data 32 47 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 47 0 := by
  decide

private theorem v4JRow32Coeff48_spec :
    mulCoeffTwo JData V4C3Data 32 48 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 48 0 := by
  decide

private theorem v4JRow32Coeff49_spec :
    mulCoeffTwo JData V4C3Data 32 49 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 49 0 := by
  decide

private theorem v4JRow32Coeff50_spec :
    mulCoeffTwo JData V4C3Data 32 50 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 50 0 := by
  decide

private theorem v4JRow32Coeff51_spec :
    mulCoeffTwo JData V4C3Data 32 51 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 51 0 := by
  decide

private theorem v4JRow32Coeff52_spec :
    mulCoeffTwo JData V4C3Data 32 52 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 52 0 := by
  decide

private theorem v4JRow32Coeff53_spec :
    mulCoeffTwo JData V4C3Data 32 53 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 53 0 := by
  decide

private theorem v4JRow32Coeff54_spec :
    mulCoeffTwo JData V4C3Data 32 54 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 54 0 := by
  decide

private theorem v4JRow32Coeff55_spec :
    mulCoeffTwo JData V4C3Data 32 55 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 55 0 := by
  decide

private theorem v4JRow32Coeff56_spec :
    mulCoeffTwo JData V4C3Data 32 56 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 56 0 := by
  decide

private theorem v4JRow32Coeff57_spec :
    mulCoeffTwo JData V4C3Data 32 57 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 57 0 := by
  decide

private theorem v4JRow32Coeff58_spec :
    mulCoeffTwo JData V4C3Data 32 58 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 58 0 := by
  decide

private theorem v4JRow32Coeff59_spec :
    mulCoeffTwo JData V4C3Data 32 59 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 59 0 := by
  decide

private theorem v4JRow32Coeff60_spec :
    mulCoeffTwo JData V4C3Data 32 60 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 60 0 := by
  decide

private theorem v4JRow32Coeff61_spec :
    mulCoeffTwo JData V4C3Data 32 61 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 61 0 := by
  decide

private theorem v4JRow32Coeff62_spec :
    mulCoeffTwo JData V4C3Data 32 62 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 62 0 := by
  decide

private theorem v4JRow32Coeff63_spec :
    mulCoeffTwo JData V4C3Data 32 63 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 63 0 := by
  decide

private theorem v4JRow32Coeff64_spec :
    mulCoeffTwo JData V4C3Data 32 64 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 64 0 := by
  decide

private theorem v4JRow32Coeff65_spec :
    mulCoeffTwo JData V4C3Data 32 65 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 65 0 := by
  decide

private theorem v4JRow32Coeff66_spec :
    mulCoeffTwo JData V4C3Data 32 66 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 66 0 := by
  decide

private theorem v4JRow32Coeff67_spec :
    mulCoeffTwo JData V4C3Data 32 67 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 67 0 := by
  decide

private theorem v4JRow32Coeff68_spec :
    mulCoeffTwo JData V4C3Data 32 68 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 68 0 := by
  decide

private theorem v4JRow32Coeff69_spec :
    mulCoeffTwo JData V4C3Data 32 69 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 69 0 := by
  decide

private theorem v4JRow32Coeff70_spec :
    mulCoeffTwo JData V4C3Data 32 70 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 70 0 := by
  decide

private theorem v4JRow32Coeff71_spec :
    mulCoeffTwo JData V4C3Data 32 71 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 71 0 := by
  decide

private theorem v4JRow32Coeff72_spec :
    mulCoeffTwo JData V4C3Data 32 72 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 72 0 := by
  decide

private theorem v4JRow32Coeff73_spec :
    mulCoeffTwo JData V4C3Data 32 73 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 73 0 := by
  decide

private theorem v4JRow32Coeff74_spec :
    mulCoeffTwo JData V4C3Data 32 74 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 74 0 := by
  decide

private theorem v4JRow32Coeff75_spec :
    mulCoeffTwo JData V4C3Data 32 75 =
      ((rectangularize 52 76 V4JData).getD 32 []).getD 75 0 := by
  decide

private theorem v4JRow32Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo JData V4C3Data 32 j =
      ((rectangularize 52 76 V4JData).getD 32 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow32Coeff0_spec
  · exact v4JRow32Coeff1_spec
  · exact v4JRow32Coeff2_spec
  · exact v4JRow32Coeff3_spec
  · exact v4JRow32Coeff4_spec
  · exact v4JRow32Coeff5_spec
  · exact v4JRow32Coeff6_spec
  · exact v4JRow32Coeff7_spec
  · exact v4JRow32Coeff8_spec
  · exact v4JRow32Coeff9_spec

private theorem v4JRow32Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo JData V4C3Data 32 j =
      ((rectangularize 52 76 V4JData).getD 32 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow32Coeff10_spec
  · exact v4JRow32Coeff11_spec
  · exact v4JRow32Coeff12_spec
  · exact v4JRow32Coeff13_spec
  · exact v4JRow32Coeff14_spec
  · exact v4JRow32Coeff15_spec
  · exact v4JRow32Coeff16_spec
  · exact v4JRow32Coeff17_spec
  · exact v4JRow32Coeff18_spec
  · exact v4JRow32Coeff19_spec

private theorem v4JRow32Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo JData V4C3Data 32 j =
      ((rectangularize 52 76 V4JData).getD 32 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow32Coeff20_spec
  · exact v4JRow32Coeff21_spec
  · exact v4JRow32Coeff22_spec
  · exact v4JRow32Coeff23_spec
  · exact v4JRow32Coeff24_spec
  · exact v4JRow32Coeff25_spec
  · exact v4JRow32Coeff26_spec
  · exact v4JRow32Coeff27_spec
  · exact v4JRow32Coeff28_spec
  · exact v4JRow32Coeff29_spec

private theorem v4JRow32Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo JData V4C3Data 32 j =
      ((rectangularize 52 76 V4JData).getD 32 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow32Coeff30_spec
  · exact v4JRow32Coeff31_spec
  · exact v4JRow32Coeff32_spec
  · exact v4JRow32Coeff33_spec
  · exact v4JRow32Coeff34_spec
  · exact v4JRow32Coeff35_spec
  · exact v4JRow32Coeff36_spec
  · exact v4JRow32Coeff37_spec
  · exact v4JRow32Coeff38_spec
  · exact v4JRow32Coeff39_spec

private theorem v4JRow32Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo JData V4C3Data 32 j =
      ((rectangularize 52 76 V4JData).getD 32 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow32Coeff40_spec
  · exact v4JRow32Coeff41_spec
  · exact v4JRow32Coeff42_spec
  · exact v4JRow32Coeff43_spec
  · exact v4JRow32Coeff44_spec
  · exact v4JRow32Coeff45_spec
  · exact v4JRow32Coeff46_spec
  · exact v4JRow32Coeff47_spec
  · exact v4JRow32Coeff48_spec
  · exact v4JRow32Coeff49_spec

private theorem v4JRow32Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo JData V4C3Data 32 j =
      ((rectangularize 52 76 V4JData).getD 32 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow32Coeff50_spec
  · exact v4JRow32Coeff51_spec
  · exact v4JRow32Coeff52_spec
  · exact v4JRow32Coeff53_spec
  · exact v4JRow32Coeff54_spec
  · exact v4JRow32Coeff55_spec
  · exact v4JRow32Coeff56_spec
  · exact v4JRow32Coeff57_spec
  · exact v4JRow32Coeff58_spec
  · exact v4JRow32Coeff59_spec

private theorem v4JRow32Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo JData V4C3Data 32 j =
      ((rectangularize 52 76 V4JData).getD 32 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow32Coeff60_spec
  · exact v4JRow32Coeff61_spec
  · exact v4JRow32Coeff62_spec
  · exact v4JRow32Coeff63_spec
  · exact v4JRow32Coeff64_spec
  · exact v4JRow32Coeff65_spec
  · exact v4JRow32Coeff66_spec
  · exact v4JRow32Coeff67_spec
  · exact v4JRow32Coeff68_spec
  · exact v4JRow32Coeff69_spec

private theorem v4JRow32Coeffs70To75_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 76) :
    mulCoeffTwo JData V4C3Data 32 j =
      ((rectangularize 52 76 V4JData).getD 32 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact v4JRow32Coeff70_spec
  · exact v4JRow32Coeff71_spec
  · exact v4JRow32Coeff72_spec
  · exact v4JRow32Coeff73_spec
  · exact v4JRow32Coeff74_spec
  · exact v4JRow32Coeff75_spec

private theorem v4JRow32_coefficients (j : ℕ) (hj : j < 76) :
    mulCoeffTwo JData V4C3Data 32 j =
      ((rectangularize 52 76 V4JData).getD 32 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4JRow32Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4JRow32Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4JRow32Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4JRow32Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4JRow32Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4JRow32Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4JRow32Coeffs60To69_spec j (by omega) h70
  exact v4JRow32Coeffs70To75_spec j (by omega) hj

private theorem v4JRow32_spec :
    padOne 76 (mulRow JData V4C3Data 32) =
      (rectangularize 52 76 V4JData).getD 32 [] := by
  apply padOne_mulRow_eq_of_coefficients 76 JData V4C3Data 32
    ((rectangularize 52 76 V4JData).getD 32 [])
  · decide
  · have hTargetSupport : (V4JData.getD 32 []).length ≤ 76 := by
      decide
    rw [getD_rectangularize 52 76 V4JData 32 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4JRow32_coefficients

private theorem v4JRow33Coeff0_spec :
    mulCoeffTwo JData V4C3Data 33 0 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 0 0 := by
  decide

private theorem v4JRow33Coeff1_spec :
    mulCoeffTwo JData V4C3Data 33 1 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 1 0 := by
  decide

private theorem v4JRow33Coeff2_spec :
    mulCoeffTwo JData V4C3Data 33 2 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 2 0 := by
  decide

private theorem v4JRow33Coeff3_spec :
    mulCoeffTwo JData V4C3Data 33 3 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 3 0 := by
  decide

private theorem v4JRow33Coeff4_spec :
    mulCoeffTwo JData V4C3Data 33 4 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 4 0 := by
  decide

private theorem v4JRow33Coeff5_spec :
    mulCoeffTwo JData V4C3Data 33 5 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 5 0 := by
  decide

private theorem v4JRow33Coeff6_spec :
    mulCoeffTwo JData V4C3Data 33 6 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 6 0 := by
  decide

private theorem v4JRow33Coeff7_spec :
    mulCoeffTwo JData V4C3Data 33 7 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 7 0 := by
  decide

private theorem v4JRow33Coeff8_spec :
    mulCoeffTwo JData V4C3Data 33 8 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 8 0 := by
  decide

private theorem v4JRow33Coeff9_spec :
    mulCoeffTwo JData V4C3Data 33 9 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 9 0 := by
  decide

private theorem v4JRow33Coeff10_spec :
    mulCoeffTwo JData V4C3Data 33 10 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 10 0 := by
  decide

private theorem v4JRow33Coeff11_spec :
    mulCoeffTwo JData V4C3Data 33 11 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 11 0 := by
  decide

private theorem v4JRow33Coeff12_spec :
    mulCoeffTwo JData V4C3Data 33 12 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 12 0 := by
  decide

private theorem v4JRow33Coeff13_spec :
    mulCoeffTwo JData V4C3Data 33 13 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 13 0 := by
  decide

private theorem v4JRow33Coeff14_spec :
    mulCoeffTwo JData V4C3Data 33 14 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 14 0 := by
  decide

private theorem v4JRow33Coeff15_spec :
    mulCoeffTwo JData V4C3Data 33 15 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 15 0 := by
  decide

private theorem v4JRow33Coeff16_spec :
    mulCoeffTwo JData V4C3Data 33 16 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 16 0 := by
  decide

private theorem v4JRow33Coeff17_spec :
    mulCoeffTwo JData V4C3Data 33 17 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 17 0 := by
  decide

private theorem v4JRow33Coeff18_spec :
    mulCoeffTwo JData V4C3Data 33 18 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 18 0 := by
  decide

private theorem v4JRow33Coeff19_spec :
    mulCoeffTwo JData V4C3Data 33 19 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 19 0 := by
  decide

private theorem v4JRow33Coeff20_spec :
    mulCoeffTwo JData V4C3Data 33 20 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 20 0 := by
  decide

private theorem v4JRow33Coeff21_spec :
    mulCoeffTwo JData V4C3Data 33 21 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 21 0 := by
  decide

private theorem v4JRow33Coeff22_spec :
    mulCoeffTwo JData V4C3Data 33 22 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 22 0 := by
  decide

private theorem v4JRow33Coeff23_spec :
    mulCoeffTwo JData V4C3Data 33 23 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 23 0 := by
  decide

private theorem v4JRow33Coeff24_spec :
    mulCoeffTwo JData V4C3Data 33 24 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 24 0 := by
  decide

private theorem v4JRow33Coeff25_spec :
    mulCoeffTwo JData V4C3Data 33 25 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 25 0 := by
  decide

private theorem v4JRow33Coeff26_spec :
    mulCoeffTwo JData V4C3Data 33 26 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 26 0 := by
  decide

private theorem v4JRow33Coeff27_spec :
    mulCoeffTwo JData V4C3Data 33 27 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 27 0 := by
  decide

private theorem v4JRow33Coeff28_spec :
    mulCoeffTwo JData V4C3Data 33 28 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 28 0 := by
  decide

private theorem v4JRow33Coeff29_spec :
    mulCoeffTwo JData V4C3Data 33 29 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 29 0 := by
  decide

private theorem v4JRow33Coeff30_spec :
    mulCoeffTwo JData V4C3Data 33 30 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 30 0 := by
  decide

private theorem v4JRow33Coeff31_spec :
    mulCoeffTwo JData V4C3Data 33 31 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 31 0 := by
  decide

private theorem v4JRow33Coeff32_spec :
    mulCoeffTwo JData V4C3Data 33 32 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 32 0 := by
  decide

private theorem v4JRow33Coeff33_spec :
    mulCoeffTwo JData V4C3Data 33 33 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 33 0 := by
  decide

private theorem v4JRow33Coeff34_spec :
    mulCoeffTwo JData V4C3Data 33 34 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 34 0 := by
  decide

private theorem v4JRow33Coeff35_spec :
    mulCoeffTwo JData V4C3Data 33 35 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 35 0 := by
  decide

private theorem v4JRow33Coeff36_spec :
    mulCoeffTwo JData V4C3Data 33 36 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 36 0 := by
  decide

private theorem v4JRow33Coeff37_spec :
    mulCoeffTwo JData V4C3Data 33 37 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 37 0 := by
  decide

private theorem v4JRow33Coeff38_spec :
    mulCoeffTwo JData V4C3Data 33 38 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 38 0 := by
  decide

private theorem v4JRow33Coeff39_spec :
    mulCoeffTwo JData V4C3Data 33 39 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 39 0 := by
  decide

private theorem v4JRow33Coeff40_spec :
    mulCoeffTwo JData V4C3Data 33 40 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 40 0 := by
  decide

private theorem v4JRow33Coeff41_spec :
    mulCoeffTwo JData V4C3Data 33 41 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 41 0 := by
  decide

private theorem v4JRow33Coeff42_spec :
    mulCoeffTwo JData V4C3Data 33 42 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 42 0 := by
  decide

private theorem v4JRow33Coeff43_spec :
    mulCoeffTwo JData V4C3Data 33 43 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 43 0 := by
  decide

private theorem v4JRow33Coeff44_spec :
    mulCoeffTwo JData V4C3Data 33 44 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 44 0 := by
  decide

private theorem v4JRow33Coeff45_spec :
    mulCoeffTwo JData V4C3Data 33 45 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 45 0 := by
  decide

private theorem v4JRow33Coeff46_spec :
    mulCoeffTwo JData V4C3Data 33 46 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 46 0 := by
  decide

private theorem v4JRow33Coeff47_spec :
    mulCoeffTwo JData V4C3Data 33 47 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 47 0 := by
  decide

private theorem v4JRow33Coeff48_spec :
    mulCoeffTwo JData V4C3Data 33 48 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 48 0 := by
  decide

private theorem v4JRow33Coeff49_spec :
    mulCoeffTwo JData V4C3Data 33 49 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 49 0 := by
  decide

private theorem v4JRow33Coeff50_spec :
    mulCoeffTwo JData V4C3Data 33 50 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 50 0 := by
  decide

private theorem v4JRow33Coeff51_spec :
    mulCoeffTwo JData V4C3Data 33 51 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 51 0 := by
  decide

private theorem v4JRow33Coeff52_spec :
    mulCoeffTwo JData V4C3Data 33 52 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 52 0 := by
  decide

private theorem v4JRow33Coeff53_spec :
    mulCoeffTwo JData V4C3Data 33 53 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 53 0 := by
  decide

private theorem v4JRow33Coeff54_spec :
    mulCoeffTwo JData V4C3Data 33 54 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 54 0 := by
  decide

private theorem v4JRow33Coeff55_spec :
    mulCoeffTwo JData V4C3Data 33 55 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 55 0 := by
  decide

private theorem v4JRow33Coeff56_spec :
    mulCoeffTwo JData V4C3Data 33 56 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 56 0 := by
  decide

private theorem v4JRow33Coeff57_spec :
    mulCoeffTwo JData V4C3Data 33 57 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 57 0 := by
  decide

private theorem v4JRow33Coeff58_spec :
    mulCoeffTwo JData V4C3Data 33 58 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 58 0 := by
  decide

private theorem v4JRow33Coeff59_spec :
    mulCoeffTwo JData V4C3Data 33 59 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 59 0 := by
  decide

private theorem v4JRow33Coeff60_spec :
    mulCoeffTwo JData V4C3Data 33 60 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 60 0 := by
  decide

private theorem v4JRow33Coeff61_spec :
    mulCoeffTwo JData V4C3Data 33 61 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 61 0 := by
  decide

private theorem v4JRow33Coeff62_spec :
    mulCoeffTwo JData V4C3Data 33 62 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 62 0 := by
  decide

private theorem v4JRow33Coeff63_spec :
    mulCoeffTwo JData V4C3Data 33 63 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 63 0 := by
  decide

private theorem v4JRow33Coeff64_spec :
    mulCoeffTwo JData V4C3Data 33 64 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 64 0 := by
  decide

private theorem v4JRow33Coeff65_spec :
    mulCoeffTwo JData V4C3Data 33 65 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 65 0 := by
  decide

private theorem v4JRow33Coeff66_spec :
    mulCoeffTwo JData V4C3Data 33 66 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 66 0 := by
  decide

private theorem v4JRow33Coeff67_spec :
    mulCoeffTwo JData V4C3Data 33 67 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 67 0 := by
  decide

private theorem v4JRow33Coeff68_spec :
    mulCoeffTwo JData V4C3Data 33 68 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 68 0 := by
  decide

private theorem v4JRow33Coeff69_spec :
    mulCoeffTwo JData V4C3Data 33 69 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 69 0 := by
  decide

private theorem v4JRow33Coeff70_spec :
    mulCoeffTwo JData V4C3Data 33 70 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 70 0 := by
  decide

private theorem v4JRow33Coeff71_spec :
    mulCoeffTwo JData V4C3Data 33 71 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 71 0 := by
  decide

private theorem v4JRow33Coeff72_spec :
    mulCoeffTwo JData V4C3Data 33 72 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 72 0 := by
  decide

private theorem v4JRow33Coeff73_spec :
    mulCoeffTwo JData V4C3Data 33 73 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 73 0 := by
  decide

private theorem v4JRow33Coeff74_spec :
    mulCoeffTwo JData V4C3Data 33 74 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 74 0 := by
  decide

private theorem v4JRow33Coeff75_spec :
    mulCoeffTwo JData V4C3Data 33 75 =
      ((rectangularize 52 76 V4JData).getD 33 []).getD 75 0 := by
  decide

private theorem v4JRow33Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo JData V4C3Data 33 j =
      ((rectangularize 52 76 V4JData).getD 33 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow33Coeff0_spec
  · exact v4JRow33Coeff1_spec
  · exact v4JRow33Coeff2_spec
  · exact v4JRow33Coeff3_spec
  · exact v4JRow33Coeff4_spec
  · exact v4JRow33Coeff5_spec
  · exact v4JRow33Coeff6_spec
  · exact v4JRow33Coeff7_spec
  · exact v4JRow33Coeff8_spec
  · exact v4JRow33Coeff9_spec

private theorem v4JRow33Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo JData V4C3Data 33 j =
      ((rectangularize 52 76 V4JData).getD 33 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow33Coeff10_spec
  · exact v4JRow33Coeff11_spec
  · exact v4JRow33Coeff12_spec
  · exact v4JRow33Coeff13_spec
  · exact v4JRow33Coeff14_spec
  · exact v4JRow33Coeff15_spec
  · exact v4JRow33Coeff16_spec
  · exact v4JRow33Coeff17_spec
  · exact v4JRow33Coeff18_spec
  · exact v4JRow33Coeff19_spec

private theorem v4JRow33Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo JData V4C3Data 33 j =
      ((rectangularize 52 76 V4JData).getD 33 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow33Coeff20_spec
  · exact v4JRow33Coeff21_spec
  · exact v4JRow33Coeff22_spec
  · exact v4JRow33Coeff23_spec
  · exact v4JRow33Coeff24_spec
  · exact v4JRow33Coeff25_spec
  · exact v4JRow33Coeff26_spec
  · exact v4JRow33Coeff27_spec
  · exact v4JRow33Coeff28_spec
  · exact v4JRow33Coeff29_spec

private theorem v4JRow33Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo JData V4C3Data 33 j =
      ((rectangularize 52 76 V4JData).getD 33 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow33Coeff30_spec
  · exact v4JRow33Coeff31_spec
  · exact v4JRow33Coeff32_spec
  · exact v4JRow33Coeff33_spec
  · exact v4JRow33Coeff34_spec
  · exact v4JRow33Coeff35_spec
  · exact v4JRow33Coeff36_spec
  · exact v4JRow33Coeff37_spec
  · exact v4JRow33Coeff38_spec
  · exact v4JRow33Coeff39_spec

private theorem v4JRow33Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo JData V4C3Data 33 j =
      ((rectangularize 52 76 V4JData).getD 33 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow33Coeff40_spec
  · exact v4JRow33Coeff41_spec
  · exact v4JRow33Coeff42_spec
  · exact v4JRow33Coeff43_spec
  · exact v4JRow33Coeff44_spec
  · exact v4JRow33Coeff45_spec
  · exact v4JRow33Coeff46_spec
  · exact v4JRow33Coeff47_spec
  · exact v4JRow33Coeff48_spec
  · exact v4JRow33Coeff49_spec

private theorem v4JRow33Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo JData V4C3Data 33 j =
      ((rectangularize 52 76 V4JData).getD 33 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow33Coeff50_spec
  · exact v4JRow33Coeff51_spec
  · exact v4JRow33Coeff52_spec
  · exact v4JRow33Coeff53_spec
  · exact v4JRow33Coeff54_spec
  · exact v4JRow33Coeff55_spec
  · exact v4JRow33Coeff56_spec
  · exact v4JRow33Coeff57_spec
  · exact v4JRow33Coeff58_spec
  · exact v4JRow33Coeff59_spec

private theorem v4JRow33Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo JData V4C3Data 33 j =
      ((rectangularize 52 76 V4JData).getD 33 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow33Coeff60_spec
  · exact v4JRow33Coeff61_spec
  · exact v4JRow33Coeff62_spec
  · exact v4JRow33Coeff63_spec
  · exact v4JRow33Coeff64_spec
  · exact v4JRow33Coeff65_spec
  · exact v4JRow33Coeff66_spec
  · exact v4JRow33Coeff67_spec
  · exact v4JRow33Coeff68_spec
  · exact v4JRow33Coeff69_spec

private theorem v4JRow33Coeffs70To75_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 76) :
    mulCoeffTwo JData V4C3Data 33 j =
      ((rectangularize 52 76 V4JData).getD 33 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact v4JRow33Coeff70_spec
  · exact v4JRow33Coeff71_spec
  · exact v4JRow33Coeff72_spec
  · exact v4JRow33Coeff73_spec
  · exact v4JRow33Coeff74_spec
  · exact v4JRow33Coeff75_spec

private theorem v4JRow33_coefficients (j : ℕ) (hj : j < 76) :
    mulCoeffTwo JData V4C3Data 33 j =
      ((rectangularize 52 76 V4JData).getD 33 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4JRow33Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4JRow33Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4JRow33Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4JRow33Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4JRow33Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4JRow33Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4JRow33Coeffs60To69_spec j (by omega) h70
  exact v4JRow33Coeffs70To75_spec j (by omega) hj

private theorem v4JRow33_spec :
    padOne 76 (mulRow JData V4C3Data 33) =
      (rectangularize 52 76 V4JData).getD 33 [] := by
  apply padOne_mulRow_eq_of_coefficients 76 JData V4C3Data 33
    ((rectangularize 52 76 V4JData).getD 33 [])
  · decide
  · have hTargetSupport : (V4JData.getD 33 []).length ≤ 76 := by
      decide
    rw [getD_rectangularize 52 76 V4JData 33 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4JRow33_coefficients

private theorem v4JRow34Coeff0_spec :
    mulCoeffTwo JData V4C3Data 34 0 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 0 0 := by
  decide

private theorem v4JRow34Coeff1_spec :
    mulCoeffTwo JData V4C3Data 34 1 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 1 0 := by
  decide

private theorem v4JRow34Coeff2_spec :
    mulCoeffTwo JData V4C3Data 34 2 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 2 0 := by
  decide

private theorem v4JRow34Coeff3_spec :
    mulCoeffTwo JData V4C3Data 34 3 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 3 0 := by
  decide

private theorem v4JRow34Coeff4_spec :
    mulCoeffTwo JData V4C3Data 34 4 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 4 0 := by
  decide

private theorem v4JRow34Coeff5_spec :
    mulCoeffTwo JData V4C3Data 34 5 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 5 0 := by
  decide

private theorem v4JRow34Coeff6_spec :
    mulCoeffTwo JData V4C3Data 34 6 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 6 0 := by
  decide

private theorem v4JRow34Coeff7_spec :
    mulCoeffTwo JData V4C3Data 34 7 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 7 0 := by
  decide

private theorem v4JRow34Coeff8_spec :
    mulCoeffTwo JData V4C3Data 34 8 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 8 0 := by
  decide

private theorem v4JRow34Coeff9_spec :
    mulCoeffTwo JData V4C3Data 34 9 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 9 0 := by
  decide

private theorem v4JRow34Coeff10_spec :
    mulCoeffTwo JData V4C3Data 34 10 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 10 0 := by
  decide

private theorem v4JRow34Coeff11_spec :
    mulCoeffTwo JData V4C3Data 34 11 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 11 0 := by
  decide

private theorem v4JRow34Coeff12_spec :
    mulCoeffTwo JData V4C3Data 34 12 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 12 0 := by
  decide

private theorem v4JRow34Coeff13_spec :
    mulCoeffTwo JData V4C3Data 34 13 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 13 0 := by
  decide

private theorem v4JRow34Coeff14_spec :
    mulCoeffTwo JData V4C3Data 34 14 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 14 0 := by
  decide

private theorem v4JRow34Coeff15_spec :
    mulCoeffTwo JData V4C3Data 34 15 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 15 0 := by
  decide

private theorem v4JRow34Coeff16_spec :
    mulCoeffTwo JData V4C3Data 34 16 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 16 0 := by
  decide

private theorem v4JRow34Coeff17_spec :
    mulCoeffTwo JData V4C3Data 34 17 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 17 0 := by
  decide

private theorem v4JRow34Coeff18_spec :
    mulCoeffTwo JData V4C3Data 34 18 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 18 0 := by
  decide

private theorem v4JRow34Coeff19_spec :
    mulCoeffTwo JData V4C3Data 34 19 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 19 0 := by
  decide

private theorem v4JRow34Coeff20_spec :
    mulCoeffTwo JData V4C3Data 34 20 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 20 0 := by
  decide

private theorem v4JRow34Coeff21_spec :
    mulCoeffTwo JData V4C3Data 34 21 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 21 0 := by
  decide

private theorem v4JRow34Coeff22_spec :
    mulCoeffTwo JData V4C3Data 34 22 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 22 0 := by
  decide

private theorem v4JRow34Coeff23_spec :
    mulCoeffTwo JData V4C3Data 34 23 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 23 0 := by
  decide

private theorem v4JRow34Coeff24_spec :
    mulCoeffTwo JData V4C3Data 34 24 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 24 0 := by
  decide

private theorem v4JRow34Coeff25_spec :
    mulCoeffTwo JData V4C3Data 34 25 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 25 0 := by
  decide

private theorem v4JRow34Coeff26_spec :
    mulCoeffTwo JData V4C3Data 34 26 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 26 0 := by
  decide

private theorem v4JRow34Coeff27_spec :
    mulCoeffTwo JData V4C3Data 34 27 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 27 0 := by
  decide

private theorem v4JRow34Coeff28_spec :
    mulCoeffTwo JData V4C3Data 34 28 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 28 0 := by
  decide

private theorem v4JRow34Coeff29_spec :
    mulCoeffTwo JData V4C3Data 34 29 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 29 0 := by
  decide

private theorem v4JRow34Coeff30_spec :
    mulCoeffTwo JData V4C3Data 34 30 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 30 0 := by
  decide

private theorem v4JRow34Coeff31_spec :
    mulCoeffTwo JData V4C3Data 34 31 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 31 0 := by
  decide

private theorem v4JRow34Coeff32_spec :
    mulCoeffTwo JData V4C3Data 34 32 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 32 0 := by
  decide

private theorem v4JRow34Coeff33_spec :
    mulCoeffTwo JData V4C3Data 34 33 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 33 0 := by
  decide

private theorem v4JRow34Coeff34_spec :
    mulCoeffTwo JData V4C3Data 34 34 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 34 0 := by
  decide

private theorem v4JRow34Coeff35_spec :
    mulCoeffTwo JData V4C3Data 34 35 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 35 0 := by
  decide

private theorem v4JRow34Coeff36_spec :
    mulCoeffTwo JData V4C3Data 34 36 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 36 0 := by
  decide

private theorem v4JRow34Coeff37_spec :
    mulCoeffTwo JData V4C3Data 34 37 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 37 0 := by
  decide

private theorem v4JRow34Coeff38_spec :
    mulCoeffTwo JData V4C3Data 34 38 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 38 0 := by
  decide

private theorem v4JRow34Coeff39_spec :
    mulCoeffTwo JData V4C3Data 34 39 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 39 0 := by
  decide

private theorem v4JRow34Coeff40_spec :
    mulCoeffTwo JData V4C3Data 34 40 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 40 0 := by
  decide

private theorem v4JRow34Coeff41_spec :
    mulCoeffTwo JData V4C3Data 34 41 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 41 0 := by
  decide

private theorem v4JRow34Coeff42_spec :
    mulCoeffTwo JData V4C3Data 34 42 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 42 0 := by
  decide

private theorem v4JRow34Coeff43_spec :
    mulCoeffTwo JData V4C3Data 34 43 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 43 0 := by
  decide

private theorem v4JRow34Coeff44_spec :
    mulCoeffTwo JData V4C3Data 34 44 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 44 0 := by
  decide

private theorem v4JRow34Coeff45_spec :
    mulCoeffTwo JData V4C3Data 34 45 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 45 0 := by
  decide

private theorem v4JRow34Coeff46_spec :
    mulCoeffTwo JData V4C3Data 34 46 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 46 0 := by
  decide

private theorem v4JRow34Coeff47_spec :
    mulCoeffTwo JData V4C3Data 34 47 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 47 0 := by
  decide

private theorem v4JRow34Coeff48_spec :
    mulCoeffTwo JData V4C3Data 34 48 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 48 0 := by
  decide

private theorem v4JRow34Coeff49_spec :
    mulCoeffTwo JData V4C3Data 34 49 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 49 0 := by
  decide

private theorem v4JRow34Coeff50_spec :
    mulCoeffTwo JData V4C3Data 34 50 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 50 0 := by
  decide

private theorem v4JRow34Coeff51_spec :
    mulCoeffTwo JData V4C3Data 34 51 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 51 0 := by
  decide

private theorem v4JRow34Coeff52_spec :
    mulCoeffTwo JData V4C3Data 34 52 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 52 0 := by
  decide

private theorem v4JRow34Coeff53_spec :
    mulCoeffTwo JData V4C3Data 34 53 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 53 0 := by
  decide

private theorem v4JRow34Coeff54_spec :
    mulCoeffTwo JData V4C3Data 34 54 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 54 0 := by
  decide

private theorem v4JRow34Coeff55_spec :
    mulCoeffTwo JData V4C3Data 34 55 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 55 0 := by
  decide

private theorem v4JRow34Coeff56_spec :
    mulCoeffTwo JData V4C3Data 34 56 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 56 0 := by
  decide

private theorem v4JRow34Coeff57_spec :
    mulCoeffTwo JData V4C3Data 34 57 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 57 0 := by
  decide

private theorem v4JRow34Coeff58_spec :
    mulCoeffTwo JData V4C3Data 34 58 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 58 0 := by
  decide

private theorem v4JRow34Coeff59_spec :
    mulCoeffTwo JData V4C3Data 34 59 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 59 0 := by
  decide

private theorem v4JRow34Coeff60_spec :
    mulCoeffTwo JData V4C3Data 34 60 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 60 0 := by
  decide

private theorem v4JRow34Coeff61_spec :
    mulCoeffTwo JData V4C3Data 34 61 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 61 0 := by
  decide

private theorem v4JRow34Coeff62_spec :
    mulCoeffTwo JData V4C3Data 34 62 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 62 0 := by
  decide

private theorem v4JRow34Coeff63_spec :
    mulCoeffTwo JData V4C3Data 34 63 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 63 0 := by
  decide

private theorem v4JRow34Coeff64_spec :
    mulCoeffTwo JData V4C3Data 34 64 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 64 0 := by
  decide

private theorem v4JRow34Coeff65_spec :
    mulCoeffTwo JData V4C3Data 34 65 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 65 0 := by
  decide

private theorem v4JRow34Coeff66_spec :
    mulCoeffTwo JData V4C3Data 34 66 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 66 0 := by
  decide

private theorem v4JRow34Coeff67_spec :
    mulCoeffTwo JData V4C3Data 34 67 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 67 0 := by
  decide

private theorem v4JRow34Coeff68_spec :
    mulCoeffTwo JData V4C3Data 34 68 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 68 0 := by
  decide

private theorem v4JRow34Coeff69_spec :
    mulCoeffTwo JData V4C3Data 34 69 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 69 0 := by
  decide

private theorem v4JRow34Coeff70_spec :
    mulCoeffTwo JData V4C3Data 34 70 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 70 0 := by
  decide

private theorem v4JRow34Coeff71_spec :
    mulCoeffTwo JData V4C3Data 34 71 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 71 0 := by
  decide

private theorem v4JRow34Coeff72_spec :
    mulCoeffTwo JData V4C3Data 34 72 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 72 0 := by
  decide

private theorem v4JRow34Coeff73_spec :
    mulCoeffTwo JData V4C3Data 34 73 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 73 0 := by
  decide

private theorem v4JRow34Coeff74_spec :
    mulCoeffTwo JData V4C3Data 34 74 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 74 0 := by
  decide

private theorem v4JRow34Coeff75_spec :
    mulCoeffTwo JData V4C3Data 34 75 =
      ((rectangularize 52 76 V4JData).getD 34 []).getD 75 0 := by
  decide

private theorem v4JRow34Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo JData V4C3Data 34 j =
      ((rectangularize 52 76 V4JData).getD 34 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow34Coeff0_spec
  · exact v4JRow34Coeff1_spec
  · exact v4JRow34Coeff2_spec
  · exact v4JRow34Coeff3_spec
  · exact v4JRow34Coeff4_spec
  · exact v4JRow34Coeff5_spec
  · exact v4JRow34Coeff6_spec
  · exact v4JRow34Coeff7_spec
  · exact v4JRow34Coeff8_spec
  · exact v4JRow34Coeff9_spec

private theorem v4JRow34Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo JData V4C3Data 34 j =
      ((rectangularize 52 76 V4JData).getD 34 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow34Coeff10_spec
  · exact v4JRow34Coeff11_spec
  · exact v4JRow34Coeff12_spec
  · exact v4JRow34Coeff13_spec
  · exact v4JRow34Coeff14_spec
  · exact v4JRow34Coeff15_spec
  · exact v4JRow34Coeff16_spec
  · exact v4JRow34Coeff17_spec
  · exact v4JRow34Coeff18_spec
  · exact v4JRow34Coeff19_spec

private theorem v4JRow34Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo JData V4C3Data 34 j =
      ((rectangularize 52 76 V4JData).getD 34 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow34Coeff20_spec
  · exact v4JRow34Coeff21_spec
  · exact v4JRow34Coeff22_spec
  · exact v4JRow34Coeff23_spec
  · exact v4JRow34Coeff24_spec
  · exact v4JRow34Coeff25_spec
  · exact v4JRow34Coeff26_spec
  · exact v4JRow34Coeff27_spec
  · exact v4JRow34Coeff28_spec
  · exact v4JRow34Coeff29_spec

private theorem v4JRow34Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo JData V4C3Data 34 j =
      ((rectangularize 52 76 V4JData).getD 34 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow34Coeff30_spec
  · exact v4JRow34Coeff31_spec
  · exact v4JRow34Coeff32_spec
  · exact v4JRow34Coeff33_spec
  · exact v4JRow34Coeff34_spec
  · exact v4JRow34Coeff35_spec
  · exact v4JRow34Coeff36_spec
  · exact v4JRow34Coeff37_spec
  · exact v4JRow34Coeff38_spec
  · exact v4JRow34Coeff39_spec

private theorem v4JRow34Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo JData V4C3Data 34 j =
      ((rectangularize 52 76 V4JData).getD 34 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow34Coeff40_spec
  · exact v4JRow34Coeff41_spec
  · exact v4JRow34Coeff42_spec
  · exact v4JRow34Coeff43_spec
  · exact v4JRow34Coeff44_spec
  · exact v4JRow34Coeff45_spec
  · exact v4JRow34Coeff46_spec
  · exact v4JRow34Coeff47_spec
  · exact v4JRow34Coeff48_spec
  · exact v4JRow34Coeff49_spec

private theorem v4JRow34Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo JData V4C3Data 34 j =
      ((rectangularize 52 76 V4JData).getD 34 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow34Coeff50_spec
  · exact v4JRow34Coeff51_spec
  · exact v4JRow34Coeff52_spec
  · exact v4JRow34Coeff53_spec
  · exact v4JRow34Coeff54_spec
  · exact v4JRow34Coeff55_spec
  · exact v4JRow34Coeff56_spec
  · exact v4JRow34Coeff57_spec
  · exact v4JRow34Coeff58_spec
  · exact v4JRow34Coeff59_spec

private theorem v4JRow34Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo JData V4C3Data 34 j =
      ((rectangularize 52 76 V4JData).getD 34 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact v4JRow34Coeff60_spec
  · exact v4JRow34Coeff61_spec
  · exact v4JRow34Coeff62_spec
  · exact v4JRow34Coeff63_spec
  · exact v4JRow34Coeff64_spec
  · exact v4JRow34Coeff65_spec
  · exact v4JRow34Coeff66_spec
  · exact v4JRow34Coeff67_spec
  · exact v4JRow34Coeff68_spec
  · exact v4JRow34Coeff69_spec

private theorem v4JRow34Coeffs70To75_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 76) :
    mulCoeffTwo JData V4C3Data 34 j =
      ((rectangularize 52 76 V4JData).getD 34 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 ∨ j = 73 ∨ j = 74 ∨
    j = 75 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact v4JRow34Coeff70_spec
  · exact v4JRow34Coeff71_spec
  · exact v4JRow34Coeff72_spec
  · exact v4JRow34Coeff73_spec
  · exact v4JRow34Coeff74_spec
  · exact v4JRow34Coeff75_spec

private theorem v4JRow34_coefficients (j : ℕ) (hj : j < 76) :
    mulCoeffTwo JData V4C3Data 34 j =
      ((rectangularize 52 76 V4JData).getD 34 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact v4JRow34Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact v4JRow34Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact v4JRow34Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact v4JRow34Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact v4JRow34Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact v4JRow34Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact v4JRow34Coeffs60To69_spec j (by omega) h70
  exact v4JRow34Coeffs70To75_spec j (by omega) hj

private theorem v4JRow34_spec :
    padOne 76 (mulRow JData V4C3Data 34) =
      (rectangularize 52 76 V4JData).getD 34 [] := by
  apply padOne_mulRow_eq_of_coefficients 76 JData V4C3Data 34
    ((rectangularize 52 76 V4JData).getD 34 [])
  · decide
  · have hTargetSupport : (V4JData.getD 34 []).length ≤ 76 := by
      decide
    rw [getD_rectangularize 52 76 V4JData 34 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact v4JRow34_coefficients

private theorem v4JRow35_spec :
    padOne 76 (mulRow JData V4C3Data 35) =
      (rectangularize 52 76 V4JData).getD 35 [] := by
  decide

private theorem v4JRow36_spec :
    padOne 76 (mulRow JData V4C3Data 36) =
      (rectangularize 52 76 V4JData).getD 36 [] := by
  decide

private theorem v4JRow37_spec :
    padOne 76 (mulRow JData V4C3Data 37) =
      (rectangularize 52 76 V4JData).getD 37 [] := by
  decide

private theorem v4JRow38_spec :
    padOne 76 (mulRow JData V4C3Data 38) =
      (rectangularize 52 76 V4JData).getD 38 [] := by
  decide

private theorem v4JRow39_spec :
    padOne 76 (mulRow JData V4C3Data 39) =
      (rectangularize 52 76 V4JData).getD 39 [] := by
  decide

private theorem v4JRow40_spec :
    padOne 76 (mulRow JData V4C3Data 40) =
      (rectangularize 52 76 V4JData).getD 40 [] := by
  decide

private theorem v4JRow41_spec :
    padOne 76 (mulRow JData V4C3Data 41) =
      (rectangularize 52 76 V4JData).getD 41 [] := by
  decide

private theorem v4JRow42_spec :
    padOne 76 (mulRow JData V4C3Data 42) =
      (rectangularize 52 76 V4JData).getD 42 [] := by
  decide

private theorem v4JRow43_spec :
    padOne 76 (mulRow JData V4C3Data 43) =
      (rectangularize 52 76 V4JData).getD 43 [] := by
  decide

private theorem v4JRow44_spec :
    padOne 76 (mulRow JData V4C3Data 44) =
      (rectangularize 52 76 V4JData).getD 44 [] := by
  decide

private theorem v4JRow45_spec :
    padOne 76 (mulRow JData V4C3Data 45) =
      (rectangularize 52 76 V4JData).getD 45 [] := by
  decide

private theorem v4JRow46_spec :
    padOne 76 (mulRow JData V4C3Data 46) =
      (rectangularize 52 76 V4JData).getD 46 [] := by
  decide

private theorem v4JRow47_spec :
    padOne 76 (mulRow JData V4C3Data 47) =
      (rectangularize 52 76 V4JData).getD 47 [] := by
  decide

private theorem v4JRow48_spec :
    padOne 76 (mulRow JData V4C3Data 48) =
      (rectangularize 52 76 V4JData).getD 48 [] := by
  decide

private theorem v4JRow49_spec :
    padOne 76 (mulRow JData V4C3Data 49) =
      (rectangularize 52 76 V4JData).getD 49 [] := by
  decide

private theorem v4JRow50_spec :
    padOne 76 (mulRow JData V4C3Data 50) =
      (rectangularize 52 76 V4JData).getD 50 [] := by
  decide

private theorem v4JRow51_spec :
    padOne 76 (mulRow JData V4C3Data 51) =
      (rectangularize 52 76 V4JData).getD 51 [] := by
  decide

private theorem v4JRows_spec (n : ℕ) (hn : n < 52) :
    padOne 76 (mulRow JData V4C3Data n) =
      (rectangularize 52 76 V4JData).getD n [] := by
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
  · exact v4JRow0_spec
  · exact v4JRow1_spec
  · exact v4JRow2_spec
  · exact v4JRow3_spec
  · exact v4JRow4_spec
  · exact v4JRow5_spec
  · exact v4JRow6_spec
  · exact v4JRow7_spec
  · exact v4JRow8_spec
  · exact v4JRow9_spec
  · exact v4JRow10_spec
  · exact v4JRow11_spec
  · exact v4JRow12_spec
  · exact v4JRow13_spec
  · exact v4JRow14_spec
  · exact v4JRow15_spec
  · exact v4JRow16_spec
  · exact v4JRow17_spec
  · exact v4JRow18_spec
  · exact v4JRow19_spec
  · exact v4JRow20_spec
  · exact v4JRow21_spec
  · exact v4JRow22_spec
  · exact v4JRow23_spec
  · exact v4JRow24_spec
  · exact v4JRow25_spec
  · exact v4JRow26_spec
  · exact v4JRow27_spec
  · exact v4JRow28_spec
  · exact v4JRow29_spec
  · exact v4JRow30_spec
  · exact v4JRow31_spec
  · exact v4JRow32_spec
  · exact v4JRow33_spec
  · exact v4JRow34_spec
  · exact v4JRow35_spec
  · exact v4JRow36_spec
  · exact v4JRow37_spec
  · exact v4JRow38_spec
  · exact v4JRow39_spec
  · exact v4JRow40_spec
  · exact v4JRow41_spec
  · exact v4JRow42_spec
  · exact v4JRow43_spec
  · exact v4JRow44_spec
  · exact v4JRow45_spec
  · exact v4JRow46_spec
  · exact v4JRow47_spec
  · exact v4JRow48_spec
  · exact v4JRow49_spec
  · exact v4JRow50_spec
  · exact v4JRow51_spec

private theorem v4JLeft_length :
    (rectangularize 52 76 (Two.mul JData V4C3Data)).length = 52 := by
  decide

private theorem v4JRight_length :
    (rectangularize 52 76 V4JData).length = 52 := by
  decide

-- Exact bidegree bound (51, 75); no row or column is discarded.
private theorem v4JData_spec :
    rectangularize 52 76 (Two.mul JData V4C3Data) =
      rectangularize 52 76 V4JData := by
  apply List.ext_getElem (v4JLeft_length.trans v4JRight_length.symm)
  intro n hn _
  rw [List.getElem_eq_getD [], List.getElem_eq_getD []]
  rw [v4JLeft_length] at hn
  rw [getD_rectangularize 52 76 (Two.mul JData V4C3Data) n hn,
    ← mulRow_eq_getD]
  exact v4JRows_spec n hn

/-- Evaluation of the checked primitive core in the fourth power of `V`. -/
theorem eval_v4JData (r s : ℚ) :
    Two.eval V4JData r s =
      OrderTwentyFiveRelationZeroCertificate.Internal.J r s *
        OrderTwentyFiveRelationZeroCertificate.Internal.C r s ^ 3 * s *
          (Two.eval VData r s * Two.eval V2Data r s) := by
  have hS := congrArg (fun p => Two.eval p r s) v4SData_spec
  have hC1 := congrArg (fun p => Two.eval p r s) v4C1Data_spec
  have hC2 := congrArg (fun p => Two.eval p r s) v4C2Data_spec
  have hC3 := congrArg (fun p => Two.eval p r s) v4C3Data_spec
  have hJ := congrArg (fun p => Two.eval p r s) v4JData_spec
  simp only [eval_rectangularize, Two.eval_mul] at hS hC1 hC2 hC3 hJ
  calc
    Two.eval V4JData r s =
        Two.eval JData r s * Two.eval V4C3Data r s := hJ.symm
    _ = Two.eval JData r s *
        (Two.eval CData r s * Two.eval V4C2Data r s) := by rw [← hC3]
    _ = Two.eval JData r s *
        (Two.eval CData r s *
          (Two.eval CData r s * Two.eval V4C1Data r s)) := by rw [← hC2]
    _ = Two.eval JData r s *
        (Two.eval CData r s *
          (Two.eval CData r s *
            (Two.eval CData r s * Two.eval V4SData r s))) := by rw [← hC1]
    _ = OrderTwentyFiveRelationZeroCertificate.Internal.J r s *
        OrderTwentyFiveRelationZeroCertificate.Internal.C r s ^ 3 * s *
          (Two.eval VData r s * Two.eval V2Data r s) := by
      rw [← hS, eval_JData, eval_CData, eval_SData, eval_v3Data]
      ring

end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
