/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialXFourNLeftCertificate
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialXFourNRightCertificate
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroBridge

/-!
# Checked canonical completion of the raw X fourth-power table

Every stated rectangle is an exact bidegree bound, and `rectangularize` only
appends zeros.  The row-sharded equalities therefore check all coefficients
and all possible tails.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveRelationZeroCertificate.Dense
open OrderTwentyFiveDensePolynomialRectangular
open OrderTwentyFiveDensePolynomialRowCertificate

private theorem x4SubRow0_spec :
    (rectangularize 53 73 (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 0 [] =
      (rectangularize 53 73 X4Data).getD 0 [] := by
  decide

private theorem x4SubRow1_spec :
    (rectangularize 53 73 (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 1 [] =
      (rectangularize 53 73 X4Data).getD 1 [] := by
  decide

private theorem x4SubRow2_spec :
    (rectangularize 53 73 (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 2 [] =
      (rectangularize 53 73 X4Data).getD 2 [] := by
  decide

private theorem x4SubRow3_spec :
    (rectangularize 53 73 (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 3 [] =
      (rectangularize 53 73 X4Data).getD 3 [] := by
  decide

private theorem x4SubRow4_spec :
    (rectangularize 53 73 (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 4 [] =
      (rectangularize 53 73 X4Data).getD 4 [] := by
  decide

private theorem x4SubRow5_spec :
    (rectangularize 53 73 (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 5 [] =
      (rectangularize 53 73 X4Data).getD 5 [] := by
  decide

private theorem x4SubRow6_spec :
    (rectangularize 53 73 (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 6 [] =
      (rectangularize 53 73 X4Data).getD 6 [] := by
  decide

private theorem x4SubRow7_spec :
    (rectangularize 53 73 (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 7 [] =
      (rectangularize 53 73 X4Data).getD 7 [] := by
  decide

private theorem x4SubRow8_spec :
    (rectangularize 53 73 (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 8 [] =
      (rectangularize 53 73 X4Data).getD 8 [] := by
  decide

private theorem x4SubRow9_spec :
    (rectangularize 53 73 (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 9 [] =
      (rectangularize 53 73 X4Data).getD 9 [] := by
  decide

private theorem x4SubRow10_spec :
    (rectangularize 53 73 (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 10 [] =
      (rectangularize 53 73 X4Data).getD 10 [] := by
  decide

private theorem x4SubRow11_spec :
    (rectangularize 53 73 (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 11 [] =
      (rectangularize 53 73 X4Data).getD 11 [] := by
  decide

private theorem x4SubRow12_spec :
    (rectangularize 53 73 (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 12 [] =
      (rectangularize 53 73 X4Data).getD 12 [] := by
  decide

private theorem x4SubRow13_spec :
    (rectangularize 53 73 (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 13 [] =
      (rectangularize 53 73 X4Data).getD 13 [] := by
  decide

private theorem x4SubRow14Coeff0_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 0 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 0 0 := by
  decide

private theorem x4SubRow14Coeff1_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 1 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 1 0 := by
  decide

private theorem x4SubRow14Coeff2_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 2 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 2 0 := by
  decide

private theorem x4SubRow14Coeff3_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 3 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 3 0 := by
  decide

private theorem x4SubRow14Coeff4_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 4 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 4 0 := by
  decide

private theorem x4SubRow14Coeff5_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 5 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 5 0 := by
  decide

private theorem x4SubRow14Coeff6_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 6 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 6 0 := by
  decide

private theorem x4SubRow14Coeff7_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 7 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 7 0 := by
  decide

private theorem x4SubRow14Coeff8_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 8 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 8 0 := by
  decide

private theorem x4SubRow14Coeff9_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 9 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 9 0 := by
  decide

private theorem x4SubRow14Coeff10_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 10 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 10 0 := by
  decide

private theorem x4SubRow14Coeff11_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 11 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 11 0 := by
  decide

private theorem x4SubRow14Coeff12_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 12 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 12 0 := by
  decide

private theorem x4SubRow14Coeff13_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 13 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 13 0 := by
  decide

private theorem x4SubRow14Coeff14_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 14 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 14 0 := by
  decide

private theorem x4SubRow14Coeff15_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 15 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 15 0 := by
  decide

private theorem x4SubRow14Coeff16_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 16 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 16 0 := by
  decide

private theorem x4SubRow14Coeff17_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 17 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 17 0 := by
  decide

private theorem x4SubRow14Coeff18_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 18 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 18 0 := by
  decide

private theorem x4SubRow14Coeff19_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 19 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 19 0 := by
  decide

private theorem x4SubRow14Coeff20_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 20 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 20 0 := by
  decide

private theorem x4SubRow14Coeff21_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 21 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 21 0 := by
  decide

private theorem x4SubRow14Coeff22_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 22 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 22 0 := by
  decide

private theorem x4SubRow14Coeff23_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 23 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 23 0 := by
  decide

private theorem x4SubRow14Coeff24_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 24 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 24 0 := by
  decide

private theorem x4SubRow14Coeff25_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 25 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 25 0 := by
  decide

private theorem x4SubRow14Coeff26_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 26 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 26 0 := by
  decide

private theorem x4SubRow14Coeff27_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 27 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 27 0 := by
  decide

private theorem x4SubRow14Coeff28_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 28 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 28 0 := by
  decide

private theorem x4SubRow14Coeff29_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 29 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 29 0 := by
  decide

private theorem x4SubRow14Coeff30_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 30 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 30 0 := by
  decide

private theorem x4SubRow14Coeff31_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 31 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 31 0 := by
  decide

private theorem x4SubRow14Coeff32_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 32 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 32 0 := by
  decide

private theorem x4SubRow14Coeff33_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 33 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 33 0 := by
  decide

private theorem x4SubRow14Coeff34_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 34 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 34 0 := by
  decide

private theorem x4SubRow14Coeff35_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 35 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 35 0 := by
  decide

private theorem x4SubRow14Coeff36_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 36 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 36 0 := by
  decide

private theorem x4SubRow14Coeff37_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 37 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 37 0 := by
  decide

private theorem x4SubRow14Coeff38_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 38 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 38 0 := by
  decide

private theorem x4SubRow14Coeff39_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 39 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 39 0 := by
  decide

private theorem x4SubRow14Coeff40_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 40 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 40 0 := by
  decide

private theorem x4SubRow14Coeff41_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 41 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 41 0 := by
  decide

private theorem x4SubRow14Coeff42_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 42 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 42 0 := by
  decide

private theorem x4SubRow14Coeff43_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 43 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 43 0 := by
  decide

private theorem x4SubRow14Coeff44_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 44 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 44 0 := by
  decide

private theorem x4SubRow14Coeff45_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 45 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 45 0 := by
  decide

private theorem x4SubRow14Coeff46_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 46 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 46 0 := by
  decide

private theorem x4SubRow14Coeff47_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 47 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 47 0 := by
  decide

private theorem x4SubRow14Coeff48_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 48 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 48 0 := by
  decide

private theorem x4SubRow14Coeff49_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 49 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 49 0 := by
  decide

private theorem x4SubRow14Coeff50_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 50 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 50 0 := by
  decide

private theorem x4SubRow14Coeff51_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 51 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 51 0 := by
  decide

private theorem x4SubRow14Coeff52_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 52 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 52 0 := by
  decide

private theorem x4SubRow14Coeff53_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 53 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 53 0 := by
  decide

private theorem x4SubRow14Coeff54_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 54 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 54 0 := by
  decide

private theorem x4SubRow14Coeff55_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 55 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 55 0 := by
  decide

private theorem x4SubRow14Coeff56_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 56 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 56 0 := by
  decide

private theorem x4SubRow14Coeff57_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 57 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 57 0 := by
  decide

private theorem x4SubRow14Coeff58_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 58 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 58 0 := by
  decide

private theorem x4SubRow14Coeff59_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 59 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 59 0 := by
  decide

private theorem x4SubRow14Coeff60_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 60 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 60 0 := by
  decide

private theorem x4SubRow14Coeff61_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 61 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 61 0 := by
  decide

private theorem x4SubRow14Coeff62_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 62 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 62 0 := by
  decide

private theorem x4SubRow14Coeff63_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 63 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 63 0 := by
  decide

private theorem x4SubRow14Coeff64_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 64 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 64 0 := by
  decide

private theorem x4SubRow14Coeff65_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 65 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 65 0 := by
  decide

private theorem x4SubRow14Coeff66_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 66 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 66 0 := by
  decide

private theorem x4SubRow14Coeff67_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 67 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 67 0 := by
  decide

private theorem x4SubRow14Coeff68_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 68 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 68 0 := by
  decide

private theorem x4SubRow14Coeff69_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 69 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 69 0 := by
  decide

private theorem x4SubRow14Coeff70_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 70 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 70 0 := by
  decide

private theorem x4SubRow14Coeff71_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 71 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 71 0 := by
  decide

private theorem x4SubRow14Coeff72_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 72 =
      ((rectangularize 53 73 X4Data).getD 14 []).getD 72 0 := by
  decide

private theorem x4SubRow14Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 j =
      ((rectangularize 53 73 X4Data).getD 14 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow14Coeff0_spec
  · exact x4SubRow14Coeff1_spec
  · exact x4SubRow14Coeff2_spec
  · exact x4SubRow14Coeff3_spec
  · exact x4SubRow14Coeff4_spec
  · exact x4SubRow14Coeff5_spec
  · exact x4SubRow14Coeff6_spec
  · exact x4SubRow14Coeff7_spec
  · exact x4SubRow14Coeff8_spec
  · exact x4SubRow14Coeff9_spec

private theorem x4SubRow14Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 j =
      ((rectangularize 53 73 X4Data).getD 14 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow14Coeff10_spec
  · exact x4SubRow14Coeff11_spec
  · exact x4SubRow14Coeff12_spec
  · exact x4SubRow14Coeff13_spec
  · exact x4SubRow14Coeff14_spec
  · exact x4SubRow14Coeff15_spec
  · exact x4SubRow14Coeff16_spec
  · exact x4SubRow14Coeff17_spec
  · exact x4SubRow14Coeff18_spec
  · exact x4SubRow14Coeff19_spec

private theorem x4SubRow14Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 j =
      ((rectangularize 53 73 X4Data).getD 14 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow14Coeff20_spec
  · exact x4SubRow14Coeff21_spec
  · exact x4SubRow14Coeff22_spec
  · exact x4SubRow14Coeff23_spec
  · exact x4SubRow14Coeff24_spec
  · exact x4SubRow14Coeff25_spec
  · exact x4SubRow14Coeff26_spec
  · exact x4SubRow14Coeff27_spec
  · exact x4SubRow14Coeff28_spec
  · exact x4SubRow14Coeff29_spec

private theorem x4SubRow14Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 j =
      ((rectangularize 53 73 X4Data).getD 14 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow14Coeff30_spec
  · exact x4SubRow14Coeff31_spec
  · exact x4SubRow14Coeff32_spec
  · exact x4SubRow14Coeff33_spec
  · exact x4SubRow14Coeff34_spec
  · exact x4SubRow14Coeff35_spec
  · exact x4SubRow14Coeff36_spec
  · exact x4SubRow14Coeff37_spec
  · exact x4SubRow14Coeff38_spec
  · exact x4SubRow14Coeff39_spec

private theorem x4SubRow14Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 j =
      ((rectangularize 53 73 X4Data).getD 14 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow14Coeff40_spec
  · exact x4SubRow14Coeff41_spec
  · exact x4SubRow14Coeff42_spec
  · exact x4SubRow14Coeff43_spec
  · exact x4SubRow14Coeff44_spec
  · exact x4SubRow14Coeff45_spec
  · exact x4SubRow14Coeff46_spec
  · exact x4SubRow14Coeff47_spec
  · exact x4SubRow14Coeff48_spec
  · exact x4SubRow14Coeff49_spec

private theorem x4SubRow14Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 j =
      ((rectangularize 53 73 X4Data).getD 14 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow14Coeff50_spec
  · exact x4SubRow14Coeff51_spec
  · exact x4SubRow14Coeff52_spec
  · exact x4SubRow14Coeff53_spec
  · exact x4SubRow14Coeff54_spec
  · exact x4SubRow14Coeff55_spec
  · exact x4SubRow14Coeff56_spec
  · exact x4SubRow14Coeff57_spec
  · exact x4SubRow14Coeff58_spec
  · exact x4SubRow14Coeff59_spec

private theorem x4SubRow14Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 j =
      ((rectangularize 53 73 X4Data).getD 14 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow14Coeff60_spec
  · exact x4SubRow14Coeff61_spec
  · exact x4SubRow14Coeff62_spec
  · exact x4SubRow14Coeff63_spec
  · exact x4SubRow14Coeff64_spec
  · exact x4SubRow14Coeff65_spec
  · exact x4SubRow14Coeff66_spec
  · exact x4SubRow14Coeff67_spec
  · exact x4SubRow14Coeff68_spec
  · exact x4SubRow14Coeff69_spec

private theorem x4SubRow14Coeffs70To72_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 73) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 j =
      ((rectangularize 53 73 X4Data).getD 14 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 := by
    omega
  rcases hCases with
    rfl | rfl | rfl
  · exact x4SubRow14Coeff70_spec
  · exact x4SubRow14Coeff71_spec
  · exact x4SubRow14Coeff72_spec

private theorem x4SubRow14_coefficients (j : ℕ) (hj : j < 73) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 14 j =
      ((rectangularize 53 73 X4Data).getD 14 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact x4SubRow14Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact x4SubRow14Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact x4SubRow14Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact x4SubRow14Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact x4SubRow14Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact x4SubRow14Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact x4SubRow14Coeffs60To69_spec j (by omega) h70
  exact x4SubRow14Coeffs70To72_spec j (by omega) hj

private theorem x4SubRow14Padded_spec :
    padOne 73
        (addMulRow X4NLK3Data NegData X4NRGData 14) =
      (rectangularize 53 73 X4Data).getD 14 [] := by
  apply padOne_addMulRow_eq_of_coefficients 73
    X4NLK3Data NegData X4NRGData 14
    ((rectangularize 53 73 X4Data).getD 14 [])
  · decide
  · have hTargetSupport : (X4Data.getD 14 []).length ≤ 73 := by
      decide
    rw [getD_rectangularize 53 73 X4Data 14 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact x4SubRow14_coefficients

private theorem x4SubRow14_spec :
    (rectangularize 53 73
        (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 14 [] =
      (rectangularize 53 73 X4Data).getD 14 [] := by
  rw [getD_rectangularize 53 73
    (Two.add X4NLK3Data (Two.mul NegData X4NRGData)) 14 (by omega),
    ← addMulRow_eq_getD]
  exact x4SubRow14Padded_spec

private theorem x4SubRow15Coeff0_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 0 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 0 0 := by
  decide

private theorem x4SubRow15Coeff1_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 1 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 1 0 := by
  decide

private theorem x4SubRow15Coeff2_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 2 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 2 0 := by
  decide

private theorem x4SubRow15Coeff3_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 3 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 3 0 := by
  decide

private theorem x4SubRow15Coeff4_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 4 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 4 0 := by
  decide

private theorem x4SubRow15Coeff5_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 5 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 5 0 := by
  decide

private theorem x4SubRow15Coeff6_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 6 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 6 0 := by
  decide

private theorem x4SubRow15Coeff7_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 7 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 7 0 := by
  decide

private theorem x4SubRow15Coeff8_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 8 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 8 0 := by
  decide

private theorem x4SubRow15Coeff9_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 9 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 9 0 := by
  decide

private theorem x4SubRow15Coeff10_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 10 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 10 0 := by
  decide

private theorem x4SubRow15Coeff11_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 11 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 11 0 := by
  decide

private theorem x4SubRow15Coeff12_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 12 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 12 0 := by
  decide

private theorem x4SubRow15Coeff13_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 13 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 13 0 := by
  decide

private theorem x4SubRow15Coeff14_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 14 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 14 0 := by
  decide

private theorem x4SubRow15Coeff15_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 15 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 15 0 := by
  decide

private theorem x4SubRow15Coeff16_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 16 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 16 0 := by
  decide

private theorem x4SubRow15Coeff17_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 17 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 17 0 := by
  decide

private theorem x4SubRow15Coeff18_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 18 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 18 0 := by
  decide

private theorem x4SubRow15Coeff19_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 19 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 19 0 := by
  decide

private theorem x4SubRow15Coeff20_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 20 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 20 0 := by
  decide

private theorem x4SubRow15Coeff21_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 21 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 21 0 := by
  decide

private theorem x4SubRow15Coeff22_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 22 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 22 0 := by
  decide

private theorem x4SubRow15Coeff23_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 23 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 23 0 := by
  decide

private theorem x4SubRow15Coeff24_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 24 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 24 0 := by
  decide

private theorem x4SubRow15Coeff25_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 25 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 25 0 := by
  decide

private theorem x4SubRow15Coeff26_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 26 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 26 0 := by
  decide

private theorem x4SubRow15Coeff27_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 27 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 27 0 := by
  decide

private theorem x4SubRow15Coeff28_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 28 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 28 0 := by
  decide

private theorem x4SubRow15Coeff29_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 29 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 29 0 := by
  decide

private theorem x4SubRow15Coeff30_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 30 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 30 0 := by
  decide

private theorem x4SubRow15Coeff31_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 31 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 31 0 := by
  decide

private theorem x4SubRow15Coeff32_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 32 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 32 0 := by
  decide

private theorem x4SubRow15Coeff33_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 33 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 33 0 := by
  decide

private theorem x4SubRow15Coeff34_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 34 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 34 0 := by
  decide

private theorem x4SubRow15Coeff35_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 35 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 35 0 := by
  decide

private theorem x4SubRow15Coeff36_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 36 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 36 0 := by
  decide

private theorem x4SubRow15Coeff37_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 37 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 37 0 := by
  decide

private theorem x4SubRow15Coeff38_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 38 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 38 0 := by
  decide

private theorem x4SubRow15Coeff39_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 39 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 39 0 := by
  decide

private theorem x4SubRow15Coeff40_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 40 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 40 0 := by
  decide

private theorem x4SubRow15Coeff41_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 41 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 41 0 := by
  decide

private theorem x4SubRow15Coeff42_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 42 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 42 0 := by
  decide

private theorem x4SubRow15Coeff43_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 43 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 43 0 := by
  decide

private theorem x4SubRow15Coeff44_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 44 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 44 0 := by
  decide

private theorem x4SubRow15Coeff45_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 45 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 45 0 := by
  decide

private theorem x4SubRow15Coeff46_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 46 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 46 0 := by
  decide

private theorem x4SubRow15Coeff47_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 47 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 47 0 := by
  decide

private theorem x4SubRow15Coeff48_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 48 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 48 0 := by
  decide

private theorem x4SubRow15Coeff49_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 49 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 49 0 := by
  decide

private theorem x4SubRow15Coeff50_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 50 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 50 0 := by
  decide

private theorem x4SubRow15Coeff51_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 51 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 51 0 := by
  decide

private theorem x4SubRow15Coeff52_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 52 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 52 0 := by
  decide

private theorem x4SubRow15Coeff53_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 53 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 53 0 := by
  decide

private theorem x4SubRow15Coeff54_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 54 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 54 0 := by
  decide

private theorem x4SubRow15Coeff55_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 55 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 55 0 := by
  decide

private theorem x4SubRow15Coeff56_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 56 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 56 0 := by
  decide

private theorem x4SubRow15Coeff57_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 57 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 57 0 := by
  decide

private theorem x4SubRow15Coeff58_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 58 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 58 0 := by
  decide

private theorem x4SubRow15Coeff59_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 59 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 59 0 := by
  decide

private theorem x4SubRow15Coeff60_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 60 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 60 0 := by
  decide

private theorem x4SubRow15Coeff61_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 61 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 61 0 := by
  decide

private theorem x4SubRow15Coeff62_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 62 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 62 0 := by
  decide

private theorem x4SubRow15Coeff63_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 63 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 63 0 := by
  decide

private theorem x4SubRow15Coeff64_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 64 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 64 0 := by
  decide

private theorem x4SubRow15Coeff65_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 65 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 65 0 := by
  decide

private theorem x4SubRow15Coeff66_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 66 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 66 0 := by
  decide

private theorem x4SubRow15Coeff67_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 67 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 67 0 := by
  decide

private theorem x4SubRow15Coeff68_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 68 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 68 0 := by
  decide

private theorem x4SubRow15Coeff69_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 69 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 69 0 := by
  decide

private theorem x4SubRow15Coeff70_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 70 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 70 0 := by
  decide

private theorem x4SubRow15Coeff71_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 71 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 71 0 := by
  decide

private theorem x4SubRow15Coeff72_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 72 =
      ((rectangularize 53 73 X4Data).getD 15 []).getD 72 0 := by
  decide

private theorem x4SubRow15Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 j =
      ((rectangularize 53 73 X4Data).getD 15 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow15Coeff0_spec
  · exact x4SubRow15Coeff1_spec
  · exact x4SubRow15Coeff2_spec
  · exact x4SubRow15Coeff3_spec
  · exact x4SubRow15Coeff4_spec
  · exact x4SubRow15Coeff5_spec
  · exact x4SubRow15Coeff6_spec
  · exact x4SubRow15Coeff7_spec
  · exact x4SubRow15Coeff8_spec
  · exact x4SubRow15Coeff9_spec

private theorem x4SubRow15Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 j =
      ((rectangularize 53 73 X4Data).getD 15 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow15Coeff10_spec
  · exact x4SubRow15Coeff11_spec
  · exact x4SubRow15Coeff12_spec
  · exact x4SubRow15Coeff13_spec
  · exact x4SubRow15Coeff14_spec
  · exact x4SubRow15Coeff15_spec
  · exact x4SubRow15Coeff16_spec
  · exact x4SubRow15Coeff17_spec
  · exact x4SubRow15Coeff18_spec
  · exact x4SubRow15Coeff19_spec

private theorem x4SubRow15Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 j =
      ((rectangularize 53 73 X4Data).getD 15 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow15Coeff20_spec
  · exact x4SubRow15Coeff21_spec
  · exact x4SubRow15Coeff22_spec
  · exact x4SubRow15Coeff23_spec
  · exact x4SubRow15Coeff24_spec
  · exact x4SubRow15Coeff25_spec
  · exact x4SubRow15Coeff26_spec
  · exact x4SubRow15Coeff27_spec
  · exact x4SubRow15Coeff28_spec
  · exact x4SubRow15Coeff29_spec

private theorem x4SubRow15Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 j =
      ((rectangularize 53 73 X4Data).getD 15 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow15Coeff30_spec
  · exact x4SubRow15Coeff31_spec
  · exact x4SubRow15Coeff32_spec
  · exact x4SubRow15Coeff33_spec
  · exact x4SubRow15Coeff34_spec
  · exact x4SubRow15Coeff35_spec
  · exact x4SubRow15Coeff36_spec
  · exact x4SubRow15Coeff37_spec
  · exact x4SubRow15Coeff38_spec
  · exact x4SubRow15Coeff39_spec

private theorem x4SubRow15Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 j =
      ((rectangularize 53 73 X4Data).getD 15 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow15Coeff40_spec
  · exact x4SubRow15Coeff41_spec
  · exact x4SubRow15Coeff42_spec
  · exact x4SubRow15Coeff43_spec
  · exact x4SubRow15Coeff44_spec
  · exact x4SubRow15Coeff45_spec
  · exact x4SubRow15Coeff46_spec
  · exact x4SubRow15Coeff47_spec
  · exact x4SubRow15Coeff48_spec
  · exact x4SubRow15Coeff49_spec

private theorem x4SubRow15Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 j =
      ((rectangularize 53 73 X4Data).getD 15 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow15Coeff50_spec
  · exact x4SubRow15Coeff51_spec
  · exact x4SubRow15Coeff52_spec
  · exact x4SubRow15Coeff53_spec
  · exact x4SubRow15Coeff54_spec
  · exact x4SubRow15Coeff55_spec
  · exact x4SubRow15Coeff56_spec
  · exact x4SubRow15Coeff57_spec
  · exact x4SubRow15Coeff58_spec
  · exact x4SubRow15Coeff59_spec

private theorem x4SubRow15Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 j =
      ((rectangularize 53 73 X4Data).getD 15 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow15Coeff60_spec
  · exact x4SubRow15Coeff61_spec
  · exact x4SubRow15Coeff62_spec
  · exact x4SubRow15Coeff63_spec
  · exact x4SubRow15Coeff64_spec
  · exact x4SubRow15Coeff65_spec
  · exact x4SubRow15Coeff66_spec
  · exact x4SubRow15Coeff67_spec
  · exact x4SubRow15Coeff68_spec
  · exact x4SubRow15Coeff69_spec

private theorem x4SubRow15Coeffs70To72_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 73) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 j =
      ((rectangularize 53 73 X4Data).getD 15 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 := by
    omega
  rcases hCases with
    rfl | rfl | rfl
  · exact x4SubRow15Coeff70_spec
  · exact x4SubRow15Coeff71_spec
  · exact x4SubRow15Coeff72_spec

private theorem x4SubRow15_coefficients (j : ℕ) (hj : j < 73) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 15 j =
      ((rectangularize 53 73 X4Data).getD 15 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact x4SubRow15Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact x4SubRow15Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact x4SubRow15Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact x4SubRow15Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact x4SubRow15Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact x4SubRow15Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact x4SubRow15Coeffs60To69_spec j (by omega) h70
  exact x4SubRow15Coeffs70To72_spec j (by omega) hj

private theorem x4SubRow15Padded_spec :
    padOne 73
        (addMulRow X4NLK3Data NegData X4NRGData 15) =
      (rectangularize 53 73 X4Data).getD 15 [] := by
  apply padOne_addMulRow_eq_of_coefficients 73
    X4NLK3Data NegData X4NRGData 15
    ((rectangularize 53 73 X4Data).getD 15 [])
  · decide
  · have hTargetSupport : (X4Data.getD 15 []).length ≤ 73 := by
      decide
    rw [getD_rectangularize 53 73 X4Data 15 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact x4SubRow15_coefficients

private theorem x4SubRow15_spec :
    (rectangularize 53 73
        (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 15 [] =
      (rectangularize 53 73 X4Data).getD 15 [] := by
  rw [getD_rectangularize 53 73
    (Two.add X4NLK3Data (Two.mul NegData X4NRGData)) 15 (by omega),
    ← addMulRow_eq_getD]
  exact x4SubRow15Padded_spec

private theorem x4SubRow16Coeff0_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 0 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 0 0 := by
  decide

private theorem x4SubRow16Coeff1_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 1 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 1 0 := by
  decide

private theorem x4SubRow16Coeff2_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 2 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 2 0 := by
  decide

private theorem x4SubRow16Coeff3_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 3 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 3 0 := by
  decide

private theorem x4SubRow16Coeff4_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 4 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 4 0 := by
  decide

private theorem x4SubRow16Coeff5_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 5 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 5 0 := by
  decide

private theorem x4SubRow16Coeff6_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 6 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 6 0 := by
  decide

private theorem x4SubRow16Coeff7_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 7 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 7 0 := by
  decide

private theorem x4SubRow16Coeff8_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 8 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 8 0 := by
  decide

private theorem x4SubRow16Coeff9_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 9 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 9 0 := by
  decide

private theorem x4SubRow16Coeff10_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 10 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 10 0 := by
  decide

private theorem x4SubRow16Coeff11_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 11 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 11 0 := by
  decide

private theorem x4SubRow16Coeff12_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 12 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 12 0 := by
  decide

private theorem x4SubRow16Coeff13_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 13 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 13 0 := by
  decide

private theorem x4SubRow16Coeff14_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 14 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 14 0 := by
  decide

private theorem x4SubRow16Coeff15_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 15 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 15 0 := by
  decide

private theorem x4SubRow16Coeff16_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 16 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 16 0 := by
  decide

private theorem x4SubRow16Coeff17_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 17 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 17 0 := by
  decide

private theorem x4SubRow16Coeff18_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 18 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 18 0 := by
  decide

private theorem x4SubRow16Coeff19_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 19 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 19 0 := by
  decide

private theorem x4SubRow16Coeff20_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 20 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 20 0 := by
  decide

private theorem x4SubRow16Coeff21_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 21 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 21 0 := by
  decide

private theorem x4SubRow16Coeff22_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 22 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 22 0 := by
  decide

private theorem x4SubRow16Coeff23_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 23 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 23 0 := by
  decide

private theorem x4SubRow16Coeff24_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 24 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 24 0 := by
  decide

private theorem x4SubRow16Coeff25_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 25 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 25 0 := by
  decide

private theorem x4SubRow16Coeff26_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 26 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 26 0 := by
  decide

private theorem x4SubRow16Coeff27_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 27 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 27 0 := by
  decide

private theorem x4SubRow16Coeff28_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 28 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 28 0 := by
  decide

private theorem x4SubRow16Coeff29_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 29 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 29 0 := by
  decide

private theorem x4SubRow16Coeff30_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 30 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 30 0 := by
  decide

private theorem x4SubRow16Coeff31_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 31 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 31 0 := by
  decide

private theorem x4SubRow16Coeff32_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 32 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 32 0 := by
  decide

private theorem x4SubRow16Coeff33_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 33 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 33 0 := by
  decide

private theorem x4SubRow16Coeff34_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 34 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 34 0 := by
  decide

private theorem x4SubRow16Coeff35_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 35 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 35 0 := by
  decide

private theorem x4SubRow16Coeff36_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 36 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 36 0 := by
  decide

private theorem x4SubRow16Coeff37_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 37 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 37 0 := by
  decide

private theorem x4SubRow16Coeff38_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 38 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 38 0 := by
  decide

private theorem x4SubRow16Coeff39_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 39 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 39 0 := by
  decide

private theorem x4SubRow16Coeff40_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 40 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 40 0 := by
  decide

private theorem x4SubRow16Coeff41_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 41 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 41 0 := by
  decide

private theorem x4SubRow16Coeff42_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 42 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 42 0 := by
  decide

private theorem x4SubRow16Coeff43_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 43 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 43 0 := by
  decide

private theorem x4SubRow16Coeff44_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 44 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 44 0 := by
  decide

private theorem x4SubRow16Coeff45_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 45 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 45 0 := by
  decide

private theorem x4SubRow16Coeff46_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 46 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 46 0 := by
  decide

private theorem x4SubRow16Coeff47_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 47 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 47 0 := by
  decide

private theorem x4SubRow16Coeff48_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 48 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 48 0 := by
  decide

private theorem x4SubRow16Coeff49_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 49 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 49 0 := by
  decide

private theorem x4SubRow16Coeff50_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 50 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 50 0 := by
  decide

private theorem x4SubRow16Coeff51_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 51 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 51 0 := by
  decide

private theorem x4SubRow16Coeff52_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 52 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 52 0 := by
  decide

private theorem x4SubRow16Coeff53_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 53 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 53 0 := by
  decide

private theorem x4SubRow16Coeff54_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 54 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 54 0 := by
  decide

private theorem x4SubRow16Coeff55_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 55 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 55 0 := by
  decide

private theorem x4SubRow16Coeff56_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 56 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 56 0 := by
  decide

private theorem x4SubRow16Coeff57_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 57 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 57 0 := by
  decide

private theorem x4SubRow16Coeff58_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 58 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 58 0 := by
  decide

private theorem x4SubRow16Coeff59_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 59 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 59 0 := by
  decide

private theorem x4SubRow16Coeff60_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 60 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 60 0 := by
  decide

private theorem x4SubRow16Coeff61_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 61 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 61 0 := by
  decide

private theorem x4SubRow16Coeff62_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 62 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 62 0 := by
  decide

private theorem x4SubRow16Coeff63_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 63 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 63 0 := by
  decide

private theorem x4SubRow16Coeff64_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 64 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 64 0 := by
  decide

private theorem x4SubRow16Coeff65_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 65 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 65 0 := by
  decide

private theorem x4SubRow16Coeff66_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 66 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 66 0 := by
  decide

private theorem x4SubRow16Coeff67_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 67 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 67 0 := by
  decide

private theorem x4SubRow16Coeff68_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 68 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 68 0 := by
  decide

private theorem x4SubRow16Coeff69_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 69 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 69 0 := by
  decide

private theorem x4SubRow16Coeff70_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 70 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 70 0 := by
  decide

private theorem x4SubRow16Coeff71_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 71 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 71 0 := by
  decide

private theorem x4SubRow16Coeff72_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 72 =
      ((rectangularize 53 73 X4Data).getD 16 []).getD 72 0 := by
  decide

private theorem x4SubRow16Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 j =
      ((rectangularize 53 73 X4Data).getD 16 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow16Coeff0_spec
  · exact x4SubRow16Coeff1_spec
  · exact x4SubRow16Coeff2_spec
  · exact x4SubRow16Coeff3_spec
  · exact x4SubRow16Coeff4_spec
  · exact x4SubRow16Coeff5_spec
  · exact x4SubRow16Coeff6_spec
  · exact x4SubRow16Coeff7_spec
  · exact x4SubRow16Coeff8_spec
  · exact x4SubRow16Coeff9_spec

private theorem x4SubRow16Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 j =
      ((rectangularize 53 73 X4Data).getD 16 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow16Coeff10_spec
  · exact x4SubRow16Coeff11_spec
  · exact x4SubRow16Coeff12_spec
  · exact x4SubRow16Coeff13_spec
  · exact x4SubRow16Coeff14_spec
  · exact x4SubRow16Coeff15_spec
  · exact x4SubRow16Coeff16_spec
  · exact x4SubRow16Coeff17_spec
  · exact x4SubRow16Coeff18_spec
  · exact x4SubRow16Coeff19_spec

private theorem x4SubRow16Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 j =
      ((rectangularize 53 73 X4Data).getD 16 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow16Coeff20_spec
  · exact x4SubRow16Coeff21_spec
  · exact x4SubRow16Coeff22_spec
  · exact x4SubRow16Coeff23_spec
  · exact x4SubRow16Coeff24_spec
  · exact x4SubRow16Coeff25_spec
  · exact x4SubRow16Coeff26_spec
  · exact x4SubRow16Coeff27_spec
  · exact x4SubRow16Coeff28_spec
  · exact x4SubRow16Coeff29_spec

private theorem x4SubRow16Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 j =
      ((rectangularize 53 73 X4Data).getD 16 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow16Coeff30_spec
  · exact x4SubRow16Coeff31_spec
  · exact x4SubRow16Coeff32_spec
  · exact x4SubRow16Coeff33_spec
  · exact x4SubRow16Coeff34_spec
  · exact x4SubRow16Coeff35_spec
  · exact x4SubRow16Coeff36_spec
  · exact x4SubRow16Coeff37_spec
  · exact x4SubRow16Coeff38_spec
  · exact x4SubRow16Coeff39_spec

private theorem x4SubRow16Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 j =
      ((rectangularize 53 73 X4Data).getD 16 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow16Coeff40_spec
  · exact x4SubRow16Coeff41_spec
  · exact x4SubRow16Coeff42_spec
  · exact x4SubRow16Coeff43_spec
  · exact x4SubRow16Coeff44_spec
  · exact x4SubRow16Coeff45_spec
  · exact x4SubRow16Coeff46_spec
  · exact x4SubRow16Coeff47_spec
  · exact x4SubRow16Coeff48_spec
  · exact x4SubRow16Coeff49_spec

private theorem x4SubRow16Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 j =
      ((rectangularize 53 73 X4Data).getD 16 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow16Coeff50_spec
  · exact x4SubRow16Coeff51_spec
  · exact x4SubRow16Coeff52_spec
  · exact x4SubRow16Coeff53_spec
  · exact x4SubRow16Coeff54_spec
  · exact x4SubRow16Coeff55_spec
  · exact x4SubRow16Coeff56_spec
  · exact x4SubRow16Coeff57_spec
  · exact x4SubRow16Coeff58_spec
  · exact x4SubRow16Coeff59_spec

private theorem x4SubRow16Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 j =
      ((rectangularize 53 73 X4Data).getD 16 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow16Coeff60_spec
  · exact x4SubRow16Coeff61_spec
  · exact x4SubRow16Coeff62_spec
  · exact x4SubRow16Coeff63_spec
  · exact x4SubRow16Coeff64_spec
  · exact x4SubRow16Coeff65_spec
  · exact x4SubRow16Coeff66_spec
  · exact x4SubRow16Coeff67_spec
  · exact x4SubRow16Coeff68_spec
  · exact x4SubRow16Coeff69_spec

private theorem x4SubRow16Coeffs70To72_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 73) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 j =
      ((rectangularize 53 73 X4Data).getD 16 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 := by
    omega
  rcases hCases with
    rfl | rfl | rfl
  · exact x4SubRow16Coeff70_spec
  · exact x4SubRow16Coeff71_spec
  · exact x4SubRow16Coeff72_spec

private theorem x4SubRow16_coefficients (j : ℕ) (hj : j < 73) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 16 j =
      ((rectangularize 53 73 X4Data).getD 16 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact x4SubRow16Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact x4SubRow16Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact x4SubRow16Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact x4SubRow16Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact x4SubRow16Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact x4SubRow16Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact x4SubRow16Coeffs60To69_spec j (by omega) h70
  exact x4SubRow16Coeffs70To72_spec j (by omega) hj

private theorem x4SubRow16Padded_spec :
    padOne 73
        (addMulRow X4NLK3Data NegData X4NRGData 16) =
      (rectangularize 53 73 X4Data).getD 16 [] := by
  apply padOne_addMulRow_eq_of_coefficients 73
    X4NLK3Data NegData X4NRGData 16
    ((rectangularize 53 73 X4Data).getD 16 [])
  · decide
  · have hTargetSupport : (X4Data.getD 16 []).length ≤ 73 := by
      decide
    rw [getD_rectangularize 53 73 X4Data 16 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact x4SubRow16_coefficients

private theorem x4SubRow16_spec :
    (rectangularize 53 73
        (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 16 [] =
      (rectangularize 53 73 X4Data).getD 16 [] := by
  rw [getD_rectangularize 53 73
    (Two.add X4NLK3Data (Two.mul NegData X4NRGData)) 16 (by omega),
    ← addMulRow_eq_getD]
  exact x4SubRow16Padded_spec

private theorem x4SubRow17Coeff0_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 0 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 0 0 := by
  decide

private theorem x4SubRow17Coeff1_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 1 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 1 0 := by
  decide

private theorem x4SubRow17Coeff2_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 2 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 2 0 := by
  decide

private theorem x4SubRow17Coeff3_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 3 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 3 0 := by
  decide

private theorem x4SubRow17Coeff4_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 4 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 4 0 := by
  decide

private theorem x4SubRow17Coeff5_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 5 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 5 0 := by
  decide

private theorem x4SubRow17Coeff6_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 6 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 6 0 := by
  decide

private theorem x4SubRow17Coeff7_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 7 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 7 0 := by
  decide

private theorem x4SubRow17Coeff8_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 8 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 8 0 := by
  decide

private theorem x4SubRow17Coeff9_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 9 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 9 0 := by
  decide

private theorem x4SubRow17Coeff10_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 10 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 10 0 := by
  decide

private theorem x4SubRow17Coeff11_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 11 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 11 0 := by
  decide

private theorem x4SubRow17Coeff12_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 12 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 12 0 := by
  decide

private theorem x4SubRow17Coeff13_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 13 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 13 0 := by
  decide

private theorem x4SubRow17Coeff14_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 14 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 14 0 := by
  decide

private theorem x4SubRow17Coeff15_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 15 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 15 0 := by
  decide

private theorem x4SubRow17Coeff16_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 16 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 16 0 := by
  decide

private theorem x4SubRow17Coeff17_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 17 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 17 0 := by
  decide

private theorem x4SubRow17Coeff18_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 18 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 18 0 := by
  decide

private theorem x4SubRow17Coeff19_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 19 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 19 0 := by
  decide

private theorem x4SubRow17Coeff20_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 20 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 20 0 := by
  decide

private theorem x4SubRow17Coeff21_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 21 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 21 0 := by
  decide

private theorem x4SubRow17Coeff22_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 22 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 22 0 := by
  decide

private theorem x4SubRow17Coeff23_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 23 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 23 0 := by
  decide

private theorem x4SubRow17Coeff24_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 24 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 24 0 := by
  decide

private theorem x4SubRow17Coeff25_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 25 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 25 0 := by
  decide

private theorem x4SubRow17Coeff26_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 26 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 26 0 := by
  decide

private theorem x4SubRow17Coeff27_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 27 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 27 0 := by
  decide

private theorem x4SubRow17Coeff28_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 28 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 28 0 := by
  decide

private theorem x4SubRow17Coeff29_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 29 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 29 0 := by
  decide

private theorem x4SubRow17Coeff30_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 30 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 30 0 := by
  decide

private theorem x4SubRow17Coeff31_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 31 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 31 0 := by
  decide

private theorem x4SubRow17Coeff32_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 32 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 32 0 := by
  decide

private theorem x4SubRow17Coeff33_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 33 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 33 0 := by
  decide

private theorem x4SubRow17Coeff34_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 34 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 34 0 := by
  decide

private theorem x4SubRow17Coeff35_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 35 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 35 0 := by
  decide

private theorem x4SubRow17Coeff36_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 36 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 36 0 := by
  decide

private theorem x4SubRow17Coeff37_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 37 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 37 0 := by
  decide

private theorem x4SubRow17Coeff38_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 38 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 38 0 := by
  decide

private theorem x4SubRow17Coeff39_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 39 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 39 0 := by
  decide

private theorem x4SubRow17Coeff40_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 40 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 40 0 := by
  decide

private theorem x4SubRow17Coeff41_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 41 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 41 0 := by
  decide

private theorem x4SubRow17Coeff42_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 42 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 42 0 := by
  decide

private theorem x4SubRow17Coeff43_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 43 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 43 0 := by
  decide

private theorem x4SubRow17Coeff44_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 44 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 44 0 := by
  decide

private theorem x4SubRow17Coeff45_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 45 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 45 0 := by
  decide

private theorem x4SubRow17Coeff46_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 46 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 46 0 := by
  decide

private theorem x4SubRow17Coeff47_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 47 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 47 0 := by
  decide

private theorem x4SubRow17Coeff48_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 48 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 48 0 := by
  decide

private theorem x4SubRow17Coeff49_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 49 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 49 0 := by
  decide

private theorem x4SubRow17Coeff50_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 50 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 50 0 := by
  decide

private theorem x4SubRow17Coeff51_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 51 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 51 0 := by
  decide

private theorem x4SubRow17Coeff52_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 52 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 52 0 := by
  decide

private theorem x4SubRow17Coeff53_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 53 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 53 0 := by
  decide

private theorem x4SubRow17Coeff54_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 54 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 54 0 := by
  decide

private theorem x4SubRow17Coeff55_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 55 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 55 0 := by
  decide

private theorem x4SubRow17Coeff56_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 56 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 56 0 := by
  decide

private theorem x4SubRow17Coeff57_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 57 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 57 0 := by
  decide

private theorem x4SubRow17Coeff58_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 58 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 58 0 := by
  decide

private theorem x4SubRow17Coeff59_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 59 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 59 0 := by
  decide

private theorem x4SubRow17Coeff60_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 60 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 60 0 := by
  decide

private theorem x4SubRow17Coeff61_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 61 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 61 0 := by
  decide

private theorem x4SubRow17Coeff62_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 62 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 62 0 := by
  decide

private theorem x4SubRow17Coeff63_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 63 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 63 0 := by
  decide

private theorem x4SubRow17Coeff64_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 64 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 64 0 := by
  decide

private theorem x4SubRow17Coeff65_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 65 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 65 0 := by
  decide

private theorem x4SubRow17Coeff66_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 66 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 66 0 := by
  decide

private theorem x4SubRow17Coeff67_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 67 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 67 0 := by
  decide

private theorem x4SubRow17Coeff68_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 68 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 68 0 := by
  decide

private theorem x4SubRow17Coeff69_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 69 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 69 0 := by
  decide

private theorem x4SubRow17Coeff70_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 70 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 70 0 := by
  decide

private theorem x4SubRow17Coeff71_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 71 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 71 0 := by
  decide

private theorem x4SubRow17Coeff72_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 72 =
      ((rectangularize 53 73 X4Data).getD 17 []).getD 72 0 := by
  decide

private theorem x4SubRow17Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 j =
      ((rectangularize 53 73 X4Data).getD 17 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow17Coeff0_spec
  · exact x4SubRow17Coeff1_spec
  · exact x4SubRow17Coeff2_spec
  · exact x4SubRow17Coeff3_spec
  · exact x4SubRow17Coeff4_spec
  · exact x4SubRow17Coeff5_spec
  · exact x4SubRow17Coeff6_spec
  · exact x4SubRow17Coeff7_spec
  · exact x4SubRow17Coeff8_spec
  · exact x4SubRow17Coeff9_spec

private theorem x4SubRow17Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 j =
      ((rectangularize 53 73 X4Data).getD 17 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow17Coeff10_spec
  · exact x4SubRow17Coeff11_spec
  · exact x4SubRow17Coeff12_spec
  · exact x4SubRow17Coeff13_spec
  · exact x4SubRow17Coeff14_spec
  · exact x4SubRow17Coeff15_spec
  · exact x4SubRow17Coeff16_spec
  · exact x4SubRow17Coeff17_spec
  · exact x4SubRow17Coeff18_spec
  · exact x4SubRow17Coeff19_spec

private theorem x4SubRow17Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 j =
      ((rectangularize 53 73 X4Data).getD 17 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow17Coeff20_spec
  · exact x4SubRow17Coeff21_spec
  · exact x4SubRow17Coeff22_spec
  · exact x4SubRow17Coeff23_spec
  · exact x4SubRow17Coeff24_spec
  · exact x4SubRow17Coeff25_spec
  · exact x4SubRow17Coeff26_spec
  · exact x4SubRow17Coeff27_spec
  · exact x4SubRow17Coeff28_spec
  · exact x4SubRow17Coeff29_spec

private theorem x4SubRow17Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 j =
      ((rectangularize 53 73 X4Data).getD 17 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow17Coeff30_spec
  · exact x4SubRow17Coeff31_spec
  · exact x4SubRow17Coeff32_spec
  · exact x4SubRow17Coeff33_spec
  · exact x4SubRow17Coeff34_spec
  · exact x4SubRow17Coeff35_spec
  · exact x4SubRow17Coeff36_spec
  · exact x4SubRow17Coeff37_spec
  · exact x4SubRow17Coeff38_spec
  · exact x4SubRow17Coeff39_spec

private theorem x4SubRow17Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 j =
      ((rectangularize 53 73 X4Data).getD 17 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow17Coeff40_spec
  · exact x4SubRow17Coeff41_spec
  · exact x4SubRow17Coeff42_spec
  · exact x4SubRow17Coeff43_spec
  · exact x4SubRow17Coeff44_spec
  · exact x4SubRow17Coeff45_spec
  · exact x4SubRow17Coeff46_spec
  · exact x4SubRow17Coeff47_spec
  · exact x4SubRow17Coeff48_spec
  · exact x4SubRow17Coeff49_spec

private theorem x4SubRow17Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 j =
      ((rectangularize 53 73 X4Data).getD 17 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow17Coeff50_spec
  · exact x4SubRow17Coeff51_spec
  · exact x4SubRow17Coeff52_spec
  · exact x4SubRow17Coeff53_spec
  · exact x4SubRow17Coeff54_spec
  · exact x4SubRow17Coeff55_spec
  · exact x4SubRow17Coeff56_spec
  · exact x4SubRow17Coeff57_spec
  · exact x4SubRow17Coeff58_spec
  · exact x4SubRow17Coeff59_spec

private theorem x4SubRow17Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 j =
      ((rectangularize 53 73 X4Data).getD 17 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow17Coeff60_spec
  · exact x4SubRow17Coeff61_spec
  · exact x4SubRow17Coeff62_spec
  · exact x4SubRow17Coeff63_spec
  · exact x4SubRow17Coeff64_spec
  · exact x4SubRow17Coeff65_spec
  · exact x4SubRow17Coeff66_spec
  · exact x4SubRow17Coeff67_spec
  · exact x4SubRow17Coeff68_spec
  · exact x4SubRow17Coeff69_spec

private theorem x4SubRow17Coeffs70To72_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 73) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 j =
      ((rectangularize 53 73 X4Data).getD 17 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 := by
    omega
  rcases hCases with
    rfl | rfl | rfl
  · exact x4SubRow17Coeff70_spec
  · exact x4SubRow17Coeff71_spec
  · exact x4SubRow17Coeff72_spec

private theorem x4SubRow17_coefficients (j : ℕ) (hj : j < 73) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 17 j =
      ((rectangularize 53 73 X4Data).getD 17 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact x4SubRow17Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact x4SubRow17Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact x4SubRow17Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact x4SubRow17Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact x4SubRow17Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact x4SubRow17Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact x4SubRow17Coeffs60To69_spec j (by omega) h70
  exact x4SubRow17Coeffs70To72_spec j (by omega) hj

private theorem x4SubRow17Padded_spec :
    padOne 73
        (addMulRow X4NLK3Data NegData X4NRGData 17) =
      (rectangularize 53 73 X4Data).getD 17 [] := by
  apply padOne_addMulRow_eq_of_coefficients 73
    X4NLK3Data NegData X4NRGData 17
    ((rectangularize 53 73 X4Data).getD 17 [])
  · decide
  · have hTargetSupport : (X4Data.getD 17 []).length ≤ 73 := by
      decide
    rw [getD_rectangularize 53 73 X4Data 17 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact x4SubRow17_coefficients

private theorem x4SubRow17_spec :
    (rectangularize 53 73
        (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 17 [] =
      (rectangularize 53 73 X4Data).getD 17 [] := by
  rw [getD_rectangularize 53 73
    (Two.add X4NLK3Data (Two.mul NegData X4NRGData)) 17 (by omega),
    ← addMulRow_eq_getD]
  exact x4SubRow17Padded_spec

private theorem x4SubRow18Coeff0_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 0 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 0 0 := by
  decide

private theorem x4SubRow18Coeff1_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 1 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 1 0 := by
  decide

private theorem x4SubRow18Coeff2_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 2 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 2 0 := by
  decide

private theorem x4SubRow18Coeff3_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 3 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 3 0 := by
  decide

private theorem x4SubRow18Coeff4_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 4 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 4 0 := by
  decide

private theorem x4SubRow18Coeff5_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 5 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 5 0 := by
  decide

private theorem x4SubRow18Coeff6_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 6 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 6 0 := by
  decide

private theorem x4SubRow18Coeff7_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 7 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 7 0 := by
  decide

private theorem x4SubRow18Coeff8_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 8 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 8 0 := by
  decide

private theorem x4SubRow18Coeff9_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 9 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 9 0 := by
  decide

private theorem x4SubRow18Coeff10_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 10 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 10 0 := by
  decide

private theorem x4SubRow18Coeff11_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 11 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 11 0 := by
  decide

private theorem x4SubRow18Coeff12_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 12 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 12 0 := by
  decide

private theorem x4SubRow18Coeff13_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 13 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 13 0 := by
  decide

private theorem x4SubRow18Coeff14_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 14 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 14 0 := by
  decide

private theorem x4SubRow18Coeff15_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 15 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 15 0 := by
  decide

private theorem x4SubRow18Coeff16_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 16 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 16 0 := by
  decide

private theorem x4SubRow18Coeff17_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 17 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 17 0 := by
  decide

private theorem x4SubRow18Coeff18_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 18 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 18 0 := by
  decide

private theorem x4SubRow18Coeff19_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 19 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 19 0 := by
  decide

private theorem x4SubRow18Coeff20_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 20 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 20 0 := by
  decide

private theorem x4SubRow18Coeff21_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 21 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 21 0 := by
  decide

private theorem x4SubRow18Coeff22_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 22 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 22 0 := by
  decide

private theorem x4SubRow18Coeff23_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 23 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 23 0 := by
  decide

private theorem x4SubRow18Coeff24_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 24 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 24 0 := by
  decide

private theorem x4SubRow18Coeff25_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 25 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 25 0 := by
  decide

private theorem x4SubRow18Coeff26_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 26 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 26 0 := by
  decide

private theorem x4SubRow18Coeff27_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 27 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 27 0 := by
  decide

private theorem x4SubRow18Coeff28_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 28 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 28 0 := by
  decide

private theorem x4SubRow18Coeff29_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 29 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 29 0 := by
  decide

private theorem x4SubRow18Coeff30_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 30 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 30 0 := by
  decide

private theorem x4SubRow18Coeff31_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 31 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 31 0 := by
  decide

private theorem x4SubRow18Coeff32_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 32 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 32 0 := by
  decide

private theorem x4SubRow18Coeff33_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 33 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 33 0 := by
  decide

private theorem x4SubRow18Coeff34_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 34 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 34 0 := by
  decide

private theorem x4SubRow18Coeff35_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 35 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 35 0 := by
  decide

private theorem x4SubRow18Coeff36_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 36 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 36 0 := by
  decide

private theorem x4SubRow18Coeff37_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 37 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 37 0 := by
  decide

private theorem x4SubRow18Coeff38_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 38 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 38 0 := by
  decide

private theorem x4SubRow18Coeff39_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 39 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 39 0 := by
  decide

private theorem x4SubRow18Coeff40_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 40 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 40 0 := by
  decide

private theorem x4SubRow18Coeff41_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 41 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 41 0 := by
  decide

private theorem x4SubRow18Coeff42_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 42 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 42 0 := by
  decide

private theorem x4SubRow18Coeff43_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 43 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 43 0 := by
  decide

private theorem x4SubRow18Coeff44_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 44 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 44 0 := by
  decide

private theorem x4SubRow18Coeff45_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 45 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 45 0 := by
  decide

private theorem x4SubRow18Coeff46_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 46 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 46 0 := by
  decide

private theorem x4SubRow18Coeff47_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 47 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 47 0 := by
  decide

private theorem x4SubRow18Coeff48_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 48 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 48 0 := by
  decide

private theorem x4SubRow18Coeff49_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 49 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 49 0 := by
  decide

private theorem x4SubRow18Coeff50_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 50 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 50 0 := by
  decide

private theorem x4SubRow18Coeff51_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 51 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 51 0 := by
  decide

private theorem x4SubRow18Coeff52_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 52 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 52 0 := by
  decide

private theorem x4SubRow18Coeff53_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 53 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 53 0 := by
  decide

private theorem x4SubRow18Coeff54_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 54 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 54 0 := by
  decide

private theorem x4SubRow18Coeff55_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 55 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 55 0 := by
  decide

private theorem x4SubRow18Coeff56_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 56 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 56 0 := by
  decide

private theorem x4SubRow18Coeff57_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 57 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 57 0 := by
  decide

private theorem x4SubRow18Coeff58_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 58 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 58 0 := by
  decide

private theorem x4SubRow18Coeff59_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 59 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 59 0 := by
  decide

private theorem x4SubRow18Coeff60_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 60 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 60 0 := by
  decide

private theorem x4SubRow18Coeff61_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 61 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 61 0 := by
  decide

private theorem x4SubRow18Coeff62_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 62 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 62 0 := by
  decide

private theorem x4SubRow18Coeff63_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 63 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 63 0 := by
  decide

private theorem x4SubRow18Coeff64_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 64 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 64 0 := by
  decide

private theorem x4SubRow18Coeff65_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 65 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 65 0 := by
  decide

private theorem x4SubRow18Coeff66_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 66 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 66 0 := by
  decide

private theorem x4SubRow18Coeff67_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 67 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 67 0 := by
  decide

private theorem x4SubRow18Coeff68_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 68 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 68 0 := by
  decide

private theorem x4SubRow18Coeff69_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 69 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 69 0 := by
  decide

private theorem x4SubRow18Coeff70_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 70 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 70 0 := by
  decide

private theorem x4SubRow18Coeff71_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 71 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 71 0 := by
  decide

private theorem x4SubRow18Coeff72_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 72 =
      ((rectangularize 53 73 X4Data).getD 18 []).getD 72 0 := by
  decide

private theorem x4SubRow18Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 j =
      ((rectangularize 53 73 X4Data).getD 18 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow18Coeff0_spec
  · exact x4SubRow18Coeff1_spec
  · exact x4SubRow18Coeff2_spec
  · exact x4SubRow18Coeff3_spec
  · exact x4SubRow18Coeff4_spec
  · exact x4SubRow18Coeff5_spec
  · exact x4SubRow18Coeff6_spec
  · exact x4SubRow18Coeff7_spec
  · exact x4SubRow18Coeff8_spec
  · exact x4SubRow18Coeff9_spec

private theorem x4SubRow18Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 j =
      ((rectangularize 53 73 X4Data).getD 18 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow18Coeff10_spec
  · exact x4SubRow18Coeff11_spec
  · exact x4SubRow18Coeff12_spec
  · exact x4SubRow18Coeff13_spec
  · exact x4SubRow18Coeff14_spec
  · exact x4SubRow18Coeff15_spec
  · exact x4SubRow18Coeff16_spec
  · exact x4SubRow18Coeff17_spec
  · exact x4SubRow18Coeff18_spec
  · exact x4SubRow18Coeff19_spec

private theorem x4SubRow18Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 j =
      ((rectangularize 53 73 X4Data).getD 18 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow18Coeff20_spec
  · exact x4SubRow18Coeff21_spec
  · exact x4SubRow18Coeff22_spec
  · exact x4SubRow18Coeff23_spec
  · exact x4SubRow18Coeff24_spec
  · exact x4SubRow18Coeff25_spec
  · exact x4SubRow18Coeff26_spec
  · exact x4SubRow18Coeff27_spec
  · exact x4SubRow18Coeff28_spec
  · exact x4SubRow18Coeff29_spec

private theorem x4SubRow18Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 j =
      ((rectangularize 53 73 X4Data).getD 18 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow18Coeff30_spec
  · exact x4SubRow18Coeff31_spec
  · exact x4SubRow18Coeff32_spec
  · exact x4SubRow18Coeff33_spec
  · exact x4SubRow18Coeff34_spec
  · exact x4SubRow18Coeff35_spec
  · exact x4SubRow18Coeff36_spec
  · exact x4SubRow18Coeff37_spec
  · exact x4SubRow18Coeff38_spec
  · exact x4SubRow18Coeff39_spec

private theorem x4SubRow18Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 j =
      ((rectangularize 53 73 X4Data).getD 18 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow18Coeff40_spec
  · exact x4SubRow18Coeff41_spec
  · exact x4SubRow18Coeff42_spec
  · exact x4SubRow18Coeff43_spec
  · exact x4SubRow18Coeff44_spec
  · exact x4SubRow18Coeff45_spec
  · exact x4SubRow18Coeff46_spec
  · exact x4SubRow18Coeff47_spec
  · exact x4SubRow18Coeff48_spec
  · exact x4SubRow18Coeff49_spec

private theorem x4SubRow18Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 j =
      ((rectangularize 53 73 X4Data).getD 18 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow18Coeff50_spec
  · exact x4SubRow18Coeff51_spec
  · exact x4SubRow18Coeff52_spec
  · exact x4SubRow18Coeff53_spec
  · exact x4SubRow18Coeff54_spec
  · exact x4SubRow18Coeff55_spec
  · exact x4SubRow18Coeff56_spec
  · exact x4SubRow18Coeff57_spec
  · exact x4SubRow18Coeff58_spec
  · exact x4SubRow18Coeff59_spec

private theorem x4SubRow18Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 j =
      ((rectangularize 53 73 X4Data).getD 18 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow18Coeff60_spec
  · exact x4SubRow18Coeff61_spec
  · exact x4SubRow18Coeff62_spec
  · exact x4SubRow18Coeff63_spec
  · exact x4SubRow18Coeff64_spec
  · exact x4SubRow18Coeff65_spec
  · exact x4SubRow18Coeff66_spec
  · exact x4SubRow18Coeff67_spec
  · exact x4SubRow18Coeff68_spec
  · exact x4SubRow18Coeff69_spec

private theorem x4SubRow18Coeffs70To72_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 73) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 j =
      ((rectangularize 53 73 X4Data).getD 18 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 := by
    omega
  rcases hCases with
    rfl | rfl | rfl
  · exact x4SubRow18Coeff70_spec
  · exact x4SubRow18Coeff71_spec
  · exact x4SubRow18Coeff72_spec

private theorem x4SubRow18_coefficients (j : ℕ) (hj : j < 73) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 18 j =
      ((rectangularize 53 73 X4Data).getD 18 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact x4SubRow18Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact x4SubRow18Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact x4SubRow18Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact x4SubRow18Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact x4SubRow18Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact x4SubRow18Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact x4SubRow18Coeffs60To69_spec j (by omega) h70
  exact x4SubRow18Coeffs70To72_spec j (by omega) hj

private theorem x4SubRow18Padded_spec :
    padOne 73
        (addMulRow X4NLK3Data NegData X4NRGData 18) =
      (rectangularize 53 73 X4Data).getD 18 [] := by
  apply padOne_addMulRow_eq_of_coefficients 73
    X4NLK3Data NegData X4NRGData 18
    ((rectangularize 53 73 X4Data).getD 18 [])
  · decide
  · have hTargetSupport : (X4Data.getD 18 []).length ≤ 73 := by
      decide
    rw [getD_rectangularize 53 73 X4Data 18 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact x4SubRow18_coefficients

private theorem x4SubRow18_spec :
    (rectangularize 53 73
        (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 18 [] =
      (rectangularize 53 73 X4Data).getD 18 [] := by
  rw [getD_rectangularize 53 73
    (Two.add X4NLK3Data (Two.mul NegData X4NRGData)) 18 (by omega),
    ← addMulRow_eq_getD]
  exact x4SubRow18Padded_spec

private theorem x4SubRow19Coeff0_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 0 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 0 0 := by
  decide

private theorem x4SubRow19Coeff1_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 1 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 1 0 := by
  decide

private theorem x4SubRow19Coeff2_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 2 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 2 0 := by
  decide

private theorem x4SubRow19Coeff3_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 3 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 3 0 := by
  decide

private theorem x4SubRow19Coeff4_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 4 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 4 0 := by
  decide

private theorem x4SubRow19Coeff5_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 5 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 5 0 := by
  decide

private theorem x4SubRow19Coeff6_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 6 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 6 0 := by
  decide

private theorem x4SubRow19Coeff7_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 7 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 7 0 := by
  decide

private theorem x4SubRow19Coeff8_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 8 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 8 0 := by
  decide

private theorem x4SubRow19Coeff9_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 9 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 9 0 := by
  decide

private theorem x4SubRow19Coeff10_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 10 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 10 0 := by
  decide

private theorem x4SubRow19Coeff11_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 11 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 11 0 := by
  decide

private theorem x4SubRow19Coeff12_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 12 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 12 0 := by
  decide

private theorem x4SubRow19Coeff13_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 13 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 13 0 := by
  decide

private theorem x4SubRow19Coeff14_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 14 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 14 0 := by
  decide

private theorem x4SubRow19Coeff15_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 15 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 15 0 := by
  decide

private theorem x4SubRow19Coeff16_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 16 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 16 0 := by
  decide

private theorem x4SubRow19Coeff17_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 17 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 17 0 := by
  decide

private theorem x4SubRow19Coeff18_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 18 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 18 0 := by
  decide

private theorem x4SubRow19Coeff19_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 19 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 19 0 := by
  decide

private theorem x4SubRow19Coeff20_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 20 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 20 0 := by
  decide

private theorem x4SubRow19Coeff21_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 21 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 21 0 := by
  decide

private theorem x4SubRow19Coeff22_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 22 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 22 0 := by
  decide

private theorem x4SubRow19Coeff23_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 23 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 23 0 := by
  decide

private theorem x4SubRow19Coeff24_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 24 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 24 0 := by
  decide

private theorem x4SubRow19Coeff25_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 25 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 25 0 := by
  decide

private theorem x4SubRow19Coeff26_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 26 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 26 0 := by
  decide

private theorem x4SubRow19Coeff27_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 27 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 27 0 := by
  decide

private theorem x4SubRow19Coeff28_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 28 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 28 0 := by
  decide

private theorem x4SubRow19Coeff29_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 29 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 29 0 := by
  decide

private theorem x4SubRow19Coeff30_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 30 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 30 0 := by
  decide

private theorem x4SubRow19Coeff31_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 31 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 31 0 := by
  decide

private theorem x4SubRow19Coeff32_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 32 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 32 0 := by
  decide

private theorem x4SubRow19Coeff33_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 33 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 33 0 := by
  decide

private theorem x4SubRow19Coeff34_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 34 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 34 0 := by
  decide

private theorem x4SubRow19Coeff35_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 35 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 35 0 := by
  decide

private theorem x4SubRow19Coeff36_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 36 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 36 0 := by
  decide

private theorem x4SubRow19Coeff37_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 37 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 37 0 := by
  decide

private theorem x4SubRow19Coeff38_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 38 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 38 0 := by
  decide

private theorem x4SubRow19Coeff39_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 39 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 39 0 := by
  decide

private theorem x4SubRow19Coeff40_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 40 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 40 0 := by
  decide

private theorem x4SubRow19Coeff41_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 41 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 41 0 := by
  decide

private theorem x4SubRow19Coeff42_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 42 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 42 0 := by
  decide

private theorem x4SubRow19Coeff43_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 43 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 43 0 := by
  decide

private theorem x4SubRow19Coeff44_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 44 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 44 0 := by
  decide

private theorem x4SubRow19Coeff45_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 45 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 45 0 := by
  decide

private theorem x4SubRow19Coeff46_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 46 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 46 0 := by
  decide

private theorem x4SubRow19Coeff47_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 47 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 47 0 := by
  decide

private theorem x4SubRow19Coeff48_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 48 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 48 0 := by
  decide

private theorem x4SubRow19Coeff49_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 49 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 49 0 := by
  decide

private theorem x4SubRow19Coeff50_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 50 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 50 0 := by
  decide

private theorem x4SubRow19Coeff51_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 51 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 51 0 := by
  decide

private theorem x4SubRow19Coeff52_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 52 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 52 0 := by
  decide

private theorem x4SubRow19Coeff53_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 53 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 53 0 := by
  decide

private theorem x4SubRow19Coeff54_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 54 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 54 0 := by
  decide

private theorem x4SubRow19Coeff55_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 55 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 55 0 := by
  decide

private theorem x4SubRow19Coeff56_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 56 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 56 0 := by
  decide

private theorem x4SubRow19Coeff57_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 57 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 57 0 := by
  decide

private theorem x4SubRow19Coeff58_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 58 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 58 0 := by
  decide

private theorem x4SubRow19Coeff59_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 59 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 59 0 := by
  decide

private theorem x4SubRow19Coeff60_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 60 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 60 0 := by
  decide

private theorem x4SubRow19Coeff61_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 61 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 61 0 := by
  decide

private theorem x4SubRow19Coeff62_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 62 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 62 0 := by
  decide

private theorem x4SubRow19Coeff63_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 63 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 63 0 := by
  decide

private theorem x4SubRow19Coeff64_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 64 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 64 0 := by
  decide

private theorem x4SubRow19Coeff65_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 65 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 65 0 := by
  decide

private theorem x4SubRow19Coeff66_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 66 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 66 0 := by
  decide

private theorem x4SubRow19Coeff67_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 67 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 67 0 := by
  decide

private theorem x4SubRow19Coeff68_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 68 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 68 0 := by
  decide

private theorem x4SubRow19Coeff69_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 69 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 69 0 := by
  decide

private theorem x4SubRow19Coeff70_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 70 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 70 0 := by
  decide

private theorem x4SubRow19Coeff71_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 71 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 71 0 := by
  decide

private theorem x4SubRow19Coeff72_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 72 =
      ((rectangularize 53 73 X4Data).getD 19 []).getD 72 0 := by
  decide

private theorem x4SubRow19Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 j =
      ((rectangularize 53 73 X4Data).getD 19 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow19Coeff0_spec
  · exact x4SubRow19Coeff1_spec
  · exact x4SubRow19Coeff2_spec
  · exact x4SubRow19Coeff3_spec
  · exact x4SubRow19Coeff4_spec
  · exact x4SubRow19Coeff5_spec
  · exact x4SubRow19Coeff6_spec
  · exact x4SubRow19Coeff7_spec
  · exact x4SubRow19Coeff8_spec
  · exact x4SubRow19Coeff9_spec

private theorem x4SubRow19Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 j =
      ((rectangularize 53 73 X4Data).getD 19 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow19Coeff10_spec
  · exact x4SubRow19Coeff11_spec
  · exact x4SubRow19Coeff12_spec
  · exact x4SubRow19Coeff13_spec
  · exact x4SubRow19Coeff14_spec
  · exact x4SubRow19Coeff15_spec
  · exact x4SubRow19Coeff16_spec
  · exact x4SubRow19Coeff17_spec
  · exact x4SubRow19Coeff18_spec
  · exact x4SubRow19Coeff19_spec

private theorem x4SubRow19Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 j =
      ((rectangularize 53 73 X4Data).getD 19 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow19Coeff20_spec
  · exact x4SubRow19Coeff21_spec
  · exact x4SubRow19Coeff22_spec
  · exact x4SubRow19Coeff23_spec
  · exact x4SubRow19Coeff24_spec
  · exact x4SubRow19Coeff25_spec
  · exact x4SubRow19Coeff26_spec
  · exact x4SubRow19Coeff27_spec
  · exact x4SubRow19Coeff28_spec
  · exact x4SubRow19Coeff29_spec

private theorem x4SubRow19Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 j =
      ((rectangularize 53 73 X4Data).getD 19 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow19Coeff30_spec
  · exact x4SubRow19Coeff31_spec
  · exact x4SubRow19Coeff32_spec
  · exact x4SubRow19Coeff33_spec
  · exact x4SubRow19Coeff34_spec
  · exact x4SubRow19Coeff35_spec
  · exact x4SubRow19Coeff36_spec
  · exact x4SubRow19Coeff37_spec
  · exact x4SubRow19Coeff38_spec
  · exact x4SubRow19Coeff39_spec

private theorem x4SubRow19Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 j =
      ((rectangularize 53 73 X4Data).getD 19 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow19Coeff40_spec
  · exact x4SubRow19Coeff41_spec
  · exact x4SubRow19Coeff42_spec
  · exact x4SubRow19Coeff43_spec
  · exact x4SubRow19Coeff44_spec
  · exact x4SubRow19Coeff45_spec
  · exact x4SubRow19Coeff46_spec
  · exact x4SubRow19Coeff47_spec
  · exact x4SubRow19Coeff48_spec
  · exact x4SubRow19Coeff49_spec

private theorem x4SubRow19Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 j =
      ((rectangularize 53 73 X4Data).getD 19 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow19Coeff50_spec
  · exact x4SubRow19Coeff51_spec
  · exact x4SubRow19Coeff52_spec
  · exact x4SubRow19Coeff53_spec
  · exact x4SubRow19Coeff54_spec
  · exact x4SubRow19Coeff55_spec
  · exact x4SubRow19Coeff56_spec
  · exact x4SubRow19Coeff57_spec
  · exact x4SubRow19Coeff58_spec
  · exact x4SubRow19Coeff59_spec

private theorem x4SubRow19Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 j =
      ((rectangularize 53 73 X4Data).getD 19 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow19Coeff60_spec
  · exact x4SubRow19Coeff61_spec
  · exact x4SubRow19Coeff62_spec
  · exact x4SubRow19Coeff63_spec
  · exact x4SubRow19Coeff64_spec
  · exact x4SubRow19Coeff65_spec
  · exact x4SubRow19Coeff66_spec
  · exact x4SubRow19Coeff67_spec
  · exact x4SubRow19Coeff68_spec
  · exact x4SubRow19Coeff69_spec

private theorem x4SubRow19Coeffs70To72_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 73) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 j =
      ((rectangularize 53 73 X4Data).getD 19 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 := by
    omega
  rcases hCases with
    rfl | rfl | rfl
  · exact x4SubRow19Coeff70_spec
  · exact x4SubRow19Coeff71_spec
  · exact x4SubRow19Coeff72_spec

private theorem x4SubRow19_coefficients (j : ℕ) (hj : j < 73) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 19 j =
      ((rectangularize 53 73 X4Data).getD 19 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact x4SubRow19Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact x4SubRow19Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact x4SubRow19Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact x4SubRow19Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact x4SubRow19Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact x4SubRow19Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact x4SubRow19Coeffs60To69_spec j (by omega) h70
  exact x4SubRow19Coeffs70To72_spec j (by omega) hj

private theorem x4SubRow19Padded_spec :
    padOne 73
        (addMulRow X4NLK3Data NegData X4NRGData 19) =
      (rectangularize 53 73 X4Data).getD 19 [] := by
  apply padOne_addMulRow_eq_of_coefficients 73
    X4NLK3Data NegData X4NRGData 19
    ((rectangularize 53 73 X4Data).getD 19 [])
  · decide
  · have hTargetSupport : (X4Data.getD 19 []).length ≤ 73 := by
      decide
    rw [getD_rectangularize 53 73 X4Data 19 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact x4SubRow19_coefficients

private theorem x4SubRow19_spec :
    (rectangularize 53 73
        (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 19 [] =
      (rectangularize 53 73 X4Data).getD 19 [] := by
  rw [getD_rectangularize 53 73
    (Two.add X4NLK3Data (Two.mul NegData X4NRGData)) 19 (by omega),
    ← addMulRow_eq_getD]
  exact x4SubRow19Padded_spec

private theorem x4SubRow20Coeff0_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 0 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 0 0 := by
  decide

private theorem x4SubRow20Coeff1_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 1 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 1 0 := by
  decide

private theorem x4SubRow20Coeff2_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 2 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 2 0 := by
  decide

private theorem x4SubRow20Coeff3_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 3 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 3 0 := by
  decide

private theorem x4SubRow20Coeff4_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 4 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 4 0 := by
  decide

private theorem x4SubRow20Coeff5_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 5 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 5 0 := by
  decide

private theorem x4SubRow20Coeff6_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 6 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 6 0 := by
  decide

private theorem x4SubRow20Coeff7_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 7 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 7 0 := by
  decide

private theorem x4SubRow20Coeff8_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 8 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 8 0 := by
  decide

private theorem x4SubRow20Coeff9_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 9 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 9 0 := by
  decide

private theorem x4SubRow20Coeff10_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 10 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 10 0 := by
  decide

private theorem x4SubRow20Coeff11_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 11 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 11 0 := by
  decide

private theorem x4SubRow20Coeff12_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 12 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 12 0 := by
  decide

private theorem x4SubRow20Coeff13_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 13 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 13 0 := by
  decide

private theorem x4SubRow20Coeff14_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 14 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 14 0 := by
  decide

private theorem x4SubRow20Coeff15_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 15 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 15 0 := by
  decide

private theorem x4SubRow20Coeff16_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 16 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 16 0 := by
  decide

private theorem x4SubRow20Coeff17_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 17 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 17 0 := by
  decide

private theorem x4SubRow20Coeff18_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 18 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 18 0 := by
  decide

private theorem x4SubRow20Coeff19_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 19 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 19 0 := by
  decide

private theorem x4SubRow20Coeff20_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 20 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 20 0 := by
  decide

private theorem x4SubRow20Coeff21_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 21 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 21 0 := by
  decide

private theorem x4SubRow20Coeff22_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 22 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 22 0 := by
  decide

private theorem x4SubRow20Coeff23_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 23 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 23 0 := by
  decide

private theorem x4SubRow20Coeff24_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 24 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 24 0 := by
  decide

private theorem x4SubRow20Coeff25_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 25 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 25 0 := by
  decide

private theorem x4SubRow20Coeff26_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 26 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 26 0 := by
  decide

private theorem x4SubRow20Coeff27_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 27 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 27 0 := by
  decide

private theorem x4SubRow20Coeff28_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 28 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 28 0 := by
  decide

private theorem x4SubRow20Coeff29_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 29 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 29 0 := by
  decide

private theorem x4SubRow20Coeff30_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 30 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 30 0 := by
  decide

private theorem x4SubRow20Coeff31_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 31 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 31 0 := by
  decide

private theorem x4SubRow20Coeff32_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 32 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 32 0 := by
  decide

private theorem x4SubRow20Coeff33_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 33 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 33 0 := by
  decide

private theorem x4SubRow20Coeff34_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 34 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 34 0 := by
  decide

private theorem x4SubRow20Coeff35_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 35 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 35 0 := by
  decide

private theorem x4SubRow20Coeff36_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 36 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 36 0 := by
  decide

private theorem x4SubRow20Coeff37_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 37 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 37 0 := by
  decide

private theorem x4SubRow20Coeff38_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 38 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 38 0 := by
  decide

private theorem x4SubRow20Coeff39_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 39 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 39 0 := by
  decide

private theorem x4SubRow20Coeff40_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 40 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 40 0 := by
  decide

private theorem x4SubRow20Coeff41_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 41 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 41 0 := by
  decide

private theorem x4SubRow20Coeff42_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 42 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 42 0 := by
  decide

private theorem x4SubRow20Coeff43_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 43 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 43 0 := by
  decide

private theorem x4SubRow20Coeff44_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 44 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 44 0 := by
  decide

private theorem x4SubRow20Coeff45_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 45 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 45 0 := by
  decide

private theorem x4SubRow20Coeff46_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 46 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 46 0 := by
  decide

private theorem x4SubRow20Coeff47_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 47 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 47 0 := by
  decide

private theorem x4SubRow20Coeff48_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 48 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 48 0 := by
  decide

private theorem x4SubRow20Coeff49_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 49 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 49 0 := by
  decide

private theorem x4SubRow20Coeff50_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 50 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 50 0 := by
  decide

private theorem x4SubRow20Coeff51_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 51 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 51 0 := by
  decide

private theorem x4SubRow20Coeff52_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 52 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 52 0 := by
  decide

private theorem x4SubRow20Coeff53_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 53 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 53 0 := by
  decide

private theorem x4SubRow20Coeff54_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 54 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 54 0 := by
  decide

private theorem x4SubRow20Coeff55_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 55 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 55 0 := by
  decide

private theorem x4SubRow20Coeff56_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 56 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 56 0 := by
  decide

private theorem x4SubRow20Coeff57_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 57 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 57 0 := by
  decide

private theorem x4SubRow20Coeff58_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 58 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 58 0 := by
  decide

private theorem x4SubRow20Coeff59_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 59 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 59 0 := by
  decide

private theorem x4SubRow20Coeff60_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 60 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 60 0 := by
  decide

private theorem x4SubRow20Coeff61_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 61 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 61 0 := by
  decide

private theorem x4SubRow20Coeff62_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 62 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 62 0 := by
  decide

private theorem x4SubRow20Coeff63_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 63 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 63 0 := by
  decide

private theorem x4SubRow20Coeff64_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 64 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 64 0 := by
  decide

private theorem x4SubRow20Coeff65_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 65 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 65 0 := by
  decide

private theorem x4SubRow20Coeff66_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 66 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 66 0 := by
  decide

private theorem x4SubRow20Coeff67_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 67 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 67 0 := by
  decide

private theorem x4SubRow20Coeff68_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 68 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 68 0 := by
  decide

private theorem x4SubRow20Coeff69_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 69 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 69 0 := by
  decide

private theorem x4SubRow20Coeff70_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 70 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 70 0 := by
  decide

private theorem x4SubRow20Coeff71_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 71 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 71 0 := by
  decide

private theorem x4SubRow20Coeff72_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 72 =
      ((rectangularize 53 73 X4Data).getD 20 []).getD 72 0 := by
  decide

private theorem x4SubRow20Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 j =
      ((rectangularize 53 73 X4Data).getD 20 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow20Coeff0_spec
  · exact x4SubRow20Coeff1_spec
  · exact x4SubRow20Coeff2_spec
  · exact x4SubRow20Coeff3_spec
  · exact x4SubRow20Coeff4_spec
  · exact x4SubRow20Coeff5_spec
  · exact x4SubRow20Coeff6_spec
  · exact x4SubRow20Coeff7_spec
  · exact x4SubRow20Coeff8_spec
  · exact x4SubRow20Coeff9_spec

private theorem x4SubRow20Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 j =
      ((rectangularize 53 73 X4Data).getD 20 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow20Coeff10_spec
  · exact x4SubRow20Coeff11_spec
  · exact x4SubRow20Coeff12_spec
  · exact x4SubRow20Coeff13_spec
  · exact x4SubRow20Coeff14_spec
  · exact x4SubRow20Coeff15_spec
  · exact x4SubRow20Coeff16_spec
  · exact x4SubRow20Coeff17_spec
  · exact x4SubRow20Coeff18_spec
  · exact x4SubRow20Coeff19_spec

private theorem x4SubRow20Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 j =
      ((rectangularize 53 73 X4Data).getD 20 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow20Coeff20_spec
  · exact x4SubRow20Coeff21_spec
  · exact x4SubRow20Coeff22_spec
  · exact x4SubRow20Coeff23_spec
  · exact x4SubRow20Coeff24_spec
  · exact x4SubRow20Coeff25_spec
  · exact x4SubRow20Coeff26_spec
  · exact x4SubRow20Coeff27_spec
  · exact x4SubRow20Coeff28_spec
  · exact x4SubRow20Coeff29_spec

private theorem x4SubRow20Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 j =
      ((rectangularize 53 73 X4Data).getD 20 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow20Coeff30_spec
  · exact x4SubRow20Coeff31_spec
  · exact x4SubRow20Coeff32_spec
  · exact x4SubRow20Coeff33_spec
  · exact x4SubRow20Coeff34_spec
  · exact x4SubRow20Coeff35_spec
  · exact x4SubRow20Coeff36_spec
  · exact x4SubRow20Coeff37_spec
  · exact x4SubRow20Coeff38_spec
  · exact x4SubRow20Coeff39_spec

private theorem x4SubRow20Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 j =
      ((rectangularize 53 73 X4Data).getD 20 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow20Coeff40_spec
  · exact x4SubRow20Coeff41_spec
  · exact x4SubRow20Coeff42_spec
  · exact x4SubRow20Coeff43_spec
  · exact x4SubRow20Coeff44_spec
  · exact x4SubRow20Coeff45_spec
  · exact x4SubRow20Coeff46_spec
  · exact x4SubRow20Coeff47_spec
  · exact x4SubRow20Coeff48_spec
  · exact x4SubRow20Coeff49_spec

private theorem x4SubRow20Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 j =
      ((rectangularize 53 73 X4Data).getD 20 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow20Coeff50_spec
  · exact x4SubRow20Coeff51_spec
  · exact x4SubRow20Coeff52_spec
  · exact x4SubRow20Coeff53_spec
  · exact x4SubRow20Coeff54_spec
  · exact x4SubRow20Coeff55_spec
  · exact x4SubRow20Coeff56_spec
  · exact x4SubRow20Coeff57_spec
  · exact x4SubRow20Coeff58_spec
  · exact x4SubRow20Coeff59_spec

private theorem x4SubRow20Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 j =
      ((rectangularize 53 73 X4Data).getD 20 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow20Coeff60_spec
  · exact x4SubRow20Coeff61_spec
  · exact x4SubRow20Coeff62_spec
  · exact x4SubRow20Coeff63_spec
  · exact x4SubRow20Coeff64_spec
  · exact x4SubRow20Coeff65_spec
  · exact x4SubRow20Coeff66_spec
  · exact x4SubRow20Coeff67_spec
  · exact x4SubRow20Coeff68_spec
  · exact x4SubRow20Coeff69_spec

private theorem x4SubRow20Coeffs70To72_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 73) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 j =
      ((rectangularize 53 73 X4Data).getD 20 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 := by
    omega
  rcases hCases with
    rfl | rfl | rfl
  · exact x4SubRow20Coeff70_spec
  · exact x4SubRow20Coeff71_spec
  · exact x4SubRow20Coeff72_spec

private theorem x4SubRow20_coefficients (j : ℕ) (hj : j < 73) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 20 j =
      ((rectangularize 53 73 X4Data).getD 20 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact x4SubRow20Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact x4SubRow20Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact x4SubRow20Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact x4SubRow20Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact x4SubRow20Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact x4SubRow20Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact x4SubRow20Coeffs60To69_spec j (by omega) h70
  exact x4SubRow20Coeffs70To72_spec j (by omega) hj

private theorem x4SubRow20Padded_spec :
    padOne 73
        (addMulRow X4NLK3Data NegData X4NRGData 20) =
      (rectangularize 53 73 X4Data).getD 20 [] := by
  apply padOne_addMulRow_eq_of_coefficients 73
    X4NLK3Data NegData X4NRGData 20
    ((rectangularize 53 73 X4Data).getD 20 [])
  · decide
  · have hTargetSupport : (X4Data.getD 20 []).length ≤ 73 := by
      decide
    rw [getD_rectangularize 53 73 X4Data 20 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact x4SubRow20_coefficients

private theorem x4SubRow20_spec :
    (rectangularize 53 73
        (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 20 [] =
      (rectangularize 53 73 X4Data).getD 20 [] := by
  rw [getD_rectangularize 53 73
    (Two.add X4NLK3Data (Two.mul NegData X4NRGData)) 20 (by omega),
    ← addMulRow_eq_getD]
  exact x4SubRow20Padded_spec

private theorem x4SubRow21Coeff0_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 0 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 0 0 := by
  decide

private theorem x4SubRow21Coeff1_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 1 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 1 0 := by
  decide

private theorem x4SubRow21Coeff2_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 2 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 2 0 := by
  decide

private theorem x4SubRow21Coeff3_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 3 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 3 0 := by
  decide

private theorem x4SubRow21Coeff4_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 4 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 4 0 := by
  decide

private theorem x4SubRow21Coeff5_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 5 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 5 0 := by
  decide

private theorem x4SubRow21Coeff6_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 6 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 6 0 := by
  decide

private theorem x4SubRow21Coeff7_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 7 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 7 0 := by
  decide

private theorem x4SubRow21Coeff8_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 8 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 8 0 := by
  decide

private theorem x4SubRow21Coeff9_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 9 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 9 0 := by
  decide

private theorem x4SubRow21Coeff10_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 10 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 10 0 := by
  decide

private theorem x4SubRow21Coeff11_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 11 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 11 0 := by
  decide

private theorem x4SubRow21Coeff12_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 12 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 12 0 := by
  decide

private theorem x4SubRow21Coeff13_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 13 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 13 0 := by
  decide

private theorem x4SubRow21Coeff14_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 14 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 14 0 := by
  decide

private theorem x4SubRow21Coeff15_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 15 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 15 0 := by
  decide

private theorem x4SubRow21Coeff16_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 16 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 16 0 := by
  decide

private theorem x4SubRow21Coeff17_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 17 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 17 0 := by
  decide

private theorem x4SubRow21Coeff18_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 18 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 18 0 := by
  decide

private theorem x4SubRow21Coeff19_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 19 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 19 0 := by
  decide

private theorem x4SubRow21Coeff20_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 20 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 20 0 := by
  decide

private theorem x4SubRow21Coeff21_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 21 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 21 0 := by
  decide

private theorem x4SubRow21Coeff22_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 22 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 22 0 := by
  decide

private theorem x4SubRow21Coeff23_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 23 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 23 0 := by
  decide

private theorem x4SubRow21Coeff24_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 24 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 24 0 := by
  decide

private theorem x4SubRow21Coeff25_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 25 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 25 0 := by
  decide

private theorem x4SubRow21Coeff26_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 26 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 26 0 := by
  decide

private theorem x4SubRow21Coeff27_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 27 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 27 0 := by
  decide

private theorem x4SubRow21Coeff28_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 28 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 28 0 := by
  decide

private theorem x4SubRow21Coeff29_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 29 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 29 0 := by
  decide

private theorem x4SubRow21Coeff30_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 30 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 30 0 := by
  decide

private theorem x4SubRow21Coeff31_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 31 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 31 0 := by
  decide

private theorem x4SubRow21Coeff32_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 32 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 32 0 := by
  decide

private theorem x4SubRow21Coeff33_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 33 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 33 0 := by
  decide

private theorem x4SubRow21Coeff34_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 34 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 34 0 := by
  decide

private theorem x4SubRow21Coeff35_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 35 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 35 0 := by
  decide

private theorem x4SubRow21Coeff36_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 36 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 36 0 := by
  decide

private theorem x4SubRow21Coeff37_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 37 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 37 0 := by
  decide

private theorem x4SubRow21Coeff38_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 38 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 38 0 := by
  decide

private theorem x4SubRow21Coeff39_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 39 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 39 0 := by
  decide

private theorem x4SubRow21Coeff40_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 40 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 40 0 := by
  decide

private theorem x4SubRow21Coeff41_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 41 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 41 0 := by
  decide

private theorem x4SubRow21Coeff42_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 42 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 42 0 := by
  decide

private theorem x4SubRow21Coeff43_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 43 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 43 0 := by
  decide

private theorem x4SubRow21Coeff44_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 44 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 44 0 := by
  decide

private theorem x4SubRow21Coeff45_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 45 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 45 0 := by
  decide

private theorem x4SubRow21Coeff46_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 46 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 46 0 := by
  decide

private theorem x4SubRow21Coeff47_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 47 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 47 0 := by
  decide

private theorem x4SubRow21Coeff48_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 48 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 48 0 := by
  decide

private theorem x4SubRow21Coeff49_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 49 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 49 0 := by
  decide

private theorem x4SubRow21Coeff50_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 50 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 50 0 := by
  decide

private theorem x4SubRow21Coeff51_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 51 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 51 0 := by
  decide

private theorem x4SubRow21Coeff52_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 52 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 52 0 := by
  decide

private theorem x4SubRow21Coeff53_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 53 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 53 0 := by
  decide

private theorem x4SubRow21Coeff54_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 54 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 54 0 := by
  decide

private theorem x4SubRow21Coeff55_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 55 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 55 0 := by
  decide

private theorem x4SubRow21Coeff56_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 56 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 56 0 := by
  decide

private theorem x4SubRow21Coeff57_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 57 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 57 0 := by
  decide

private theorem x4SubRow21Coeff58_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 58 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 58 0 := by
  decide

private theorem x4SubRow21Coeff59_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 59 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 59 0 := by
  decide

private theorem x4SubRow21Coeff60_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 60 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 60 0 := by
  decide

private theorem x4SubRow21Coeff61_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 61 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 61 0 := by
  decide

private theorem x4SubRow21Coeff62_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 62 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 62 0 := by
  decide

private theorem x4SubRow21Coeff63_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 63 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 63 0 := by
  decide

private theorem x4SubRow21Coeff64_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 64 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 64 0 := by
  decide

private theorem x4SubRow21Coeff65_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 65 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 65 0 := by
  decide

private theorem x4SubRow21Coeff66_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 66 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 66 0 := by
  decide

private theorem x4SubRow21Coeff67_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 67 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 67 0 := by
  decide

private theorem x4SubRow21Coeff68_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 68 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 68 0 := by
  decide

private theorem x4SubRow21Coeff69_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 69 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 69 0 := by
  decide

private theorem x4SubRow21Coeff70_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 70 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 70 0 := by
  decide

private theorem x4SubRow21Coeff71_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 71 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 71 0 := by
  decide

private theorem x4SubRow21Coeff72_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 72 =
      ((rectangularize 53 73 X4Data).getD 21 []).getD 72 0 := by
  decide

private theorem x4SubRow21Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 j =
      ((rectangularize 53 73 X4Data).getD 21 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow21Coeff0_spec
  · exact x4SubRow21Coeff1_spec
  · exact x4SubRow21Coeff2_spec
  · exact x4SubRow21Coeff3_spec
  · exact x4SubRow21Coeff4_spec
  · exact x4SubRow21Coeff5_spec
  · exact x4SubRow21Coeff6_spec
  · exact x4SubRow21Coeff7_spec
  · exact x4SubRow21Coeff8_spec
  · exact x4SubRow21Coeff9_spec

private theorem x4SubRow21Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 j =
      ((rectangularize 53 73 X4Data).getD 21 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow21Coeff10_spec
  · exact x4SubRow21Coeff11_spec
  · exact x4SubRow21Coeff12_spec
  · exact x4SubRow21Coeff13_spec
  · exact x4SubRow21Coeff14_spec
  · exact x4SubRow21Coeff15_spec
  · exact x4SubRow21Coeff16_spec
  · exact x4SubRow21Coeff17_spec
  · exact x4SubRow21Coeff18_spec
  · exact x4SubRow21Coeff19_spec

private theorem x4SubRow21Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 j =
      ((rectangularize 53 73 X4Data).getD 21 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow21Coeff20_spec
  · exact x4SubRow21Coeff21_spec
  · exact x4SubRow21Coeff22_spec
  · exact x4SubRow21Coeff23_spec
  · exact x4SubRow21Coeff24_spec
  · exact x4SubRow21Coeff25_spec
  · exact x4SubRow21Coeff26_spec
  · exact x4SubRow21Coeff27_spec
  · exact x4SubRow21Coeff28_spec
  · exact x4SubRow21Coeff29_spec

private theorem x4SubRow21Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 j =
      ((rectangularize 53 73 X4Data).getD 21 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow21Coeff30_spec
  · exact x4SubRow21Coeff31_spec
  · exact x4SubRow21Coeff32_spec
  · exact x4SubRow21Coeff33_spec
  · exact x4SubRow21Coeff34_spec
  · exact x4SubRow21Coeff35_spec
  · exact x4SubRow21Coeff36_spec
  · exact x4SubRow21Coeff37_spec
  · exact x4SubRow21Coeff38_spec
  · exact x4SubRow21Coeff39_spec

private theorem x4SubRow21Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 j =
      ((rectangularize 53 73 X4Data).getD 21 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow21Coeff40_spec
  · exact x4SubRow21Coeff41_spec
  · exact x4SubRow21Coeff42_spec
  · exact x4SubRow21Coeff43_spec
  · exact x4SubRow21Coeff44_spec
  · exact x4SubRow21Coeff45_spec
  · exact x4SubRow21Coeff46_spec
  · exact x4SubRow21Coeff47_spec
  · exact x4SubRow21Coeff48_spec
  · exact x4SubRow21Coeff49_spec

private theorem x4SubRow21Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 j =
      ((rectangularize 53 73 X4Data).getD 21 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow21Coeff50_spec
  · exact x4SubRow21Coeff51_spec
  · exact x4SubRow21Coeff52_spec
  · exact x4SubRow21Coeff53_spec
  · exact x4SubRow21Coeff54_spec
  · exact x4SubRow21Coeff55_spec
  · exact x4SubRow21Coeff56_spec
  · exact x4SubRow21Coeff57_spec
  · exact x4SubRow21Coeff58_spec
  · exact x4SubRow21Coeff59_spec

private theorem x4SubRow21Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 j =
      ((rectangularize 53 73 X4Data).getD 21 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow21Coeff60_spec
  · exact x4SubRow21Coeff61_spec
  · exact x4SubRow21Coeff62_spec
  · exact x4SubRow21Coeff63_spec
  · exact x4SubRow21Coeff64_spec
  · exact x4SubRow21Coeff65_spec
  · exact x4SubRow21Coeff66_spec
  · exact x4SubRow21Coeff67_spec
  · exact x4SubRow21Coeff68_spec
  · exact x4SubRow21Coeff69_spec

private theorem x4SubRow21Coeffs70To72_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 73) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 j =
      ((rectangularize 53 73 X4Data).getD 21 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 := by
    omega
  rcases hCases with
    rfl | rfl | rfl
  · exact x4SubRow21Coeff70_spec
  · exact x4SubRow21Coeff71_spec
  · exact x4SubRow21Coeff72_spec

private theorem x4SubRow21_coefficients (j : ℕ) (hj : j < 73) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 21 j =
      ((rectangularize 53 73 X4Data).getD 21 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact x4SubRow21Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact x4SubRow21Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact x4SubRow21Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact x4SubRow21Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact x4SubRow21Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact x4SubRow21Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact x4SubRow21Coeffs60To69_spec j (by omega) h70
  exact x4SubRow21Coeffs70To72_spec j (by omega) hj

private theorem x4SubRow21Padded_spec :
    padOne 73
        (addMulRow X4NLK3Data NegData X4NRGData 21) =
      (rectangularize 53 73 X4Data).getD 21 [] := by
  apply padOne_addMulRow_eq_of_coefficients 73
    X4NLK3Data NegData X4NRGData 21
    ((rectangularize 53 73 X4Data).getD 21 [])
  · decide
  · have hTargetSupport : (X4Data.getD 21 []).length ≤ 73 := by
      decide
    rw [getD_rectangularize 53 73 X4Data 21 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact x4SubRow21_coefficients

private theorem x4SubRow21_spec :
    (rectangularize 53 73
        (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 21 [] =
      (rectangularize 53 73 X4Data).getD 21 [] := by
  rw [getD_rectangularize 53 73
    (Two.add X4NLK3Data (Two.mul NegData X4NRGData)) 21 (by omega),
    ← addMulRow_eq_getD]
  exact x4SubRow21Padded_spec

private theorem x4SubRow22Coeff0_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 0 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 0 0 := by
  decide

private theorem x4SubRow22Coeff1_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 1 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 1 0 := by
  decide

private theorem x4SubRow22Coeff2_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 2 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 2 0 := by
  decide

private theorem x4SubRow22Coeff3_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 3 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 3 0 := by
  decide

private theorem x4SubRow22Coeff4_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 4 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 4 0 := by
  decide

private theorem x4SubRow22Coeff5_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 5 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 5 0 := by
  decide

private theorem x4SubRow22Coeff6_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 6 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 6 0 := by
  decide

private theorem x4SubRow22Coeff7_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 7 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 7 0 := by
  decide

private theorem x4SubRow22Coeff8_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 8 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 8 0 := by
  decide

private theorem x4SubRow22Coeff9_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 9 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 9 0 := by
  decide

private theorem x4SubRow22Coeff10_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 10 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 10 0 := by
  decide

private theorem x4SubRow22Coeff11_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 11 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 11 0 := by
  decide

private theorem x4SubRow22Coeff12_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 12 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 12 0 := by
  decide

private theorem x4SubRow22Coeff13_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 13 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 13 0 := by
  decide

private theorem x4SubRow22Coeff14_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 14 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 14 0 := by
  decide

private theorem x4SubRow22Coeff15_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 15 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 15 0 := by
  decide

private theorem x4SubRow22Coeff16_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 16 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 16 0 := by
  decide

private theorem x4SubRow22Coeff17_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 17 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 17 0 := by
  decide

private theorem x4SubRow22Coeff18_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 18 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 18 0 := by
  decide

private theorem x4SubRow22Coeff19_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 19 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 19 0 := by
  decide

private theorem x4SubRow22Coeff20_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 20 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 20 0 := by
  decide

private theorem x4SubRow22Coeff21_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 21 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 21 0 := by
  decide

private theorem x4SubRow22Coeff22_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 22 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 22 0 := by
  decide

private theorem x4SubRow22Coeff23_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 23 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 23 0 := by
  decide

private theorem x4SubRow22Coeff24_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 24 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 24 0 := by
  decide

private theorem x4SubRow22Coeff25_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 25 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 25 0 := by
  decide

private theorem x4SubRow22Coeff26_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 26 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 26 0 := by
  decide

private theorem x4SubRow22Coeff27_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 27 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 27 0 := by
  decide

private theorem x4SubRow22Coeff28_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 28 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 28 0 := by
  decide

private theorem x4SubRow22Coeff29_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 29 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 29 0 := by
  decide

private theorem x4SubRow22Coeff30_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 30 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 30 0 := by
  decide

private theorem x4SubRow22Coeff31_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 31 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 31 0 := by
  decide

private theorem x4SubRow22Coeff32_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 32 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 32 0 := by
  decide

private theorem x4SubRow22Coeff33_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 33 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 33 0 := by
  decide

private theorem x4SubRow22Coeff34_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 34 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 34 0 := by
  decide

private theorem x4SubRow22Coeff35_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 35 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 35 0 := by
  decide

private theorem x4SubRow22Coeff36_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 36 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 36 0 := by
  decide

private theorem x4SubRow22Coeff37_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 37 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 37 0 := by
  decide

private theorem x4SubRow22Coeff38_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 38 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 38 0 := by
  decide

private theorem x4SubRow22Coeff39_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 39 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 39 0 := by
  decide

private theorem x4SubRow22Coeff40_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 40 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 40 0 := by
  decide

private theorem x4SubRow22Coeff41_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 41 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 41 0 := by
  decide

private theorem x4SubRow22Coeff42_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 42 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 42 0 := by
  decide

private theorem x4SubRow22Coeff43_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 43 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 43 0 := by
  decide

private theorem x4SubRow22Coeff44_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 44 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 44 0 := by
  decide

private theorem x4SubRow22Coeff45_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 45 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 45 0 := by
  decide

private theorem x4SubRow22Coeff46_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 46 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 46 0 := by
  decide

private theorem x4SubRow22Coeff47_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 47 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 47 0 := by
  decide

private theorem x4SubRow22Coeff48_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 48 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 48 0 := by
  decide

private theorem x4SubRow22Coeff49_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 49 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 49 0 := by
  decide

private theorem x4SubRow22Coeff50_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 50 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 50 0 := by
  decide

private theorem x4SubRow22Coeff51_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 51 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 51 0 := by
  decide

private theorem x4SubRow22Coeff52_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 52 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 52 0 := by
  decide

private theorem x4SubRow22Coeff53_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 53 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 53 0 := by
  decide

private theorem x4SubRow22Coeff54_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 54 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 54 0 := by
  decide

private theorem x4SubRow22Coeff55_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 55 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 55 0 := by
  decide

private theorem x4SubRow22Coeff56_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 56 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 56 0 := by
  decide

private theorem x4SubRow22Coeff57_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 57 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 57 0 := by
  decide

private theorem x4SubRow22Coeff58_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 58 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 58 0 := by
  decide

private theorem x4SubRow22Coeff59_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 59 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 59 0 := by
  decide

private theorem x4SubRow22Coeff60_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 60 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 60 0 := by
  decide

private theorem x4SubRow22Coeff61_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 61 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 61 0 := by
  decide

private theorem x4SubRow22Coeff62_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 62 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 62 0 := by
  decide

private theorem x4SubRow22Coeff63_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 63 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 63 0 := by
  decide

private theorem x4SubRow22Coeff64_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 64 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 64 0 := by
  decide

private theorem x4SubRow22Coeff65_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 65 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 65 0 := by
  decide

private theorem x4SubRow22Coeff66_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 66 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 66 0 := by
  decide

private theorem x4SubRow22Coeff67_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 67 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 67 0 := by
  decide

private theorem x4SubRow22Coeff68_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 68 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 68 0 := by
  decide

private theorem x4SubRow22Coeff69_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 69 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 69 0 := by
  decide

private theorem x4SubRow22Coeff70_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 70 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 70 0 := by
  decide

private theorem x4SubRow22Coeff71_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 71 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 71 0 := by
  decide

private theorem x4SubRow22Coeff72_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 72 =
      ((rectangularize 53 73 X4Data).getD 22 []).getD 72 0 := by
  decide

private theorem x4SubRow22Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 j =
      ((rectangularize 53 73 X4Data).getD 22 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow22Coeff0_spec
  · exact x4SubRow22Coeff1_spec
  · exact x4SubRow22Coeff2_spec
  · exact x4SubRow22Coeff3_spec
  · exact x4SubRow22Coeff4_spec
  · exact x4SubRow22Coeff5_spec
  · exact x4SubRow22Coeff6_spec
  · exact x4SubRow22Coeff7_spec
  · exact x4SubRow22Coeff8_spec
  · exact x4SubRow22Coeff9_spec

private theorem x4SubRow22Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 j =
      ((rectangularize 53 73 X4Data).getD 22 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow22Coeff10_spec
  · exact x4SubRow22Coeff11_spec
  · exact x4SubRow22Coeff12_spec
  · exact x4SubRow22Coeff13_spec
  · exact x4SubRow22Coeff14_spec
  · exact x4SubRow22Coeff15_spec
  · exact x4SubRow22Coeff16_spec
  · exact x4SubRow22Coeff17_spec
  · exact x4SubRow22Coeff18_spec
  · exact x4SubRow22Coeff19_spec

private theorem x4SubRow22Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 j =
      ((rectangularize 53 73 X4Data).getD 22 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow22Coeff20_spec
  · exact x4SubRow22Coeff21_spec
  · exact x4SubRow22Coeff22_spec
  · exact x4SubRow22Coeff23_spec
  · exact x4SubRow22Coeff24_spec
  · exact x4SubRow22Coeff25_spec
  · exact x4SubRow22Coeff26_spec
  · exact x4SubRow22Coeff27_spec
  · exact x4SubRow22Coeff28_spec
  · exact x4SubRow22Coeff29_spec

private theorem x4SubRow22Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 j =
      ((rectangularize 53 73 X4Data).getD 22 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow22Coeff30_spec
  · exact x4SubRow22Coeff31_spec
  · exact x4SubRow22Coeff32_spec
  · exact x4SubRow22Coeff33_spec
  · exact x4SubRow22Coeff34_spec
  · exact x4SubRow22Coeff35_spec
  · exact x4SubRow22Coeff36_spec
  · exact x4SubRow22Coeff37_spec
  · exact x4SubRow22Coeff38_spec
  · exact x4SubRow22Coeff39_spec

private theorem x4SubRow22Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 j =
      ((rectangularize 53 73 X4Data).getD 22 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow22Coeff40_spec
  · exact x4SubRow22Coeff41_spec
  · exact x4SubRow22Coeff42_spec
  · exact x4SubRow22Coeff43_spec
  · exact x4SubRow22Coeff44_spec
  · exact x4SubRow22Coeff45_spec
  · exact x4SubRow22Coeff46_spec
  · exact x4SubRow22Coeff47_spec
  · exact x4SubRow22Coeff48_spec
  · exact x4SubRow22Coeff49_spec

private theorem x4SubRow22Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 j =
      ((rectangularize 53 73 X4Data).getD 22 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow22Coeff50_spec
  · exact x4SubRow22Coeff51_spec
  · exact x4SubRow22Coeff52_spec
  · exact x4SubRow22Coeff53_spec
  · exact x4SubRow22Coeff54_spec
  · exact x4SubRow22Coeff55_spec
  · exact x4SubRow22Coeff56_spec
  · exact x4SubRow22Coeff57_spec
  · exact x4SubRow22Coeff58_spec
  · exact x4SubRow22Coeff59_spec

private theorem x4SubRow22Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 j =
      ((rectangularize 53 73 X4Data).getD 22 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow22Coeff60_spec
  · exact x4SubRow22Coeff61_spec
  · exact x4SubRow22Coeff62_spec
  · exact x4SubRow22Coeff63_spec
  · exact x4SubRow22Coeff64_spec
  · exact x4SubRow22Coeff65_spec
  · exact x4SubRow22Coeff66_spec
  · exact x4SubRow22Coeff67_spec
  · exact x4SubRow22Coeff68_spec
  · exact x4SubRow22Coeff69_spec

private theorem x4SubRow22Coeffs70To72_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 73) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 j =
      ((rectangularize 53 73 X4Data).getD 22 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 := by
    omega
  rcases hCases with
    rfl | rfl | rfl
  · exact x4SubRow22Coeff70_spec
  · exact x4SubRow22Coeff71_spec
  · exact x4SubRow22Coeff72_spec

private theorem x4SubRow22_coefficients (j : ℕ) (hj : j < 73) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 22 j =
      ((rectangularize 53 73 X4Data).getD 22 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact x4SubRow22Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact x4SubRow22Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact x4SubRow22Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact x4SubRow22Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact x4SubRow22Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact x4SubRow22Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact x4SubRow22Coeffs60To69_spec j (by omega) h70
  exact x4SubRow22Coeffs70To72_spec j (by omega) hj

private theorem x4SubRow22Padded_spec :
    padOne 73
        (addMulRow X4NLK3Data NegData X4NRGData 22) =
      (rectangularize 53 73 X4Data).getD 22 [] := by
  apply padOne_addMulRow_eq_of_coefficients 73
    X4NLK3Data NegData X4NRGData 22
    ((rectangularize 53 73 X4Data).getD 22 [])
  · decide
  · have hTargetSupport : (X4Data.getD 22 []).length ≤ 73 := by
      decide
    rw [getD_rectangularize 53 73 X4Data 22 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact x4SubRow22_coefficients

private theorem x4SubRow22_spec :
    (rectangularize 53 73
        (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 22 [] =
      (rectangularize 53 73 X4Data).getD 22 [] := by
  rw [getD_rectangularize 53 73
    (Two.add X4NLK3Data (Two.mul NegData X4NRGData)) 22 (by omega),
    ← addMulRow_eq_getD]
  exact x4SubRow22Padded_spec

private theorem x4SubRow23Coeff0_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 0 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 0 0 := by
  decide

private theorem x4SubRow23Coeff1_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 1 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 1 0 := by
  decide

private theorem x4SubRow23Coeff2_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 2 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 2 0 := by
  decide

private theorem x4SubRow23Coeff3_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 3 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 3 0 := by
  decide

private theorem x4SubRow23Coeff4_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 4 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 4 0 := by
  decide

private theorem x4SubRow23Coeff5_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 5 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 5 0 := by
  decide

private theorem x4SubRow23Coeff6_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 6 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 6 0 := by
  decide

private theorem x4SubRow23Coeff7_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 7 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 7 0 := by
  decide

private theorem x4SubRow23Coeff8_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 8 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 8 0 := by
  decide

private theorem x4SubRow23Coeff9_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 9 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 9 0 := by
  decide

private theorem x4SubRow23Coeff10_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 10 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 10 0 := by
  decide

private theorem x4SubRow23Coeff11_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 11 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 11 0 := by
  decide

private theorem x4SubRow23Coeff12_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 12 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 12 0 := by
  decide

private theorem x4SubRow23Coeff13_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 13 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 13 0 := by
  decide

private theorem x4SubRow23Coeff14_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 14 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 14 0 := by
  decide

private theorem x4SubRow23Coeff15_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 15 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 15 0 := by
  decide

private theorem x4SubRow23Coeff16_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 16 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 16 0 := by
  decide

private theorem x4SubRow23Coeff17_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 17 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 17 0 := by
  decide

private theorem x4SubRow23Coeff18_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 18 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 18 0 := by
  decide

private theorem x4SubRow23Coeff19_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 19 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 19 0 := by
  decide

private theorem x4SubRow23Coeff20_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 20 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 20 0 := by
  decide

private theorem x4SubRow23Coeff21_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 21 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 21 0 := by
  decide

private theorem x4SubRow23Coeff22_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 22 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 22 0 := by
  decide

private theorem x4SubRow23Coeff23_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 23 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 23 0 := by
  decide

private theorem x4SubRow23Coeff24_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 24 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 24 0 := by
  decide

private theorem x4SubRow23Coeff25_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 25 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 25 0 := by
  decide

private theorem x4SubRow23Coeff26_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 26 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 26 0 := by
  decide

private theorem x4SubRow23Coeff27_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 27 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 27 0 := by
  decide

private theorem x4SubRow23Coeff28_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 28 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 28 0 := by
  decide

private theorem x4SubRow23Coeff29_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 29 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 29 0 := by
  decide

private theorem x4SubRow23Coeff30_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 30 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 30 0 := by
  decide

private theorem x4SubRow23Coeff31_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 31 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 31 0 := by
  decide

private theorem x4SubRow23Coeff32_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 32 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 32 0 := by
  decide

private theorem x4SubRow23Coeff33_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 33 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 33 0 := by
  decide

private theorem x4SubRow23Coeff34_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 34 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 34 0 := by
  decide

private theorem x4SubRow23Coeff35_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 35 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 35 0 := by
  decide

private theorem x4SubRow23Coeff36_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 36 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 36 0 := by
  decide

private theorem x4SubRow23Coeff37_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 37 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 37 0 := by
  decide

private theorem x4SubRow23Coeff38_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 38 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 38 0 := by
  decide

private theorem x4SubRow23Coeff39_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 39 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 39 0 := by
  decide

private theorem x4SubRow23Coeff40_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 40 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 40 0 := by
  decide

private theorem x4SubRow23Coeff41_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 41 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 41 0 := by
  decide

private theorem x4SubRow23Coeff42_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 42 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 42 0 := by
  decide

private theorem x4SubRow23Coeff43_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 43 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 43 0 := by
  decide

private theorem x4SubRow23Coeff44_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 44 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 44 0 := by
  decide

private theorem x4SubRow23Coeff45_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 45 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 45 0 := by
  decide

private theorem x4SubRow23Coeff46_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 46 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 46 0 := by
  decide

private theorem x4SubRow23Coeff47_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 47 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 47 0 := by
  decide

private theorem x4SubRow23Coeff48_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 48 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 48 0 := by
  decide

private theorem x4SubRow23Coeff49_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 49 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 49 0 := by
  decide

private theorem x4SubRow23Coeff50_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 50 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 50 0 := by
  decide

private theorem x4SubRow23Coeff51_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 51 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 51 0 := by
  decide

private theorem x4SubRow23Coeff52_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 52 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 52 0 := by
  decide

private theorem x4SubRow23Coeff53_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 53 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 53 0 := by
  decide

private theorem x4SubRow23Coeff54_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 54 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 54 0 := by
  decide

private theorem x4SubRow23Coeff55_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 55 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 55 0 := by
  decide

private theorem x4SubRow23Coeff56_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 56 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 56 0 := by
  decide

private theorem x4SubRow23Coeff57_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 57 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 57 0 := by
  decide

private theorem x4SubRow23Coeff58_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 58 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 58 0 := by
  decide

private theorem x4SubRow23Coeff59_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 59 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 59 0 := by
  decide

private theorem x4SubRow23Coeff60_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 60 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 60 0 := by
  decide

private theorem x4SubRow23Coeff61_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 61 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 61 0 := by
  decide

private theorem x4SubRow23Coeff62_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 62 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 62 0 := by
  decide

private theorem x4SubRow23Coeff63_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 63 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 63 0 := by
  decide

private theorem x4SubRow23Coeff64_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 64 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 64 0 := by
  decide

private theorem x4SubRow23Coeff65_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 65 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 65 0 := by
  decide

private theorem x4SubRow23Coeff66_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 66 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 66 0 := by
  decide

private theorem x4SubRow23Coeff67_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 67 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 67 0 := by
  decide

private theorem x4SubRow23Coeff68_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 68 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 68 0 := by
  decide

private theorem x4SubRow23Coeff69_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 69 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 69 0 := by
  decide

private theorem x4SubRow23Coeff70_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 70 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 70 0 := by
  decide

private theorem x4SubRow23Coeff71_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 71 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 71 0 := by
  decide

private theorem x4SubRow23Coeff72_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 72 =
      ((rectangularize 53 73 X4Data).getD 23 []).getD 72 0 := by
  decide

private theorem x4SubRow23Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 j =
      ((rectangularize 53 73 X4Data).getD 23 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow23Coeff0_spec
  · exact x4SubRow23Coeff1_spec
  · exact x4SubRow23Coeff2_spec
  · exact x4SubRow23Coeff3_spec
  · exact x4SubRow23Coeff4_spec
  · exact x4SubRow23Coeff5_spec
  · exact x4SubRow23Coeff6_spec
  · exact x4SubRow23Coeff7_spec
  · exact x4SubRow23Coeff8_spec
  · exact x4SubRow23Coeff9_spec

private theorem x4SubRow23Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 j =
      ((rectangularize 53 73 X4Data).getD 23 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow23Coeff10_spec
  · exact x4SubRow23Coeff11_spec
  · exact x4SubRow23Coeff12_spec
  · exact x4SubRow23Coeff13_spec
  · exact x4SubRow23Coeff14_spec
  · exact x4SubRow23Coeff15_spec
  · exact x4SubRow23Coeff16_spec
  · exact x4SubRow23Coeff17_spec
  · exact x4SubRow23Coeff18_spec
  · exact x4SubRow23Coeff19_spec

private theorem x4SubRow23Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 j =
      ((rectangularize 53 73 X4Data).getD 23 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow23Coeff20_spec
  · exact x4SubRow23Coeff21_spec
  · exact x4SubRow23Coeff22_spec
  · exact x4SubRow23Coeff23_spec
  · exact x4SubRow23Coeff24_spec
  · exact x4SubRow23Coeff25_spec
  · exact x4SubRow23Coeff26_spec
  · exact x4SubRow23Coeff27_spec
  · exact x4SubRow23Coeff28_spec
  · exact x4SubRow23Coeff29_spec

private theorem x4SubRow23Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 j =
      ((rectangularize 53 73 X4Data).getD 23 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow23Coeff30_spec
  · exact x4SubRow23Coeff31_spec
  · exact x4SubRow23Coeff32_spec
  · exact x4SubRow23Coeff33_spec
  · exact x4SubRow23Coeff34_spec
  · exact x4SubRow23Coeff35_spec
  · exact x4SubRow23Coeff36_spec
  · exact x4SubRow23Coeff37_spec
  · exact x4SubRow23Coeff38_spec
  · exact x4SubRow23Coeff39_spec

private theorem x4SubRow23Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 j =
      ((rectangularize 53 73 X4Data).getD 23 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow23Coeff40_spec
  · exact x4SubRow23Coeff41_spec
  · exact x4SubRow23Coeff42_spec
  · exact x4SubRow23Coeff43_spec
  · exact x4SubRow23Coeff44_spec
  · exact x4SubRow23Coeff45_spec
  · exact x4SubRow23Coeff46_spec
  · exact x4SubRow23Coeff47_spec
  · exact x4SubRow23Coeff48_spec
  · exact x4SubRow23Coeff49_spec

private theorem x4SubRow23Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 j =
      ((rectangularize 53 73 X4Data).getD 23 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow23Coeff50_spec
  · exact x4SubRow23Coeff51_spec
  · exact x4SubRow23Coeff52_spec
  · exact x4SubRow23Coeff53_spec
  · exact x4SubRow23Coeff54_spec
  · exact x4SubRow23Coeff55_spec
  · exact x4SubRow23Coeff56_spec
  · exact x4SubRow23Coeff57_spec
  · exact x4SubRow23Coeff58_spec
  · exact x4SubRow23Coeff59_spec

private theorem x4SubRow23Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 j =
      ((rectangularize 53 73 X4Data).getD 23 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow23Coeff60_spec
  · exact x4SubRow23Coeff61_spec
  · exact x4SubRow23Coeff62_spec
  · exact x4SubRow23Coeff63_spec
  · exact x4SubRow23Coeff64_spec
  · exact x4SubRow23Coeff65_spec
  · exact x4SubRow23Coeff66_spec
  · exact x4SubRow23Coeff67_spec
  · exact x4SubRow23Coeff68_spec
  · exact x4SubRow23Coeff69_spec

private theorem x4SubRow23Coeffs70To72_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 73) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 j =
      ((rectangularize 53 73 X4Data).getD 23 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 := by
    omega
  rcases hCases with
    rfl | rfl | rfl
  · exact x4SubRow23Coeff70_spec
  · exact x4SubRow23Coeff71_spec
  · exact x4SubRow23Coeff72_spec

private theorem x4SubRow23_coefficients (j : ℕ) (hj : j < 73) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 23 j =
      ((rectangularize 53 73 X4Data).getD 23 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact x4SubRow23Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact x4SubRow23Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact x4SubRow23Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact x4SubRow23Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact x4SubRow23Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact x4SubRow23Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact x4SubRow23Coeffs60To69_spec j (by omega) h70
  exact x4SubRow23Coeffs70To72_spec j (by omega) hj

private theorem x4SubRow23Padded_spec :
    padOne 73
        (addMulRow X4NLK3Data NegData X4NRGData 23) =
      (rectangularize 53 73 X4Data).getD 23 [] := by
  apply padOne_addMulRow_eq_of_coefficients 73
    X4NLK3Data NegData X4NRGData 23
    ((rectangularize 53 73 X4Data).getD 23 [])
  · decide
  · have hTargetSupport : (X4Data.getD 23 []).length ≤ 73 := by
      decide
    rw [getD_rectangularize 53 73 X4Data 23 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact x4SubRow23_coefficients

private theorem x4SubRow23_spec :
    (rectangularize 53 73
        (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 23 [] =
      (rectangularize 53 73 X4Data).getD 23 [] := by
  rw [getD_rectangularize 53 73
    (Two.add X4NLK3Data (Two.mul NegData X4NRGData)) 23 (by omega),
    ← addMulRow_eq_getD]
  exact x4SubRow23Padded_spec

private theorem x4SubRow24Coeff0_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 0 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 0 0 := by
  decide

private theorem x4SubRow24Coeff1_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 1 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 1 0 := by
  decide

private theorem x4SubRow24Coeff2_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 2 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 2 0 := by
  decide

private theorem x4SubRow24Coeff3_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 3 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 3 0 := by
  decide

private theorem x4SubRow24Coeff4_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 4 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 4 0 := by
  decide

private theorem x4SubRow24Coeff5_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 5 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 5 0 := by
  decide

private theorem x4SubRow24Coeff6_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 6 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 6 0 := by
  decide

private theorem x4SubRow24Coeff7_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 7 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 7 0 := by
  decide

private theorem x4SubRow24Coeff8_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 8 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 8 0 := by
  decide

private theorem x4SubRow24Coeff9_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 9 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 9 0 := by
  decide

private theorem x4SubRow24Coeff10_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 10 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 10 0 := by
  decide

private theorem x4SubRow24Coeff11_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 11 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 11 0 := by
  decide

private theorem x4SubRow24Coeff12_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 12 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 12 0 := by
  decide

private theorem x4SubRow24Coeff13_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 13 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 13 0 := by
  decide

private theorem x4SubRow24Coeff14_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 14 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 14 0 := by
  decide

private theorem x4SubRow24Coeff15_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 15 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 15 0 := by
  decide

private theorem x4SubRow24Coeff16_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 16 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 16 0 := by
  decide

private theorem x4SubRow24Coeff17_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 17 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 17 0 := by
  decide

private theorem x4SubRow24Coeff18_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 18 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 18 0 := by
  decide

private theorem x4SubRow24Coeff19_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 19 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 19 0 := by
  decide

private theorem x4SubRow24Coeff20_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 20 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 20 0 := by
  decide

private theorem x4SubRow24Coeff21_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 21 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 21 0 := by
  decide

private theorem x4SubRow24Coeff22_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 22 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 22 0 := by
  decide

private theorem x4SubRow24Coeff23_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 23 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 23 0 := by
  decide

private theorem x4SubRow24Coeff24_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 24 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 24 0 := by
  decide

private theorem x4SubRow24Coeff25_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 25 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 25 0 := by
  decide

private theorem x4SubRow24Coeff26_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 26 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 26 0 := by
  decide

private theorem x4SubRow24Coeff27_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 27 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 27 0 := by
  decide

private theorem x4SubRow24Coeff28_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 28 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 28 0 := by
  decide

private theorem x4SubRow24Coeff29_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 29 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 29 0 := by
  decide

private theorem x4SubRow24Coeff30_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 30 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 30 0 := by
  decide

private theorem x4SubRow24Coeff31_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 31 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 31 0 := by
  decide

private theorem x4SubRow24Coeff32_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 32 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 32 0 := by
  decide

private theorem x4SubRow24Coeff33_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 33 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 33 0 := by
  decide

private theorem x4SubRow24Coeff34_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 34 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 34 0 := by
  decide

private theorem x4SubRow24Coeff35_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 35 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 35 0 := by
  decide

private theorem x4SubRow24Coeff36_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 36 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 36 0 := by
  decide

private theorem x4SubRow24Coeff37_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 37 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 37 0 := by
  decide

private theorem x4SubRow24Coeff38_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 38 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 38 0 := by
  decide

private theorem x4SubRow24Coeff39_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 39 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 39 0 := by
  decide

private theorem x4SubRow24Coeff40_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 40 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 40 0 := by
  decide

private theorem x4SubRow24Coeff41_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 41 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 41 0 := by
  decide

private theorem x4SubRow24Coeff42_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 42 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 42 0 := by
  decide

private theorem x4SubRow24Coeff43_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 43 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 43 0 := by
  decide

private theorem x4SubRow24Coeff44_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 44 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 44 0 := by
  decide

private theorem x4SubRow24Coeff45_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 45 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 45 0 := by
  decide

private theorem x4SubRow24Coeff46_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 46 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 46 0 := by
  decide

private theorem x4SubRow24Coeff47_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 47 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 47 0 := by
  decide

private theorem x4SubRow24Coeff48_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 48 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 48 0 := by
  decide

private theorem x4SubRow24Coeff49_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 49 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 49 0 := by
  decide

private theorem x4SubRow24Coeff50_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 50 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 50 0 := by
  decide

private theorem x4SubRow24Coeff51_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 51 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 51 0 := by
  decide

private theorem x4SubRow24Coeff52_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 52 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 52 0 := by
  decide

private theorem x4SubRow24Coeff53_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 53 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 53 0 := by
  decide

private theorem x4SubRow24Coeff54_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 54 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 54 0 := by
  decide

private theorem x4SubRow24Coeff55_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 55 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 55 0 := by
  decide

private theorem x4SubRow24Coeff56_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 56 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 56 0 := by
  decide

private theorem x4SubRow24Coeff57_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 57 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 57 0 := by
  decide

private theorem x4SubRow24Coeff58_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 58 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 58 0 := by
  decide

private theorem x4SubRow24Coeff59_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 59 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 59 0 := by
  decide

private theorem x4SubRow24Coeff60_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 60 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 60 0 := by
  decide

private theorem x4SubRow24Coeff61_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 61 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 61 0 := by
  decide

private theorem x4SubRow24Coeff62_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 62 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 62 0 := by
  decide

private theorem x4SubRow24Coeff63_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 63 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 63 0 := by
  decide

private theorem x4SubRow24Coeff64_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 64 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 64 0 := by
  decide

private theorem x4SubRow24Coeff65_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 65 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 65 0 := by
  decide

private theorem x4SubRow24Coeff66_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 66 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 66 0 := by
  decide

private theorem x4SubRow24Coeff67_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 67 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 67 0 := by
  decide

private theorem x4SubRow24Coeff68_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 68 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 68 0 := by
  decide

private theorem x4SubRow24Coeff69_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 69 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 69 0 := by
  decide

private theorem x4SubRow24Coeff70_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 70 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 70 0 := by
  decide

private theorem x4SubRow24Coeff71_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 71 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 71 0 := by
  decide

private theorem x4SubRow24Coeff72_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 72 =
      ((rectangularize 53 73 X4Data).getD 24 []).getD 72 0 := by
  decide

private theorem x4SubRow24Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 j =
      ((rectangularize 53 73 X4Data).getD 24 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow24Coeff0_spec
  · exact x4SubRow24Coeff1_spec
  · exact x4SubRow24Coeff2_spec
  · exact x4SubRow24Coeff3_spec
  · exact x4SubRow24Coeff4_spec
  · exact x4SubRow24Coeff5_spec
  · exact x4SubRow24Coeff6_spec
  · exact x4SubRow24Coeff7_spec
  · exact x4SubRow24Coeff8_spec
  · exact x4SubRow24Coeff9_spec

private theorem x4SubRow24Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 j =
      ((rectangularize 53 73 X4Data).getD 24 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow24Coeff10_spec
  · exact x4SubRow24Coeff11_spec
  · exact x4SubRow24Coeff12_spec
  · exact x4SubRow24Coeff13_spec
  · exact x4SubRow24Coeff14_spec
  · exact x4SubRow24Coeff15_spec
  · exact x4SubRow24Coeff16_spec
  · exact x4SubRow24Coeff17_spec
  · exact x4SubRow24Coeff18_spec
  · exact x4SubRow24Coeff19_spec

private theorem x4SubRow24Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 j =
      ((rectangularize 53 73 X4Data).getD 24 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow24Coeff20_spec
  · exact x4SubRow24Coeff21_spec
  · exact x4SubRow24Coeff22_spec
  · exact x4SubRow24Coeff23_spec
  · exact x4SubRow24Coeff24_spec
  · exact x4SubRow24Coeff25_spec
  · exact x4SubRow24Coeff26_spec
  · exact x4SubRow24Coeff27_spec
  · exact x4SubRow24Coeff28_spec
  · exact x4SubRow24Coeff29_spec

private theorem x4SubRow24Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 j =
      ((rectangularize 53 73 X4Data).getD 24 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow24Coeff30_spec
  · exact x4SubRow24Coeff31_spec
  · exact x4SubRow24Coeff32_spec
  · exact x4SubRow24Coeff33_spec
  · exact x4SubRow24Coeff34_spec
  · exact x4SubRow24Coeff35_spec
  · exact x4SubRow24Coeff36_spec
  · exact x4SubRow24Coeff37_spec
  · exact x4SubRow24Coeff38_spec
  · exact x4SubRow24Coeff39_spec

private theorem x4SubRow24Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 j =
      ((rectangularize 53 73 X4Data).getD 24 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow24Coeff40_spec
  · exact x4SubRow24Coeff41_spec
  · exact x4SubRow24Coeff42_spec
  · exact x4SubRow24Coeff43_spec
  · exact x4SubRow24Coeff44_spec
  · exact x4SubRow24Coeff45_spec
  · exact x4SubRow24Coeff46_spec
  · exact x4SubRow24Coeff47_spec
  · exact x4SubRow24Coeff48_spec
  · exact x4SubRow24Coeff49_spec

private theorem x4SubRow24Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 j =
      ((rectangularize 53 73 X4Data).getD 24 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow24Coeff50_spec
  · exact x4SubRow24Coeff51_spec
  · exact x4SubRow24Coeff52_spec
  · exact x4SubRow24Coeff53_spec
  · exact x4SubRow24Coeff54_spec
  · exact x4SubRow24Coeff55_spec
  · exact x4SubRow24Coeff56_spec
  · exact x4SubRow24Coeff57_spec
  · exact x4SubRow24Coeff58_spec
  · exact x4SubRow24Coeff59_spec

private theorem x4SubRow24Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 j =
      ((rectangularize 53 73 X4Data).getD 24 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow24Coeff60_spec
  · exact x4SubRow24Coeff61_spec
  · exact x4SubRow24Coeff62_spec
  · exact x4SubRow24Coeff63_spec
  · exact x4SubRow24Coeff64_spec
  · exact x4SubRow24Coeff65_spec
  · exact x4SubRow24Coeff66_spec
  · exact x4SubRow24Coeff67_spec
  · exact x4SubRow24Coeff68_spec
  · exact x4SubRow24Coeff69_spec

private theorem x4SubRow24Coeffs70To72_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 73) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 j =
      ((rectangularize 53 73 X4Data).getD 24 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 := by
    omega
  rcases hCases with
    rfl | rfl | rfl
  · exact x4SubRow24Coeff70_spec
  · exact x4SubRow24Coeff71_spec
  · exact x4SubRow24Coeff72_spec

private theorem x4SubRow24_coefficients (j : ℕ) (hj : j < 73) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 24 j =
      ((rectangularize 53 73 X4Data).getD 24 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact x4SubRow24Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact x4SubRow24Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact x4SubRow24Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact x4SubRow24Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact x4SubRow24Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact x4SubRow24Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact x4SubRow24Coeffs60To69_spec j (by omega) h70
  exact x4SubRow24Coeffs70To72_spec j (by omega) hj

private theorem x4SubRow24Padded_spec :
    padOne 73
        (addMulRow X4NLK3Data NegData X4NRGData 24) =
      (rectangularize 53 73 X4Data).getD 24 [] := by
  apply padOne_addMulRow_eq_of_coefficients 73
    X4NLK3Data NegData X4NRGData 24
    ((rectangularize 53 73 X4Data).getD 24 [])
  · decide
  · have hTargetSupport : (X4Data.getD 24 []).length ≤ 73 := by
      decide
    rw [getD_rectangularize 53 73 X4Data 24 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact x4SubRow24_coefficients

private theorem x4SubRow24_spec :
    (rectangularize 53 73
        (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 24 [] =
      (rectangularize 53 73 X4Data).getD 24 [] := by
  rw [getD_rectangularize 53 73
    (Two.add X4NLK3Data (Two.mul NegData X4NRGData)) 24 (by omega),
    ← addMulRow_eq_getD]
  exact x4SubRow24Padded_spec

private theorem x4SubRow25Coeff0_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 0 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 0 0 := by
  decide

private theorem x4SubRow25Coeff1_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 1 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 1 0 := by
  decide

private theorem x4SubRow25Coeff2_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 2 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 2 0 := by
  decide

private theorem x4SubRow25Coeff3_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 3 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 3 0 := by
  decide

private theorem x4SubRow25Coeff4_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 4 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 4 0 := by
  decide

private theorem x4SubRow25Coeff5_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 5 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 5 0 := by
  decide

private theorem x4SubRow25Coeff6_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 6 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 6 0 := by
  decide

private theorem x4SubRow25Coeff7_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 7 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 7 0 := by
  decide

private theorem x4SubRow25Coeff8_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 8 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 8 0 := by
  decide

private theorem x4SubRow25Coeff9_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 9 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 9 0 := by
  decide

private theorem x4SubRow25Coeff10_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 10 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 10 0 := by
  decide

private theorem x4SubRow25Coeff11_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 11 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 11 0 := by
  decide

private theorem x4SubRow25Coeff12_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 12 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 12 0 := by
  decide

private theorem x4SubRow25Coeff13_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 13 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 13 0 := by
  decide

private theorem x4SubRow25Coeff14_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 14 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 14 0 := by
  decide

private theorem x4SubRow25Coeff15_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 15 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 15 0 := by
  decide

private theorem x4SubRow25Coeff16_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 16 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 16 0 := by
  decide

private theorem x4SubRow25Coeff17_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 17 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 17 0 := by
  decide

private theorem x4SubRow25Coeff18_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 18 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 18 0 := by
  decide

private theorem x4SubRow25Coeff19_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 19 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 19 0 := by
  decide

private theorem x4SubRow25Coeff20_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 20 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 20 0 := by
  decide

private theorem x4SubRow25Coeff21_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 21 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 21 0 := by
  decide

private theorem x4SubRow25Coeff22_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 22 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 22 0 := by
  decide

private theorem x4SubRow25Coeff23_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 23 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 23 0 := by
  decide

private theorem x4SubRow25Coeff24_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 24 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 24 0 := by
  decide

private theorem x4SubRow25Coeff25_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 25 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 25 0 := by
  decide

private theorem x4SubRow25Coeff26_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 26 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 26 0 := by
  decide

private theorem x4SubRow25Coeff27_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 27 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 27 0 := by
  decide

private theorem x4SubRow25Coeff28_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 28 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 28 0 := by
  decide

private theorem x4SubRow25Coeff29_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 29 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 29 0 := by
  decide

private theorem x4SubRow25Coeff30_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 30 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 30 0 := by
  decide

private theorem x4SubRow25Coeff31_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 31 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 31 0 := by
  decide

private theorem x4SubRow25Coeff32_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 32 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 32 0 := by
  decide

private theorem x4SubRow25Coeff33_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 33 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 33 0 := by
  decide

private theorem x4SubRow25Coeff34_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 34 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 34 0 := by
  decide

private theorem x4SubRow25Coeff35_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 35 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 35 0 := by
  decide

private theorem x4SubRow25Coeff36_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 36 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 36 0 := by
  decide

private theorem x4SubRow25Coeff37_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 37 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 37 0 := by
  decide

private theorem x4SubRow25Coeff38_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 38 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 38 0 := by
  decide

private theorem x4SubRow25Coeff39_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 39 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 39 0 := by
  decide

private theorem x4SubRow25Coeff40_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 40 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 40 0 := by
  decide

private theorem x4SubRow25Coeff41_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 41 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 41 0 := by
  decide

private theorem x4SubRow25Coeff42_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 42 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 42 0 := by
  decide

private theorem x4SubRow25Coeff43_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 43 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 43 0 := by
  decide

private theorem x4SubRow25Coeff44_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 44 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 44 0 := by
  decide

private theorem x4SubRow25Coeff45_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 45 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 45 0 := by
  decide

private theorem x4SubRow25Coeff46_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 46 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 46 0 := by
  decide

private theorem x4SubRow25Coeff47_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 47 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 47 0 := by
  decide

private theorem x4SubRow25Coeff48_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 48 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 48 0 := by
  decide

private theorem x4SubRow25Coeff49_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 49 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 49 0 := by
  decide

private theorem x4SubRow25Coeff50_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 50 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 50 0 := by
  decide

private theorem x4SubRow25Coeff51_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 51 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 51 0 := by
  decide

private theorem x4SubRow25Coeff52_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 52 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 52 0 := by
  decide

private theorem x4SubRow25Coeff53_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 53 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 53 0 := by
  decide

private theorem x4SubRow25Coeff54_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 54 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 54 0 := by
  decide

private theorem x4SubRow25Coeff55_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 55 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 55 0 := by
  decide

private theorem x4SubRow25Coeff56_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 56 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 56 0 := by
  decide

private theorem x4SubRow25Coeff57_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 57 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 57 0 := by
  decide

private theorem x4SubRow25Coeff58_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 58 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 58 0 := by
  decide

private theorem x4SubRow25Coeff59_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 59 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 59 0 := by
  decide

private theorem x4SubRow25Coeff60_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 60 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 60 0 := by
  decide

private theorem x4SubRow25Coeff61_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 61 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 61 0 := by
  decide

private theorem x4SubRow25Coeff62_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 62 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 62 0 := by
  decide

private theorem x4SubRow25Coeff63_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 63 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 63 0 := by
  decide

private theorem x4SubRow25Coeff64_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 64 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 64 0 := by
  decide

private theorem x4SubRow25Coeff65_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 65 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 65 0 := by
  decide

private theorem x4SubRow25Coeff66_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 66 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 66 0 := by
  decide

private theorem x4SubRow25Coeff67_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 67 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 67 0 := by
  decide

private theorem x4SubRow25Coeff68_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 68 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 68 0 := by
  decide

private theorem x4SubRow25Coeff69_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 69 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 69 0 := by
  decide

private theorem x4SubRow25Coeff70_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 70 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 70 0 := by
  decide

private theorem x4SubRow25Coeff71_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 71 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 71 0 := by
  decide

private theorem x4SubRow25Coeff72_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 72 =
      ((rectangularize 53 73 X4Data).getD 25 []).getD 72 0 := by
  decide

private theorem x4SubRow25Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 j =
      ((rectangularize 53 73 X4Data).getD 25 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow25Coeff0_spec
  · exact x4SubRow25Coeff1_spec
  · exact x4SubRow25Coeff2_spec
  · exact x4SubRow25Coeff3_spec
  · exact x4SubRow25Coeff4_spec
  · exact x4SubRow25Coeff5_spec
  · exact x4SubRow25Coeff6_spec
  · exact x4SubRow25Coeff7_spec
  · exact x4SubRow25Coeff8_spec
  · exact x4SubRow25Coeff9_spec

private theorem x4SubRow25Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 j =
      ((rectangularize 53 73 X4Data).getD 25 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow25Coeff10_spec
  · exact x4SubRow25Coeff11_spec
  · exact x4SubRow25Coeff12_spec
  · exact x4SubRow25Coeff13_spec
  · exact x4SubRow25Coeff14_spec
  · exact x4SubRow25Coeff15_spec
  · exact x4SubRow25Coeff16_spec
  · exact x4SubRow25Coeff17_spec
  · exact x4SubRow25Coeff18_spec
  · exact x4SubRow25Coeff19_spec

private theorem x4SubRow25Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 j =
      ((rectangularize 53 73 X4Data).getD 25 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow25Coeff20_spec
  · exact x4SubRow25Coeff21_spec
  · exact x4SubRow25Coeff22_spec
  · exact x4SubRow25Coeff23_spec
  · exact x4SubRow25Coeff24_spec
  · exact x4SubRow25Coeff25_spec
  · exact x4SubRow25Coeff26_spec
  · exact x4SubRow25Coeff27_spec
  · exact x4SubRow25Coeff28_spec
  · exact x4SubRow25Coeff29_spec

private theorem x4SubRow25Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 j =
      ((rectangularize 53 73 X4Data).getD 25 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow25Coeff30_spec
  · exact x4SubRow25Coeff31_spec
  · exact x4SubRow25Coeff32_spec
  · exact x4SubRow25Coeff33_spec
  · exact x4SubRow25Coeff34_spec
  · exact x4SubRow25Coeff35_spec
  · exact x4SubRow25Coeff36_spec
  · exact x4SubRow25Coeff37_spec
  · exact x4SubRow25Coeff38_spec
  · exact x4SubRow25Coeff39_spec

private theorem x4SubRow25Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 j =
      ((rectangularize 53 73 X4Data).getD 25 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow25Coeff40_spec
  · exact x4SubRow25Coeff41_spec
  · exact x4SubRow25Coeff42_spec
  · exact x4SubRow25Coeff43_spec
  · exact x4SubRow25Coeff44_spec
  · exact x4SubRow25Coeff45_spec
  · exact x4SubRow25Coeff46_spec
  · exact x4SubRow25Coeff47_spec
  · exact x4SubRow25Coeff48_spec
  · exact x4SubRow25Coeff49_spec

private theorem x4SubRow25Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 j =
      ((rectangularize 53 73 X4Data).getD 25 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow25Coeff50_spec
  · exact x4SubRow25Coeff51_spec
  · exact x4SubRow25Coeff52_spec
  · exact x4SubRow25Coeff53_spec
  · exact x4SubRow25Coeff54_spec
  · exact x4SubRow25Coeff55_spec
  · exact x4SubRow25Coeff56_spec
  · exact x4SubRow25Coeff57_spec
  · exact x4SubRow25Coeff58_spec
  · exact x4SubRow25Coeff59_spec

private theorem x4SubRow25Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 j =
      ((rectangularize 53 73 X4Data).getD 25 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow25Coeff60_spec
  · exact x4SubRow25Coeff61_spec
  · exact x4SubRow25Coeff62_spec
  · exact x4SubRow25Coeff63_spec
  · exact x4SubRow25Coeff64_spec
  · exact x4SubRow25Coeff65_spec
  · exact x4SubRow25Coeff66_spec
  · exact x4SubRow25Coeff67_spec
  · exact x4SubRow25Coeff68_spec
  · exact x4SubRow25Coeff69_spec

private theorem x4SubRow25Coeffs70To72_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 73) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 j =
      ((rectangularize 53 73 X4Data).getD 25 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 := by
    omega
  rcases hCases with
    rfl | rfl | rfl
  · exact x4SubRow25Coeff70_spec
  · exact x4SubRow25Coeff71_spec
  · exact x4SubRow25Coeff72_spec

private theorem x4SubRow25_coefficients (j : ℕ) (hj : j < 73) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 25 j =
      ((rectangularize 53 73 X4Data).getD 25 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact x4SubRow25Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact x4SubRow25Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact x4SubRow25Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact x4SubRow25Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact x4SubRow25Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact x4SubRow25Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact x4SubRow25Coeffs60To69_spec j (by omega) h70
  exact x4SubRow25Coeffs70To72_spec j (by omega) hj

private theorem x4SubRow25Padded_spec :
    padOne 73
        (addMulRow X4NLK3Data NegData X4NRGData 25) =
      (rectangularize 53 73 X4Data).getD 25 [] := by
  apply padOne_addMulRow_eq_of_coefficients 73
    X4NLK3Data NegData X4NRGData 25
    ((rectangularize 53 73 X4Data).getD 25 [])
  · decide
  · have hTargetSupport : (X4Data.getD 25 []).length ≤ 73 := by
      decide
    rw [getD_rectangularize 53 73 X4Data 25 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact x4SubRow25_coefficients

private theorem x4SubRow25_spec :
    (rectangularize 53 73
        (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 25 [] =
      (rectangularize 53 73 X4Data).getD 25 [] := by
  rw [getD_rectangularize 53 73
    (Two.add X4NLK3Data (Two.mul NegData X4NRGData)) 25 (by omega),
    ← addMulRow_eq_getD]
  exact x4SubRow25Padded_spec

private theorem x4SubRow26Coeff0_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 0 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 0 0 := by
  decide

private theorem x4SubRow26Coeff1_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 1 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 1 0 := by
  decide

private theorem x4SubRow26Coeff2_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 2 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 2 0 := by
  decide

private theorem x4SubRow26Coeff3_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 3 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 3 0 := by
  decide

private theorem x4SubRow26Coeff4_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 4 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 4 0 := by
  decide

private theorem x4SubRow26Coeff5_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 5 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 5 0 := by
  decide

private theorem x4SubRow26Coeff6_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 6 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 6 0 := by
  decide

private theorem x4SubRow26Coeff7_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 7 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 7 0 := by
  decide

private theorem x4SubRow26Coeff8_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 8 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 8 0 := by
  decide

private theorem x4SubRow26Coeff9_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 9 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 9 0 := by
  decide

private theorem x4SubRow26Coeff10_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 10 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 10 0 := by
  decide

private theorem x4SubRow26Coeff11_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 11 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 11 0 := by
  decide

private theorem x4SubRow26Coeff12_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 12 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 12 0 := by
  decide

private theorem x4SubRow26Coeff13_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 13 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 13 0 := by
  decide

private theorem x4SubRow26Coeff14_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 14 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 14 0 := by
  decide

private theorem x4SubRow26Coeff15_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 15 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 15 0 := by
  decide

private theorem x4SubRow26Coeff16_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 16 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 16 0 := by
  decide

private theorem x4SubRow26Coeff17_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 17 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 17 0 := by
  decide

private theorem x4SubRow26Coeff18_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 18 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 18 0 := by
  decide

private theorem x4SubRow26Coeff19_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 19 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 19 0 := by
  decide

private theorem x4SubRow26Coeff20_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 20 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 20 0 := by
  decide

private theorem x4SubRow26Coeff21_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 21 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 21 0 := by
  decide

private theorem x4SubRow26Coeff22_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 22 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 22 0 := by
  decide

private theorem x4SubRow26Coeff23_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 23 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 23 0 := by
  decide

private theorem x4SubRow26Coeff24_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 24 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 24 0 := by
  decide

private theorem x4SubRow26Coeff25_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 25 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 25 0 := by
  decide

private theorem x4SubRow26Coeff26_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 26 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 26 0 := by
  decide

private theorem x4SubRow26Coeff27_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 27 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 27 0 := by
  decide

private theorem x4SubRow26Coeff28_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 28 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 28 0 := by
  decide

private theorem x4SubRow26Coeff29_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 29 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 29 0 := by
  decide

private theorem x4SubRow26Coeff30_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 30 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 30 0 := by
  decide

private theorem x4SubRow26Coeff31_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 31 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 31 0 := by
  decide

private theorem x4SubRow26Coeff32_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 32 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 32 0 := by
  decide

private theorem x4SubRow26Coeff33_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 33 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 33 0 := by
  decide

private theorem x4SubRow26Coeff34_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 34 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 34 0 := by
  decide

private theorem x4SubRow26Coeff35_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 35 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 35 0 := by
  decide

private theorem x4SubRow26Coeff36_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 36 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 36 0 := by
  decide

private theorem x4SubRow26Coeff37_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 37 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 37 0 := by
  decide

private theorem x4SubRow26Coeff38_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 38 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 38 0 := by
  decide

private theorem x4SubRow26Coeff39_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 39 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 39 0 := by
  decide

private theorem x4SubRow26Coeff40_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 40 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 40 0 := by
  decide

private theorem x4SubRow26Coeff41_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 41 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 41 0 := by
  decide

private theorem x4SubRow26Coeff42_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 42 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 42 0 := by
  decide

private theorem x4SubRow26Coeff43_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 43 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 43 0 := by
  decide

private theorem x4SubRow26Coeff44_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 44 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 44 0 := by
  decide

private theorem x4SubRow26Coeff45_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 45 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 45 0 := by
  decide

private theorem x4SubRow26Coeff46_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 46 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 46 0 := by
  decide

private theorem x4SubRow26Coeff47_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 47 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 47 0 := by
  decide

private theorem x4SubRow26Coeff48_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 48 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 48 0 := by
  decide

private theorem x4SubRow26Coeff49_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 49 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 49 0 := by
  decide

private theorem x4SubRow26Coeff50_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 50 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 50 0 := by
  decide

private theorem x4SubRow26Coeff51_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 51 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 51 0 := by
  decide

private theorem x4SubRow26Coeff52_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 52 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 52 0 := by
  decide

private theorem x4SubRow26Coeff53_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 53 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 53 0 := by
  decide

private theorem x4SubRow26Coeff54_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 54 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 54 0 := by
  decide

private theorem x4SubRow26Coeff55_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 55 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 55 0 := by
  decide

private theorem x4SubRow26Coeff56_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 56 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 56 0 := by
  decide

private theorem x4SubRow26Coeff57_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 57 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 57 0 := by
  decide

private theorem x4SubRow26Coeff58_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 58 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 58 0 := by
  decide

private theorem x4SubRow26Coeff59_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 59 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 59 0 := by
  decide

private theorem x4SubRow26Coeff60_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 60 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 60 0 := by
  decide

private theorem x4SubRow26Coeff61_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 61 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 61 0 := by
  decide

private theorem x4SubRow26Coeff62_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 62 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 62 0 := by
  decide

private theorem x4SubRow26Coeff63_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 63 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 63 0 := by
  decide

private theorem x4SubRow26Coeff64_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 64 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 64 0 := by
  decide

private theorem x4SubRow26Coeff65_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 65 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 65 0 := by
  decide

private theorem x4SubRow26Coeff66_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 66 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 66 0 := by
  decide

private theorem x4SubRow26Coeff67_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 67 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 67 0 := by
  decide

private theorem x4SubRow26Coeff68_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 68 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 68 0 := by
  decide

private theorem x4SubRow26Coeff69_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 69 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 69 0 := by
  decide

private theorem x4SubRow26Coeff70_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 70 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 70 0 := by
  decide

private theorem x4SubRow26Coeff71_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 71 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 71 0 := by
  decide

private theorem x4SubRow26Coeff72_spec :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 72 =
      ((rectangularize 53 73 X4Data).getD 26 []).getD 72 0 := by
  decide

private theorem x4SubRow26Coeffs0To9_spec
    (j : ℕ) (hHi : j < 10) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 j =
      ((rectangularize 53 73 X4Data).getD 26 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow26Coeff0_spec
  · exact x4SubRow26Coeff1_spec
  · exact x4SubRow26Coeff2_spec
  · exact x4SubRow26Coeff3_spec
  · exact x4SubRow26Coeff4_spec
  · exact x4SubRow26Coeff5_spec
  · exact x4SubRow26Coeff6_spec
  · exact x4SubRow26Coeff7_spec
  · exact x4SubRow26Coeff8_spec
  · exact x4SubRow26Coeff9_spec

private theorem x4SubRow26Coeffs10To19_spec
    (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 j =
      ((rectangularize 53 73 X4Data).getD 26 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow26Coeff10_spec
  · exact x4SubRow26Coeff11_spec
  · exact x4SubRow26Coeff12_spec
  · exact x4SubRow26Coeff13_spec
  · exact x4SubRow26Coeff14_spec
  · exact x4SubRow26Coeff15_spec
  · exact x4SubRow26Coeff16_spec
  · exact x4SubRow26Coeff17_spec
  · exact x4SubRow26Coeff18_spec
  · exact x4SubRow26Coeff19_spec

private theorem x4SubRow26Coeffs20To29_spec
    (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 j =
      ((rectangularize 53 73 X4Data).getD 26 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow26Coeff20_spec
  · exact x4SubRow26Coeff21_spec
  · exact x4SubRow26Coeff22_spec
  · exact x4SubRow26Coeff23_spec
  · exact x4SubRow26Coeff24_spec
  · exact x4SubRow26Coeff25_spec
  · exact x4SubRow26Coeff26_spec
  · exact x4SubRow26Coeff27_spec
  · exact x4SubRow26Coeff28_spec
  · exact x4SubRow26Coeff29_spec

private theorem x4SubRow26Coeffs30To39_spec
    (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 j =
      ((rectangularize 53 73 X4Data).getD 26 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow26Coeff30_spec
  · exact x4SubRow26Coeff31_spec
  · exact x4SubRow26Coeff32_spec
  · exact x4SubRow26Coeff33_spec
  · exact x4SubRow26Coeff34_spec
  · exact x4SubRow26Coeff35_spec
  · exact x4SubRow26Coeff36_spec
  · exact x4SubRow26Coeff37_spec
  · exact x4SubRow26Coeff38_spec
  · exact x4SubRow26Coeff39_spec

private theorem x4SubRow26Coeffs40To49_spec
    (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 j =
      ((rectangularize 53 73 X4Data).getD 26 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow26Coeff40_spec
  · exact x4SubRow26Coeff41_spec
  · exact x4SubRow26Coeff42_spec
  · exact x4SubRow26Coeff43_spec
  · exact x4SubRow26Coeff44_spec
  · exact x4SubRow26Coeff45_spec
  · exact x4SubRow26Coeff46_spec
  · exact x4SubRow26Coeff47_spec
  · exact x4SubRow26Coeff48_spec
  · exact x4SubRow26Coeff49_spec

private theorem x4SubRow26Coeffs50To59_spec
    (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 j =
      ((rectangularize 53 73 X4Data).getD 26 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow26Coeff50_spec
  · exact x4SubRow26Coeff51_spec
  · exact x4SubRow26Coeff52_spec
  · exact x4SubRow26Coeff53_spec
  · exact x4SubRow26Coeff54_spec
  · exact x4SubRow26Coeff55_spec
  · exact x4SubRow26Coeff56_spec
  · exact x4SubRow26Coeff57_spec
  · exact x4SubRow26Coeff58_spec
  · exact x4SubRow26Coeff59_spec

private theorem x4SubRow26Coeffs60To69_spec
    (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 j =
      ((rectangularize 53 73 X4Data).getD 26 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4SubRow26Coeff60_spec
  · exact x4SubRow26Coeff61_spec
  · exact x4SubRow26Coeff62_spec
  · exact x4SubRow26Coeff63_spec
  · exact x4SubRow26Coeff64_spec
  · exact x4SubRow26Coeff65_spec
  · exact x4SubRow26Coeff66_spec
  · exact x4SubRow26Coeff67_spec
  · exact x4SubRow26Coeff68_spec
  · exact x4SubRow26Coeff69_spec

private theorem x4SubRow26Coeffs70To72_spec
    (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 73) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 j =
      ((rectangularize 53 73 X4Data).getD 26 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 := by
    omega
  rcases hCases with
    rfl | rfl | rfl
  · exact x4SubRow26Coeff70_spec
  · exact x4SubRow26Coeff71_spec
  · exact x4SubRow26Coeff72_spec

private theorem x4SubRow26_coefficients (j : ℕ) (hj : j < 73) :
    addMulCoeffTwo X4NLK3Data NegData X4NRGData 26 j =
      ((rectangularize 53 73 X4Data).getD 26 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact x4SubRow26Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact x4SubRow26Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact x4SubRow26Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact x4SubRow26Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact x4SubRow26Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact x4SubRow26Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact x4SubRow26Coeffs60To69_spec j (by omega) h70
  exact x4SubRow26Coeffs70To72_spec j (by omega) hj

private theorem x4SubRow26Padded_spec :
    padOne 73
        (addMulRow X4NLK3Data NegData X4NRGData 26) =
      (rectangularize 53 73 X4Data).getD 26 [] := by
  apply padOne_addMulRow_eq_of_coefficients 73
    X4NLK3Data NegData X4NRGData 26
    ((rectangularize 53 73 X4Data).getD 26 [])
  · decide
  · have hTargetSupport : (X4Data.getD 26 []).length ≤ 73 := by
      decide
    rw [getD_rectangularize 53 73 X4Data 26 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact x4SubRow26_coefficients

private theorem x4SubRow26_spec :
    (rectangularize 53 73
        (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 26 [] =
      (rectangularize 53 73 X4Data).getD 26 [] := by
  rw [getD_rectangularize 53 73
    (Two.add X4NLK3Data (Two.mul NegData X4NRGData)) 26 (by omega),
    ← addMulRow_eq_getD]
  exact x4SubRow26Padded_spec

private theorem x4SubRow27_spec :
    (rectangularize 53 73 (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 27 [] =
      (rectangularize 53 73 X4Data).getD 27 [] := by
  decide

private theorem x4SubRow28_spec :
    (rectangularize 53 73 (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 28 [] =
      (rectangularize 53 73 X4Data).getD 28 [] := by
  decide

private theorem x4SubRow29_spec :
    (rectangularize 53 73 (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 29 [] =
      (rectangularize 53 73 X4Data).getD 29 [] := by
  decide

private theorem x4SubRow30_spec :
    (rectangularize 53 73 (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 30 [] =
      (rectangularize 53 73 X4Data).getD 30 [] := by
  decide

private theorem x4SubRow31_spec :
    (rectangularize 53 73 (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 31 [] =
      (rectangularize 53 73 X4Data).getD 31 [] := by
  decide

private theorem x4SubRow32_spec :
    (rectangularize 53 73 (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 32 [] =
      (rectangularize 53 73 X4Data).getD 32 [] := by
  decide

private theorem x4SubRow33_spec :
    (rectangularize 53 73 (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 33 [] =
      (rectangularize 53 73 X4Data).getD 33 [] := by
  decide

private theorem x4SubRow34_spec :
    (rectangularize 53 73 (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 34 [] =
      (rectangularize 53 73 X4Data).getD 34 [] := by
  decide

private theorem x4SubRow35_spec :
    (rectangularize 53 73 (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 35 [] =
      (rectangularize 53 73 X4Data).getD 35 [] := by
  decide

private theorem x4SubRow36_spec :
    (rectangularize 53 73 (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 36 [] =
      (rectangularize 53 73 X4Data).getD 36 [] := by
  decide

private theorem x4SubRow37_spec :
    (rectangularize 53 73 (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 37 [] =
      (rectangularize 53 73 X4Data).getD 37 [] := by
  decide

private theorem x4SubRow38_spec :
    (rectangularize 53 73 (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 38 [] =
      (rectangularize 53 73 X4Data).getD 38 [] := by
  decide

private theorem x4SubRow39_spec :
    (rectangularize 53 73 (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 39 [] =
      (rectangularize 53 73 X4Data).getD 39 [] := by
  decide

private theorem x4SubRow40_spec :
    (rectangularize 53 73 (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 40 [] =
      (rectangularize 53 73 X4Data).getD 40 [] := by
  decide

private theorem x4SubRow41_spec :
    (rectangularize 53 73 (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 41 [] =
      (rectangularize 53 73 X4Data).getD 41 [] := by
  decide

private theorem x4SubRow42_spec :
    (rectangularize 53 73 (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 42 [] =
      (rectangularize 53 73 X4Data).getD 42 [] := by
  decide

private theorem x4SubRow43_spec :
    (rectangularize 53 73 (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 43 [] =
      (rectangularize 53 73 X4Data).getD 43 [] := by
  decide

private theorem x4SubRow44_spec :
    (rectangularize 53 73 (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 44 [] =
      (rectangularize 53 73 X4Data).getD 44 [] := by
  decide

private theorem x4SubRow45_spec :
    (rectangularize 53 73 (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 45 [] =
      (rectangularize 53 73 X4Data).getD 45 [] := by
  decide

private theorem x4SubRow46_spec :
    (rectangularize 53 73 (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 46 [] =
      (rectangularize 53 73 X4Data).getD 46 [] := by
  decide

private theorem x4SubRow47_spec :
    (rectangularize 53 73 (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 47 [] =
      (rectangularize 53 73 X4Data).getD 47 [] := by
  decide

private theorem x4SubRow48_spec :
    (rectangularize 53 73 (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 48 [] =
      (rectangularize 53 73 X4Data).getD 48 [] := by
  decide

private theorem x4SubRow49_spec :
    (rectangularize 53 73 (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 49 [] =
      (rectangularize 53 73 X4Data).getD 49 [] := by
  decide

private theorem x4SubRow50_spec :
    (rectangularize 53 73 (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 50 [] =
      (rectangularize 53 73 X4Data).getD 50 [] := by
  decide

private theorem x4SubRow51_spec :
    (rectangularize 53 73 (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 51 [] =
      (rectangularize 53 73 X4Data).getD 51 [] := by
  decide

private theorem x4SubRow52_spec :
    (rectangularize 53 73 (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD 52 [] =
      (rectangularize 53 73 X4Data).getD 52 [] := by
  decide

private theorem x4SubRows_spec (n : ℕ) (hn : n < 53) :
    (rectangularize 53 73 (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).getD n [] =
      (rectangularize 53 73 X4Data).getD n [] := by
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
    n = 50 ∨ n = 51 ∨ n = 52 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · exact x4SubRow0_spec
  · exact x4SubRow1_spec
  · exact x4SubRow2_spec
  · exact x4SubRow3_spec
  · exact x4SubRow4_spec
  · exact x4SubRow5_spec
  · exact x4SubRow6_spec
  · exact x4SubRow7_spec
  · exact x4SubRow8_spec
  · exact x4SubRow9_spec
  · exact x4SubRow10_spec
  · exact x4SubRow11_spec
  · exact x4SubRow12_spec
  · exact x4SubRow13_spec
  · exact x4SubRow14_spec
  · exact x4SubRow15_spec
  · exact x4SubRow16_spec
  · exact x4SubRow17_spec
  · exact x4SubRow18_spec
  · exact x4SubRow19_spec
  · exact x4SubRow20_spec
  · exact x4SubRow21_spec
  · exact x4SubRow22_spec
  · exact x4SubRow23_spec
  · exact x4SubRow24_spec
  · exact x4SubRow25_spec
  · exact x4SubRow26_spec
  · exact x4SubRow27_spec
  · exact x4SubRow28_spec
  · exact x4SubRow29_spec
  · exact x4SubRow30_spec
  · exact x4SubRow31_spec
  · exact x4SubRow32_spec
  · exact x4SubRow33_spec
  · exact x4SubRow34_spec
  · exact x4SubRow35_spec
  · exact x4SubRow36_spec
  · exact x4SubRow37_spec
  · exact x4SubRow38_spec
  · exact x4SubRow39_spec
  · exact x4SubRow40_spec
  · exact x4SubRow41_spec
  · exact x4SubRow42_spec
  · exact x4SubRow43_spec
  · exact x4SubRow44_spec
  · exact x4SubRow45_spec
  · exact x4SubRow46_spec
  · exact x4SubRow47_spec
  · exact x4SubRow48_spec
  · exact x4SubRow49_spec
  · exact x4SubRow50_spec
  · exact x4SubRow51_spec
  · exact x4SubRow52_spec

private theorem x4SubLeft_length :
    (rectangularize 53 73 (Two.add X4NLK3Data (Two.mul NegData X4NRGData))).length = 53 := by
  decide

private theorem x4SubRight_length :
    (rectangularize 53 73 X4Data).length = 53 := by
  decide

-- Exact bidegree bound (52, 72); no row or column is discarded.
theorem x4SubData_spec :
    rectangularize 53 73 (Two.add X4NLK3Data (Two.mul NegData X4NRGData)) =
      rectangularize 53 73 X4Data := by
  apply List.ext_getElem (x4SubLeft_length.trans x4SubRight_length.symm)
  intro n hn _
  rw [List.getElem_eq_getD [], List.getElem_eq_getD []]
  rw [x4SubLeft_length] at hn
  exact x4SubRows_spec n hn

/-- Evaluation of the checked fourth-power table through the canonical `N`. -/
theorem eval_x4Data (r s : ℚ) :
    Two.eval X4Data r s =
      Two.eval XData r s * Two.eval X2Data r s *
        (r * OrderTwentyFiveRelationZeroCertificate.Internal.K r s ^ 3 *
          OrderTwentyFiveRelationZeroCertificate.Internal.M r s *
          OrderTwentyFiveRawOrbitFactorCertificate.N r s) := by
  have hSub := congrArg (fun p => Two.eval p r s) x4SubData_spec
  simp only [eval_rectangularize, Two.eval_add, Two.eval_mul] at hSub
  calc
    Two.eval X4Data r s =
        Two.eval X4NLK3Data r s +
          Two.eval NegData r s * Two.eval X4NRGData r s := hSub.symm
    _ = OrderTwentyFiveRawOrbitFactorCertificate.N r s *
        Two.eval X4MData r s := by
      rw [eval_x4NLeftData, eval_x4NRightData, eval_NegData,
        eval_KData, eval_AData, eval_RData, eval_SData, eval_CData]
      rw [← OrderTwentyFiveRelationZeroCertificate.Internal.N_eq_factor]
      simp only [OrderTwentyFiveRelationZeroCertificate.Internal.N,
        OrderTwentyFiveRelationZeroCertificate.Internal.A,
        OrderTwentyFiveRelationZeroCertificate.Internal.C,
        OrderTwentyFiveRelationZeroCertificate.Internal.K,
        OrderTwentyFiveRawOrbitFactorCertificate.G]
      ring
    _ = Two.eval XData r s * Two.eval X2Data r s *
        (r * OrderTwentyFiveRelationZeroCertificate.Internal.K r s ^ 3 *
          OrderTwentyFiveRelationZeroCertificate.Internal.M r s *
          OrderTwentyFiveRawOrbitFactorCertificate.N r s) := by
      rw [eval_x4MData, eval_MData, eval_KData, eval_RData, eval_x3Data]
      ring

end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
