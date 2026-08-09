/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialXFourCoreCertificate
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialXFourNLeftData
import MazurTorsion.Kubert.OrderTwentyFiveDensePolynomialRowCertificate

/-!
# Checked left branch of the canonical N factor

Every stated rectangle is an exact bidegree bound, and `rectangularize` only
appends zeros.  The row-sharded equalities therefore check all coefficients
and all possible tails.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveRelationZeroCertificate.Dense
open OrderTwentyFiveDensePolynomialRectangular
open OrderTwentyFiveDensePolynomialRowCertificate

private theorem x4NLRRow0_spec :
    padOne 66 (mulRow RData X4MData 0) =
      (rectangularize 49 66 X4NLRData).getD 0 [] := by
  decide

private theorem x4NLRRow1_spec :
    padOne 66 (mulRow RData X4MData 1) =
      (rectangularize 49 66 X4NLRData).getD 1 [] := by
  decide

private theorem x4NLRRow2_spec :
    padOne 66 (mulRow RData X4MData 2) =
      (rectangularize 49 66 X4NLRData).getD 2 [] := by
  decide

private theorem x4NLRRow3_spec :
    padOne 66 (mulRow RData X4MData 3) =
      (rectangularize 49 66 X4NLRData).getD 3 [] := by
  decide

private theorem x4NLRRow4_spec :
    padOne 66 (mulRow RData X4MData 4) =
      (rectangularize 49 66 X4NLRData).getD 4 [] := by
  decide

private theorem x4NLRRow5_spec :
    padOne 66 (mulRow RData X4MData 5) =
      (rectangularize 49 66 X4NLRData).getD 5 [] := by
  decide

private theorem x4NLRRow6_spec :
    padOne 66 (mulRow RData X4MData 6) =
      (rectangularize 49 66 X4NLRData).getD 6 [] := by
  decide

private theorem x4NLRRow7_spec :
    padOne 66 (mulRow RData X4MData 7) =
      (rectangularize 49 66 X4NLRData).getD 7 [] := by
  decide

private theorem x4NLRRow8_spec :
    padOne 66 (mulRow RData X4MData 8) =
      (rectangularize 49 66 X4NLRData).getD 8 [] := by
  decide

private theorem x4NLRRow9_spec :
    padOne 66 (mulRow RData X4MData 9) =
      (rectangularize 49 66 X4NLRData).getD 9 [] := by
  decide

private theorem x4NLRRow10_spec :
    padOne 66 (mulRow RData X4MData 10) =
      (rectangularize 49 66 X4NLRData).getD 10 [] := by
  decide

private theorem x4NLRRow11_spec :
    padOne 66 (mulRow RData X4MData 11) =
      (rectangularize 49 66 X4NLRData).getD 11 [] := by
  decide

private theorem x4NLRRow12_spec :
    padOne 66 (mulRow RData X4MData 12) =
      (rectangularize 49 66 X4NLRData).getD 12 [] := by
  decide

private theorem x4NLRRow13_spec :
    padOne 66 (mulRow RData X4MData 13) =
      (rectangularize 49 66 X4NLRData).getD 13 [] := by
  decide

private theorem x4NLRRow14_spec :
    padOne 66 (mulRow RData X4MData 14) =
      (rectangularize 49 66 X4NLRData).getD 14 [] := by
  decide

private theorem x4NLRRow15_spec :
    padOne 66 (mulRow RData X4MData 15) =
      (rectangularize 49 66 X4NLRData).getD 15 [] := by
  decide

private theorem x4NLRRow16_spec :
    padOne 66 (mulRow RData X4MData 16) =
      (rectangularize 49 66 X4NLRData).getD 16 [] := by
  decide

private theorem x4NLRRow17_spec :
    padOne 66 (mulRow RData X4MData 17) =
      (rectangularize 49 66 X4NLRData).getD 17 [] := by
  decide

private theorem x4NLRRow18_spec :
    padOne 66 (mulRow RData X4MData 18) =
      (rectangularize 49 66 X4NLRData).getD 18 [] := by
  decide

private theorem x4NLRRow19_spec :
    padOne 66 (mulRow RData X4MData 19) =
      (rectangularize 49 66 X4NLRData).getD 19 [] := by
  decide

private theorem x4NLRRow20_spec :
    padOne 66 (mulRow RData X4MData 20) =
      (rectangularize 49 66 X4NLRData).getD 20 [] := by
  decide

private theorem x4NLRRow21_spec :
    padOne 66 (mulRow RData X4MData 21) =
      (rectangularize 49 66 X4NLRData).getD 21 [] := by
  decide

private theorem x4NLRRow22_spec :
    padOne 66 (mulRow RData X4MData 22) =
      (rectangularize 49 66 X4NLRData).getD 22 [] := by
  decide

private theorem x4NLRRow23_spec :
    padOne 66 (mulRow RData X4MData 23) =
      (rectangularize 49 66 X4NLRData).getD 23 [] := by
  decide

private theorem x4NLRRow24_spec :
    padOne 66 (mulRow RData X4MData 24) =
      (rectangularize 49 66 X4NLRData).getD 24 [] := by
  decide

private theorem x4NLRRow25_spec :
    padOne 66 (mulRow RData X4MData 25) =
      (rectangularize 49 66 X4NLRData).getD 25 [] := by
  decide

private theorem x4NLRRow26_spec :
    padOne 66 (mulRow RData X4MData 26) =
      (rectangularize 49 66 X4NLRData).getD 26 [] := by
  decide

private theorem x4NLRRow27_spec :
    padOne 66 (mulRow RData X4MData 27) =
      (rectangularize 49 66 X4NLRData).getD 27 [] := by
  decide

private theorem x4NLRRow28_spec :
    padOne 66 (mulRow RData X4MData 28) =
      (rectangularize 49 66 X4NLRData).getD 28 [] := by
  decide

private theorem x4NLRRow29_spec :
    padOne 66 (mulRow RData X4MData 29) =
      (rectangularize 49 66 X4NLRData).getD 29 [] := by
  decide

private theorem x4NLRRow30_spec :
    padOne 66 (mulRow RData X4MData 30) =
      (rectangularize 49 66 X4NLRData).getD 30 [] := by
  decide

private theorem x4NLRRow31_spec :
    padOne 66 (mulRow RData X4MData 31) =
      (rectangularize 49 66 X4NLRData).getD 31 [] := by
  decide

private theorem x4NLRRow32_spec :
    padOne 66 (mulRow RData X4MData 32) =
      (rectangularize 49 66 X4NLRData).getD 32 [] := by
  decide

private theorem x4NLRRow33_spec :
    padOne 66 (mulRow RData X4MData 33) =
      (rectangularize 49 66 X4NLRData).getD 33 [] := by
  decide

private theorem x4NLRRow34_spec :
    padOne 66 (mulRow RData X4MData 34) =
      (rectangularize 49 66 X4NLRData).getD 34 [] := by
  decide

private theorem x4NLRRow35_spec :
    padOne 66 (mulRow RData X4MData 35) =
      (rectangularize 49 66 X4NLRData).getD 35 [] := by
  decide

private theorem x4NLRRow36_spec :
    padOne 66 (mulRow RData X4MData 36) =
      (rectangularize 49 66 X4NLRData).getD 36 [] := by
  decide

private theorem x4NLRRow37_spec :
    padOne 66 (mulRow RData X4MData 37) =
      (rectangularize 49 66 X4NLRData).getD 37 [] := by
  decide

private theorem x4NLRRow38_spec :
    padOne 66 (mulRow RData X4MData 38) =
      (rectangularize 49 66 X4NLRData).getD 38 [] := by
  decide

private theorem x4NLRRow39_spec :
    padOne 66 (mulRow RData X4MData 39) =
      (rectangularize 49 66 X4NLRData).getD 39 [] := by
  decide

private theorem x4NLRRow40_spec :
    padOne 66 (mulRow RData X4MData 40) =
      (rectangularize 49 66 X4NLRData).getD 40 [] := by
  decide

private theorem x4NLRRow41_spec :
    padOne 66 (mulRow RData X4MData 41) =
      (rectangularize 49 66 X4NLRData).getD 41 [] := by
  decide

private theorem x4NLRRow42_spec :
    padOne 66 (mulRow RData X4MData 42) =
      (rectangularize 49 66 X4NLRData).getD 42 [] := by
  decide

private theorem x4NLRRow43_spec :
    padOne 66 (mulRow RData X4MData 43) =
      (rectangularize 49 66 X4NLRData).getD 43 [] := by
  decide

private theorem x4NLRRow44_spec :
    padOne 66 (mulRow RData X4MData 44) =
      (rectangularize 49 66 X4NLRData).getD 44 [] := by
  decide

private theorem x4NLRRow45_spec :
    padOne 66 (mulRow RData X4MData 45) =
      (rectangularize 49 66 X4NLRData).getD 45 [] := by
  decide

private theorem x4NLRRow46_spec :
    padOne 66 (mulRow RData X4MData 46) =
      (rectangularize 49 66 X4NLRData).getD 46 [] := by
  decide

private theorem x4NLRRow47_spec :
    padOne 66 (mulRow RData X4MData 47) =
      (rectangularize 49 66 X4NLRData).getD 47 [] := by
  decide

private theorem x4NLRRow48_spec :
    padOne 66 (mulRow RData X4MData 48) =
      (rectangularize 49 66 X4NLRData).getD 48 [] := by
  decide

private theorem x4NLRRows_spec (n : ℕ) (hn : n < 49) :
    padOne 66 (mulRow RData X4MData n) =
      (rectangularize 49 66 X4NLRData).getD n [] := by
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
  · exact x4NLRRow0_spec
  · exact x4NLRRow1_spec
  · exact x4NLRRow2_spec
  · exact x4NLRRow3_spec
  · exact x4NLRRow4_spec
  · exact x4NLRRow5_spec
  · exact x4NLRRow6_spec
  · exact x4NLRRow7_spec
  · exact x4NLRRow8_spec
  · exact x4NLRRow9_spec
  · exact x4NLRRow10_spec
  · exact x4NLRRow11_spec
  · exact x4NLRRow12_spec
  · exact x4NLRRow13_spec
  · exact x4NLRRow14_spec
  · exact x4NLRRow15_spec
  · exact x4NLRRow16_spec
  · exact x4NLRRow17_spec
  · exact x4NLRRow18_spec
  · exact x4NLRRow19_spec
  · exact x4NLRRow20_spec
  · exact x4NLRRow21_spec
  · exact x4NLRRow22_spec
  · exact x4NLRRow23_spec
  · exact x4NLRRow24_spec
  · exact x4NLRRow25_spec
  · exact x4NLRRow26_spec
  · exact x4NLRRow27_spec
  · exact x4NLRRow28_spec
  · exact x4NLRRow29_spec
  · exact x4NLRRow30_spec
  · exact x4NLRRow31_spec
  · exact x4NLRRow32_spec
  · exact x4NLRRow33_spec
  · exact x4NLRRow34_spec
  · exact x4NLRRow35_spec
  · exact x4NLRRow36_spec
  · exact x4NLRRow37_spec
  · exact x4NLRRow38_spec
  · exact x4NLRRow39_spec
  · exact x4NLRRow40_spec
  · exact x4NLRRow41_spec
  · exact x4NLRRow42_spec
  · exact x4NLRRow43_spec
  · exact x4NLRRow44_spec
  · exact x4NLRRow45_spec
  · exact x4NLRRow46_spec
  · exact x4NLRRow47_spec
  · exact x4NLRRow48_spec

private theorem x4NLRLeft_length :
    (rectangularize 49 66 (Two.mul RData X4MData)).length = 49 := by
  decide

private theorem x4NLRRight_length :
    (rectangularize 49 66 X4NLRData).length = 49 := by
  decide

-- Exact bidegree bound (48, 65); no row or column is discarded.
theorem x4NLRData_spec :
    rectangularize 49 66 (Two.mul RData X4MData) =
      rectangularize 49 66 X4NLRData := by
  apply List.ext_getElem (x4NLRLeft_length.trans x4NLRRight_length.symm)
  intro n hn _
  rw [List.getElem_eq_getD [], List.getElem_eq_getD []]
  rw [x4NLRLeft_length] at hn
  rw [getD_rectangularize 49 66 (Two.mul RData X4MData) n hn,
    ← mulRow_eq_getD]
  exact x4NLRRows_spec n hn

private theorem x4NLARow0_spec :
    padOne 67 (mulRow AData X4NLRData 0) =
      (rectangularize 50 67 X4NLAData).getD 0 [] := by
  decide

private theorem x4NLARow1_spec :
    padOne 67 (mulRow AData X4NLRData 1) =
      (rectangularize 50 67 X4NLAData).getD 1 [] := by
  decide

private theorem x4NLARow2_spec :
    padOne 67 (mulRow AData X4NLRData 2) =
      (rectangularize 50 67 X4NLAData).getD 2 [] := by
  decide

private theorem x4NLARow3_spec :
    padOne 67 (mulRow AData X4NLRData 3) =
      (rectangularize 50 67 X4NLAData).getD 3 [] := by
  decide

private theorem x4NLARow4_spec :
    padOne 67 (mulRow AData X4NLRData 4) =
      (rectangularize 50 67 X4NLAData).getD 4 [] := by
  decide

private theorem x4NLARow5_spec :
    padOne 67 (mulRow AData X4NLRData 5) =
      (rectangularize 50 67 X4NLAData).getD 5 [] := by
  decide

private theorem x4NLARow6_spec :
    padOne 67 (mulRow AData X4NLRData 6) =
      (rectangularize 50 67 X4NLAData).getD 6 [] := by
  decide

private theorem x4NLARow7_spec :
    padOne 67 (mulRow AData X4NLRData 7) =
      (rectangularize 50 67 X4NLAData).getD 7 [] := by
  decide

private theorem x4NLARow8_spec :
    padOne 67 (mulRow AData X4NLRData 8) =
      (rectangularize 50 67 X4NLAData).getD 8 [] := by
  decide

private theorem x4NLARow9_spec :
    padOne 67 (mulRow AData X4NLRData 9) =
      (rectangularize 50 67 X4NLAData).getD 9 [] := by
  decide

private theorem x4NLARow10_spec :
    padOne 67 (mulRow AData X4NLRData 10) =
      (rectangularize 50 67 X4NLAData).getD 10 [] := by
  decide

private theorem x4NLARow11_spec :
    padOne 67 (mulRow AData X4NLRData 11) =
      (rectangularize 50 67 X4NLAData).getD 11 [] := by
  decide

private theorem x4NLARow12_spec :
    padOne 67 (mulRow AData X4NLRData 12) =
      (rectangularize 50 67 X4NLAData).getD 12 [] := by
  decide

private theorem x4NLARow13_spec :
    padOne 67 (mulRow AData X4NLRData 13) =
      (rectangularize 50 67 X4NLAData).getD 13 [] := by
  decide

private theorem x4NLARow14_spec :
    padOne 67 (mulRow AData X4NLRData 14) =
      (rectangularize 50 67 X4NLAData).getD 14 [] := by
  decide

private theorem x4NLARow15_spec :
    padOne 67 (mulRow AData X4NLRData 15) =
      (rectangularize 50 67 X4NLAData).getD 15 [] := by
  decide

private theorem x4NLARow16_spec :
    padOne 67 (mulRow AData X4NLRData 16) =
      (rectangularize 50 67 X4NLAData).getD 16 [] := by
  decide

private theorem x4NLARow17_spec :
    padOne 67 (mulRow AData X4NLRData 17) =
      (rectangularize 50 67 X4NLAData).getD 17 [] := by
  decide

private theorem x4NLARow18_spec :
    padOne 67 (mulRow AData X4NLRData 18) =
      (rectangularize 50 67 X4NLAData).getD 18 [] := by
  decide

private theorem x4NLARow19_spec :
    padOne 67 (mulRow AData X4NLRData 19) =
      (rectangularize 50 67 X4NLAData).getD 19 [] := by
  decide

private theorem x4NLARow20_spec :
    padOne 67 (mulRow AData X4NLRData 20) =
      (rectangularize 50 67 X4NLAData).getD 20 [] := by
  decide

private theorem x4NLARow21_spec :
    padOne 67 (mulRow AData X4NLRData 21) =
      (rectangularize 50 67 X4NLAData).getD 21 [] := by
  decide

private theorem x4NLARow22_spec :
    padOne 67 (mulRow AData X4NLRData 22) =
      (rectangularize 50 67 X4NLAData).getD 22 [] := by
  decide

private theorem x4NLARow23_spec :
    padOne 67 (mulRow AData X4NLRData 23) =
      (rectangularize 50 67 X4NLAData).getD 23 [] := by
  decide

private theorem x4NLARow24_spec :
    padOne 67 (mulRow AData X4NLRData 24) =
      (rectangularize 50 67 X4NLAData).getD 24 [] := by
  decide

private theorem x4NLARow25_spec :
    padOne 67 (mulRow AData X4NLRData 25) =
      (rectangularize 50 67 X4NLAData).getD 25 [] := by
  decide

private theorem x4NLARow26_spec :
    padOne 67 (mulRow AData X4NLRData 26) =
      (rectangularize 50 67 X4NLAData).getD 26 [] := by
  decide

private theorem x4NLARow27_spec :
    padOne 67 (mulRow AData X4NLRData 27) =
      (rectangularize 50 67 X4NLAData).getD 27 [] := by
  decide

private theorem x4NLARow28_spec :
    padOne 67 (mulRow AData X4NLRData 28) =
      (rectangularize 50 67 X4NLAData).getD 28 [] := by
  decide

private theorem x4NLARow29_spec :
    padOne 67 (mulRow AData X4NLRData 29) =
      (rectangularize 50 67 X4NLAData).getD 29 [] := by
  decide

private theorem x4NLARow30_spec :
    padOne 67 (mulRow AData X4NLRData 30) =
      (rectangularize 50 67 X4NLAData).getD 30 [] := by
  decide

private theorem x4NLARow31_spec :
    padOne 67 (mulRow AData X4NLRData 31) =
      (rectangularize 50 67 X4NLAData).getD 31 [] := by
  decide

private theorem x4NLARow32_spec :
    padOne 67 (mulRow AData X4NLRData 32) =
      (rectangularize 50 67 X4NLAData).getD 32 [] := by
  decide

private theorem x4NLARow33_spec :
    padOne 67 (mulRow AData X4NLRData 33) =
      (rectangularize 50 67 X4NLAData).getD 33 [] := by
  decide

private theorem x4NLARow34_spec :
    padOne 67 (mulRow AData X4NLRData 34) =
      (rectangularize 50 67 X4NLAData).getD 34 [] := by
  decide

private theorem x4NLARow35_spec :
    padOne 67 (mulRow AData X4NLRData 35) =
      (rectangularize 50 67 X4NLAData).getD 35 [] := by
  decide

private theorem x4NLARow36_spec :
    padOne 67 (mulRow AData X4NLRData 36) =
      (rectangularize 50 67 X4NLAData).getD 36 [] := by
  decide

private theorem x4NLARow37_spec :
    padOne 67 (mulRow AData X4NLRData 37) =
      (rectangularize 50 67 X4NLAData).getD 37 [] := by
  decide

private theorem x4NLARow38_spec :
    padOne 67 (mulRow AData X4NLRData 38) =
      (rectangularize 50 67 X4NLAData).getD 38 [] := by
  decide

private theorem x4NLARow39_spec :
    padOne 67 (mulRow AData X4NLRData 39) =
      (rectangularize 50 67 X4NLAData).getD 39 [] := by
  decide

private theorem x4NLARow40_spec :
    padOne 67 (mulRow AData X4NLRData 40) =
      (rectangularize 50 67 X4NLAData).getD 40 [] := by
  decide

private theorem x4NLARow41_spec :
    padOne 67 (mulRow AData X4NLRData 41) =
      (rectangularize 50 67 X4NLAData).getD 41 [] := by
  decide

private theorem x4NLARow42_spec :
    padOne 67 (mulRow AData X4NLRData 42) =
      (rectangularize 50 67 X4NLAData).getD 42 [] := by
  decide

private theorem x4NLARow43_spec :
    padOne 67 (mulRow AData X4NLRData 43) =
      (rectangularize 50 67 X4NLAData).getD 43 [] := by
  decide

private theorem x4NLARow44_spec :
    padOne 67 (mulRow AData X4NLRData 44) =
      (rectangularize 50 67 X4NLAData).getD 44 [] := by
  decide

private theorem x4NLARow45_spec :
    padOne 67 (mulRow AData X4NLRData 45) =
      (rectangularize 50 67 X4NLAData).getD 45 [] := by
  decide

private theorem x4NLARow46_spec :
    padOne 67 (mulRow AData X4NLRData 46) =
      (rectangularize 50 67 X4NLAData).getD 46 [] := by
  decide

private theorem x4NLARow47_spec :
    padOne 67 (mulRow AData X4NLRData 47) =
      (rectangularize 50 67 X4NLAData).getD 47 [] := by
  decide

private theorem x4NLARow48_spec :
    padOne 67 (mulRow AData X4NLRData 48) =
      (rectangularize 50 67 X4NLAData).getD 48 [] := by
  decide

private theorem x4NLARow49_spec :
    padOne 67 (mulRow AData X4NLRData 49) =
      (rectangularize 50 67 X4NLAData).getD 49 [] := by
  decide

private theorem x4NLARows_spec (n : ℕ) (hn : n < 50) :
    padOne 67 (mulRow AData X4NLRData n) =
      (rectangularize 50 67 X4NLAData).getD n [] := by
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
  · exact x4NLARow0_spec
  · exact x4NLARow1_spec
  · exact x4NLARow2_spec
  · exact x4NLARow3_spec
  · exact x4NLARow4_spec
  · exact x4NLARow5_spec
  · exact x4NLARow6_spec
  · exact x4NLARow7_spec
  · exact x4NLARow8_spec
  · exact x4NLARow9_spec
  · exact x4NLARow10_spec
  · exact x4NLARow11_spec
  · exact x4NLARow12_spec
  · exact x4NLARow13_spec
  · exact x4NLARow14_spec
  · exact x4NLARow15_spec
  · exact x4NLARow16_spec
  · exact x4NLARow17_spec
  · exact x4NLARow18_spec
  · exact x4NLARow19_spec
  · exact x4NLARow20_spec
  · exact x4NLARow21_spec
  · exact x4NLARow22_spec
  · exact x4NLARow23_spec
  · exact x4NLARow24_spec
  · exact x4NLARow25_spec
  · exact x4NLARow26_spec
  · exact x4NLARow27_spec
  · exact x4NLARow28_spec
  · exact x4NLARow29_spec
  · exact x4NLARow30_spec
  · exact x4NLARow31_spec
  · exact x4NLARow32_spec
  · exact x4NLARow33_spec
  · exact x4NLARow34_spec
  · exact x4NLARow35_spec
  · exact x4NLARow36_spec
  · exact x4NLARow37_spec
  · exact x4NLARow38_spec
  · exact x4NLARow39_spec
  · exact x4NLARow40_spec
  · exact x4NLARow41_spec
  · exact x4NLARow42_spec
  · exact x4NLARow43_spec
  · exact x4NLARow44_spec
  · exact x4NLARow45_spec
  · exact x4NLARow46_spec
  · exact x4NLARow47_spec
  · exact x4NLARow48_spec
  · exact x4NLARow49_spec

private theorem x4NLALeft_length :
    (rectangularize 50 67 (Two.mul AData X4NLRData)).length = 50 := by
  decide

private theorem x4NLARight_length :
    (rectangularize 50 67 X4NLAData).length = 50 := by
  decide

-- Exact bidegree bound (49, 66); no row or column is discarded.
theorem x4NLAData_spec :
    rectangularize 50 67 (Two.mul AData X4NLRData) =
      rectangularize 50 67 X4NLAData := by
  apply List.ext_getElem (x4NLALeft_length.trans x4NLARight_length.symm)
  intro n hn _
  rw [List.getElem_eq_getD [], List.getElem_eq_getD []]
  rw [x4NLALeft_length] at hn
  rw [getD_rectangularize 50 67 (Two.mul AData X4NLRData) n hn,
    ← mulRow_eq_getD]
  exact x4NLARows_spec n hn

private theorem x4NLK1Row0_spec :
    padOne 69 (mulRow KData X4NLAData 0) =
      (rectangularize 51 69 X4NLK1Data).getD 0 [] := by
  decide

private theorem x4NLK1Row1_spec :
    padOne 69 (mulRow KData X4NLAData 1) =
      (rectangularize 51 69 X4NLK1Data).getD 1 [] := by
  decide

private theorem x4NLK1Row2_spec :
    padOne 69 (mulRow KData X4NLAData 2) =
      (rectangularize 51 69 X4NLK1Data).getD 2 [] := by
  decide

private theorem x4NLK1Row3_spec :
    padOne 69 (mulRow KData X4NLAData 3) =
      (rectangularize 51 69 X4NLK1Data).getD 3 [] := by
  decide

private theorem x4NLK1Row4_spec :
    padOne 69 (mulRow KData X4NLAData 4) =
      (rectangularize 51 69 X4NLK1Data).getD 4 [] := by
  decide

private theorem x4NLK1Row5_spec :
    padOne 69 (mulRow KData X4NLAData 5) =
      (rectangularize 51 69 X4NLK1Data).getD 5 [] := by
  decide

private theorem x4NLK1Row6_spec :
    padOne 69 (mulRow KData X4NLAData 6) =
      (rectangularize 51 69 X4NLK1Data).getD 6 [] := by
  decide

private theorem x4NLK1Row7_spec :
    padOne 69 (mulRow KData X4NLAData 7) =
      (rectangularize 51 69 X4NLK1Data).getD 7 [] := by
  decide

private theorem x4NLK1Row8_spec :
    padOne 69 (mulRow KData X4NLAData 8) =
      (rectangularize 51 69 X4NLK1Data).getD 8 [] := by
  decide

private theorem x4NLK1Row9_spec :
    padOne 69 (mulRow KData X4NLAData 9) =
      (rectangularize 51 69 X4NLK1Data).getD 9 [] := by
  decide

private theorem x4NLK1Row10_spec :
    padOne 69 (mulRow KData X4NLAData 10) =
      (rectangularize 51 69 X4NLK1Data).getD 10 [] := by
  decide

private theorem x4NLK1Row11_spec :
    padOne 69 (mulRow KData X4NLAData 11) =
      (rectangularize 51 69 X4NLK1Data).getD 11 [] := by
  decide

private theorem x4NLK1Row12_spec :
    padOne 69 (mulRow KData X4NLAData 12) =
      (rectangularize 51 69 X4NLK1Data).getD 12 [] := by
  decide

private theorem x4NLK1Row13_spec :
    padOne 69 (mulRow KData X4NLAData 13) =
      (rectangularize 51 69 X4NLK1Data).getD 13 [] := by
  decide

private theorem x4NLK1Row14_spec :
    padOne 69 (mulRow KData X4NLAData 14) =
      (rectangularize 51 69 X4NLK1Data).getD 14 [] := by
  decide

private theorem x4NLK1Row15_spec :
    padOne 69 (mulRow KData X4NLAData 15) =
      (rectangularize 51 69 X4NLK1Data).getD 15 [] := by
  decide

private theorem x4NLK1Row16_spec :
    padOne 69 (mulRow KData X4NLAData 16) =
      (rectangularize 51 69 X4NLK1Data).getD 16 [] := by
  decide

private theorem x4NLK1Row17_spec :
    padOne 69 (mulRow KData X4NLAData 17) =
      (rectangularize 51 69 X4NLK1Data).getD 17 [] := by
  decide

private theorem x4NLK1Row18_spec :
    padOne 69 (mulRow KData X4NLAData 18) =
      (rectangularize 51 69 X4NLK1Data).getD 18 [] := by
  decide

private theorem x4NLK1Row19_spec :
    padOne 69 (mulRow KData X4NLAData 19) =
      (rectangularize 51 69 X4NLK1Data).getD 19 [] := by
  decide

private theorem x4NLK1Row20_spec :
    padOne 69 (mulRow KData X4NLAData 20) =
      (rectangularize 51 69 X4NLK1Data).getD 20 [] := by
  decide

private theorem x4NLK1Row21_spec :
    padOne 69 (mulRow KData X4NLAData 21) =
      (rectangularize 51 69 X4NLK1Data).getD 21 [] := by
  decide

private theorem x4NLK1Row22_spec :
    padOne 69 (mulRow KData X4NLAData 22) =
      (rectangularize 51 69 X4NLK1Data).getD 22 [] := by
  decide

private theorem x4NLK1Row23_spec :
    padOne 69 (mulRow KData X4NLAData 23) =
      (rectangularize 51 69 X4NLK1Data).getD 23 [] := by
  decide

private theorem x4NLK1Row24_spec :
    padOne 69 (mulRow KData X4NLAData 24) =
      (rectangularize 51 69 X4NLK1Data).getD 24 [] := by
  decide

private theorem x4NLK1Row25_spec :
    padOne 69 (mulRow KData X4NLAData 25) =
      (rectangularize 51 69 X4NLK1Data).getD 25 [] := by
  decide

private theorem x4NLK1Row26_spec :
    padOne 69 (mulRow KData X4NLAData 26) =
      (rectangularize 51 69 X4NLK1Data).getD 26 [] := by
  decide

private theorem x4NLK1Row27_spec :
    padOne 69 (mulRow KData X4NLAData 27) =
      (rectangularize 51 69 X4NLK1Data).getD 27 [] := by
  decide

private theorem x4NLK1Row28_spec :
    padOne 69 (mulRow KData X4NLAData 28) =
      (rectangularize 51 69 X4NLK1Data).getD 28 [] := by
  decide

private theorem x4NLK1Row29_spec :
    padOne 69 (mulRow KData X4NLAData 29) =
      (rectangularize 51 69 X4NLK1Data).getD 29 [] := by
  decide

private theorem x4NLK1Row30_spec :
    padOne 69 (mulRow KData X4NLAData 30) =
      (rectangularize 51 69 X4NLK1Data).getD 30 [] := by
  decide

private theorem x4NLK1Row31_spec :
    padOne 69 (mulRow KData X4NLAData 31) =
      (rectangularize 51 69 X4NLK1Data).getD 31 [] := by
  decide

private theorem x4NLK1Row32_spec :
    padOne 69 (mulRow KData X4NLAData 32) =
      (rectangularize 51 69 X4NLK1Data).getD 32 [] := by
  decide

private theorem x4NLK1Row33_spec :
    padOne 69 (mulRow KData X4NLAData 33) =
      (rectangularize 51 69 X4NLK1Data).getD 33 [] := by
  decide

private theorem x4NLK1Row34_spec :
    padOne 69 (mulRow KData X4NLAData 34) =
      (rectangularize 51 69 X4NLK1Data).getD 34 [] := by
  decide

private theorem x4NLK1Row35_spec :
    padOne 69 (mulRow KData X4NLAData 35) =
      (rectangularize 51 69 X4NLK1Data).getD 35 [] := by
  decide

private theorem x4NLK1Row36_spec :
    padOne 69 (mulRow KData X4NLAData 36) =
      (rectangularize 51 69 X4NLK1Data).getD 36 [] := by
  decide

private theorem x4NLK1Row37_spec :
    padOne 69 (mulRow KData X4NLAData 37) =
      (rectangularize 51 69 X4NLK1Data).getD 37 [] := by
  decide

private theorem x4NLK1Row38_spec :
    padOne 69 (mulRow KData X4NLAData 38) =
      (rectangularize 51 69 X4NLK1Data).getD 38 [] := by
  decide

private theorem x4NLK1Row39_spec :
    padOne 69 (mulRow KData X4NLAData 39) =
      (rectangularize 51 69 X4NLK1Data).getD 39 [] := by
  decide

private theorem x4NLK1Row40_spec :
    padOne 69 (mulRow KData X4NLAData 40) =
      (rectangularize 51 69 X4NLK1Data).getD 40 [] := by
  decide

private theorem x4NLK1Row41_spec :
    padOne 69 (mulRow KData X4NLAData 41) =
      (rectangularize 51 69 X4NLK1Data).getD 41 [] := by
  decide

private theorem x4NLK1Row42_spec :
    padOne 69 (mulRow KData X4NLAData 42) =
      (rectangularize 51 69 X4NLK1Data).getD 42 [] := by
  decide

private theorem x4NLK1Row43_spec :
    padOne 69 (mulRow KData X4NLAData 43) =
      (rectangularize 51 69 X4NLK1Data).getD 43 [] := by
  decide

private theorem x4NLK1Row44_spec :
    padOne 69 (mulRow KData X4NLAData 44) =
      (rectangularize 51 69 X4NLK1Data).getD 44 [] := by
  decide

private theorem x4NLK1Row45_spec :
    padOne 69 (mulRow KData X4NLAData 45) =
      (rectangularize 51 69 X4NLK1Data).getD 45 [] := by
  decide

private theorem x4NLK1Row46_spec :
    padOne 69 (mulRow KData X4NLAData 46) =
      (rectangularize 51 69 X4NLK1Data).getD 46 [] := by
  decide

private theorem x4NLK1Row47_spec :
    padOne 69 (mulRow KData X4NLAData 47) =
      (rectangularize 51 69 X4NLK1Data).getD 47 [] := by
  decide

private theorem x4NLK1Row48_spec :
    padOne 69 (mulRow KData X4NLAData 48) =
      (rectangularize 51 69 X4NLK1Data).getD 48 [] := by
  decide

private theorem x4NLK1Row49_spec :
    padOne 69 (mulRow KData X4NLAData 49) =
      (rectangularize 51 69 X4NLK1Data).getD 49 [] := by
  decide

private theorem x4NLK1Row50_spec :
    padOne 69 (mulRow KData X4NLAData 50) =
      (rectangularize 51 69 X4NLK1Data).getD 50 [] := by
  decide

private theorem x4NLK1Rows_spec (n : ℕ) (hn : n < 51) :
    padOne 69 (mulRow KData X4NLAData n) =
      (rectangularize 51 69 X4NLK1Data).getD n [] := by
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
  · exact x4NLK1Row0_spec
  · exact x4NLK1Row1_spec
  · exact x4NLK1Row2_spec
  · exact x4NLK1Row3_spec
  · exact x4NLK1Row4_spec
  · exact x4NLK1Row5_spec
  · exact x4NLK1Row6_spec
  · exact x4NLK1Row7_spec
  · exact x4NLK1Row8_spec
  · exact x4NLK1Row9_spec
  · exact x4NLK1Row10_spec
  · exact x4NLK1Row11_spec
  · exact x4NLK1Row12_spec
  · exact x4NLK1Row13_spec
  · exact x4NLK1Row14_spec
  · exact x4NLK1Row15_spec
  · exact x4NLK1Row16_spec
  · exact x4NLK1Row17_spec
  · exact x4NLK1Row18_spec
  · exact x4NLK1Row19_spec
  · exact x4NLK1Row20_spec
  · exact x4NLK1Row21_spec
  · exact x4NLK1Row22_spec
  · exact x4NLK1Row23_spec
  · exact x4NLK1Row24_spec
  · exact x4NLK1Row25_spec
  · exact x4NLK1Row26_spec
  · exact x4NLK1Row27_spec
  · exact x4NLK1Row28_spec
  · exact x4NLK1Row29_spec
  · exact x4NLK1Row30_spec
  · exact x4NLK1Row31_spec
  · exact x4NLK1Row32_spec
  · exact x4NLK1Row33_spec
  · exact x4NLK1Row34_spec
  · exact x4NLK1Row35_spec
  · exact x4NLK1Row36_spec
  · exact x4NLK1Row37_spec
  · exact x4NLK1Row38_spec
  · exact x4NLK1Row39_spec
  · exact x4NLK1Row40_spec
  · exact x4NLK1Row41_spec
  · exact x4NLK1Row42_spec
  · exact x4NLK1Row43_spec
  · exact x4NLK1Row44_spec
  · exact x4NLK1Row45_spec
  · exact x4NLK1Row46_spec
  · exact x4NLK1Row47_spec
  · exact x4NLK1Row48_spec
  · exact x4NLK1Row49_spec
  · exact x4NLK1Row50_spec

private theorem x4NLK1Left_length :
    (rectangularize 51 69 (Two.mul KData X4NLAData)).length = 51 := by
  decide

private theorem x4NLK1Right_length :
    (rectangularize 51 69 X4NLK1Data).length = 51 := by
  decide

-- Exact bidegree bound (50, 68); no row or column is discarded.
theorem x4NLK1Data_spec :
    rectangularize 51 69 (Two.mul KData X4NLAData) =
      rectangularize 51 69 X4NLK1Data := by
  apply List.ext_getElem (x4NLK1Left_length.trans x4NLK1Right_length.symm)
  intro n hn _
  rw [List.getElem_eq_getD [], List.getElem_eq_getD []]
  rw [x4NLK1Left_length] at hn
  rw [getD_rectangularize 51 69 (Two.mul KData X4NLAData) n hn,
    ← mulRow_eq_getD]
  exact x4NLK1Rows_spec n hn

private theorem x4NLK2Row0_spec :
    padOne 71 (mulRow KData X4NLK1Data 0) =
      (rectangularize 52 71 X4NLK2Data).getD 0 [] := by
  decide

private theorem x4NLK2Row1_spec :
    padOne 71 (mulRow KData X4NLK1Data 1) =
      (rectangularize 52 71 X4NLK2Data).getD 1 [] := by
  decide

private theorem x4NLK2Row2_spec :
    padOne 71 (mulRow KData X4NLK1Data 2) =
      (rectangularize 52 71 X4NLK2Data).getD 2 [] := by
  decide

private theorem x4NLK2Row3_spec :
    padOne 71 (mulRow KData X4NLK1Data 3) =
      (rectangularize 52 71 X4NLK2Data).getD 3 [] := by
  decide

private theorem x4NLK2Row4_spec :
    padOne 71 (mulRow KData X4NLK1Data 4) =
      (rectangularize 52 71 X4NLK2Data).getD 4 [] := by
  decide

private theorem x4NLK2Row5_spec :
    padOne 71 (mulRow KData X4NLK1Data 5) =
      (rectangularize 52 71 X4NLK2Data).getD 5 [] := by
  decide

private theorem x4NLK2Row6_spec :
    padOne 71 (mulRow KData X4NLK1Data 6) =
      (rectangularize 52 71 X4NLK2Data).getD 6 [] := by
  decide

private theorem x4NLK2Row7_spec :
    padOne 71 (mulRow KData X4NLK1Data 7) =
      (rectangularize 52 71 X4NLK2Data).getD 7 [] := by
  decide

private theorem x4NLK2Row8_spec :
    padOne 71 (mulRow KData X4NLK1Data 8) =
      (rectangularize 52 71 X4NLK2Data).getD 8 [] := by
  decide

private theorem x4NLK2Row9_spec :
    padOne 71 (mulRow KData X4NLK1Data 9) =
      (rectangularize 52 71 X4NLK2Data).getD 9 [] := by
  decide

private theorem x4NLK2Row10_spec :
    padOne 71 (mulRow KData X4NLK1Data 10) =
      (rectangularize 52 71 X4NLK2Data).getD 10 [] := by
  decide

private theorem x4NLK2Row11_spec :
    padOne 71 (mulRow KData X4NLK1Data 11) =
      (rectangularize 52 71 X4NLK2Data).getD 11 [] := by
  decide

private theorem x4NLK2Row12_spec :
    padOne 71 (mulRow KData X4NLK1Data 12) =
      (rectangularize 52 71 X4NLK2Data).getD 12 [] := by
  decide

private theorem x4NLK2Row13_spec :
    padOne 71 (mulRow KData X4NLK1Data 13) =
      (rectangularize 52 71 X4NLK2Data).getD 13 [] := by
  decide

private theorem x4NLK2Row14_spec :
    padOne 71 (mulRow KData X4NLK1Data 14) =
      (rectangularize 52 71 X4NLK2Data).getD 14 [] := by
  decide

private theorem x4NLK2Row15_spec :
    padOne 71 (mulRow KData X4NLK1Data 15) =
      (rectangularize 52 71 X4NLK2Data).getD 15 [] := by
  decide

private theorem x4NLK2Row16_spec :
    padOne 71 (mulRow KData X4NLK1Data 16) =
      (rectangularize 52 71 X4NLK2Data).getD 16 [] := by
  decide

private theorem x4NLK2Row17_spec :
    padOne 71 (mulRow KData X4NLK1Data 17) =
      (rectangularize 52 71 X4NLK2Data).getD 17 [] := by
  decide

private theorem x4NLK2Row18_spec :
    padOne 71 (mulRow KData X4NLK1Data 18) =
      (rectangularize 52 71 X4NLK2Data).getD 18 [] := by
  decide

private theorem x4NLK2Row19_spec :
    padOne 71 (mulRow KData X4NLK1Data 19) =
      (rectangularize 52 71 X4NLK2Data).getD 19 [] := by
  decide

private theorem x4NLK2Row20Coeff0_spec :
    mulCoeffTwo KData X4NLK1Data 20 0 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 0 0 := by
  decide

private theorem x4NLK2Row20Coeff1_spec :
    mulCoeffTwo KData X4NLK1Data 20 1 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 1 0 := by
  decide

private theorem x4NLK2Row20Coeff2_spec :
    mulCoeffTwo KData X4NLK1Data 20 2 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 2 0 := by
  decide

private theorem x4NLK2Row20Coeff3_spec :
    mulCoeffTwo KData X4NLK1Data 20 3 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 3 0 := by
  decide

private theorem x4NLK2Row20Coeff4_spec :
    mulCoeffTwo KData X4NLK1Data 20 4 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 4 0 := by
  decide

private theorem x4NLK2Row20Coeff5_spec :
    mulCoeffTwo KData X4NLK1Data 20 5 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 5 0 := by
  decide

private theorem x4NLK2Row20Coeff6_spec :
    mulCoeffTwo KData X4NLK1Data 20 6 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 6 0 := by
  decide

private theorem x4NLK2Row20Coeff7_spec :
    mulCoeffTwo KData X4NLK1Data 20 7 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 7 0 := by
  decide

private theorem x4NLK2Row20Coeff8_spec :
    mulCoeffTwo KData X4NLK1Data 20 8 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 8 0 := by
  decide

private theorem x4NLK2Row20Coeff9_spec :
    mulCoeffTwo KData X4NLK1Data 20 9 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 9 0 := by
  decide

private theorem x4NLK2Row20Coeff10_spec :
    mulCoeffTwo KData X4NLK1Data 20 10 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 10 0 := by
  decide

private theorem x4NLK2Row20Coeff11_spec :
    mulCoeffTwo KData X4NLK1Data 20 11 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 11 0 := by
  decide

private theorem x4NLK2Row20Coeff12_spec :
    mulCoeffTwo KData X4NLK1Data 20 12 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 12 0 := by
  decide

private theorem x4NLK2Row20Coeff13_spec :
    mulCoeffTwo KData X4NLK1Data 20 13 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 13 0 := by
  decide

private theorem x4NLK2Row20Coeff14_spec :
    mulCoeffTwo KData X4NLK1Data 20 14 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 14 0 := by
  decide

private theorem x4NLK2Row20Coeff15_spec :
    mulCoeffTwo KData X4NLK1Data 20 15 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 15 0 := by
  decide

private theorem x4NLK2Row20Coeff16_spec :
    mulCoeffTwo KData X4NLK1Data 20 16 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 16 0 := by
  decide

private theorem x4NLK2Row20Coeff17_spec :
    mulCoeffTwo KData X4NLK1Data 20 17 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 17 0 := by
  decide

private theorem x4NLK2Row20Coeff18_spec :
    mulCoeffTwo KData X4NLK1Data 20 18 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 18 0 := by
  decide

private theorem x4NLK2Row20Coeff19_spec :
    mulCoeffTwo KData X4NLK1Data 20 19 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 19 0 := by
  decide

private theorem x4NLK2Row20Coeff20_spec :
    mulCoeffTwo KData X4NLK1Data 20 20 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 20 0 := by
  decide

private theorem x4NLK2Row20Coeff21_spec :
    mulCoeffTwo KData X4NLK1Data 20 21 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 21 0 := by
  decide

private theorem x4NLK2Row20Coeff22_spec :
    mulCoeffTwo KData X4NLK1Data 20 22 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 22 0 := by
  decide

private theorem x4NLK2Row20Coeff23_spec :
    mulCoeffTwo KData X4NLK1Data 20 23 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 23 0 := by
  decide

private theorem x4NLK2Row20Coeff24_spec :
    mulCoeffTwo KData X4NLK1Data 20 24 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 24 0 := by
  decide

private theorem x4NLK2Row20Coeff25_spec :
    mulCoeffTwo KData X4NLK1Data 20 25 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 25 0 := by
  decide

private theorem x4NLK2Row20Coeff26_spec :
    mulCoeffTwo KData X4NLK1Data 20 26 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 26 0 := by
  decide

private theorem x4NLK2Row20Coeff27_spec :
    mulCoeffTwo KData X4NLK1Data 20 27 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 27 0 := by
  decide

private theorem x4NLK2Row20Coeff28_spec :
    mulCoeffTwo KData X4NLK1Data 20 28 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 28 0 := by
  decide

private theorem x4NLK2Row20Coeff29_spec :
    mulCoeffTwo KData X4NLK1Data 20 29 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 29 0 := by
  decide

private theorem x4NLK2Row20Coeff30_spec :
    mulCoeffTwo KData X4NLK1Data 20 30 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 30 0 := by
  decide

private theorem x4NLK2Row20Coeff31_spec :
    mulCoeffTwo KData X4NLK1Data 20 31 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 31 0 := by
  decide

private theorem x4NLK2Row20Coeff32_spec :
    mulCoeffTwo KData X4NLK1Data 20 32 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 32 0 := by
  decide

private theorem x4NLK2Row20Coeff33_spec :
    mulCoeffTwo KData X4NLK1Data 20 33 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 33 0 := by
  decide

private theorem x4NLK2Row20Coeff34_spec :
    mulCoeffTwo KData X4NLK1Data 20 34 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 34 0 := by
  decide

private theorem x4NLK2Row20Coeff35_spec :
    mulCoeffTwo KData X4NLK1Data 20 35 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 35 0 := by
  decide

private theorem x4NLK2Row20Coeff36_spec :
    mulCoeffTwo KData X4NLK1Data 20 36 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 36 0 := by
  decide

private theorem x4NLK2Row20Coeff37_spec :
    mulCoeffTwo KData X4NLK1Data 20 37 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 37 0 := by
  decide

private theorem x4NLK2Row20Coeff38_spec :
    mulCoeffTwo KData X4NLK1Data 20 38 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 38 0 := by
  decide

private theorem x4NLK2Row20Coeff39_spec :
    mulCoeffTwo KData X4NLK1Data 20 39 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 39 0 := by
  decide

private theorem x4NLK2Row20Coeff40_spec :
    mulCoeffTwo KData X4NLK1Data 20 40 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 40 0 := by
  decide

private theorem x4NLK2Row20Coeff41_spec :
    mulCoeffTwo KData X4NLK1Data 20 41 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 41 0 := by
  decide

private theorem x4NLK2Row20Coeff42_spec :
    mulCoeffTwo KData X4NLK1Data 20 42 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 42 0 := by
  decide

private theorem x4NLK2Row20Coeff43_spec :
    mulCoeffTwo KData X4NLK1Data 20 43 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 43 0 := by
  decide

private theorem x4NLK2Row20Coeff44_spec :
    mulCoeffTwo KData X4NLK1Data 20 44 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 44 0 := by
  decide

private theorem x4NLK2Row20Coeff45_spec :
    mulCoeffTwo KData X4NLK1Data 20 45 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 45 0 := by
  decide

private theorem x4NLK2Row20Coeff46_spec :
    mulCoeffTwo KData X4NLK1Data 20 46 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 46 0 := by
  decide

private theorem x4NLK2Row20Coeff47_spec :
    mulCoeffTwo KData X4NLK1Data 20 47 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 47 0 := by
  decide

private theorem x4NLK2Row20Coeff48_spec :
    mulCoeffTwo KData X4NLK1Data 20 48 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 48 0 := by
  decide

private theorem x4NLK2Row20Coeff49_spec :
    mulCoeffTwo KData X4NLK1Data 20 49 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 49 0 := by
  decide

private theorem x4NLK2Row20Coeff50_spec :
    mulCoeffTwo KData X4NLK1Data 20 50 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 50 0 := by
  decide

private theorem x4NLK2Row20Coeff51_spec :
    mulCoeffTwo KData X4NLK1Data 20 51 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 51 0 := by
  decide

private theorem x4NLK2Row20Coeff52_spec :
    mulCoeffTwo KData X4NLK1Data 20 52 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 52 0 := by
  decide

private theorem x4NLK2Row20Coeff53_spec :
    mulCoeffTwo KData X4NLK1Data 20 53 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 53 0 := by
  decide

private theorem x4NLK2Row20Coeff54_spec :
    mulCoeffTwo KData X4NLK1Data 20 54 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 54 0 := by
  decide

private theorem x4NLK2Row20Coeff55_spec :
    mulCoeffTwo KData X4NLK1Data 20 55 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 55 0 := by
  decide

private theorem x4NLK2Row20Coeff56_spec :
    mulCoeffTwo KData X4NLK1Data 20 56 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 56 0 := by
  decide

private theorem x4NLK2Row20Coeff57_spec :
    mulCoeffTwo KData X4NLK1Data 20 57 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 57 0 := by
  decide

private theorem x4NLK2Row20Coeff58_spec :
    mulCoeffTwo KData X4NLK1Data 20 58 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 58 0 := by
  decide

private theorem x4NLK2Row20Coeff59_spec :
    mulCoeffTwo KData X4NLK1Data 20 59 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 59 0 := by
  decide

private theorem x4NLK2Row20Coeff60_spec :
    mulCoeffTwo KData X4NLK1Data 20 60 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 60 0 := by
  decide

private theorem x4NLK2Row20Coeff61_spec :
    mulCoeffTwo KData X4NLK1Data 20 61 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 61 0 := by
  decide

private theorem x4NLK2Row20Coeff62_spec :
    mulCoeffTwo KData X4NLK1Data 20 62 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 62 0 := by
  decide

private theorem x4NLK2Row20Coeff63_spec :
    mulCoeffTwo KData X4NLK1Data 20 63 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 63 0 := by
  decide

private theorem x4NLK2Row20Coeff64_spec :
    mulCoeffTwo KData X4NLK1Data 20 64 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 64 0 := by
  decide

private theorem x4NLK2Row20Coeff65_spec :
    mulCoeffTwo KData X4NLK1Data 20 65 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 65 0 := by
  decide

private theorem x4NLK2Row20Coeff66_spec :
    mulCoeffTwo KData X4NLK1Data 20 66 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 66 0 := by
  decide

private theorem x4NLK2Row20Coeff67_spec :
    mulCoeffTwo KData X4NLK1Data 20 67 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 67 0 := by
  decide

private theorem x4NLK2Row20Coeff68_spec :
    mulCoeffTwo KData X4NLK1Data 20 68 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 68 0 := by
  decide

private theorem x4NLK2Row20Coeff69_spec :
    mulCoeffTwo KData X4NLK1Data 20 69 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 69 0 := by
  decide

private theorem x4NLK2Row20Coeff70_spec :
    mulCoeffTwo KData X4NLK1Data 20 70 =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD 70 0 := by
  decide

private theorem x4NLK2Row20Coeffs0To9_spec (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo KData X4NLK1Data 20 j =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK2Row20Coeff0_spec
  · exact x4NLK2Row20Coeff1_spec
  · exact x4NLK2Row20Coeff2_spec
  · exact x4NLK2Row20Coeff3_spec
  · exact x4NLK2Row20Coeff4_spec
  · exact x4NLK2Row20Coeff5_spec
  · exact x4NLK2Row20Coeff6_spec
  · exact x4NLK2Row20Coeff7_spec
  · exact x4NLK2Row20Coeff8_spec
  · exact x4NLK2Row20Coeff9_spec

private theorem x4NLK2Row20Coeffs10To19_spec (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo KData X4NLK1Data 20 j =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK2Row20Coeff10_spec
  · exact x4NLK2Row20Coeff11_spec
  · exact x4NLK2Row20Coeff12_spec
  · exact x4NLK2Row20Coeff13_spec
  · exact x4NLK2Row20Coeff14_spec
  · exact x4NLK2Row20Coeff15_spec
  · exact x4NLK2Row20Coeff16_spec
  · exact x4NLK2Row20Coeff17_spec
  · exact x4NLK2Row20Coeff18_spec
  · exact x4NLK2Row20Coeff19_spec

private theorem x4NLK2Row20Coeffs20To29_spec (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo KData X4NLK1Data 20 j =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK2Row20Coeff20_spec
  · exact x4NLK2Row20Coeff21_spec
  · exact x4NLK2Row20Coeff22_spec
  · exact x4NLK2Row20Coeff23_spec
  · exact x4NLK2Row20Coeff24_spec
  · exact x4NLK2Row20Coeff25_spec
  · exact x4NLK2Row20Coeff26_spec
  · exact x4NLK2Row20Coeff27_spec
  · exact x4NLK2Row20Coeff28_spec
  · exact x4NLK2Row20Coeff29_spec

private theorem x4NLK2Row20Coeffs30To39_spec (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo KData X4NLK1Data 20 j =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK2Row20Coeff30_spec
  · exact x4NLK2Row20Coeff31_spec
  · exact x4NLK2Row20Coeff32_spec
  · exact x4NLK2Row20Coeff33_spec
  · exact x4NLK2Row20Coeff34_spec
  · exact x4NLK2Row20Coeff35_spec
  · exact x4NLK2Row20Coeff36_spec
  · exact x4NLK2Row20Coeff37_spec
  · exact x4NLK2Row20Coeff38_spec
  · exact x4NLK2Row20Coeff39_spec

private theorem x4NLK2Row20Coeffs40To49_spec (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo KData X4NLK1Data 20 j =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK2Row20Coeff40_spec
  · exact x4NLK2Row20Coeff41_spec
  · exact x4NLK2Row20Coeff42_spec
  · exact x4NLK2Row20Coeff43_spec
  · exact x4NLK2Row20Coeff44_spec
  · exact x4NLK2Row20Coeff45_spec
  · exact x4NLK2Row20Coeff46_spec
  · exact x4NLK2Row20Coeff47_spec
  · exact x4NLK2Row20Coeff48_spec
  · exact x4NLK2Row20Coeff49_spec

private theorem x4NLK2Row20Coeffs50To59_spec (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo KData X4NLK1Data 20 j =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK2Row20Coeff50_spec
  · exact x4NLK2Row20Coeff51_spec
  · exact x4NLK2Row20Coeff52_spec
  · exact x4NLK2Row20Coeff53_spec
  · exact x4NLK2Row20Coeff54_spec
  · exact x4NLK2Row20Coeff55_spec
  · exact x4NLK2Row20Coeff56_spec
  · exact x4NLK2Row20Coeff57_spec
  · exact x4NLK2Row20Coeff58_spec
  · exact x4NLK2Row20Coeff59_spec

private theorem x4NLK2Row20Coeffs60To69_spec (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo KData X4NLK1Data 20 j =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK2Row20Coeff60_spec
  · exact x4NLK2Row20Coeff61_spec
  · exact x4NLK2Row20Coeff62_spec
  · exact x4NLK2Row20Coeff63_spec
  · exact x4NLK2Row20Coeff64_spec
  · exact x4NLK2Row20Coeff65_spec
  · exact x4NLK2Row20Coeff66_spec
  · exact x4NLK2Row20Coeff67_spec
  · exact x4NLK2Row20Coeff68_spec
  · exact x4NLK2Row20Coeff69_spec

private theorem x4NLK2Row20Coeffs70To70_spec (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 71) :
    mulCoeffTwo KData X4NLK1Data 20 j =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD j 0 := by
  have hj : j = 70 := by omega
  subst j
  exact x4NLK2Row20Coeff70_spec

private theorem x4NLK2Row20_coefficients (j : ℕ) (hj : j < 71) :
    mulCoeffTwo KData X4NLK1Data 20 j =
      ((rectangularize 52 71 X4NLK2Data).getD 20 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact x4NLK2Row20Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact x4NLK2Row20Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact x4NLK2Row20Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact x4NLK2Row20Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact x4NLK2Row20Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact x4NLK2Row20Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact x4NLK2Row20Coeffs60To69_spec j (by omega) h70
  exact x4NLK2Row20Coeffs70To70_spec j (by omega) hj

private theorem x4NLK2Row20_spec :
    padOne 71 (mulRow KData X4NLK1Data 20) =
      (rectangularize 52 71 X4NLK2Data).getD 20 [] := by
  apply padOne_mulRow_eq_of_coefficients 71 KData X4NLK1Data 20
    ((rectangularize 52 71 X4NLK2Data).getD 20 [])
  · decide
  · have hTargetSupport : (X4NLK2Data.getD 20 []).length ≤ 71 := by
      decide
    rw [getD_rectangularize 52 71 X4NLK2Data 20 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact x4NLK2Row20_coefficients

private theorem x4NLK2Row21_spec :
    padOne 71 (mulRow KData X4NLK1Data 21) =
      (rectangularize 52 71 X4NLK2Data).getD 21 [] := by
  decide

private theorem x4NLK2Row22_spec :
    padOne 71 (mulRow KData X4NLK1Data 22) =
      (rectangularize 52 71 X4NLK2Data).getD 22 [] := by
  decide

private theorem x4NLK2Row23_spec :
    padOne 71 (mulRow KData X4NLK1Data 23) =
      (rectangularize 52 71 X4NLK2Data).getD 23 [] := by
  decide

private theorem x4NLK2Row24_spec :
    padOne 71 (mulRow KData X4NLK1Data 24) =
      (rectangularize 52 71 X4NLK2Data).getD 24 [] := by
  decide

private theorem x4NLK2Row25_spec :
    padOne 71 (mulRow KData X4NLK1Data 25) =
      (rectangularize 52 71 X4NLK2Data).getD 25 [] := by
  decide

private theorem x4NLK2Row26_spec :
    padOne 71 (mulRow KData X4NLK1Data 26) =
      (rectangularize 52 71 X4NLK2Data).getD 26 [] := by
  decide

private theorem x4NLK2Row27_spec :
    padOne 71 (mulRow KData X4NLK1Data 27) =
      (rectangularize 52 71 X4NLK2Data).getD 27 [] := by
  decide

private theorem x4NLK2Row28_spec :
    padOne 71 (mulRow KData X4NLK1Data 28) =
      (rectangularize 52 71 X4NLK2Data).getD 28 [] := by
  decide

private theorem x4NLK2Row29_spec :
    padOne 71 (mulRow KData X4NLK1Data 29) =
      (rectangularize 52 71 X4NLK2Data).getD 29 [] := by
  decide

private theorem x4NLK2Row30_spec :
    padOne 71 (mulRow KData X4NLK1Data 30) =
      (rectangularize 52 71 X4NLK2Data).getD 30 [] := by
  decide

private theorem x4NLK2Row31_spec :
    padOne 71 (mulRow KData X4NLK1Data 31) =
      (rectangularize 52 71 X4NLK2Data).getD 31 [] := by
  decide

private theorem x4NLK2Row32_spec :
    padOne 71 (mulRow KData X4NLK1Data 32) =
      (rectangularize 52 71 X4NLK2Data).getD 32 [] := by
  decide

private theorem x4NLK2Row33_spec :
    padOne 71 (mulRow KData X4NLK1Data 33) =
      (rectangularize 52 71 X4NLK2Data).getD 33 [] := by
  decide

private theorem x4NLK2Row34_spec :
    padOne 71 (mulRow KData X4NLK1Data 34) =
      (rectangularize 52 71 X4NLK2Data).getD 34 [] := by
  decide

private theorem x4NLK2Row35_spec :
    padOne 71 (mulRow KData X4NLK1Data 35) =
      (rectangularize 52 71 X4NLK2Data).getD 35 [] := by
  decide

private theorem x4NLK2Row36_spec :
    padOne 71 (mulRow KData X4NLK1Data 36) =
      (rectangularize 52 71 X4NLK2Data).getD 36 [] := by
  decide

private theorem x4NLK2Row37_spec :
    padOne 71 (mulRow KData X4NLK1Data 37) =
      (rectangularize 52 71 X4NLK2Data).getD 37 [] := by
  decide

private theorem x4NLK2Row38_spec :
    padOne 71 (mulRow KData X4NLK1Data 38) =
      (rectangularize 52 71 X4NLK2Data).getD 38 [] := by
  decide

private theorem x4NLK2Row39_spec :
    padOne 71 (mulRow KData X4NLK1Data 39) =
      (rectangularize 52 71 X4NLK2Data).getD 39 [] := by
  decide

private theorem x4NLK2Row40_spec :
    padOne 71 (mulRow KData X4NLK1Data 40) =
      (rectangularize 52 71 X4NLK2Data).getD 40 [] := by
  decide

private theorem x4NLK2Row41_spec :
    padOne 71 (mulRow KData X4NLK1Data 41) =
      (rectangularize 52 71 X4NLK2Data).getD 41 [] := by
  decide

private theorem x4NLK2Row42_spec :
    padOne 71 (mulRow KData X4NLK1Data 42) =
      (rectangularize 52 71 X4NLK2Data).getD 42 [] := by
  decide

private theorem x4NLK2Row43_spec :
    padOne 71 (mulRow KData X4NLK1Data 43) =
      (rectangularize 52 71 X4NLK2Data).getD 43 [] := by
  decide

private theorem x4NLK2Row44_spec :
    padOne 71 (mulRow KData X4NLK1Data 44) =
      (rectangularize 52 71 X4NLK2Data).getD 44 [] := by
  decide

private theorem x4NLK2Row45_spec :
    padOne 71 (mulRow KData X4NLK1Data 45) =
      (rectangularize 52 71 X4NLK2Data).getD 45 [] := by
  decide

private theorem x4NLK2Row46_spec :
    padOne 71 (mulRow KData X4NLK1Data 46) =
      (rectangularize 52 71 X4NLK2Data).getD 46 [] := by
  decide

private theorem x4NLK2Row47_spec :
    padOne 71 (mulRow KData X4NLK1Data 47) =
      (rectangularize 52 71 X4NLK2Data).getD 47 [] := by
  decide

private theorem x4NLK2Row48_spec :
    padOne 71 (mulRow KData X4NLK1Data 48) =
      (rectangularize 52 71 X4NLK2Data).getD 48 [] := by
  decide

private theorem x4NLK2Row49_spec :
    padOne 71 (mulRow KData X4NLK1Data 49) =
      (rectangularize 52 71 X4NLK2Data).getD 49 [] := by
  decide

private theorem x4NLK2Row50_spec :
    padOne 71 (mulRow KData X4NLK1Data 50) =
      (rectangularize 52 71 X4NLK2Data).getD 50 [] := by
  decide

private theorem x4NLK2Row51_spec :
    padOne 71 (mulRow KData X4NLK1Data 51) =
      (rectangularize 52 71 X4NLK2Data).getD 51 [] := by
  decide

private theorem x4NLK2Rows_spec (n : ℕ) (hn : n < 52) :
    padOne 71 (mulRow KData X4NLK1Data n) =
      (rectangularize 52 71 X4NLK2Data).getD n [] := by
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
  · exact x4NLK2Row0_spec
  · exact x4NLK2Row1_spec
  · exact x4NLK2Row2_spec
  · exact x4NLK2Row3_spec
  · exact x4NLK2Row4_spec
  · exact x4NLK2Row5_spec
  · exact x4NLK2Row6_spec
  · exact x4NLK2Row7_spec
  · exact x4NLK2Row8_spec
  · exact x4NLK2Row9_spec
  · exact x4NLK2Row10_spec
  · exact x4NLK2Row11_spec
  · exact x4NLK2Row12_spec
  · exact x4NLK2Row13_spec
  · exact x4NLK2Row14_spec
  · exact x4NLK2Row15_spec
  · exact x4NLK2Row16_spec
  · exact x4NLK2Row17_spec
  · exact x4NLK2Row18_spec
  · exact x4NLK2Row19_spec
  · exact x4NLK2Row20_spec
  · exact x4NLK2Row21_spec
  · exact x4NLK2Row22_spec
  · exact x4NLK2Row23_spec
  · exact x4NLK2Row24_spec
  · exact x4NLK2Row25_spec
  · exact x4NLK2Row26_spec
  · exact x4NLK2Row27_spec
  · exact x4NLK2Row28_spec
  · exact x4NLK2Row29_spec
  · exact x4NLK2Row30_spec
  · exact x4NLK2Row31_spec
  · exact x4NLK2Row32_spec
  · exact x4NLK2Row33_spec
  · exact x4NLK2Row34_spec
  · exact x4NLK2Row35_spec
  · exact x4NLK2Row36_spec
  · exact x4NLK2Row37_spec
  · exact x4NLK2Row38_spec
  · exact x4NLK2Row39_spec
  · exact x4NLK2Row40_spec
  · exact x4NLK2Row41_spec
  · exact x4NLK2Row42_spec
  · exact x4NLK2Row43_spec
  · exact x4NLK2Row44_spec
  · exact x4NLK2Row45_spec
  · exact x4NLK2Row46_spec
  · exact x4NLK2Row47_spec
  · exact x4NLK2Row48_spec
  · exact x4NLK2Row49_spec
  · exact x4NLK2Row50_spec
  · exact x4NLK2Row51_spec

private theorem x4NLK2Left_length :
    (rectangularize 52 71 (Two.mul KData X4NLK1Data)).length = 52 := by
  decide

private theorem x4NLK2Right_length :
    (rectangularize 52 71 X4NLK2Data).length = 52 := by
  decide

-- Exact bidegree bound (51, 70); no row or column is discarded.
theorem x4NLK2Data_spec :
    rectangularize 52 71 (Two.mul KData X4NLK1Data) =
      rectangularize 52 71 X4NLK2Data := by
  apply List.ext_getElem (x4NLK2Left_length.trans x4NLK2Right_length.symm)
  intro n hn _
  rw [List.getElem_eq_getD [], List.getElem_eq_getD []]
  rw [x4NLK2Left_length] at hn
  rw [getD_rectangularize 52 71 (Two.mul KData X4NLK1Data) n hn,
    ← mulRow_eq_getD]
  exact x4NLK2Rows_spec n hn

private theorem x4NLK3Row0_spec :
    padOne 73 (mulRow KData X4NLK2Data 0) =
      (rectangularize 53 73 X4NLK3Data).getD 0 [] := by
  decide

private theorem x4NLK3Row1_spec :
    padOne 73 (mulRow KData X4NLK2Data 1) =
      (rectangularize 53 73 X4NLK3Data).getD 1 [] := by
  decide

private theorem x4NLK3Row2_spec :
    padOne 73 (mulRow KData X4NLK2Data 2) =
      (rectangularize 53 73 X4NLK3Data).getD 2 [] := by
  decide

private theorem x4NLK3Row3_spec :
    padOne 73 (mulRow KData X4NLK2Data 3) =
      (rectangularize 53 73 X4NLK3Data).getD 3 [] := by
  decide

private theorem x4NLK3Row4_spec :
    padOne 73 (mulRow KData X4NLK2Data 4) =
      (rectangularize 53 73 X4NLK3Data).getD 4 [] := by
  decide

private theorem x4NLK3Row5_spec :
    padOne 73 (mulRow KData X4NLK2Data 5) =
      (rectangularize 53 73 X4NLK3Data).getD 5 [] := by
  decide

private theorem x4NLK3Row6_spec :
    padOne 73 (mulRow KData X4NLK2Data 6) =
      (rectangularize 53 73 X4NLK3Data).getD 6 [] := by
  decide

private theorem x4NLK3Row7_spec :
    padOne 73 (mulRow KData X4NLK2Data 7) =
      (rectangularize 53 73 X4NLK3Data).getD 7 [] := by
  decide

private theorem x4NLK3Row8_spec :
    padOne 73 (mulRow KData X4NLK2Data 8) =
      (rectangularize 53 73 X4NLK3Data).getD 8 [] := by
  decide

private theorem x4NLK3Row9_spec :
    padOne 73 (mulRow KData X4NLK2Data 9) =
      (rectangularize 53 73 X4NLK3Data).getD 9 [] := by
  decide

private theorem x4NLK3Row10_spec :
    padOne 73 (mulRow KData X4NLK2Data 10) =
      (rectangularize 53 73 X4NLK3Data).getD 10 [] := by
  decide

private theorem x4NLK3Row11_spec :
    padOne 73 (mulRow KData X4NLK2Data 11) =
      (rectangularize 53 73 X4NLK3Data).getD 11 [] := by
  decide

private theorem x4NLK3Row12_spec :
    padOne 73 (mulRow KData X4NLK2Data 12) =
      (rectangularize 53 73 X4NLK3Data).getD 12 [] := by
  decide

private theorem x4NLK3Row13_spec :
    padOne 73 (mulRow KData X4NLK2Data 13) =
      (rectangularize 53 73 X4NLK3Data).getD 13 [] := by
  decide

private theorem x4NLK3Row14Coeff0_spec :
    mulCoeffTwo KData X4NLK2Data 14 0 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 0 0 := by
  decide

private theorem x4NLK3Row14Coeff1_spec :
    mulCoeffTwo KData X4NLK2Data 14 1 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 1 0 := by
  decide

private theorem x4NLK3Row14Coeff2_spec :
    mulCoeffTwo KData X4NLK2Data 14 2 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 2 0 := by
  decide

private theorem x4NLK3Row14Coeff3_spec :
    mulCoeffTwo KData X4NLK2Data 14 3 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 3 0 := by
  decide

private theorem x4NLK3Row14Coeff4_spec :
    mulCoeffTwo KData X4NLK2Data 14 4 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 4 0 := by
  decide

private theorem x4NLK3Row14Coeff5_spec :
    mulCoeffTwo KData X4NLK2Data 14 5 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 5 0 := by
  decide

private theorem x4NLK3Row14Coeff6_spec :
    mulCoeffTwo KData X4NLK2Data 14 6 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 6 0 := by
  decide

private theorem x4NLK3Row14Coeff7_spec :
    mulCoeffTwo KData X4NLK2Data 14 7 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 7 0 := by
  decide

private theorem x4NLK3Row14Coeff8_spec :
    mulCoeffTwo KData X4NLK2Data 14 8 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 8 0 := by
  decide

private theorem x4NLK3Row14Coeff9_spec :
    mulCoeffTwo KData X4NLK2Data 14 9 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 9 0 := by
  decide

private theorem x4NLK3Row14Coeff10_spec :
    mulCoeffTwo KData X4NLK2Data 14 10 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 10 0 := by
  decide

private theorem x4NLK3Row14Coeff11_spec :
    mulCoeffTwo KData X4NLK2Data 14 11 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 11 0 := by
  decide

private theorem x4NLK3Row14Coeff12_spec :
    mulCoeffTwo KData X4NLK2Data 14 12 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 12 0 := by
  decide

private theorem x4NLK3Row14Coeff13_spec :
    mulCoeffTwo KData X4NLK2Data 14 13 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 13 0 := by
  decide

private theorem x4NLK3Row14Coeff14_spec :
    mulCoeffTwo KData X4NLK2Data 14 14 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 14 0 := by
  decide

private theorem x4NLK3Row14Coeff15_spec :
    mulCoeffTwo KData X4NLK2Data 14 15 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 15 0 := by
  decide

private theorem x4NLK3Row14Coeff16_spec :
    mulCoeffTwo KData X4NLK2Data 14 16 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 16 0 := by
  decide

private theorem x4NLK3Row14Coeff17_spec :
    mulCoeffTwo KData X4NLK2Data 14 17 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 17 0 := by
  decide

private theorem x4NLK3Row14Coeff18_spec :
    mulCoeffTwo KData X4NLK2Data 14 18 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 18 0 := by
  decide

private theorem x4NLK3Row14Coeff19_spec :
    mulCoeffTwo KData X4NLK2Data 14 19 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 19 0 := by
  decide

private theorem x4NLK3Row14Coeff20_spec :
    mulCoeffTwo KData X4NLK2Data 14 20 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 20 0 := by
  decide

private theorem x4NLK3Row14Coeff21_spec :
    mulCoeffTwo KData X4NLK2Data 14 21 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 21 0 := by
  decide

private theorem x4NLK3Row14Coeff22_spec :
    mulCoeffTwo KData X4NLK2Data 14 22 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 22 0 := by
  decide

private theorem x4NLK3Row14Coeff23_spec :
    mulCoeffTwo KData X4NLK2Data 14 23 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 23 0 := by
  decide

private theorem x4NLK3Row14Coeff24_spec :
    mulCoeffTwo KData X4NLK2Data 14 24 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 24 0 := by
  decide

private theorem x4NLK3Row14Coeff25_spec :
    mulCoeffTwo KData X4NLK2Data 14 25 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 25 0 := by
  decide

private theorem x4NLK3Row14Coeff26_spec :
    mulCoeffTwo KData X4NLK2Data 14 26 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 26 0 := by
  decide

private theorem x4NLK3Row14Coeff27_spec :
    mulCoeffTwo KData X4NLK2Data 14 27 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 27 0 := by
  decide

private theorem x4NLK3Row14Coeff28_spec :
    mulCoeffTwo KData X4NLK2Data 14 28 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 28 0 := by
  decide

private theorem x4NLK3Row14Coeff29_spec :
    mulCoeffTwo KData X4NLK2Data 14 29 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 29 0 := by
  decide

private theorem x4NLK3Row14Coeff30_spec :
    mulCoeffTwo KData X4NLK2Data 14 30 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 30 0 := by
  decide

private theorem x4NLK3Row14Coeff31_spec :
    mulCoeffTwo KData X4NLK2Data 14 31 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 31 0 := by
  decide

private theorem x4NLK3Row14Coeff32_spec :
    mulCoeffTwo KData X4NLK2Data 14 32 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 32 0 := by
  decide

private theorem x4NLK3Row14Coeff33_spec :
    mulCoeffTwo KData X4NLK2Data 14 33 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 33 0 := by
  decide

private theorem x4NLK3Row14Coeff34_spec :
    mulCoeffTwo KData X4NLK2Data 14 34 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 34 0 := by
  decide

private theorem x4NLK3Row14Coeff35_spec :
    mulCoeffTwo KData X4NLK2Data 14 35 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 35 0 := by
  decide

private theorem x4NLK3Row14Coeff36_spec :
    mulCoeffTwo KData X4NLK2Data 14 36 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 36 0 := by
  decide

private theorem x4NLK3Row14Coeff37_spec :
    mulCoeffTwo KData X4NLK2Data 14 37 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 37 0 := by
  decide

private theorem x4NLK3Row14Coeff38_spec :
    mulCoeffTwo KData X4NLK2Data 14 38 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 38 0 := by
  decide

private theorem x4NLK3Row14Coeff39_spec :
    mulCoeffTwo KData X4NLK2Data 14 39 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 39 0 := by
  decide

private theorem x4NLK3Row14Coeff40_spec :
    mulCoeffTwo KData X4NLK2Data 14 40 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 40 0 := by
  decide

private theorem x4NLK3Row14Coeff41_spec :
    mulCoeffTwo KData X4NLK2Data 14 41 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 41 0 := by
  decide

private theorem x4NLK3Row14Coeff42_spec :
    mulCoeffTwo KData X4NLK2Data 14 42 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 42 0 := by
  decide

private theorem x4NLK3Row14Coeff43_spec :
    mulCoeffTwo KData X4NLK2Data 14 43 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 43 0 := by
  decide

private theorem x4NLK3Row14Coeff44_spec :
    mulCoeffTwo KData X4NLK2Data 14 44 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 44 0 := by
  decide

private theorem x4NLK3Row14Coeff45_spec :
    mulCoeffTwo KData X4NLK2Data 14 45 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 45 0 := by
  decide

private theorem x4NLK3Row14Coeff46_spec :
    mulCoeffTwo KData X4NLK2Data 14 46 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 46 0 := by
  decide

private theorem x4NLK3Row14Coeff47_spec :
    mulCoeffTwo KData X4NLK2Data 14 47 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 47 0 := by
  decide

private theorem x4NLK3Row14Coeff48_spec :
    mulCoeffTwo KData X4NLK2Data 14 48 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 48 0 := by
  decide

private theorem x4NLK3Row14Coeff49_spec :
    mulCoeffTwo KData X4NLK2Data 14 49 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 49 0 := by
  decide

private theorem x4NLK3Row14Coeff50_spec :
    mulCoeffTwo KData X4NLK2Data 14 50 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 50 0 := by
  decide

private theorem x4NLK3Row14Coeff51_spec :
    mulCoeffTwo KData X4NLK2Data 14 51 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 51 0 := by
  decide

private theorem x4NLK3Row14Coeff52_spec :
    mulCoeffTwo KData X4NLK2Data 14 52 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 52 0 := by
  decide

private theorem x4NLK3Row14Coeff53_spec :
    mulCoeffTwo KData X4NLK2Data 14 53 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 53 0 := by
  decide

private theorem x4NLK3Row14Coeff54_spec :
    mulCoeffTwo KData X4NLK2Data 14 54 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 54 0 := by
  decide

private theorem x4NLK3Row14Coeff55_spec :
    mulCoeffTwo KData X4NLK2Data 14 55 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 55 0 := by
  decide

private theorem x4NLK3Row14Coeff56_spec :
    mulCoeffTwo KData X4NLK2Data 14 56 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 56 0 := by
  decide

private theorem x4NLK3Row14Coeff57_spec :
    mulCoeffTwo KData X4NLK2Data 14 57 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 57 0 := by
  decide

private theorem x4NLK3Row14Coeff58_spec :
    mulCoeffTwo KData X4NLK2Data 14 58 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 58 0 := by
  decide

private theorem x4NLK3Row14Coeff59_spec :
    mulCoeffTwo KData X4NLK2Data 14 59 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 59 0 := by
  decide

private theorem x4NLK3Row14Coeff60_spec :
    mulCoeffTwo KData X4NLK2Data 14 60 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 60 0 := by
  decide

private theorem x4NLK3Row14Coeff61_spec :
    mulCoeffTwo KData X4NLK2Data 14 61 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 61 0 := by
  decide

private theorem x4NLK3Row14Coeff62_spec :
    mulCoeffTwo KData X4NLK2Data 14 62 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 62 0 := by
  decide

private theorem x4NLK3Row14Coeff63_spec :
    mulCoeffTwo KData X4NLK2Data 14 63 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 63 0 := by
  decide

private theorem x4NLK3Row14Coeff64_spec :
    mulCoeffTwo KData X4NLK2Data 14 64 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 64 0 := by
  decide

private theorem x4NLK3Row14Coeff65_spec :
    mulCoeffTwo KData X4NLK2Data 14 65 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 65 0 := by
  decide

private theorem x4NLK3Row14Coeff66_spec :
    mulCoeffTwo KData X4NLK2Data 14 66 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 66 0 := by
  decide

private theorem x4NLK3Row14Coeff67_spec :
    mulCoeffTwo KData X4NLK2Data 14 67 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 67 0 := by
  decide

private theorem x4NLK3Row14Coeff68_spec :
    mulCoeffTwo KData X4NLK2Data 14 68 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 68 0 := by
  decide

private theorem x4NLK3Row14Coeff69_spec :
    mulCoeffTwo KData X4NLK2Data 14 69 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 69 0 := by
  decide

private theorem x4NLK3Row14Coeff70_spec :
    mulCoeffTwo KData X4NLK2Data 14 70 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 70 0 := by
  decide

private theorem x4NLK3Row14Coeff71_spec :
    mulCoeffTwo KData X4NLK2Data 14 71 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 71 0 := by
  decide

private theorem x4NLK3Row14Coeff72_spec :
    mulCoeffTwo KData X4NLK2Data 14 72 =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD 72 0 := by
  decide

private theorem x4NLK3Row14Coeffs0To9_spec (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo KData X4NLK2Data 14 j =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row14Coeff0_spec
  · exact x4NLK3Row14Coeff1_spec
  · exact x4NLK3Row14Coeff2_spec
  · exact x4NLK3Row14Coeff3_spec
  · exact x4NLK3Row14Coeff4_spec
  · exact x4NLK3Row14Coeff5_spec
  · exact x4NLK3Row14Coeff6_spec
  · exact x4NLK3Row14Coeff7_spec
  · exact x4NLK3Row14Coeff8_spec
  · exact x4NLK3Row14Coeff9_spec

private theorem x4NLK3Row14Coeffs10To19_spec (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo KData X4NLK2Data 14 j =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row14Coeff10_spec
  · exact x4NLK3Row14Coeff11_spec
  · exact x4NLK3Row14Coeff12_spec
  · exact x4NLK3Row14Coeff13_spec
  · exact x4NLK3Row14Coeff14_spec
  · exact x4NLK3Row14Coeff15_spec
  · exact x4NLK3Row14Coeff16_spec
  · exact x4NLK3Row14Coeff17_spec
  · exact x4NLK3Row14Coeff18_spec
  · exact x4NLK3Row14Coeff19_spec

private theorem x4NLK3Row14Coeffs20To29_spec (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo KData X4NLK2Data 14 j =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row14Coeff20_spec
  · exact x4NLK3Row14Coeff21_spec
  · exact x4NLK3Row14Coeff22_spec
  · exact x4NLK3Row14Coeff23_spec
  · exact x4NLK3Row14Coeff24_spec
  · exact x4NLK3Row14Coeff25_spec
  · exact x4NLK3Row14Coeff26_spec
  · exact x4NLK3Row14Coeff27_spec
  · exact x4NLK3Row14Coeff28_spec
  · exact x4NLK3Row14Coeff29_spec

private theorem x4NLK3Row14Coeffs30To39_spec (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo KData X4NLK2Data 14 j =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row14Coeff30_spec
  · exact x4NLK3Row14Coeff31_spec
  · exact x4NLK3Row14Coeff32_spec
  · exact x4NLK3Row14Coeff33_spec
  · exact x4NLK3Row14Coeff34_spec
  · exact x4NLK3Row14Coeff35_spec
  · exact x4NLK3Row14Coeff36_spec
  · exact x4NLK3Row14Coeff37_spec
  · exact x4NLK3Row14Coeff38_spec
  · exact x4NLK3Row14Coeff39_spec

private theorem x4NLK3Row14Coeffs40To49_spec (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo KData X4NLK2Data 14 j =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row14Coeff40_spec
  · exact x4NLK3Row14Coeff41_spec
  · exact x4NLK3Row14Coeff42_spec
  · exact x4NLK3Row14Coeff43_spec
  · exact x4NLK3Row14Coeff44_spec
  · exact x4NLK3Row14Coeff45_spec
  · exact x4NLK3Row14Coeff46_spec
  · exact x4NLK3Row14Coeff47_spec
  · exact x4NLK3Row14Coeff48_spec
  · exact x4NLK3Row14Coeff49_spec

private theorem x4NLK3Row14Coeffs50To59_spec (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo KData X4NLK2Data 14 j =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row14Coeff50_spec
  · exact x4NLK3Row14Coeff51_spec
  · exact x4NLK3Row14Coeff52_spec
  · exact x4NLK3Row14Coeff53_spec
  · exact x4NLK3Row14Coeff54_spec
  · exact x4NLK3Row14Coeff55_spec
  · exact x4NLK3Row14Coeff56_spec
  · exact x4NLK3Row14Coeff57_spec
  · exact x4NLK3Row14Coeff58_spec
  · exact x4NLK3Row14Coeff59_spec

private theorem x4NLK3Row14Coeffs60To69_spec (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo KData X4NLK2Data 14 j =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row14Coeff60_spec
  · exact x4NLK3Row14Coeff61_spec
  · exact x4NLK3Row14Coeff62_spec
  · exact x4NLK3Row14Coeff63_spec
  · exact x4NLK3Row14Coeff64_spec
  · exact x4NLK3Row14Coeff65_spec
  · exact x4NLK3Row14Coeff66_spec
  · exact x4NLK3Row14Coeff67_spec
  · exact x4NLK3Row14Coeff68_spec
  · exact x4NLK3Row14Coeff69_spec

private theorem x4NLK3Row14Coeffs70To72_spec (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 73) :
    mulCoeffTwo KData X4NLK2Data 14 j =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 := by
    omega
  rcases hCases with
    rfl | rfl | rfl
  · exact x4NLK3Row14Coeff70_spec
  · exact x4NLK3Row14Coeff71_spec
  · exact x4NLK3Row14Coeff72_spec

private theorem x4NLK3Row14_coefficients (j : ℕ) (hj : j < 73) :
    mulCoeffTwo KData X4NLK2Data 14 j =
      ((rectangularize 53 73 X4NLK3Data).getD 14 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact x4NLK3Row14Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact x4NLK3Row14Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact x4NLK3Row14Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact x4NLK3Row14Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact x4NLK3Row14Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact x4NLK3Row14Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact x4NLK3Row14Coeffs60To69_spec j (by omega) h70
  exact x4NLK3Row14Coeffs70To72_spec j (by omega) hj

private theorem x4NLK3Row14_spec :
    padOne 73 (mulRow KData X4NLK2Data 14) =
      (rectangularize 53 73 X4NLK3Data).getD 14 [] := by
  apply padOne_mulRow_eq_of_coefficients 73 KData X4NLK2Data 14
    ((rectangularize 53 73 X4NLK3Data).getD 14 [])
  · decide
  · have hTargetSupport : (X4NLK3Data.getD 14 []).length ≤ 73 := by
      decide
    rw [getD_rectangularize 53 73 X4NLK3Data 14 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact x4NLK3Row14_coefficients

private theorem x4NLK3Row15Coeff0_spec :
    mulCoeffTwo KData X4NLK2Data 15 0 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 0 0 := by
  decide

private theorem x4NLK3Row15Coeff1_spec :
    mulCoeffTwo KData X4NLK2Data 15 1 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 1 0 := by
  decide

private theorem x4NLK3Row15Coeff2_spec :
    mulCoeffTwo KData X4NLK2Data 15 2 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 2 0 := by
  decide

private theorem x4NLK3Row15Coeff3_spec :
    mulCoeffTwo KData X4NLK2Data 15 3 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 3 0 := by
  decide

private theorem x4NLK3Row15Coeff4_spec :
    mulCoeffTwo KData X4NLK2Data 15 4 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 4 0 := by
  decide

private theorem x4NLK3Row15Coeff5_spec :
    mulCoeffTwo KData X4NLK2Data 15 5 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 5 0 := by
  decide

private theorem x4NLK3Row15Coeff6_spec :
    mulCoeffTwo KData X4NLK2Data 15 6 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 6 0 := by
  decide

private theorem x4NLK3Row15Coeff7_spec :
    mulCoeffTwo KData X4NLK2Data 15 7 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 7 0 := by
  decide

private theorem x4NLK3Row15Coeff8_spec :
    mulCoeffTwo KData X4NLK2Data 15 8 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 8 0 := by
  decide

private theorem x4NLK3Row15Coeff9_spec :
    mulCoeffTwo KData X4NLK2Data 15 9 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 9 0 := by
  decide

private theorem x4NLK3Row15Coeff10_spec :
    mulCoeffTwo KData X4NLK2Data 15 10 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 10 0 := by
  decide

private theorem x4NLK3Row15Coeff11_spec :
    mulCoeffTwo KData X4NLK2Data 15 11 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 11 0 := by
  decide

private theorem x4NLK3Row15Coeff12_spec :
    mulCoeffTwo KData X4NLK2Data 15 12 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 12 0 := by
  decide

private theorem x4NLK3Row15Coeff13_spec :
    mulCoeffTwo KData X4NLK2Data 15 13 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 13 0 := by
  decide

private theorem x4NLK3Row15Coeff14_spec :
    mulCoeffTwo KData X4NLK2Data 15 14 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 14 0 := by
  decide

private theorem x4NLK3Row15Coeff15_spec :
    mulCoeffTwo KData X4NLK2Data 15 15 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 15 0 := by
  decide

private theorem x4NLK3Row15Coeff16_spec :
    mulCoeffTwo KData X4NLK2Data 15 16 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 16 0 := by
  decide

private theorem x4NLK3Row15Coeff17_spec :
    mulCoeffTwo KData X4NLK2Data 15 17 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 17 0 := by
  decide

private theorem x4NLK3Row15Coeff18_spec :
    mulCoeffTwo KData X4NLK2Data 15 18 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 18 0 := by
  decide

private theorem x4NLK3Row15Coeff19_spec :
    mulCoeffTwo KData X4NLK2Data 15 19 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 19 0 := by
  decide

private theorem x4NLK3Row15Coeff20_spec :
    mulCoeffTwo KData X4NLK2Data 15 20 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 20 0 := by
  decide

private theorem x4NLK3Row15Coeff21_spec :
    mulCoeffTwo KData X4NLK2Data 15 21 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 21 0 := by
  decide

private theorem x4NLK3Row15Coeff22_spec :
    mulCoeffTwo KData X4NLK2Data 15 22 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 22 0 := by
  decide

private theorem x4NLK3Row15Coeff23_spec :
    mulCoeffTwo KData X4NLK2Data 15 23 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 23 0 := by
  decide

private theorem x4NLK3Row15Coeff24_spec :
    mulCoeffTwo KData X4NLK2Data 15 24 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 24 0 := by
  decide

private theorem x4NLK3Row15Coeff25_spec :
    mulCoeffTwo KData X4NLK2Data 15 25 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 25 0 := by
  decide

private theorem x4NLK3Row15Coeff26_spec :
    mulCoeffTwo KData X4NLK2Data 15 26 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 26 0 := by
  decide

private theorem x4NLK3Row15Coeff27_spec :
    mulCoeffTwo KData X4NLK2Data 15 27 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 27 0 := by
  decide

private theorem x4NLK3Row15Coeff28_spec :
    mulCoeffTwo KData X4NLK2Data 15 28 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 28 0 := by
  decide

private theorem x4NLK3Row15Coeff29_spec :
    mulCoeffTwo KData X4NLK2Data 15 29 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 29 0 := by
  decide

private theorem x4NLK3Row15Coeff30_spec :
    mulCoeffTwo KData X4NLK2Data 15 30 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 30 0 := by
  decide

private theorem x4NLK3Row15Coeff31_spec :
    mulCoeffTwo KData X4NLK2Data 15 31 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 31 0 := by
  decide

private theorem x4NLK3Row15Coeff32_spec :
    mulCoeffTwo KData X4NLK2Data 15 32 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 32 0 := by
  decide

private theorem x4NLK3Row15Coeff33_spec :
    mulCoeffTwo KData X4NLK2Data 15 33 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 33 0 := by
  decide

private theorem x4NLK3Row15Coeff34_spec :
    mulCoeffTwo KData X4NLK2Data 15 34 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 34 0 := by
  decide

private theorem x4NLK3Row15Coeff35_spec :
    mulCoeffTwo KData X4NLK2Data 15 35 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 35 0 := by
  decide

private theorem x4NLK3Row15Coeff36_spec :
    mulCoeffTwo KData X4NLK2Data 15 36 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 36 0 := by
  decide

private theorem x4NLK3Row15Coeff37_spec :
    mulCoeffTwo KData X4NLK2Data 15 37 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 37 0 := by
  decide

private theorem x4NLK3Row15Coeff38_spec :
    mulCoeffTwo KData X4NLK2Data 15 38 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 38 0 := by
  decide

private theorem x4NLK3Row15Coeff39_spec :
    mulCoeffTwo KData X4NLK2Data 15 39 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 39 0 := by
  decide

private theorem x4NLK3Row15Coeff40_spec :
    mulCoeffTwo KData X4NLK2Data 15 40 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 40 0 := by
  decide

private theorem x4NLK3Row15Coeff41_spec :
    mulCoeffTwo KData X4NLK2Data 15 41 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 41 0 := by
  decide

private theorem x4NLK3Row15Coeff42_spec :
    mulCoeffTwo KData X4NLK2Data 15 42 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 42 0 := by
  decide

private theorem x4NLK3Row15Coeff43_spec :
    mulCoeffTwo KData X4NLK2Data 15 43 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 43 0 := by
  decide

private theorem x4NLK3Row15Coeff44_spec :
    mulCoeffTwo KData X4NLK2Data 15 44 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 44 0 := by
  decide

private theorem x4NLK3Row15Coeff45_spec :
    mulCoeffTwo KData X4NLK2Data 15 45 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 45 0 := by
  decide

private theorem x4NLK3Row15Coeff46_spec :
    mulCoeffTwo KData X4NLK2Data 15 46 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 46 0 := by
  decide

private theorem x4NLK3Row15Coeff47_spec :
    mulCoeffTwo KData X4NLK2Data 15 47 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 47 0 := by
  decide

private theorem x4NLK3Row15Coeff48_spec :
    mulCoeffTwo KData X4NLK2Data 15 48 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 48 0 := by
  decide

private theorem x4NLK3Row15Coeff49_spec :
    mulCoeffTwo KData X4NLK2Data 15 49 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 49 0 := by
  decide

private theorem x4NLK3Row15Coeff50_spec :
    mulCoeffTwo KData X4NLK2Data 15 50 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 50 0 := by
  decide

private theorem x4NLK3Row15Coeff51_spec :
    mulCoeffTwo KData X4NLK2Data 15 51 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 51 0 := by
  decide

private theorem x4NLK3Row15Coeff52_spec :
    mulCoeffTwo KData X4NLK2Data 15 52 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 52 0 := by
  decide

private theorem x4NLK3Row15Coeff53_spec :
    mulCoeffTwo KData X4NLK2Data 15 53 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 53 0 := by
  decide

private theorem x4NLK3Row15Coeff54_spec :
    mulCoeffTwo KData X4NLK2Data 15 54 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 54 0 := by
  decide

private theorem x4NLK3Row15Coeff55_spec :
    mulCoeffTwo KData X4NLK2Data 15 55 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 55 0 := by
  decide

private theorem x4NLK3Row15Coeff56_spec :
    mulCoeffTwo KData X4NLK2Data 15 56 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 56 0 := by
  decide

private theorem x4NLK3Row15Coeff57_spec :
    mulCoeffTwo KData X4NLK2Data 15 57 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 57 0 := by
  decide

private theorem x4NLK3Row15Coeff58_spec :
    mulCoeffTwo KData X4NLK2Data 15 58 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 58 0 := by
  decide

private theorem x4NLK3Row15Coeff59_spec :
    mulCoeffTwo KData X4NLK2Data 15 59 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 59 0 := by
  decide

private theorem x4NLK3Row15Coeff60_spec :
    mulCoeffTwo KData X4NLK2Data 15 60 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 60 0 := by
  decide

private theorem x4NLK3Row15Coeff61_spec :
    mulCoeffTwo KData X4NLK2Data 15 61 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 61 0 := by
  decide

private theorem x4NLK3Row15Coeff62_spec :
    mulCoeffTwo KData X4NLK2Data 15 62 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 62 0 := by
  decide

private theorem x4NLK3Row15Coeff63_spec :
    mulCoeffTwo KData X4NLK2Data 15 63 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 63 0 := by
  decide

private theorem x4NLK3Row15Coeff64_spec :
    mulCoeffTwo KData X4NLK2Data 15 64 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 64 0 := by
  decide

private theorem x4NLK3Row15Coeff65_spec :
    mulCoeffTwo KData X4NLK2Data 15 65 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 65 0 := by
  decide

private theorem x4NLK3Row15Coeff66_spec :
    mulCoeffTwo KData X4NLK2Data 15 66 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 66 0 := by
  decide

private theorem x4NLK3Row15Coeff67_spec :
    mulCoeffTwo KData X4NLK2Data 15 67 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 67 0 := by
  decide

private theorem x4NLK3Row15Coeff68_spec :
    mulCoeffTwo KData X4NLK2Data 15 68 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 68 0 := by
  decide

private theorem x4NLK3Row15Coeff69_spec :
    mulCoeffTwo KData X4NLK2Data 15 69 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 69 0 := by
  decide

private theorem x4NLK3Row15Coeff70_spec :
    mulCoeffTwo KData X4NLK2Data 15 70 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 70 0 := by
  decide

private theorem x4NLK3Row15Coeff71_spec :
    mulCoeffTwo KData X4NLK2Data 15 71 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 71 0 := by
  decide

private theorem x4NLK3Row15Coeff72_spec :
    mulCoeffTwo KData X4NLK2Data 15 72 =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD 72 0 := by
  decide

private theorem x4NLK3Row15Coeffs0To9_spec (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo KData X4NLK2Data 15 j =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row15Coeff0_spec
  · exact x4NLK3Row15Coeff1_spec
  · exact x4NLK3Row15Coeff2_spec
  · exact x4NLK3Row15Coeff3_spec
  · exact x4NLK3Row15Coeff4_spec
  · exact x4NLK3Row15Coeff5_spec
  · exact x4NLK3Row15Coeff6_spec
  · exact x4NLK3Row15Coeff7_spec
  · exact x4NLK3Row15Coeff8_spec
  · exact x4NLK3Row15Coeff9_spec

private theorem x4NLK3Row15Coeffs10To19_spec (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo KData X4NLK2Data 15 j =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row15Coeff10_spec
  · exact x4NLK3Row15Coeff11_spec
  · exact x4NLK3Row15Coeff12_spec
  · exact x4NLK3Row15Coeff13_spec
  · exact x4NLK3Row15Coeff14_spec
  · exact x4NLK3Row15Coeff15_spec
  · exact x4NLK3Row15Coeff16_spec
  · exact x4NLK3Row15Coeff17_spec
  · exact x4NLK3Row15Coeff18_spec
  · exact x4NLK3Row15Coeff19_spec

private theorem x4NLK3Row15Coeffs20To29_spec (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo KData X4NLK2Data 15 j =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row15Coeff20_spec
  · exact x4NLK3Row15Coeff21_spec
  · exact x4NLK3Row15Coeff22_spec
  · exact x4NLK3Row15Coeff23_spec
  · exact x4NLK3Row15Coeff24_spec
  · exact x4NLK3Row15Coeff25_spec
  · exact x4NLK3Row15Coeff26_spec
  · exact x4NLK3Row15Coeff27_spec
  · exact x4NLK3Row15Coeff28_spec
  · exact x4NLK3Row15Coeff29_spec

private theorem x4NLK3Row15Coeffs30To39_spec (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo KData X4NLK2Data 15 j =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row15Coeff30_spec
  · exact x4NLK3Row15Coeff31_spec
  · exact x4NLK3Row15Coeff32_spec
  · exact x4NLK3Row15Coeff33_spec
  · exact x4NLK3Row15Coeff34_spec
  · exact x4NLK3Row15Coeff35_spec
  · exact x4NLK3Row15Coeff36_spec
  · exact x4NLK3Row15Coeff37_spec
  · exact x4NLK3Row15Coeff38_spec
  · exact x4NLK3Row15Coeff39_spec

private theorem x4NLK3Row15Coeffs40To49_spec (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo KData X4NLK2Data 15 j =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row15Coeff40_spec
  · exact x4NLK3Row15Coeff41_spec
  · exact x4NLK3Row15Coeff42_spec
  · exact x4NLK3Row15Coeff43_spec
  · exact x4NLK3Row15Coeff44_spec
  · exact x4NLK3Row15Coeff45_spec
  · exact x4NLK3Row15Coeff46_spec
  · exact x4NLK3Row15Coeff47_spec
  · exact x4NLK3Row15Coeff48_spec
  · exact x4NLK3Row15Coeff49_spec

private theorem x4NLK3Row15Coeffs50To59_spec (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo KData X4NLK2Data 15 j =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row15Coeff50_spec
  · exact x4NLK3Row15Coeff51_spec
  · exact x4NLK3Row15Coeff52_spec
  · exact x4NLK3Row15Coeff53_spec
  · exact x4NLK3Row15Coeff54_spec
  · exact x4NLK3Row15Coeff55_spec
  · exact x4NLK3Row15Coeff56_spec
  · exact x4NLK3Row15Coeff57_spec
  · exact x4NLK3Row15Coeff58_spec
  · exact x4NLK3Row15Coeff59_spec

private theorem x4NLK3Row15Coeffs60To69_spec (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo KData X4NLK2Data 15 j =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row15Coeff60_spec
  · exact x4NLK3Row15Coeff61_spec
  · exact x4NLK3Row15Coeff62_spec
  · exact x4NLK3Row15Coeff63_spec
  · exact x4NLK3Row15Coeff64_spec
  · exact x4NLK3Row15Coeff65_spec
  · exact x4NLK3Row15Coeff66_spec
  · exact x4NLK3Row15Coeff67_spec
  · exact x4NLK3Row15Coeff68_spec
  · exact x4NLK3Row15Coeff69_spec

private theorem x4NLK3Row15Coeffs70To72_spec (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 73) :
    mulCoeffTwo KData X4NLK2Data 15 j =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 := by
    omega
  rcases hCases with
    rfl | rfl | rfl
  · exact x4NLK3Row15Coeff70_spec
  · exact x4NLK3Row15Coeff71_spec
  · exact x4NLK3Row15Coeff72_spec

private theorem x4NLK3Row15_coefficients (j : ℕ) (hj : j < 73) :
    mulCoeffTwo KData X4NLK2Data 15 j =
      ((rectangularize 53 73 X4NLK3Data).getD 15 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact x4NLK3Row15Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact x4NLK3Row15Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact x4NLK3Row15Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact x4NLK3Row15Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact x4NLK3Row15Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact x4NLK3Row15Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact x4NLK3Row15Coeffs60To69_spec j (by omega) h70
  exact x4NLK3Row15Coeffs70To72_spec j (by omega) hj

private theorem x4NLK3Row15_spec :
    padOne 73 (mulRow KData X4NLK2Data 15) =
      (rectangularize 53 73 X4NLK3Data).getD 15 [] := by
  apply padOne_mulRow_eq_of_coefficients 73 KData X4NLK2Data 15
    ((rectangularize 53 73 X4NLK3Data).getD 15 [])
  · decide
  · have hTargetSupport : (X4NLK3Data.getD 15 []).length ≤ 73 := by
      decide
    rw [getD_rectangularize 53 73 X4NLK3Data 15 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact x4NLK3Row15_coefficients

private theorem x4NLK3Row16Coeff0_spec :
    mulCoeffTwo KData X4NLK2Data 16 0 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 0 0 := by
  decide

private theorem x4NLK3Row16Coeff1_spec :
    mulCoeffTwo KData X4NLK2Data 16 1 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 1 0 := by
  decide

private theorem x4NLK3Row16Coeff2_spec :
    mulCoeffTwo KData X4NLK2Data 16 2 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 2 0 := by
  decide

private theorem x4NLK3Row16Coeff3_spec :
    mulCoeffTwo KData X4NLK2Data 16 3 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 3 0 := by
  decide

private theorem x4NLK3Row16Coeff4_spec :
    mulCoeffTwo KData X4NLK2Data 16 4 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 4 0 := by
  decide

private theorem x4NLK3Row16Coeff5_spec :
    mulCoeffTwo KData X4NLK2Data 16 5 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 5 0 := by
  decide

private theorem x4NLK3Row16Coeff6_spec :
    mulCoeffTwo KData X4NLK2Data 16 6 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 6 0 := by
  decide

private theorem x4NLK3Row16Coeff7_spec :
    mulCoeffTwo KData X4NLK2Data 16 7 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 7 0 := by
  decide

private theorem x4NLK3Row16Coeff8_spec :
    mulCoeffTwo KData X4NLK2Data 16 8 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 8 0 := by
  decide

private theorem x4NLK3Row16Coeff9_spec :
    mulCoeffTwo KData X4NLK2Data 16 9 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 9 0 := by
  decide

private theorem x4NLK3Row16Coeff10_spec :
    mulCoeffTwo KData X4NLK2Data 16 10 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 10 0 := by
  decide

private theorem x4NLK3Row16Coeff11_spec :
    mulCoeffTwo KData X4NLK2Data 16 11 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 11 0 := by
  decide

private theorem x4NLK3Row16Coeff12_spec :
    mulCoeffTwo KData X4NLK2Data 16 12 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 12 0 := by
  decide

private theorem x4NLK3Row16Coeff13_spec :
    mulCoeffTwo KData X4NLK2Data 16 13 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 13 0 := by
  decide

private theorem x4NLK3Row16Coeff14_spec :
    mulCoeffTwo KData X4NLK2Data 16 14 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 14 0 := by
  decide

private theorem x4NLK3Row16Coeff15_spec :
    mulCoeffTwo KData X4NLK2Data 16 15 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 15 0 := by
  decide

private theorem x4NLK3Row16Coeff16_spec :
    mulCoeffTwo KData X4NLK2Data 16 16 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 16 0 := by
  decide

private theorem x4NLK3Row16Coeff17_spec :
    mulCoeffTwo KData X4NLK2Data 16 17 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 17 0 := by
  decide

private theorem x4NLK3Row16Coeff18_spec :
    mulCoeffTwo KData X4NLK2Data 16 18 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 18 0 := by
  decide

private theorem x4NLK3Row16Coeff19_spec :
    mulCoeffTwo KData X4NLK2Data 16 19 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 19 0 := by
  decide

private theorem x4NLK3Row16Coeff20_spec :
    mulCoeffTwo KData X4NLK2Data 16 20 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 20 0 := by
  decide

private theorem x4NLK3Row16Coeff21_spec :
    mulCoeffTwo KData X4NLK2Data 16 21 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 21 0 := by
  decide

private theorem x4NLK3Row16Coeff22_spec :
    mulCoeffTwo KData X4NLK2Data 16 22 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 22 0 := by
  decide

private theorem x4NLK3Row16Coeff23_spec :
    mulCoeffTwo KData X4NLK2Data 16 23 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 23 0 := by
  decide

private theorem x4NLK3Row16Coeff24_spec :
    mulCoeffTwo KData X4NLK2Data 16 24 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 24 0 := by
  decide

private theorem x4NLK3Row16Coeff25_spec :
    mulCoeffTwo KData X4NLK2Data 16 25 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 25 0 := by
  decide

private theorem x4NLK3Row16Coeff26_spec :
    mulCoeffTwo KData X4NLK2Data 16 26 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 26 0 := by
  decide

private theorem x4NLK3Row16Coeff27_spec :
    mulCoeffTwo KData X4NLK2Data 16 27 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 27 0 := by
  decide

private theorem x4NLK3Row16Coeff28_spec :
    mulCoeffTwo KData X4NLK2Data 16 28 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 28 0 := by
  decide

private theorem x4NLK3Row16Coeff29_spec :
    mulCoeffTwo KData X4NLK2Data 16 29 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 29 0 := by
  decide

private theorem x4NLK3Row16Coeff30_spec :
    mulCoeffTwo KData X4NLK2Data 16 30 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 30 0 := by
  decide

private theorem x4NLK3Row16Coeff31_spec :
    mulCoeffTwo KData X4NLK2Data 16 31 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 31 0 := by
  decide

private theorem x4NLK3Row16Coeff32_spec :
    mulCoeffTwo KData X4NLK2Data 16 32 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 32 0 := by
  decide

private theorem x4NLK3Row16Coeff33_spec :
    mulCoeffTwo KData X4NLK2Data 16 33 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 33 0 := by
  decide

private theorem x4NLK3Row16Coeff34_spec :
    mulCoeffTwo KData X4NLK2Data 16 34 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 34 0 := by
  decide

private theorem x4NLK3Row16Coeff35_spec :
    mulCoeffTwo KData X4NLK2Data 16 35 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 35 0 := by
  decide

private theorem x4NLK3Row16Coeff36_spec :
    mulCoeffTwo KData X4NLK2Data 16 36 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 36 0 := by
  decide

private theorem x4NLK3Row16Coeff37_spec :
    mulCoeffTwo KData X4NLK2Data 16 37 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 37 0 := by
  decide

private theorem x4NLK3Row16Coeff38_spec :
    mulCoeffTwo KData X4NLK2Data 16 38 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 38 0 := by
  decide

private theorem x4NLK3Row16Coeff39_spec :
    mulCoeffTwo KData X4NLK2Data 16 39 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 39 0 := by
  decide

private theorem x4NLK3Row16Coeff40_spec :
    mulCoeffTwo KData X4NLK2Data 16 40 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 40 0 := by
  decide

private theorem x4NLK3Row16Coeff41_spec :
    mulCoeffTwo KData X4NLK2Data 16 41 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 41 0 := by
  decide

private theorem x4NLK3Row16Coeff42_spec :
    mulCoeffTwo KData X4NLK2Data 16 42 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 42 0 := by
  decide

private theorem x4NLK3Row16Coeff43_spec :
    mulCoeffTwo KData X4NLK2Data 16 43 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 43 0 := by
  decide

private theorem x4NLK3Row16Coeff44_spec :
    mulCoeffTwo KData X4NLK2Data 16 44 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 44 0 := by
  decide

private theorem x4NLK3Row16Coeff45_spec :
    mulCoeffTwo KData X4NLK2Data 16 45 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 45 0 := by
  decide

private theorem x4NLK3Row16Coeff46_spec :
    mulCoeffTwo KData X4NLK2Data 16 46 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 46 0 := by
  decide

private theorem x4NLK3Row16Coeff47_spec :
    mulCoeffTwo KData X4NLK2Data 16 47 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 47 0 := by
  decide

private theorem x4NLK3Row16Coeff48_spec :
    mulCoeffTwo KData X4NLK2Data 16 48 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 48 0 := by
  decide

private theorem x4NLK3Row16Coeff49_spec :
    mulCoeffTwo KData X4NLK2Data 16 49 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 49 0 := by
  decide

private theorem x4NLK3Row16Coeff50_spec :
    mulCoeffTwo KData X4NLK2Data 16 50 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 50 0 := by
  decide

private theorem x4NLK3Row16Coeff51_spec :
    mulCoeffTwo KData X4NLK2Data 16 51 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 51 0 := by
  decide

private theorem x4NLK3Row16Coeff52_spec :
    mulCoeffTwo KData X4NLK2Data 16 52 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 52 0 := by
  decide

private theorem x4NLK3Row16Coeff53_spec :
    mulCoeffTwo KData X4NLK2Data 16 53 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 53 0 := by
  decide

private theorem x4NLK3Row16Coeff54_spec :
    mulCoeffTwo KData X4NLK2Data 16 54 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 54 0 := by
  decide

private theorem x4NLK3Row16Coeff55_spec :
    mulCoeffTwo KData X4NLK2Data 16 55 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 55 0 := by
  decide

private theorem x4NLK3Row16Coeff56_spec :
    mulCoeffTwo KData X4NLK2Data 16 56 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 56 0 := by
  decide

private theorem x4NLK3Row16Coeff57_spec :
    mulCoeffTwo KData X4NLK2Data 16 57 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 57 0 := by
  decide

private theorem x4NLK3Row16Coeff58_spec :
    mulCoeffTwo KData X4NLK2Data 16 58 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 58 0 := by
  decide

private theorem x4NLK3Row16Coeff59_spec :
    mulCoeffTwo KData X4NLK2Data 16 59 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 59 0 := by
  decide

private theorem x4NLK3Row16Coeff60_spec :
    mulCoeffTwo KData X4NLK2Data 16 60 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 60 0 := by
  decide

private theorem x4NLK3Row16Coeff61_spec :
    mulCoeffTwo KData X4NLK2Data 16 61 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 61 0 := by
  decide

private theorem x4NLK3Row16Coeff62_spec :
    mulCoeffTwo KData X4NLK2Data 16 62 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 62 0 := by
  decide

private theorem x4NLK3Row16Coeff63_spec :
    mulCoeffTwo KData X4NLK2Data 16 63 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 63 0 := by
  decide

private theorem x4NLK3Row16Coeff64_spec :
    mulCoeffTwo KData X4NLK2Data 16 64 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 64 0 := by
  decide

private theorem x4NLK3Row16Coeff65_spec :
    mulCoeffTwo KData X4NLK2Data 16 65 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 65 0 := by
  decide

private theorem x4NLK3Row16Coeff66_spec :
    mulCoeffTwo KData X4NLK2Data 16 66 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 66 0 := by
  decide

private theorem x4NLK3Row16Coeff67_spec :
    mulCoeffTwo KData X4NLK2Data 16 67 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 67 0 := by
  decide

private theorem x4NLK3Row16Coeff68_spec :
    mulCoeffTwo KData X4NLK2Data 16 68 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 68 0 := by
  decide

private theorem x4NLK3Row16Coeff69_spec :
    mulCoeffTwo KData X4NLK2Data 16 69 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 69 0 := by
  decide

private theorem x4NLK3Row16Coeff70_spec :
    mulCoeffTwo KData X4NLK2Data 16 70 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 70 0 := by
  decide

private theorem x4NLK3Row16Coeff71_spec :
    mulCoeffTwo KData X4NLK2Data 16 71 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 71 0 := by
  decide

private theorem x4NLK3Row16Coeff72_spec :
    mulCoeffTwo KData X4NLK2Data 16 72 =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD 72 0 := by
  decide

private theorem x4NLK3Row16Coeffs0To9_spec (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo KData X4NLK2Data 16 j =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row16Coeff0_spec
  · exact x4NLK3Row16Coeff1_spec
  · exact x4NLK3Row16Coeff2_spec
  · exact x4NLK3Row16Coeff3_spec
  · exact x4NLK3Row16Coeff4_spec
  · exact x4NLK3Row16Coeff5_spec
  · exact x4NLK3Row16Coeff6_spec
  · exact x4NLK3Row16Coeff7_spec
  · exact x4NLK3Row16Coeff8_spec
  · exact x4NLK3Row16Coeff9_spec

private theorem x4NLK3Row16Coeffs10To19_spec (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo KData X4NLK2Data 16 j =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row16Coeff10_spec
  · exact x4NLK3Row16Coeff11_spec
  · exact x4NLK3Row16Coeff12_spec
  · exact x4NLK3Row16Coeff13_spec
  · exact x4NLK3Row16Coeff14_spec
  · exact x4NLK3Row16Coeff15_spec
  · exact x4NLK3Row16Coeff16_spec
  · exact x4NLK3Row16Coeff17_spec
  · exact x4NLK3Row16Coeff18_spec
  · exact x4NLK3Row16Coeff19_spec

private theorem x4NLK3Row16Coeffs20To29_spec (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo KData X4NLK2Data 16 j =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row16Coeff20_spec
  · exact x4NLK3Row16Coeff21_spec
  · exact x4NLK3Row16Coeff22_spec
  · exact x4NLK3Row16Coeff23_spec
  · exact x4NLK3Row16Coeff24_spec
  · exact x4NLK3Row16Coeff25_spec
  · exact x4NLK3Row16Coeff26_spec
  · exact x4NLK3Row16Coeff27_spec
  · exact x4NLK3Row16Coeff28_spec
  · exact x4NLK3Row16Coeff29_spec

private theorem x4NLK3Row16Coeffs30To39_spec (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo KData X4NLK2Data 16 j =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row16Coeff30_spec
  · exact x4NLK3Row16Coeff31_spec
  · exact x4NLK3Row16Coeff32_spec
  · exact x4NLK3Row16Coeff33_spec
  · exact x4NLK3Row16Coeff34_spec
  · exact x4NLK3Row16Coeff35_spec
  · exact x4NLK3Row16Coeff36_spec
  · exact x4NLK3Row16Coeff37_spec
  · exact x4NLK3Row16Coeff38_spec
  · exact x4NLK3Row16Coeff39_spec

private theorem x4NLK3Row16Coeffs40To49_spec (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo KData X4NLK2Data 16 j =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row16Coeff40_spec
  · exact x4NLK3Row16Coeff41_spec
  · exact x4NLK3Row16Coeff42_spec
  · exact x4NLK3Row16Coeff43_spec
  · exact x4NLK3Row16Coeff44_spec
  · exact x4NLK3Row16Coeff45_spec
  · exact x4NLK3Row16Coeff46_spec
  · exact x4NLK3Row16Coeff47_spec
  · exact x4NLK3Row16Coeff48_spec
  · exact x4NLK3Row16Coeff49_spec

private theorem x4NLK3Row16Coeffs50To59_spec (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo KData X4NLK2Data 16 j =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row16Coeff50_spec
  · exact x4NLK3Row16Coeff51_spec
  · exact x4NLK3Row16Coeff52_spec
  · exact x4NLK3Row16Coeff53_spec
  · exact x4NLK3Row16Coeff54_spec
  · exact x4NLK3Row16Coeff55_spec
  · exact x4NLK3Row16Coeff56_spec
  · exact x4NLK3Row16Coeff57_spec
  · exact x4NLK3Row16Coeff58_spec
  · exact x4NLK3Row16Coeff59_spec

private theorem x4NLK3Row16Coeffs60To69_spec (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo KData X4NLK2Data 16 j =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row16Coeff60_spec
  · exact x4NLK3Row16Coeff61_spec
  · exact x4NLK3Row16Coeff62_spec
  · exact x4NLK3Row16Coeff63_spec
  · exact x4NLK3Row16Coeff64_spec
  · exact x4NLK3Row16Coeff65_spec
  · exact x4NLK3Row16Coeff66_spec
  · exact x4NLK3Row16Coeff67_spec
  · exact x4NLK3Row16Coeff68_spec
  · exact x4NLK3Row16Coeff69_spec

private theorem x4NLK3Row16Coeffs70To72_spec (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 73) :
    mulCoeffTwo KData X4NLK2Data 16 j =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 := by
    omega
  rcases hCases with
    rfl | rfl | rfl
  · exact x4NLK3Row16Coeff70_spec
  · exact x4NLK3Row16Coeff71_spec
  · exact x4NLK3Row16Coeff72_spec

private theorem x4NLK3Row16_coefficients (j : ℕ) (hj : j < 73) :
    mulCoeffTwo KData X4NLK2Data 16 j =
      ((rectangularize 53 73 X4NLK3Data).getD 16 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact x4NLK3Row16Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact x4NLK3Row16Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact x4NLK3Row16Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact x4NLK3Row16Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact x4NLK3Row16Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact x4NLK3Row16Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact x4NLK3Row16Coeffs60To69_spec j (by omega) h70
  exact x4NLK3Row16Coeffs70To72_spec j (by omega) hj

private theorem x4NLK3Row16_spec :
    padOne 73 (mulRow KData X4NLK2Data 16) =
      (rectangularize 53 73 X4NLK3Data).getD 16 [] := by
  apply padOne_mulRow_eq_of_coefficients 73 KData X4NLK2Data 16
    ((rectangularize 53 73 X4NLK3Data).getD 16 [])
  · decide
  · have hTargetSupport : (X4NLK3Data.getD 16 []).length ≤ 73 := by
      decide
    rw [getD_rectangularize 53 73 X4NLK3Data 16 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact x4NLK3Row16_coefficients

private theorem x4NLK3Row17Coeff0_spec :
    mulCoeffTwo KData X4NLK2Data 17 0 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 0 0 := by
  decide

private theorem x4NLK3Row17Coeff1_spec :
    mulCoeffTwo KData X4NLK2Data 17 1 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 1 0 := by
  decide

private theorem x4NLK3Row17Coeff2_spec :
    mulCoeffTwo KData X4NLK2Data 17 2 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 2 0 := by
  decide

private theorem x4NLK3Row17Coeff3_spec :
    mulCoeffTwo KData X4NLK2Data 17 3 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 3 0 := by
  decide

private theorem x4NLK3Row17Coeff4_spec :
    mulCoeffTwo KData X4NLK2Data 17 4 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 4 0 := by
  decide

private theorem x4NLK3Row17Coeff5_spec :
    mulCoeffTwo KData X4NLK2Data 17 5 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 5 0 := by
  decide

private theorem x4NLK3Row17Coeff6_spec :
    mulCoeffTwo KData X4NLK2Data 17 6 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 6 0 := by
  decide

private theorem x4NLK3Row17Coeff7_spec :
    mulCoeffTwo KData X4NLK2Data 17 7 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 7 0 := by
  decide

private theorem x4NLK3Row17Coeff8_spec :
    mulCoeffTwo KData X4NLK2Data 17 8 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 8 0 := by
  decide

private theorem x4NLK3Row17Coeff9_spec :
    mulCoeffTwo KData X4NLK2Data 17 9 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 9 0 := by
  decide

private theorem x4NLK3Row17Coeff10_spec :
    mulCoeffTwo KData X4NLK2Data 17 10 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 10 0 := by
  decide

private theorem x4NLK3Row17Coeff11_spec :
    mulCoeffTwo KData X4NLK2Data 17 11 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 11 0 := by
  decide

private theorem x4NLK3Row17Coeff12_spec :
    mulCoeffTwo KData X4NLK2Data 17 12 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 12 0 := by
  decide

private theorem x4NLK3Row17Coeff13_spec :
    mulCoeffTwo KData X4NLK2Data 17 13 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 13 0 := by
  decide

private theorem x4NLK3Row17Coeff14_spec :
    mulCoeffTwo KData X4NLK2Data 17 14 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 14 0 := by
  decide

private theorem x4NLK3Row17Coeff15_spec :
    mulCoeffTwo KData X4NLK2Data 17 15 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 15 0 := by
  decide

private theorem x4NLK3Row17Coeff16_spec :
    mulCoeffTwo KData X4NLK2Data 17 16 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 16 0 := by
  decide

private theorem x4NLK3Row17Coeff17_spec :
    mulCoeffTwo KData X4NLK2Data 17 17 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 17 0 := by
  decide

private theorem x4NLK3Row17Coeff18_spec :
    mulCoeffTwo KData X4NLK2Data 17 18 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 18 0 := by
  decide

private theorem x4NLK3Row17Coeff19_spec :
    mulCoeffTwo KData X4NLK2Data 17 19 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 19 0 := by
  decide

private theorem x4NLK3Row17Coeff20_spec :
    mulCoeffTwo KData X4NLK2Data 17 20 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 20 0 := by
  decide

private theorem x4NLK3Row17Coeff21_spec :
    mulCoeffTwo KData X4NLK2Data 17 21 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 21 0 := by
  decide

private theorem x4NLK3Row17Coeff22_spec :
    mulCoeffTwo KData X4NLK2Data 17 22 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 22 0 := by
  decide

private theorem x4NLK3Row17Coeff23_spec :
    mulCoeffTwo KData X4NLK2Data 17 23 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 23 0 := by
  decide

private theorem x4NLK3Row17Coeff24_spec :
    mulCoeffTwo KData X4NLK2Data 17 24 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 24 0 := by
  decide

private theorem x4NLK3Row17Coeff25_spec :
    mulCoeffTwo KData X4NLK2Data 17 25 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 25 0 := by
  decide

private theorem x4NLK3Row17Coeff26_spec :
    mulCoeffTwo KData X4NLK2Data 17 26 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 26 0 := by
  decide

private theorem x4NLK3Row17Coeff27_spec :
    mulCoeffTwo KData X4NLK2Data 17 27 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 27 0 := by
  decide

private theorem x4NLK3Row17Coeff28_spec :
    mulCoeffTwo KData X4NLK2Data 17 28 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 28 0 := by
  decide

private theorem x4NLK3Row17Coeff29_spec :
    mulCoeffTwo KData X4NLK2Data 17 29 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 29 0 := by
  decide

private theorem x4NLK3Row17Coeff30_spec :
    mulCoeffTwo KData X4NLK2Data 17 30 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 30 0 := by
  decide

private theorem x4NLK3Row17Coeff31_spec :
    mulCoeffTwo KData X4NLK2Data 17 31 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 31 0 := by
  decide

private theorem x4NLK3Row17Coeff32_spec :
    mulCoeffTwo KData X4NLK2Data 17 32 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 32 0 := by
  decide

private theorem x4NLK3Row17Coeff33_spec :
    mulCoeffTwo KData X4NLK2Data 17 33 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 33 0 := by
  decide

private theorem x4NLK3Row17Coeff34_spec :
    mulCoeffTwo KData X4NLK2Data 17 34 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 34 0 := by
  decide

private theorem x4NLK3Row17Coeff35_spec :
    mulCoeffTwo KData X4NLK2Data 17 35 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 35 0 := by
  decide

private theorem x4NLK3Row17Coeff36_spec :
    mulCoeffTwo KData X4NLK2Data 17 36 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 36 0 := by
  decide

private theorem x4NLK3Row17Coeff37_spec :
    mulCoeffTwo KData X4NLK2Data 17 37 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 37 0 := by
  decide

private theorem x4NLK3Row17Coeff38_spec :
    mulCoeffTwo KData X4NLK2Data 17 38 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 38 0 := by
  decide

private theorem x4NLK3Row17Coeff39_spec :
    mulCoeffTwo KData X4NLK2Data 17 39 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 39 0 := by
  decide

private theorem x4NLK3Row17Coeff40_spec :
    mulCoeffTwo KData X4NLK2Data 17 40 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 40 0 := by
  decide

private theorem x4NLK3Row17Coeff41_spec :
    mulCoeffTwo KData X4NLK2Data 17 41 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 41 0 := by
  decide

private theorem x4NLK3Row17Coeff42_spec :
    mulCoeffTwo KData X4NLK2Data 17 42 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 42 0 := by
  decide

private theorem x4NLK3Row17Coeff43_spec :
    mulCoeffTwo KData X4NLK2Data 17 43 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 43 0 := by
  decide

private theorem x4NLK3Row17Coeff44_spec :
    mulCoeffTwo KData X4NLK2Data 17 44 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 44 0 := by
  decide

private theorem x4NLK3Row17Coeff45_spec :
    mulCoeffTwo KData X4NLK2Data 17 45 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 45 0 := by
  decide

private theorem x4NLK3Row17Coeff46_spec :
    mulCoeffTwo KData X4NLK2Data 17 46 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 46 0 := by
  decide

private theorem x4NLK3Row17Coeff47_spec :
    mulCoeffTwo KData X4NLK2Data 17 47 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 47 0 := by
  decide

private theorem x4NLK3Row17Coeff48_spec :
    mulCoeffTwo KData X4NLK2Data 17 48 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 48 0 := by
  decide

private theorem x4NLK3Row17Coeff49_spec :
    mulCoeffTwo KData X4NLK2Data 17 49 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 49 0 := by
  decide

private theorem x4NLK3Row17Coeff50_spec :
    mulCoeffTwo KData X4NLK2Data 17 50 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 50 0 := by
  decide

private theorem x4NLK3Row17Coeff51_spec :
    mulCoeffTwo KData X4NLK2Data 17 51 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 51 0 := by
  decide

private theorem x4NLK3Row17Coeff52_spec :
    mulCoeffTwo KData X4NLK2Data 17 52 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 52 0 := by
  decide

private theorem x4NLK3Row17Coeff53_spec :
    mulCoeffTwo KData X4NLK2Data 17 53 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 53 0 := by
  decide

private theorem x4NLK3Row17Coeff54_spec :
    mulCoeffTwo KData X4NLK2Data 17 54 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 54 0 := by
  decide

private theorem x4NLK3Row17Coeff55_spec :
    mulCoeffTwo KData X4NLK2Data 17 55 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 55 0 := by
  decide

private theorem x4NLK3Row17Coeff56_spec :
    mulCoeffTwo KData X4NLK2Data 17 56 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 56 0 := by
  decide

private theorem x4NLK3Row17Coeff57_spec :
    mulCoeffTwo KData X4NLK2Data 17 57 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 57 0 := by
  decide

private theorem x4NLK3Row17Coeff58_spec :
    mulCoeffTwo KData X4NLK2Data 17 58 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 58 0 := by
  decide

private theorem x4NLK3Row17Coeff59_spec :
    mulCoeffTwo KData X4NLK2Data 17 59 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 59 0 := by
  decide

private theorem x4NLK3Row17Coeff60_spec :
    mulCoeffTwo KData X4NLK2Data 17 60 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 60 0 := by
  decide

private theorem x4NLK3Row17Coeff61_spec :
    mulCoeffTwo KData X4NLK2Data 17 61 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 61 0 := by
  decide

private theorem x4NLK3Row17Coeff62_spec :
    mulCoeffTwo KData X4NLK2Data 17 62 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 62 0 := by
  decide

private theorem x4NLK3Row17Coeff63_spec :
    mulCoeffTwo KData X4NLK2Data 17 63 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 63 0 := by
  decide

private theorem x4NLK3Row17Coeff64_spec :
    mulCoeffTwo KData X4NLK2Data 17 64 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 64 0 := by
  decide

private theorem x4NLK3Row17Coeff65_spec :
    mulCoeffTwo KData X4NLK2Data 17 65 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 65 0 := by
  decide

private theorem x4NLK3Row17Coeff66_spec :
    mulCoeffTwo KData X4NLK2Data 17 66 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 66 0 := by
  decide

private theorem x4NLK3Row17Coeff67_spec :
    mulCoeffTwo KData X4NLK2Data 17 67 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 67 0 := by
  decide

private theorem x4NLK3Row17Coeff68_spec :
    mulCoeffTwo KData X4NLK2Data 17 68 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 68 0 := by
  decide

private theorem x4NLK3Row17Coeff69_spec :
    mulCoeffTwo KData X4NLK2Data 17 69 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 69 0 := by
  decide

private theorem x4NLK3Row17Coeff70_spec :
    mulCoeffTwo KData X4NLK2Data 17 70 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 70 0 := by
  decide

private theorem x4NLK3Row17Coeff71_spec :
    mulCoeffTwo KData X4NLK2Data 17 71 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 71 0 := by
  decide

private theorem x4NLK3Row17Coeff72_spec :
    mulCoeffTwo KData X4NLK2Data 17 72 =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD 72 0 := by
  decide

private theorem x4NLK3Row17Coeffs0To9_spec (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo KData X4NLK2Data 17 j =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row17Coeff0_spec
  · exact x4NLK3Row17Coeff1_spec
  · exact x4NLK3Row17Coeff2_spec
  · exact x4NLK3Row17Coeff3_spec
  · exact x4NLK3Row17Coeff4_spec
  · exact x4NLK3Row17Coeff5_spec
  · exact x4NLK3Row17Coeff6_spec
  · exact x4NLK3Row17Coeff7_spec
  · exact x4NLK3Row17Coeff8_spec
  · exact x4NLK3Row17Coeff9_spec

private theorem x4NLK3Row17Coeffs10To19_spec (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo KData X4NLK2Data 17 j =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row17Coeff10_spec
  · exact x4NLK3Row17Coeff11_spec
  · exact x4NLK3Row17Coeff12_spec
  · exact x4NLK3Row17Coeff13_spec
  · exact x4NLK3Row17Coeff14_spec
  · exact x4NLK3Row17Coeff15_spec
  · exact x4NLK3Row17Coeff16_spec
  · exact x4NLK3Row17Coeff17_spec
  · exact x4NLK3Row17Coeff18_spec
  · exact x4NLK3Row17Coeff19_spec

private theorem x4NLK3Row17Coeffs20To29_spec (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo KData X4NLK2Data 17 j =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row17Coeff20_spec
  · exact x4NLK3Row17Coeff21_spec
  · exact x4NLK3Row17Coeff22_spec
  · exact x4NLK3Row17Coeff23_spec
  · exact x4NLK3Row17Coeff24_spec
  · exact x4NLK3Row17Coeff25_spec
  · exact x4NLK3Row17Coeff26_spec
  · exact x4NLK3Row17Coeff27_spec
  · exact x4NLK3Row17Coeff28_spec
  · exact x4NLK3Row17Coeff29_spec

private theorem x4NLK3Row17Coeffs30To39_spec (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo KData X4NLK2Data 17 j =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row17Coeff30_spec
  · exact x4NLK3Row17Coeff31_spec
  · exact x4NLK3Row17Coeff32_spec
  · exact x4NLK3Row17Coeff33_spec
  · exact x4NLK3Row17Coeff34_spec
  · exact x4NLK3Row17Coeff35_spec
  · exact x4NLK3Row17Coeff36_spec
  · exact x4NLK3Row17Coeff37_spec
  · exact x4NLK3Row17Coeff38_spec
  · exact x4NLK3Row17Coeff39_spec

private theorem x4NLK3Row17Coeffs40To49_spec (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo KData X4NLK2Data 17 j =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row17Coeff40_spec
  · exact x4NLK3Row17Coeff41_spec
  · exact x4NLK3Row17Coeff42_spec
  · exact x4NLK3Row17Coeff43_spec
  · exact x4NLK3Row17Coeff44_spec
  · exact x4NLK3Row17Coeff45_spec
  · exact x4NLK3Row17Coeff46_spec
  · exact x4NLK3Row17Coeff47_spec
  · exact x4NLK3Row17Coeff48_spec
  · exact x4NLK3Row17Coeff49_spec

private theorem x4NLK3Row17Coeffs50To59_spec (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo KData X4NLK2Data 17 j =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row17Coeff50_spec
  · exact x4NLK3Row17Coeff51_spec
  · exact x4NLK3Row17Coeff52_spec
  · exact x4NLK3Row17Coeff53_spec
  · exact x4NLK3Row17Coeff54_spec
  · exact x4NLK3Row17Coeff55_spec
  · exact x4NLK3Row17Coeff56_spec
  · exact x4NLK3Row17Coeff57_spec
  · exact x4NLK3Row17Coeff58_spec
  · exact x4NLK3Row17Coeff59_spec

private theorem x4NLK3Row17Coeffs60To69_spec (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo KData X4NLK2Data 17 j =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row17Coeff60_spec
  · exact x4NLK3Row17Coeff61_spec
  · exact x4NLK3Row17Coeff62_spec
  · exact x4NLK3Row17Coeff63_spec
  · exact x4NLK3Row17Coeff64_spec
  · exact x4NLK3Row17Coeff65_spec
  · exact x4NLK3Row17Coeff66_spec
  · exact x4NLK3Row17Coeff67_spec
  · exact x4NLK3Row17Coeff68_spec
  · exact x4NLK3Row17Coeff69_spec

private theorem x4NLK3Row17Coeffs70To72_spec (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 73) :
    mulCoeffTwo KData X4NLK2Data 17 j =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 := by
    omega
  rcases hCases with
    rfl | rfl | rfl
  · exact x4NLK3Row17Coeff70_spec
  · exact x4NLK3Row17Coeff71_spec
  · exact x4NLK3Row17Coeff72_spec

private theorem x4NLK3Row17_coefficients (j : ℕ) (hj : j < 73) :
    mulCoeffTwo KData X4NLK2Data 17 j =
      ((rectangularize 53 73 X4NLK3Data).getD 17 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact x4NLK3Row17Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact x4NLK3Row17Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact x4NLK3Row17Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact x4NLK3Row17Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact x4NLK3Row17Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact x4NLK3Row17Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact x4NLK3Row17Coeffs60To69_spec j (by omega) h70
  exact x4NLK3Row17Coeffs70To72_spec j (by omega) hj

private theorem x4NLK3Row17_spec :
    padOne 73 (mulRow KData X4NLK2Data 17) =
      (rectangularize 53 73 X4NLK3Data).getD 17 [] := by
  apply padOne_mulRow_eq_of_coefficients 73 KData X4NLK2Data 17
    ((rectangularize 53 73 X4NLK3Data).getD 17 [])
  · decide
  · have hTargetSupport : (X4NLK3Data.getD 17 []).length ≤ 73 := by
      decide
    rw [getD_rectangularize 53 73 X4NLK3Data 17 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact x4NLK3Row17_coefficients

private theorem x4NLK3Row18Coeff0_spec :
    mulCoeffTwo KData X4NLK2Data 18 0 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 0 0 := by
  decide

private theorem x4NLK3Row18Coeff1_spec :
    mulCoeffTwo KData X4NLK2Data 18 1 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 1 0 := by
  decide

private theorem x4NLK3Row18Coeff2_spec :
    mulCoeffTwo KData X4NLK2Data 18 2 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 2 0 := by
  decide

private theorem x4NLK3Row18Coeff3_spec :
    mulCoeffTwo KData X4NLK2Data 18 3 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 3 0 := by
  decide

private theorem x4NLK3Row18Coeff4_spec :
    mulCoeffTwo KData X4NLK2Data 18 4 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 4 0 := by
  decide

private theorem x4NLK3Row18Coeff5_spec :
    mulCoeffTwo KData X4NLK2Data 18 5 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 5 0 := by
  decide

private theorem x4NLK3Row18Coeff6_spec :
    mulCoeffTwo KData X4NLK2Data 18 6 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 6 0 := by
  decide

private theorem x4NLK3Row18Coeff7_spec :
    mulCoeffTwo KData X4NLK2Data 18 7 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 7 0 := by
  decide

private theorem x4NLK3Row18Coeff8_spec :
    mulCoeffTwo KData X4NLK2Data 18 8 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 8 0 := by
  decide

private theorem x4NLK3Row18Coeff9_spec :
    mulCoeffTwo KData X4NLK2Data 18 9 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 9 0 := by
  decide

private theorem x4NLK3Row18Coeff10_spec :
    mulCoeffTwo KData X4NLK2Data 18 10 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 10 0 := by
  decide

private theorem x4NLK3Row18Coeff11_spec :
    mulCoeffTwo KData X4NLK2Data 18 11 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 11 0 := by
  decide

private theorem x4NLK3Row18Coeff12_spec :
    mulCoeffTwo KData X4NLK2Data 18 12 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 12 0 := by
  decide

private theorem x4NLK3Row18Coeff13_spec :
    mulCoeffTwo KData X4NLK2Data 18 13 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 13 0 := by
  decide

private theorem x4NLK3Row18Coeff14_spec :
    mulCoeffTwo KData X4NLK2Data 18 14 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 14 0 := by
  decide

private theorem x4NLK3Row18Coeff15_spec :
    mulCoeffTwo KData X4NLK2Data 18 15 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 15 0 := by
  decide

private theorem x4NLK3Row18Coeff16_spec :
    mulCoeffTwo KData X4NLK2Data 18 16 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 16 0 := by
  decide

private theorem x4NLK3Row18Coeff17_spec :
    mulCoeffTwo KData X4NLK2Data 18 17 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 17 0 := by
  decide

private theorem x4NLK3Row18Coeff18_spec :
    mulCoeffTwo KData X4NLK2Data 18 18 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 18 0 := by
  decide

private theorem x4NLK3Row18Coeff19_spec :
    mulCoeffTwo KData X4NLK2Data 18 19 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 19 0 := by
  decide

private theorem x4NLK3Row18Coeff20_spec :
    mulCoeffTwo KData X4NLK2Data 18 20 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 20 0 := by
  decide

private theorem x4NLK3Row18Coeff21_spec :
    mulCoeffTwo KData X4NLK2Data 18 21 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 21 0 := by
  decide

private theorem x4NLK3Row18Coeff22_spec :
    mulCoeffTwo KData X4NLK2Data 18 22 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 22 0 := by
  decide

private theorem x4NLK3Row18Coeff23_spec :
    mulCoeffTwo KData X4NLK2Data 18 23 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 23 0 := by
  decide

private theorem x4NLK3Row18Coeff24_spec :
    mulCoeffTwo KData X4NLK2Data 18 24 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 24 0 := by
  decide

private theorem x4NLK3Row18Coeff25_spec :
    mulCoeffTwo KData X4NLK2Data 18 25 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 25 0 := by
  decide

private theorem x4NLK3Row18Coeff26_spec :
    mulCoeffTwo KData X4NLK2Data 18 26 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 26 0 := by
  decide

private theorem x4NLK3Row18Coeff27_spec :
    mulCoeffTwo KData X4NLK2Data 18 27 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 27 0 := by
  decide

private theorem x4NLK3Row18Coeff28_spec :
    mulCoeffTwo KData X4NLK2Data 18 28 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 28 0 := by
  decide

private theorem x4NLK3Row18Coeff29_spec :
    mulCoeffTwo KData X4NLK2Data 18 29 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 29 0 := by
  decide

private theorem x4NLK3Row18Coeff30_spec :
    mulCoeffTwo KData X4NLK2Data 18 30 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 30 0 := by
  decide

private theorem x4NLK3Row18Coeff31_spec :
    mulCoeffTwo KData X4NLK2Data 18 31 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 31 0 := by
  decide

private theorem x4NLK3Row18Coeff32_spec :
    mulCoeffTwo KData X4NLK2Data 18 32 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 32 0 := by
  decide

private theorem x4NLK3Row18Coeff33_spec :
    mulCoeffTwo KData X4NLK2Data 18 33 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 33 0 := by
  decide

private theorem x4NLK3Row18Coeff34_spec :
    mulCoeffTwo KData X4NLK2Data 18 34 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 34 0 := by
  decide

private theorem x4NLK3Row18Coeff35_spec :
    mulCoeffTwo KData X4NLK2Data 18 35 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 35 0 := by
  decide

private theorem x4NLK3Row18Coeff36_spec :
    mulCoeffTwo KData X4NLK2Data 18 36 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 36 0 := by
  decide

private theorem x4NLK3Row18Coeff37_spec :
    mulCoeffTwo KData X4NLK2Data 18 37 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 37 0 := by
  decide

private theorem x4NLK3Row18Coeff38_spec :
    mulCoeffTwo KData X4NLK2Data 18 38 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 38 0 := by
  decide

private theorem x4NLK3Row18Coeff39_spec :
    mulCoeffTwo KData X4NLK2Data 18 39 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 39 0 := by
  decide

private theorem x4NLK3Row18Coeff40_spec :
    mulCoeffTwo KData X4NLK2Data 18 40 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 40 0 := by
  decide

private theorem x4NLK3Row18Coeff41_spec :
    mulCoeffTwo KData X4NLK2Data 18 41 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 41 0 := by
  decide

private theorem x4NLK3Row18Coeff42_spec :
    mulCoeffTwo KData X4NLK2Data 18 42 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 42 0 := by
  decide

private theorem x4NLK3Row18Coeff43_spec :
    mulCoeffTwo KData X4NLK2Data 18 43 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 43 0 := by
  decide

private theorem x4NLK3Row18Coeff44_spec :
    mulCoeffTwo KData X4NLK2Data 18 44 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 44 0 := by
  decide

private theorem x4NLK3Row18Coeff45_spec :
    mulCoeffTwo KData X4NLK2Data 18 45 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 45 0 := by
  decide

private theorem x4NLK3Row18Coeff46_spec :
    mulCoeffTwo KData X4NLK2Data 18 46 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 46 0 := by
  decide

private theorem x4NLK3Row18Coeff47_spec :
    mulCoeffTwo KData X4NLK2Data 18 47 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 47 0 := by
  decide

private theorem x4NLK3Row18Coeff48_spec :
    mulCoeffTwo KData X4NLK2Data 18 48 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 48 0 := by
  decide

private theorem x4NLK3Row18Coeff49_spec :
    mulCoeffTwo KData X4NLK2Data 18 49 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 49 0 := by
  decide

private theorem x4NLK3Row18Coeff50_spec :
    mulCoeffTwo KData X4NLK2Data 18 50 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 50 0 := by
  decide

private theorem x4NLK3Row18Coeff51_spec :
    mulCoeffTwo KData X4NLK2Data 18 51 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 51 0 := by
  decide

private theorem x4NLK3Row18Coeff52_spec :
    mulCoeffTwo KData X4NLK2Data 18 52 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 52 0 := by
  decide

private theorem x4NLK3Row18Coeff53_spec :
    mulCoeffTwo KData X4NLK2Data 18 53 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 53 0 := by
  decide

private theorem x4NLK3Row18Coeff54_spec :
    mulCoeffTwo KData X4NLK2Data 18 54 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 54 0 := by
  decide

private theorem x4NLK3Row18Coeff55_spec :
    mulCoeffTwo KData X4NLK2Data 18 55 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 55 0 := by
  decide

private theorem x4NLK3Row18Coeff56_spec :
    mulCoeffTwo KData X4NLK2Data 18 56 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 56 0 := by
  decide

private theorem x4NLK3Row18Coeff57_spec :
    mulCoeffTwo KData X4NLK2Data 18 57 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 57 0 := by
  decide

private theorem x4NLK3Row18Coeff58_spec :
    mulCoeffTwo KData X4NLK2Data 18 58 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 58 0 := by
  decide

private theorem x4NLK3Row18Coeff59_spec :
    mulCoeffTwo KData X4NLK2Data 18 59 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 59 0 := by
  decide

private theorem x4NLK3Row18Coeff60_spec :
    mulCoeffTwo KData X4NLK2Data 18 60 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 60 0 := by
  decide

private theorem x4NLK3Row18Coeff61_spec :
    mulCoeffTwo KData X4NLK2Data 18 61 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 61 0 := by
  decide

private theorem x4NLK3Row18Coeff62_spec :
    mulCoeffTwo KData X4NLK2Data 18 62 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 62 0 := by
  decide

private theorem x4NLK3Row18Coeff63_spec :
    mulCoeffTwo KData X4NLK2Data 18 63 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 63 0 := by
  decide

private theorem x4NLK3Row18Coeff64_spec :
    mulCoeffTwo KData X4NLK2Data 18 64 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 64 0 := by
  decide

private theorem x4NLK3Row18Coeff65_spec :
    mulCoeffTwo KData X4NLK2Data 18 65 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 65 0 := by
  decide

private theorem x4NLK3Row18Coeff66_spec :
    mulCoeffTwo KData X4NLK2Data 18 66 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 66 0 := by
  decide

private theorem x4NLK3Row18Coeff67_spec :
    mulCoeffTwo KData X4NLK2Data 18 67 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 67 0 := by
  decide

private theorem x4NLK3Row18Coeff68_spec :
    mulCoeffTwo KData X4NLK2Data 18 68 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 68 0 := by
  decide

private theorem x4NLK3Row18Coeff69_spec :
    mulCoeffTwo KData X4NLK2Data 18 69 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 69 0 := by
  decide

private theorem x4NLK3Row18Coeff70_spec :
    mulCoeffTwo KData X4NLK2Data 18 70 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 70 0 := by
  decide

private theorem x4NLK3Row18Coeff71_spec :
    mulCoeffTwo KData X4NLK2Data 18 71 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 71 0 := by
  decide

private theorem x4NLK3Row18Coeff72_spec :
    mulCoeffTwo KData X4NLK2Data 18 72 =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD 72 0 := by
  decide

private theorem x4NLK3Row18Coeffs0To9_spec (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo KData X4NLK2Data 18 j =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row18Coeff0_spec
  · exact x4NLK3Row18Coeff1_spec
  · exact x4NLK3Row18Coeff2_spec
  · exact x4NLK3Row18Coeff3_spec
  · exact x4NLK3Row18Coeff4_spec
  · exact x4NLK3Row18Coeff5_spec
  · exact x4NLK3Row18Coeff6_spec
  · exact x4NLK3Row18Coeff7_spec
  · exact x4NLK3Row18Coeff8_spec
  · exact x4NLK3Row18Coeff9_spec

private theorem x4NLK3Row18Coeffs10To19_spec (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo KData X4NLK2Data 18 j =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row18Coeff10_spec
  · exact x4NLK3Row18Coeff11_spec
  · exact x4NLK3Row18Coeff12_spec
  · exact x4NLK3Row18Coeff13_spec
  · exact x4NLK3Row18Coeff14_spec
  · exact x4NLK3Row18Coeff15_spec
  · exact x4NLK3Row18Coeff16_spec
  · exact x4NLK3Row18Coeff17_spec
  · exact x4NLK3Row18Coeff18_spec
  · exact x4NLK3Row18Coeff19_spec

private theorem x4NLK3Row18Coeffs20To29_spec (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo KData X4NLK2Data 18 j =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row18Coeff20_spec
  · exact x4NLK3Row18Coeff21_spec
  · exact x4NLK3Row18Coeff22_spec
  · exact x4NLK3Row18Coeff23_spec
  · exact x4NLK3Row18Coeff24_spec
  · exact x4NLK3Row18Coeff25_spec
  · exact x4NLK3Row18Coeff26_spec
  · exact x4NLK3Row18Coeff27_spec
  · exact x4NLK3Row18Coeff28_spec
  · exact x4NLK3Row18Coeff29_spec

private theorem x4NLK3Row18Coeffs30To39_spec (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo KData X4NLK2Data 18 j =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row18Coeff30_spec
  · exact x4NLK3Row18Coeff31_spec
  · exact x4NLK3Row18Coeff32_spec
  · exact x4NLK3Row18Coeff33_spec
  · exact x4NLK3Row18Coeff34_spec
  · exact x4NLK3Row18Coeff35_spec
  · exact x4NLK3Row18Coeff36_spec
  · exact x4NLK3Row18Coeff37_spec
  · exact x4NLK3Row18Coeff38_spec
  · exact x4NLK3Row18Coeff39_spec

private theorem x4NLK3Row18Coeffs40To49_spec (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo KData X4NLK2Data 18 j =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row18Coeff40_spec
  · exact x4NLK3Row18Coeff41_spec
  · exact x4NLK3Row18Coeff42_spec
  · exact x4NLK3Row18Coeff43_spec
  · exact x4NLK3Row18Coeff44_spec
  · exact x4NLK3Row18Coeff45_spec
  · exact x4NLK3Row18Coeff46_spec
  · exact x4NLK3Row18Coeff47_spec
  · exact x4NLK3Row18Coeff48_spec
  · exact x4NLK3Row18Coeff49_spec

private theorem x4NLK3Row18Coeffs50To59_spec (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo KData X4NLK2Data 18 j =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row18Coeff50_spec
  · exact x4NLK3Row18Coeff51_spec
  · exact x4NLK3Row18Coeff52_spec
  · exact x4NLK3Row18Coeff53_spec
  · exact x4NLK3Row18Coeff54_spec
  · exact x4NLK3Row18Coeff55_spec
  · exact x4NLK3Row18Coeff56_spec
  · exact x4NLK3Row18Coeff57_spec
  · exact x4NLK3Row18Coeff58_spec
  · exact x4NLK3Row18Coeff59_spec

private theorem x4NLK3Row18Coeffs60To69_spec (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo KData X4NLK2Data 18 j =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row18Coeff60_spec
  · exact x4NLK3Row18Coeff61_spec
  · exact x4NLK3Row18Coeff62_spec
  · exact x4NLK3Row18Coeff63_spec
  · exact x4NLK3Row18Coeff64_spec
  · exact x4NLK3Row18Coeff65_spec
  · exact x4NLK3Row18Coeff66_spec
  · exact x4NLK3Row18Coeff67_spec
  · exact x4NLK3Row18Coeff68_spec
  · exact x4NLK3Row18Coeff69_spec

private theorem x4NLK3Row18Coeffs70To72_spec (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 73) :
    mulCoeffTwo KData X4NLK2Data 18 j =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 := by
    omega
  rcases hCases with
    rfl | rfl | rfl
  · exact x4NLK3Row18Coeff70_spec
  · exact x4NLK3Row18Coeff71_spec
  · exact x4NLK3Row18Coeff72_spec

private theorem x4NLK3Row18_coefficients (j : ℕ) (hj : j < 73) :
    mulCoeffTwo KData X4NLK2Data 18 j =
      ((rectangularize 53 73 X4NLK3Data).getD 18 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact x4NLK3Row18Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact x4NLK3Row18Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact x4NLK3Row18Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact x4NLK3Row18Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact x4NLK3Row18Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact x4NLK3Row18Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact x4NLK3Row18Coeffs60To69_spec j (by omega) h70
  exact x4NLK3Row18Coeffs70To72_spec j (by omega) hj

private theorem x4NLK3Row18_spec :
    padOne 73 (mulRow KData X4NLK2Data 18) =
      (rectangularize 53 73 X4NLK3Data).getD 18 [] := by
  apply padOne_mulRow_eq_of_coefficients 73 KData X4NLK2Data 18
    ((rectangularize 53 73 X4NLK3Data).getD 18 [])
  · decide
  · have hTargetSupport : (X4NLK3Data.getD 18 []).length ≤ 73 := by
      decide
    rw [getD_rectangularize 53 73 X4NLK3Data 18 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact x4NLK3Row18_coefficients

private theorem x4NLK3Row19Coeff0_spec :
    mulCoeffTwo KData X4NLK2Data 19 0 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 0 0 := by
  decide

private theorem x4NLK3Row19Coeff1_spec :
    mulCoeffTwo KData X4NLK2Data 19 1 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 1 0 := by
  decide

private theorem x4NLK3Row19Coeff2_spec :
    mulCoeffTwo KData X4NLK2Data 19 2 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 2 0 := by
  decide

private theorem x4NLK3Row19Coeff3_spec :
    mulCoeffTwo KData X4NLK2Data 19 3 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 3 0 := by
  decide

private theorem x4NLK3Row19Coeff4_spec :
    mulCoeffTwo KData X4NLK2Data 19 4 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 4 0 := by
  decide

private theorem x4NLK3Row19Coeff5_spec :
    mulCoeffTwo KData X4NLK2Data 19 5 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 5 0 := by
  decide

private theorem x4NLK3Row19Coeff6_spec :
    mulCoeffTwo KData X4NLK2Data 19 6 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 6 0 := by
  decide

private theorem x4NLK3Row19Coeff7_spec :
    mulCoeffTwo KData X4NLK2Data 19 7 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 7 0 := by
  decide

private theorem x4NLK3Row19Coeff8_spec :
    mulCoeffTwo KData X4NLK2Data 19 8 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 8 0 := by
  decide

private theorem x4NLK3Row19Coeff9_spec :
    mulCoeffTwo KData X4NLK2Data 19 9 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 9 0 := by
  decide

private theorem x4NLK3Row19Coeff10_spec :
    mulCoeffTwo KData X4NLK2Data 19 10 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 10 0 := by
  decide

private theorem x4NLK3Row19Coeff11_spec :
    mulCoeffTwo KData X4NLK2Data 19 11 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 11 0 := by
  decide

private theorem x4NLK3Row19Coeff12_spec :
    mulCoeffTwo KData X4NLK2Data 19 12 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 12 0 := by
  decide

private theorem x4NLK3Row19Coeff13_spec :
    mulCoeffTwo KData X4NLK2Data 19 13 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 13 0 := by
  decide

private theorem x4NLK3Row19Coeff14_spec :
    mulCoeffTwo KData X4NLK2Data 19 14 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 14 0 := by
  decide

private theorem x4NLK3Row19Coeff15_spec :
    mulCoeffTwo KData X4NLK2Data 19 15 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 15 0 := by
  decide

private theorem x4NLK3Row19Coeff16_spec :
    mulCoeffTwo KData X4NLK2Data 19 16 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 16 0 := by
  decide

private theorem x4NLK3Row19Coeff17_spec :
    mulCoeffTwo KData X4NLK2Data 19 17 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 17 0 := by
  decide

private theorem x4NLK3Row19Coeff18_spec :
    mulCoeffTwo KData X4NLK2Data 19 18 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 18 0 := by
  decide

private theorem x4NLK3Row19Coeff19_spec :
    mulCoeffTwo KData X4NLK2Data 19 19 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 19 0 := by
  decide

private theorem x4NLK3Row19Coeff20_spec :
    mulCoeffTwo KData X4NLK2Data 19 20 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 20 0 := by
  decide

private theorem x4NLK3Row19Coeff21_spec :
    mulCoeffTwo KData X4NLK2Data 19 21 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 21 0 := by
  decide

private theorem x4NLK3Row19Coeff22_spec :
    mulCoeffTwo KData X4NLK2Data 19 22 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 22 0 := by
  decide

private theorem x4NLK3Row19Coeff23_spec :
    mulCoeffTwo KData X4NLK2Data 19 23 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 23 0 := by
  decide

private theorem x4NLK3Row19Coeff24_spec :
    mulCoeffTwo KData X4NLK2Data 19 24 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 24 0 := by
  decide

private theorem x4NLK3Row19Coeff25_spec :
    mulCoeffTwo KData X4NLK2Data 19 25 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 25 0 := by
  decide

private theorem x4NLK3Row19Coeff26_spec :
    mulCoeffTwo KData X4NLK2Data 19 26 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 26 0 := by
  decide

private theorem x4NLK3Row19Coeff27_spec :
    mulCoeffTwo KData X4NLK2Data 19 27 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 27 0 := by
  decide

private theorem x4NLK3Row19Coeff28_spec :
    mulCoeffTwo KData X4NLK2Data 19 28 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 28 0 := by
  decide

private theorem x4NLK3Row19Coeff29_spec :
    mulCoeffTwo KData X4NLK2Data 19 29 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 29 0 := by
  decide

private theorem x4NLK3Row19Coeff30_spec :
    mulCoeffTwo KData X4NLK2Data 19 30 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 30 0 := by
  decide

private theorem x4NLK3Row19Coeff31_spec :
    mulCoeffTwo KData X4NLK2Data 19 31 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 31 0 := by
  decide

private theorem x4NLK3Row19Coeff32_spec :
    mulCoeffTwo KData X4NLK2Data 19 32 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 32 0 := by
  decide

private theorem x4NLK3Row19Coeff33_spec :
    mulCoeffTwo KData X4NLK2Data 19 33 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 33 0 := by
  decide

private theorem x4NLK3Row19Coeff34_spec :
    mulCoeffTwo KData X4NLK2Data 19 34 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 34 0 := by
  decide

private theorem x4NLK3Row19Coeff35_spec :
    mulCoeffTwo KData X4NLK2Data 19 35 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 35 0 := by
  decide

private theorem x4NLK3Row19Coeff36_spec :
    mulCoeffTwo KData X4NLK2Data 19 36 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 36 0 := by
  decide

private theorem x4NLK3Row19Coeff37_spec :
    mulCoeffTwo KData X4NLK2Data 19 37 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 37 0 := by
  decide

private theorem x4NLK3Row19Coeff38_spec :
    mulCoeffTwo KData X4NLK2Data 19 38 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 38 0 := by
  decide

private theorem x4NLK3Row19Coeff39_spec :
    mulCoeffTwo KData X4NLK2Data 19 39 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 39 0 := by
  decide

private theorem x4NLK3Row19Coeff40_spec :
    mulCoeffTwo KData X4NLK2Data 19 40 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 40 0 := by
  decide

private theorem x4NLK3Row19Coeff41_spec :
    mulCoeffTwo KData X4NLK2Data 19 41 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 41 0 := by
  decide

private theorem x4NLK3Row19Coeff42_spec :
    mulCoeffTwo KData X4NLK2Data 19 42 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 42 0 := by
  decide

private theorem x4NLK3Row19Coeff43_spec :
    mulCoeffTwo KData X4NLK2Data 19 43 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 43 0 := by
  decide

private theorem x4NLK3Row19Coeff44_spec :
    mulCoeffTwo KData X4NLK2Data 19 44 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 44 0 := by
  decide

private theorem x4NLK3Row19Coeff45_spec :
    mulCoeffTwo KData X4NLK2Data 19 45 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 45 0 := by
  decide

private theorem x4NLK3Row19Coeff46_spec :
    mulCoeffTwo KData X4NLK2Data 19 46 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 46 0 := by
  decide

private theorem x4NLK3Row19Coeff47_spec :
    mulCoeffTwo KData X4NLK2Data 19 47 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 47 0 := by
  decide

private theorem x4NLK3Row19Coeff48_spec :
    mulCoeffTwo KData X4NLK2Data 19 48 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 48 0 := by
  decide

private theorem x4NLK3Row19Coeff49_spec :
    mulCoeffTwo KData X4NLK2Data 19 49 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 49 0 := by
  decide

private theorem x4NLK3Row19Coeff50_spec :
    mulCoeffTwo KData X4NLK2Data 19 50 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 50 0 := by
  decide

private theorem x4NLK3Row19Coeff51_spec :
    mulCoeffTwo KData X4NLK2Data 19 51 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 51 0 := by
  decide

private theorem x4NLK3Row19Coeff52_spec :
    mulCoeffTwo KData X4NLK2Data 19 52 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 52 0 := by
  decide

private theorem x4NLK3Row19Coeff53_spec :
    mulCoeffTwo KData X4NLK2Data 19 53 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 53 0 := by
  decide

private theorem x4NLK3Row19Coeff54_spec :
    mulCoeffTwo KData X4NLK2Data 19 54 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 54 0 := by
  decide

private theorem x4NLK3Row19Coeff55_spec :
    mulCoeffTwo KData X4NLK2Data 19 55 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 55 0 := by
  decide

private theorem x4NLK3Row19Coeff56_spec :
    mulCoeffTwo KData X4NLK2Data 19 56 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 56 0 := by
  decide

private theorem x4NLK3Row19Coeff57_spec :
    mulCoeffTwo KData X4NLK2Data 19 57 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 57 0 := by
  decide

private theorem x4NLK3Row19Coeff58_spec :
    mulCoeffTwo KData X4NLK2Data 19 58 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 58 0 := by
  decide

private theorem x4NLK3Row19Coeff59_spec :
    mulCoeffTwo KData X4NLK2Data 19 59 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 59 0 := by
  decide

private theorem x4NLK3Row19Coeff60_spec :
    mulCoeffTwo KData X4NLK2Data 19 60 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 60 0 := by
  decide

private theorem x4NLK3Row19Coeff61_spec :
    mulCoeffTwo KData X4NLK2Data 19 61 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 61 0 := by
  decide

private theorem x4NLK3Row19Coeff62_spec :
    mulCoeffTwo KData X4NLK2Data 19 62 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 62 0 := by
  decide

private theorem x4NLK3Row19Coeff63_spec :
    mulCoeffTwo KData X4NLK2Data 19 63 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 63 0 := by
  decide

private theorem x4NLK3Row19Coeff64_spec :
    mulCoeffTwo KData X4NLK2Data 19 64 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 64 0 := by
  decide

private theorem x4NLK3Row19Coeff65_spec :
    mulCoeffTwo KData X4NLK2Data 19 65 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 65 0 := by
  decide

private theorem x4NLK3Row19Coeff66_spec :
    mulCoeffTwo KData X4NLK2Data 19 66 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 66 0 := by
  decide

private theorem x4NLK3Row19Coeff67_spec :
    mulCoeffTwo KData X4NLK2Data 19 67 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 67 0 := by
  decide

private theorem x4NLK3Row19Coeff68_spec :
    mulCoeffTwo KData X4NLK2Data 19 68 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 68 0 := by
  decide

private theorem x4NLK3Row19Coeff69_spec :
    mulCoeffTwo KData X4NLK2Data 19 69 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 69 0 := by
  decide

private theorem x4NLK3Row19Coeff70_spec :
    mulCoeffTwo KData X4NLK2Data 19 70 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 70 0 := by
  decide

private theorem x4NLK3Row19Coeff71_spec :
    mulCoeffTwo KData X4NLK2Data 19 71 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 71 0 := by
  decide

private theorem x4NLK3Row19Coeff72_spec :
    mulCoeffTwo KData X4NLK2Data 19 72 =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD 72 0 := by
  decide

private theorem x4NLK3Row19Coeffs0To9_spec (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo KData X4NLK2Data 19 j =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row19Coeff0_spec
  · exact x4NLK3Row19Coeff1_spec
  · exact x4NLK3Row19Coeff2_spec
  · exact x4NLK3Row19Coeff3_spec
  · exact x4NLK3Row19Coeff4_spec
  · exact x4NLK3Row19Coeff5_spec
  · exact x4NLK3Row19Coeff6_spec
  · exact x4NLK3Row19Coeff7_spec
  · exact x4NLK3Row19Coeff8_spec
  · exact x4NLK3Row19Coeff9_spec

private theorem x4NLK3Row19Coeffs10To19_spec (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo KData X4NLK2Data 19 j =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row19Coeff10_spec
  · exact x4NLK3Row19Coeff11_spec
  · exact x4NLK3Row19Coeff12_spec
  · exact x4NLK3Row19Coeff13_spec
  · exact x4NLK3Row19Coeff14_spec
  · exact x4NLK3Row19Coeff15_spec
  · exact x4NLK3Row19Coeff16_spec
  · exact x4NLK3Row19Coeff17_spec
  · exact x4NLK3Row19Coeff18_spec
  · exact x4NLK3Row19Coeff19_spec

private theorem x4NLK3Row19Coeffs20To29_spec (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo KData X4NLK2Data 19 j =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row19Coeff20_spec
  · exact x4NLK3Row19Coeff21_spec
  · exact x4NLK3Row19Coeff22_spec
  · exact x4NLK3Row19Coeff23_spec
  · exact x4NLK3Row19Coeff24_spec
  · exact x4NLK3Row19Coeff25_spec
  · exact x4NLK3Row19Coeff26_spec
  · exact x4NLK3Row19Coeff27_spec
  · exact x4NLK3Row19Coeff28_spec
  · exact x4NLK3Row19Coeff29_spec

private theorem x4NLK3Row19Coeffs30To39_spec (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo KData X4NLK2Data 19 j =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row19Coeff30_spec
  · exact x4NLK3Row19Coeff31_spec
  · exact x4NLK3Row19Coeff32_spec
  · exact x4NLK3Row19Coeff33_spec
  · exact x4NLK3Row19Coeff34_spec
  · exact x4NLK3Row19Coeff35_spec
  · exact x4NLK3Row19Coeff36_spec
  · exact x4NLK3Row19Coeff37_spec
  · exact x4NLK3Row19Coeff38_spec
  · exact x4NLK3Row19Coeff39_spec

private theorem x4NLK3Row19Coeffs40To49_spec (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo KData X4NLK2Data 19 j =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row19Coeff40_spec
  · exact x4NLK3Row19Coeff41_spec
  · exact x4NLK3Row19Coeff42_spec
  · exact x4NLK3Row19Coeff43_spec
  · exact x4NLK3Row19Coeff44_spec
  · exact x4NLK3Row19Coeff45_spec
  · exact x4NLK3Row19Coeff46_spec
  · exact x4NLK3Row19Coeff47_spec
  · exact x4NLK3Row19Coeff48_spec
  · exact x4NLK3Row19Coeff49_spec

private theorem x4NLK3Row19Coeffs50To59_spec (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo KData X4NLK2Data 19 j =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row19Coeff50_spec
  · exact x4NLK3Row19Coeff51_spec
  · exact x4NLK3Row19Coeff52_spec
  · exact x4NLK3Row19Coeff53_spec
  · exact x4NLK3Row19Coeff54_spec
  · exact x4NLK3Row19Coeff55_spec
  · exact x4NLK3Row19Coeff56_spec
  · exact x4NLK3Row19Coeff57_spec
  · exact x4NLK3Row19Coeff58_spec
  · exact x4NLK3Row19Coeff59_spec

private theorem x4NLK3Row19Coeffs60To69_spec (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo KData X4NLK2Data 19 j =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row19Coeff60_spec
  · exact x4NLK3Row19Coeff61_spec
  · exact x4NLK3Row19Coeff62_spec
  · exact x4NLK3Row19Coeff63_spec
  · exact x4NLK3Row19Coeff64_spec
  · exact x4NLK3Row19Coeff65_spec
  · exact x4NLK3Row19Coeff66_spec
  · exact x4NLK3Row19Coeff67_spec
  · exact x4NLK3Row19Coeff68_spec
  · exact x4NLK3Row19Coeff69_spec

private theorem x4NLK3Row19Coeffs70To72_spec (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 73) :
    mulCoeffTwo KData X4NLK2Data 19 j =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 := by
    omega
  rcases hCases with
    rfl | rfl | rfl
  · exact x4NLK3Row19Coeff70_spec
  · exact x4NLK3Row19Coeff71_spec
  · exact x4NLK3Row19Coeff72_spec

private theorem x4NLK3Row19_coefficients (j : ℕ) (hj : j < 73) :
    mulCoeffTwo KData X4NLK2Data 19 j =
      ((rectangularize 53 73 X4NLK3Data).getD 19 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact x4NLK3Row19Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact x4NLK3Row19Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact x4NLK3Row19Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact x4NLK3Row19Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact x4NLK3Row19Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact x4NLK3Row19Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact x4NLK3Row19Coeffs60To69_spec j (by omega) h70
  exact x4NLK3Row19Coeffs70To72_spec j (by omega) hj

private theorem x4NLK3Row19_spec :
    padOne 73 (mulRow KData X4NLK2Data 19) =
      (rectangularize 53 73 X4NLK3Data).getD 19 [] := by
  apply padOne_mulRow_eq_of_coefficients 73 KData X4NLK2Data 19
    ((rectangularize 53 73 X4NLK3Data).getD 19 [])
  · decide
  · have hTargetSupport : (X4NLK3Data.getD 19 []).length ≤ 73 := by
      decide
    rw [getD_rectangularize 53 73 X4NLK3Data 19 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact x4NLK3Row19_coefficients

private theorem x4NLK3Row20Coeff0_spec :
    mulCoeffTwo KData X4NLK2Data 20 0 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 0 0 := by
  decide

private theorem x4NLK3Row20Coeff1_spec :
    mulCoeffTwo KData X4NLK2Data 20 1 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 1 0 := by
  decide

private theorem x4NLK3Row20Coeff2_spec :
    mulCoeffTwo KData X4NLK2Data 20 2 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 2 0 := by
  decide

private theorem x4NLK3Row20Coeff3_spec :
    mulCoeffTwo KData X4NLK2Data 20 3 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 3 0 := by
  decide

private theorem x4NLK3Row20Coeff4_spec :
    mulCoeffTwo KData X4NLK2Data 20 4 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 4 0 := by
  decide

private theorem x4NLK3Row20Coeff5_spec :
    mulCoeffTwo KData X4NLK2Data 20 5 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 5 0 := by
  decide

private theorem x4NLK3Row20Coeff6_spec :
    mulCoeffTwo KData X4NLK2Data 20 6 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 6 0 := by
  decide

private theorem x4NLK3Row20Coeff7_spec :
    mulCoeffTwo KData X4NLK2Data 20 7 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 7 0 := by
  decide

private theorem x4NLK3Row20Coeff8_spec :
    mulCoeffTwo KData X4NLK2Data 20 8 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 8 0 := by
  decide

private theorem x4NLK3Row20Coeff9_spec :
    mulCoeffTwo KData X4NLK2Data 20 9 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 9 0 := by
  decide

private theorem x4NLK3Row20Coeff10_spec :
    mulCoeffTwo KData X4NLK2Data 20 10 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 10 0 := by
  decide

private theorem x4NLK3Row20Coeff11_spec :
    mulCoeffTwo KData X4NLK2Data 20 11 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 11 0 := by
  decide

private theorem x4NLK3Row20Coeff12_spec :
    mulCoeffTwo KData X4NLK2Data 20 12 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 12 0 := by
  decide

private theorem x4NLK3Row20Coeff13_spec :
    mulCoeffTwo KData X4NLK2Data 20 13 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 13 0 := by
  decide

private theorem x4NLK3Row20Coeff14_spec :
    mulCoeffTwo KData X4NLK2Data 20 14 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 14 0 := by
  decide

private theorem x4NLK3Row20Coeff15_spec :
    mulCoeffTwo KData X4NLK2Data 20 15 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 15 0 := by
  decide

private theorem x4NLK3Row20Coeff16_spec :
    mulCoeffTwo KData X4NLK2Data 20 16 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 16 0 := by
  decide

private theorem x4NLK3Row20Coeff17_spec :
    mulCoeffTwo KData X4NLK2Data 20 17 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 17 0 := by
  decide

private theorem x4NLK3Row20Coeff18_spec :
    mulCoeffTwo KData X4NLK2Data 20 18 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 18 0 := by
  decide

private theorem x4NLK3Row20Coeff19_spec :
    mulCoeffTwo KData X4NLK2Data 20 19 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 19 0 := by
  decide

private theorem x4NLK3Row20Coeff20_spec :
    mulCoeffTwo KData X4NLK2Data 20 20 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 20 0 := by
  decide

private theorem x4NLK3Row20Coeff21_spec :
    mulCoeffTwo KData X4NLK2Data 20 21 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 21 0 := by
  decide

private theorem x4NLK3Row20Coeff22_spec :
    mulCoeffTwo KData X4NLK2Data 20 22 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 22 0 := by
  decide

private theorem x4NLK3Row20Coeff23_spec :
    mulCoeffTwo KData X4NLK2Data 20 23 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 23 0 := by
  decide

private theorem x4NLK3Row20Coeff24_spec :
    mulCoeffTwo KData X4NLK2Data 20 24 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 24 0 := by
  decide

private theorem x4NLK3Row20Coeff25_spec :
    mulCoeffTwo KData X4NLK2Data 20 25 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 25 0 := by
  decide

private theorem x4NLK3Row20Coeff26_spec :
    mulCoeffTwo KData X4NLK2Data 20 26 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 26 0 := by
  decide

private theorem x4NLK3Row20Coeff27_spec :
    mulCoeffTwo KData X4NLK2Data 20 27 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 27 0 := by
  decide

private theorem x4NLK3Row20Coeff28_spec :
    mulCoeffTwo KData X4NLK2Data 20 28 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 28 0 := by
  decide

private theorem x4NLK3Row20Coeff29_spec :
    mulCoeffTwo KData X4NLK2Data 20 29 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 29 0 := by
  decide

private theorem x4NLK3Row20Coeff30_spec :
    mulCoeffTwo KData X4NLK2Data 20 30 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 30 0 := by
  decide

private theorem x4NLK3Row20Coeff31_spec :
    mulCoeffTwo KData X4NLK2Data 20 31 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 31 0 := by
  decide

private theorem x4NLK3Row20Coeff32_spec :
    mulCoeffTwo KData X4NLK2Data 20 32 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 32 0 := by
  decide

private theorem x4NLK3Row20Coeff33_spec :
    mulCoeffTwo KData X4NLK2Data 20 33 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 33 0 := by
  decide

private theorem x4NLK3Row20Coeff34_spec :
    mulCoeffTwo KData X4NLK2Data 20 34 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 34 0 := by
  decide

private theorem x4NLK3Row20Coeff35_spec :
    mulCoeffTwo KData X4NLK2Data 20 35 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 35 0 := by
  decide

private theorem x4NLK3Row20Coeff36_spec :
    mulCoeffTwo KData X4NLK2Data 20 36 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 36 0 := by
  decide

private theorem x4NLK3Row20Coeff37_spec :
    mulCoeffTwo KData X4NLK2Data 20 37 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 37 0 := by
  decide

private theorem x4NLK3Row20Coeff38_spec :
    mulCoeffTwo KData X4NLK2Data 20 38 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 38 0 := by
  decide

private theorem x4NLK3Row20Coeff39_spec :
    mulCoeffTwo KData X4NLK2Data 20 39 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 39 0 := by
  decide

private theorem x4NLK3Row20Coeff40_spec :
    mulCoeffTwo KData X4NLK2Data 20 40 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 40 0 := by
  decide

private theorem x4NLK3Row20Coeff41_spec :
    mulCoeffTwo KData X4NLK2Data 20 41 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 41 0 := by
  decide

private theorem x4NLK3Row20Coeff42_spec :
    mulCoeffTwo KData X4NLK2Data 20 42 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 42 0 := by
  decide

private theorem x4NLK3Row20Coeff43_spec :
    mulCoeffTwo KData X4NLK2Data 20 43 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 43 0 := by
  decide

private theorem x4NLK3Row20Coeff44_spec :
    mulCoeffTwo KData X4NLK2Data 20 44 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 44 0 := by
  decide

private theorem x4NLK3Row20Coeff45_spec :
    mulCoeffTwo KData X4NLK2Data 20 45 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 45 0 := by
  decide

private theorem x4NLK3Row20Coeff46_spec :
    mulCoeffTwo KData X4NLK2Data 20 46 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 46 0 := by
  decide

private theorem x4NLK3Row20Coeff47_spec :
    mulCoeffTwo KData X4NLK2Data 20 47 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 47 0 := by
  decide

private theorem x4NLK3Row20Coeff48_spec :
    mulCoeffTwo KData X4NLK2Data 20 48 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 48 0 := by
  decide

private theorem x4NLK3Row20Coeff49_spec :
    mulCoeffTwo KData X4NLK2Data 20 49 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 49 0 := by
  decide

private theorem x4NLK3Row20Coeff50_spec :
    mulCoeffTwo KData X4NLK2Data 20 50 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 50 0 := by
  decide

private theorem x4NLK3Row20Coeff51_spec :
    mulCoeffTwo KData X4NLK2Data 20 51 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 51 0 := by
  decide

private theorem x4NLK3Row20Coeff52_spec :
    mulCoeffTwo KData X4NLK2Data 20 52 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 52 0 := by
  decide

private theorem x4NLK3Row20Coeff53_spec :
    mulCoeffTwo KData X4NLK2Data 20 53 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 53 0 := by
  decide

private theorem x4NLK3Row20Coeff54_spec :
    mulCoeffTwo KData X4NLK2Data 20 54 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 54 0 := by
  decide

private theorem x4NLK3Row20Coeff55_spec :
    mulCoeffTwo KData X4NLK2Data 20 55 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 55 0 := by
  decide

private theorem x4NLK3Row20Coeff56_spec :
    mulCoeffTwo KData X4NLK2Data 20 56 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 56 0 := by
  decide

private theorem x4NLK3Row20Coeff57_spec :
    mulCoeffTwo KData X4NLK2Data 20 57 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 57 0 := by
  decide

private theorem x4NLK3Row20Coeff58_spec :
    mulCoeffTwo KData X4NLK2Data 20 58 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 58 0 := by
  decide

private theorem x4NLK3Row20Coeff59_spec :
    mulCoeffTwo KData X4NLK2Data 20 59 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 59 0 := by
  decide

private theorem x4NLK3Row20Coeff60_spec :
    mulCoeffTwo KData X4NLK2Data 20 60 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 60 0 := by
  decide

private theorem x4NLK3Row20Coeff61_spec :
    mulCoeffTwo KData X4NLK2Data 20 61 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 61 0 := by
  decide

private theorem x4NLK3Row20Coeff62_spec :
    mulCoeffTwo KData X4NLK2Data 20 62 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 62 0 := by
  decide

private theorem x4NLK3Row20Coeff63_spec :
    mulCoeffTwo KData X4NLK2Data 20 63 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 63 0 := by
  decide

private theorem x4NLK3Row20Coeff64_spec :
    mulCoeffTwo KData X4NLK2Data 20 64 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 64 0 := by
  decide

private theorem x4NLK3Row20Coeff65_spec :
    mulCoeffTwo KData X4NLK2Data 20 65 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 65 0 := by
  decide

private theorem x4NLK3Row20Coeff66_spec :
    mulCoeffTwo KData X4NLK2Data 20 66 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 66 0 := by
  decide

private theorem x4NLK3Row20Coeff67_spec :
    mulCoeffTwo KData X4NLK2Data 20 67 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 67 0 := by
  decide

private theorem x4NLK3Row20Coeff68_spec :
    mulCoeffTwo KData X4NLK2Data 20 68 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 68 0 := by
  decide

private theorem x4NLK3Row20Coeff69_spec :
    mulCoeffTwo KData X4NLK2Data 20 69 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 69 0 := by
  decide

private theorem x4NLK3Row20Coeff70_spec :
    mulCoeffTwo KData X4NLK2Data 20 70 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 70 0 := by
  decide

private theorem x4NLK3Row20Coeff71_spec :
    mulCoeffTwo KData X4NLK2Data 20 71 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 71 0 := by
  decide

private theorem x4NLK3Row20Coeff72_spec :
    mulCoeffTwo KData X4NLK2Data 20 72 =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD 72 0 := by
  decide

private theorem x4NLK3Row20Coeffs0To9_spec (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo KData X4NLK2Data 20 j =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row20Coeff0_spec
  · exact x4NLK3Row20Coeff1_spec
  · exact x4NLK3Row20Coeff2_spec
  · exact x4NLK3Row20Coeff3_spec
  · exact x4NLK3Row20Coeff4_spec
  · exact x4NLK3Row20Coeff5_spec
  · exact x4NLK3Row20Coeff6_spec
  · exact x4NLK3Row20Coeff7_spec
  · exact x4NLK3Row20Coeff8_spec
  · exact x4NLK3Row20Coeff9_spec

private theorem x4NLK3Row20Coeffs10To19_spec (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo KData X4NLK2Data 20 j =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row20Coeff10_spec
  · exact x4NLK3Row20Coeff11_spec
  · exact x4NLK3Row20Coeff12_spec
  · exact x4NLK3Row20Coeff13_spec
  · exact x4NLK3Row20Coeff14_spec
  · exact x4NLK3Row20Coeff15_spec
  · exact x4NLK3Row20Coeff16_spec
  · exact x4NLK3Row20Coeff17_spec
  · exact x4NLK3Row20Coeff18_spec
  · exact x4NLK3Row20Coeff19_spec

private theorem x4NLK3Row20Coeffs20To29_spec (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo KData X4NLK2Data 20 j =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row20Coeff20_spec
  · exact x4NLK3Row20Coeff21_spec
  · exact x4NLK3Row20Coeff22_spec
  · exact x4NLK3Row20Coeff23_spec
  · exact x4NLK3Row20Coeff24_spec
  · exact x4NLK3Row20Coeff25_spec
  · exact x4NLK3Row20Coeff26_spec
  · exact x4NLK3Row20Coeff27_spec
  · exact x4NLK3Row20Coeff28_spec
  · exact x4NLK3Row20Coeff29_spec

private theorem x4NLK3Row20Coeffs30To39_spec (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo KData X4NLK2Data 20 j =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row20Coeff30_spec
  · exact x4NLK3Row20Coeff31_spec
  · exact x4NLK3Row20Coeff32_spec
  · exact x4NLK3Row20Coeff33_spec
  · exact x4NLK3Row20Coeff34_spec
  · exact x4NLK3Row20Coeff35_spec
  · exact x4NLK3Row20Coeff36_spec
  · exact x4NLK3Row20Coeff37_spec
  · exact x4NLK3Row20Coeff38_spec
  · exact x4NLK3Row20Coeff39_spec

private theorem x4NLK3Row20Coeffs40To49_spec (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo KData X4NLK2Data 20 j =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row20Coeff40_spec
  · exact x4NLK3Row20Coeff41_spec
  · exact x4NLK3Row20Coeff42_spec
  · exact x4NLK3Row20Coeff43_spec
  · exact x4NLK3Row20Coeff44_spec
  · exact x4NLK3Row20Coeff45_spec
  · exact x4NLK3Row20Coeff46_spec
  · exact x4NLK3Row20Coeff47_spec
  · exact x4NLK3Row20Coeff48_spec
  · exact x4NLK3Row20Coeff49_spec

private theorem x4NLK3Row20Coeffs50To59_spec (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo KData X4NLK2Data 20 j =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row20Coeff50_spec
  · exact x4NLK3Row20Coeff51_spec
  · exact x4NLK3Row20Coeff52_spec
  · exact x4NLK3Row20Coeff53_spec
  · exact x4NLK3Row20Coeff54_spec
  · exact x4NLK3Row20Coeff55_spec
  · exact x4NLK3Row20Coeff56_spec
  · exact x4NLK3Row20Coeff57_spec
  · exact x4NLK3Row20Coeff58_spec
  · exact x4NLK3Row20Coeff59_spec

private theorem x4NLK3Row20Coeffs60To69_spec (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo KData X4NLK2Data 20 j =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row20Coeff60_spec
  · exact x4NLK3Row20Coeff61_spec
  · exact x4NLK3Row20Coeff62_spec
  · exact x4NLK3Row20Coeff63_spec
  · exact x4NLK3Row20Coeff64_spec
  · exact x4NLK3Row20Coeff65_spec
  · exact x4NLK3Row20Coeff66_spec
  · exact x4NLK3Row20Coeff67_spec
  · exact x4NLK3Row20Coeff68_spec
  · exact x4NLK3Row20Coeff69_spec

private theorem x4NLK3Row20Coeffs70To72_spec (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 73) :
    mulCoeffTwo KData X4NLK2Data 20 j =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 := by
    omega
  rcases hCases with
    rfl | rfl | rfl
  · exact x4NLK3Row20Coeff70_spec
  · exact x4NLK3Row20Coeff71_spec
  · exact x4NLK3Row20Coeff72_spec

private theorem x4NLK3Row20_coefficients (j : ℕ) (hj : j < 73) :
    mulCoeffTwo KData X4NLK2Data 20 j =
      ((rectangularize 53 73 X4NLK3Data).getD 20 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact x4NLK3Row20Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact x4NLK3Row20Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact x4NLK3Row20Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact x4NLK3Row20Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact x4NLK3Row20Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact x4NLK3Row20Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact x4NLK3Row20Coeffs60To69_spec j (by omega) h70
  exact x4NLK3Row20Coeffs70To72_spec j (by omega) hj

private theorem x4NLK3Row20_spec :
    padOne 73 (mulRow KData X4NLK2Data 20) =
      (rectangularize 53 73 X4NLK3Data).getD 20 [] := by
  apply padOne_mulRow_eq_of_coefficients 73 KData X4NLK2Data 20
    ((rectangularize 53 73 X4NLK3Data).getD 20 [])
  · decide
  · have hTargetSupport : (X4NLK3Data.getD 20 []).length ≤ 73 := by
      decide
    rw [getD_rectangularize 53 73 X4NLK3Data 20 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact x4NLK3Row20_coefficients

private theorem x4NLK3Row21Coeff0_spec :
    mulCoeffTwo KData X4NLK2Data 21 0 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 0 0 := by
  decide

private theorem x4NLK3Row21Coeff1_spec :
    mulCoeffTwo KData X4NLK2Data 21 1 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 1 0 := by
  decide

private theorem x4NLK3Row21Coeff2_spec :
    mulCoeffTwo KData X4NLK2Data 21 2 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 2 0 := by
  decide

private theorem x4NLK3Row21Coeff3_spec :
    mulCoeffTwo KData X4NLK2Data 21 3 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 3 0 := by
  decide

private theorem x4NLK3Row21Coeff4_spec :
    mulCoeffTwo KData X4NLK2Data 21 4 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 4 0 := by
  decide

private theorem x4NLK3Row21Coeff5_spec :
    mulCoeffTwo KData X4NLK2Data 21 5 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 5 0 := by
  decide

private theorem x4NLK3Row21Coeff6_spec :
    mulCoeffTwo KData X4NLK2Data 21 6 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 6 0 := by
  decide

private theorem x4NLK3Row21Coeff7_spec :
    mulCoeffTwo KData X4NLK2Data 21 7 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 7 0 := by
  decide

private theorem x4NLK3Row21Coeff8_spec :
    mulCoeffTwo KData X4NLK2Data 21 8 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 8 0 := by
  decide

private theorem x4NLK3Row21Coeff9_spec :
    mulCoeffTwo KData X4NLK2Data 21 9 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 9 0 := by
  decide

private theorem x4NLK3Row21Coeff10_spec :
    mulCoeffTwo KData X4NLK2Data 21 10 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 10 0 := by
  decide

private theorem x4NLK3Row21Coeff11_spec :
    mulCoeffTwo KData X4NLK2Data 21 11 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 11 0 := by
  decide

private theorem x4NLK3Row21Coeff12_spec :
    mulCoeffTwo KData X4NLK2Data 21 12 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 12 0 := by
  decide

private theorem x4NLK3Row21Coeff13_spec :
    mulCoeffTwo KData X4NLK2Data 21 13 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 13 0 := by
  decide

private theorem x4NLK3Row21Coeff14_spec :
    mulCoeffTwo KData X4NLK2Data 21 14 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 14 0 := by
  decide

private theorem x4NLK3Row21Coeff15_spec :
    mulCoeffTwo KData X4NLK2Data 21 15 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 15 0 := by
  decide

private theorem x4NLK3Row21Coeff16_spec :
    mulCoeffTwo KData X4NLK2Data 21 16 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 16 0 := by
  decide

private theorem x4NLK3Row21Coeff17_spec :
    mulCoeffTwo KData X4NLK2Data 21 17 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 17 0 := by
  decide

private theorem x4NLK3Row21Coeff18_spec :
    mulCoeffTwo KData X4NLK2Data 21 18 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 18 0 := by
  decide

private theorem x4NLK3Row21Coeff19_spec :
    mulCoeffTwo KData X4NLK2Data 21 19 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 19 0 := by
  decide

private theorem x4NLK3Row21Coeff20_spec :
    mulCoeffTwo KData X4NLK2Data 21 20 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 20 0 := by
  decide

private theorem x4NLK3Row21Coeff21_spec :
    mulCoeffTwo KData X4NLK2Data 21 21 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 21 0 := by
  decide

private theorem x4NLK3Row21Coeff22_spec :
    mulCoeffTwo KData X4NLK2Data 21 22 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 22 0 := by
  decide

private theorem x4NLK3Row21Coeff23_spec :
    mulCoeffTwo KData X4NLK2Data 21 23 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 23 0 := by
  decide

private theorem x4NLK3Row21Coeff24_spec :
    mulCoeffTwo KData X4NLK2Data 21 24 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 24 0 := by
  decide

private theorem x4NLK3Row21Coeff25_spec :
    mulCoeffTwo KData X4NLK2Data 21 25 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 25 0 := by
  decide

private theorem x4NLK3Row21Coeff26_spec :
    mulCoeffTwo KData X4NLK2Data 21 26 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 26 0 := by
  decide

private theorem x4NLK3Row21Coeff27_spec :
    mulCoeffTwo KData X4NLK2Data 21 27 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 27 0 := by
  decide

private theorem x4NLK3Row21Coeff28_spec :
    mulCoeffTwo KData X4NLK2Data 21 28 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 28 0 := by
  decide

private theorem x4NLK3Row21Coeff29_spec :
    mulCoeffTwo KData X4NLK2Data 21 29 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 29 0 := by
  decide

private theorem x4NLK3Row21Coeff30_spec :
    mulCoeffTwo KData X4NLK2Data 21 30 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 30 0 := by
  decide

private theorem x4NLK3Row21Coeff31_spec :
    mulCoeffTwo KData X4NLK2Data 21 31 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 31 0 := by
  decide

private theorem x4NLK3Row21Coeff32_spec :
    mulCoeffTwo KData X4NLK2Data 21 32 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 32 0 := by
  decide

private theorem x4NLK3Row21Coeff33_spec :
    mulCoeffTwo KData X4NLK2Data 21 33 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 33 0 := by
  decide

private theorem x4NLK3Row21Coeff34_spec :
    mulCoeffTwo KData X4NLK2Data 21 34 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 34 0 := by
  decide

private theorem x4NLK3Row21Coeff35_spec :
    mulCoeffTwo KData X4NLK2Data 21 35 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 35 0 := by
  decide

private theorem x4NLK3Row21Coeff36_spec :
    mulCoeffTwo KData X4NLK2Data 21 36 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 36 0 := by
  decide

private theorem x4NLK3Row21Coeff37_spec :
    mulCoeffTwo KData X4NLK2Data 21 37 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 37 0 := by
  decide

private theorem x4NLK3Row21Coeff38_spec :
    mulCoeffTwo KData X4NLK2Data 21 38 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 38 0 := by
  decide

private theorem x4NLK3Row21Coeff39_spec :
    mulCoeffTwo KData X4NLK2Data 21 39 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 39 0 := by
  decide

private theorem x4NLK3Row21Coeff40_spec :
    mulCoeffTwo KData X4NLK2Data 21 40 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 40 0 := by
  decide

private theorem x4NLK3Row21Coeff41_spec :
    mulCoeffTwo KData X4NLK2Data 21 41 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 41 0 := by
  decide

private theorem x4NLK3Row21Coeff42_spec :
    mulCoeffTwo KData X4NLK2Data 21 42 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 42 0 := by
  decide

private theorem x4NLK3Row21Coeff43_spec :
    mulCoeffTwo KData X4NLK2Data 21 43 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 43 0 := by
  decide

private theorem x4NLK3Row21Coeff44_spec :
    mulCoeffTwo KData X4NLK2Data 21 44 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 44 0 := by
  decide

private theorem x4NLK3Row21Coeff45_spec :
    mulCoeffTwo KData X4NLK2Data 21 45 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 45 0 := by
  decide

private theorem x4NLK3Row21Coeff46_spec :
    mulCoeffTwo KData X4NLK2Data 21 46 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 46 0 := by
  decide

private theorem x4NLK3Row21Coeff47_spec :
    mulCoeffTwo KData X4NLK2Data 21 47 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 47 0 := by
  decide

private theorem x4NLK3Row21Coeff48_spec :
    mulCoeffTwo KData X4NLK2Data 21 48 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 48 0 := by
  decide

private theorem x4NLK3Row21Coeff49_spec :
    mulCoeffTwo KData X4NLK2Data 21 49 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 49 0 := by
  decide

private theorem x4NLK3Row21Coeff50_spec :
    mulCoeffTwo KData X4NLK2Data 21 50 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 50 0 := by
  decide

private theorem x4NLK3Row21Coeff51_spec :
    mulCoeffTwo KData X4NLK2Data 21 51 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 51 0 := by
  decide

private theorem x4NLK3Row21Coeff52_spec :
    mulCoeffTwo KData X4NLK2Data 21 52 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 52 0 := by
  decide

private theorem x4NLK3Row21Coeff53_spec :
    mulCoeffTwo KData X4NLK2Data 21 53 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 53 0 := by
  decide

private theorem x4NLK3Row21Coeff54_spec :
    mulCoeffTwo KData X4NLK2Data 21 54 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 54 0 := by
  decide

private theorem x4NLK3Row21Coeff55_spec :
    mulCoeffTwo KData X4NLK2Data 21 55 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 55 0 := by
  decide

private theorem x4NLK3Row21Coeff56_spec :
    mulCoeffTwo KData X4NLK2Data 21 56 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 56 0 := by
  decide

private theorem x4NLK3Row21Coeff57_spec :
    mulCoeffTwo KData X4NLK2Data 21 57 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 57 0 := by
  decide

private theorem x4NLK3Row21Coeff58_spec :
    mulCoeffTwo KData X4NLK2Data 21 58 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 58 0 := by
  decide

private theorem x4NLK3Row21Coeff59_spec :
    mulCoeffTwo KData X4NLK2Data 21 59 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 59 0 := by
  decide

private theorem x4NLK3Row21Coeff60_spec :
    mulCoeffTwo KData X4NLK2Data 21 60 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 60 0 := by
  decide

private theorem x4NLK3Row21Coeff61_spec :
    mulCoeffTwo KData X4NLK2Data 21 61 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 61 0 := by
  decide

private theorem x4NLK3Row21Coeff62_spec :
    mulCoeffTwo KData X4NLK2Data 21 62 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 62 0 := by
  decide

private theorem x4NLK3Row21Coeff63_spec :
    mulCoeffTwo KData X4NLK2Data 21 63 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 63 0 := by
  decide

private theorem x4NLK3Row21Coeff64_spec :
    mulCoeffTwo KData X4NLK2Data 21 64 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 64 0 := by
  decide

private theorem x4NLK3Row21Coeff65_spec :
    mulCoeffTwo KData X4NLK2Data 21 65 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 65 0 := by
  decide

private theorem x4NLK3Row21Coeff66_spec :
    mulCoeffTwo KData X4NLK2Data 21 66 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 66 0 := by
  decide

private theorem x4NLK3Row21Coeff67_spec :
    mulCoeffTwo KData X4NLK2Data 21 67 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 67 0 := by
  decide

private theorem x4NLK3Row21Coeff68_spec :
    mulCoeffTwo KData X4NLK2Data 21 68 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 68 0 := by
  decide

private theorem x4NLK3Row21Coeff69_spec :
    mulCoeffTwo KData X4NLK2Data 21 69 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 69 0 := by
  decide

private theorem x4NLK3Row21Coeff70_spec :
    mulCoeffTwo KData X4NLK2Data 21 70 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 70 0 := by
  decide

private theorem x4NLK3Row21Coeff71_spec :
    mulCoeffTwo KData X4NLK2Data 21 71 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 71 0 := by
  decide

private theorem x4NLK3Row21Coeff72_spec :
    mulCoeffTwo KData X4NLK2Data 21 72 =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD 72 0 := by
  decide

private theorem x4NLK3Row21Coeffs0To9_spec (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo KData X4NLK2Data 21 j =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row21Coeff0_spec
  · exact x4NLK3Row21Coeff1_spec
  · exact x4NLK3Row21Coeff2_spec
  · exact x4NLK3Row21Coeff3_spec
  · exact x4NLK3Row21Coeff4_spec
  · exact x4NLK3Row21Coeff5_spec
  · exact x4NLK3Row21Coeff6_spec
  · exact x4NLK3Row21Coeff7_spec
  · exact x4NLK3Row21Coeff8_spec
  · exact x4NLK3Row21Coeff9_spec

private theorem x4NLK3Row21Coeffs10To19_spec (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo KData X4NLK2Data 21 j =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row21Coeff10_spec
  · exact x4NLK3Row21Coeff11_spec
  · exact x4NLK3Row21Coeff12_spec
  · exact x4NLK3Row21Coeff13_spec
  · exact x4NLK3Row21Coeff14_spec
  · exact x4NLK3Row21Coeff15_spec
  · exact x4NLK3Row21Coeff16_spec
  · exact x4NLK3Row21Coeff17_spec
  · exact x4NLK3Row21Coeff18_spec
  · exact x4NLK3Row21Coeff19_spec

private theorem x4NLK3Row21Coeffs20To29_spec (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo KData X4NLK2Data 21 j =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row21Coeff20_spec
  · exact x4NLK3Row21Coeff21_spec
  · exact x4NLK3Row21Coeff22_spec
  · exact x4NLK3Row21Coeff23_spec
  · exact x4NLK3Row21Coeff24_spec
  · exact x4NLK3Row21Coeff25_spec
  · exact x4NLK3Row21Coeff26_spec
  · exact x4NLK3Row21Coeff27_spec
  · exact x4NLK3Row21Coeff28_spec
  · exact x4NLK3Row21Coeff29_spec

private theorem x4NLK3Row21Coeffs30To39_spec (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo KData X4NLK2Data 21 j =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row21Coeff30_spec
  · exact x4NLK3Row21Coeff31_spec
  · exact x4NLK3Row21Coeff32_spec
  · exact x4NLK3Row21Coeff33_spec
  · exact x4NLK3Row21Coeff34_spec
  · exact x4NLK3Row21Coeff35_spec
  · exact x4NLK3Row21Coeff36_spec
  · exact x4NLK3Row21Coeff37_spec
  · exact x4NLK3Row21Coeff38_spec
  · exact x4NLK3Row21Coeff39_spec

private theorem x4NLK3Row21Coeffs40To49_spec (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo KData X4NLK2Data 21 j =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row21Coeff40_spec
  · exact x4NLK3Row21Coeff41_spec
  · exact x4NLK3Row21Coeff42_spec
  · exact x4NLK3Row21Coeff43_spec
  · exact x4NLK3Row21Coeff44_spec
  · exact x4NLK3Row21Coeff45_spec
  · exact x4NLK3Row21Coeff46_spec
  · exact x4NLK3Row21Coeff47_spec
  · exact x4NLK3Row21Coeff48_spec
  · exact x4NLK3Row21Coeff49_spec

private theorem x4NLK3Row21Coeffs50To59_spec (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo KData X4NLK2Data 21 j =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row21Coeff50_spec
  · exact x4NLK3Row21Coeff51_spec
  · exact x4NLK3Row21Coeff52_spec
  · exact x4NLK3Row21Coeff53_spec
  · exact x4NLK3Row21Coeff54_spec
  · exact x4NLK3Row21Coeff55_spec
  · exact x4NLK3Row21Coeff56_spec
  · exact x4NLK3Row21Coeff57_spec
  · exact x4NLK3Row21Coeff58_spec
  · exact x4NLK3Row21Coeff59_spec

private theorem x4NLK3Row21Coeffs60To69_spec (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo KData X4NLK2Data 21 j =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row21Coeff60_spec
  · exact x4NLK3Row21Coeff61_spec
  · exact x4NLK3Row21Coeff62_spec
  · exact x4NLK3Row21Coeff63_spec
  · exact x4NLK3Row21Coeff64_spec
  · exact x4NLK3Row21Coeff65_spec
  · exact x4NLK3Row21Coeff66_spec
  · exact x4NLK3Row21Coeff67_spec
  · exact x4NLK3Row21Coeff68_spec
  · exact x4NLK3Row21Coeff69_spec

private theorem x4NLK3Row21Coeffs70To72_spec (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 73) :
    mulCoeffTwo KData X4NLK2Data 21 j =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 := by
    omega
  rcases hCases with
    rfl | rfl | rfl
  · exact x4NLK3Row21Coeff70_spec
  · exact x4NLK3Row21Coeff71_spec
  · exact x4NLK3Row21Coeff72_spec

private theorem x4NLK3Row21_coefficients (j : ℕ) (hj : j < 73) :
    mulCoeffTwo KData X4NLK2Data 21 j =
      ((rectangularize 53 73 X4NLK3Data).getD 21 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact x4NLK3Row21Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact x4NLK3Row21Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact x4NLK3Row21Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact x4NLK3Row21Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact x4NLK3Row21Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact x4NLK3Row21Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact x4NLK3Row21Coeffs60To69_spec j (by omega) h70
  exact x4NLK3Row21Coeffs70To72_spec j (by omega) hj

private theorem x4NLK3Row21_spec :
    padOne 73 (mulRow KData X4NLK2Data 21) =
      (rectangularize 53 73 X4NLK3Data).getD 21 [] := by
  apply padOne_mulRow_eq_of_coefficients 73 KData X4NLK2Data 21
    ((rectangularize 53 73 X4NLK3Data).getD 21 [])
  · decide
  · have hTargetSupport : (X4NLK3Data.getD 21 []).length ≤ 73 := by
      decide
    rw [getD_rectangularize 53 73 X4NLK3Data 21 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact x4NLK3Row21_coefficients

private theorem x4NLK3Row22Coeff0_spec :
    mulCoeffTwo KData X4NLK2Data 22 0 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 0 0 := by
  decide

private theorem x4NLK3Row22Coeff1_spec :
    mulCoeffTwo KData X4NLK2Data 22 1 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 1 0 := by
  decide

private theorem x4NLK3Row22Coeff2_spec :
    mulCoeffTwo KData X4NLK2Data 22 2 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 2 0 := by
  decide

private theorem x4NLK3Row22Coeff3_spec :
    mulCoeffTwo KData X4NLK2Data 22 3 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 3 0 := by
  decide

private theorem x4NLK3Row22Coeff4_spec :
    mulCoeffTwo KData X4NLK2Data 22 4 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 4 0 := by
  decide

private theorem x4NLK3Row22Coeff5_spec :
    mulCoeffTwo KData X4NLK2Data 22 5 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 5 0 := by
  decide

private theorem x4NLK3Row22Coeff6_spec :
    mulCoeffTwo KData X4NLK2Data 22 6 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 6 0 := by
  decide

private theorem x4NLK3Row22Coeff7_spec :
    mulCoeffTwo KData X4NLK2Data 22 7 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 7 0 := by
  decide

private theorem x4NLK3Row22Coeff8_spec :
    mulCoeffTwo KData X4NLK2Data 22 8 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 8 0 := by
  decide

private theorem x4NLK3Row22Coeff9_spec :
    mulCoeffTwo KData X4NLK2Data 22 9 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 9 0 := by
  decide

private theorem x4NLK3Row22Coeff10_spec :
    mulCoeffTwo KData X4NLK2Data 22 10 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 10 0 := by
  decide

private theorem x4NLK3Row22Coeff11_spec :
    mulCoeffTwo KData X4NLK2Data 22 11 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 11 0 := by
  decide

private theorem x4NLK3Row22Coeff12_spec :
    mulCoeffTwo KData X4NLK2Data 22 12 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 12 0 := by
  decide

private theorem x4NLK3Row22Coeff13_spec :
    mulCoeffTwo KData X4NLK2Data 22 13 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 13 0 := by
  decide

private theorem x4NLK3Row22Coeff14_spec :
    mulCoeffTwo KData X4NLK2Data 22 14 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 14 0 := by
  decide

private theorem x4NLK3Row22Coeff15_spec :
    mulCoeffTwo KData X4NLK2Data 22 15 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 15 0 := by
  decide

private theorem x4NLK3Row22Coeff16_spec :
    mulCoeffTwo KData X4NLK2Data 22 16 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 16 0 := by
  decide

private theorem x4NLK3Row22Coeff17_spec :
    mulCoeffTwo KData X4NLK2Data 22 17 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 17 0 := by
  decide

private theorem x4NLK3Row22Coeff18_spec :
    mulCoeffTwo KData X4NLK2Data 22 18 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 18 0 := by
  decide

private theorem x4NLK3Row22Coeff19_spec :
    mulCoeffTwo KData X4NLK2Data 22 19 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 19 0 := by
  decide

private theorem x4NLK3Row22Coeff20_spec :
    mulCoeffTwo KData X4NLK2Data 22 20 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 20 0 := by
  decide

private theorem x4NLK3Row22Coeff21_spec :
    mulCoeffTwo KData X4NLK2Data 22 21 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 21 0 := by
  decide

private theorem x4NLK3Row22Coeff22_spec :
    mulCoeffTwo KData X4NLK2Data 22 22 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 22 0 := by
  decide

private theorem x4NLK3Row22Coeff23_spec :
    mulCoeffTwo KData X4NLK2Data 22 23 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 23 0 := by
  decide

private theorem x4NLK3Row22Coeff24_spec :
    mulCoeffTwo KData X4NLK2Data 22 24 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 24 0 := by
  decide

private theorem x4NLK3Row22Coeff25_spec :
    mulCoeffTwo KData X4NLK2Data 22 25 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 25 0 := by
  decide

private theorem x4NLK3Row22Coeff26_spec :
    mulCoeffTwo KData X4NLK2Data 22 26 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 26 0 := by
  decide

private theorem x4NLK3Row22Coeff27_spec :
    mulCoeffTwo KData X4NLK2Data 22 27 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 27 0 := by
  decide

private theorem x4NLK3Row22Coeff28_spec :
    mulCoeffTwo KData X4NLK2Data 22 28 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 28 0 := by
  decide

private theorem x4NLK3Row22Coeff29_spec :
    mulCoeffTwo KData X4NLK2Data 22 29 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 29 0 := by
  decide

private theorem x4NLK3Row22Coeff30_spec :
    mulCoeffTwo KData X4NLK2Data 22 30 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 30 0 := by
  decide

private theorem x4NLK3Row22Coeff31_spec :
    mulCoeffTwo KData X4NLK2Data 22 31 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 31 0 := by
  decide

private theorem x4NLK3Row22Coeff32_spec :
    mulCoeffTwo KData X4NLK2Data 22 32 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 32 0 := by
  decide

private theorem x4NLK3Row22Coeff33_spec :
    mulCoeffTwo KData X4NLK2Data 22 33 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 33 0 := by
  decide

private theorem x4NLK3Row22Coeff34_spec :
    mulCoeffTwo KData X4NLK2Data 22 34 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 34 0 := by
  decide

private theorem x4NLK3Row22Coeff35_spec :
    mulCoeffTwo KData X4NLK2Data 22 35 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 35 0 := by
  decide

private theorem x4NLK3Row22Coeff36_spec :
    mulCoeffTwo KData X4NLK2Data 22 36 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 36 0 := by
  decide

private theorem x4NLK3Row22Coeff37_spec :
    mulCoeffTwo KData X4NLK2Data 22 37 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 37 0 := by
  decide

private theorem x4NLK3Row22Coeff38_spec :
    mulCoeffTwo KData X4NLK2Data 22 38 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 38 0 := by
  decide

private theorem x4NLK3Row22Coeff39_spec :
    mulCoeffTwo KData X4NLK2Data 22 39 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 39 0 := by
  decide

private theorem x4NLK3Row22Coeff40_spec :
    mulCoeffTwo KData X4NLK2Data 22 40 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 40 0 := by
  decide

private theorem x4NLK3Row22Coeff41_spec :
    mulCoeffTwo KData X4NLK2Data 22 41 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 41 0 := by
  decide

private theorem x4NLK3Row22Coeff42_spec :
    mulCoeffTwo KData X4NLK2Data 22 42 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 42 0 := by
  decide

private theorem x4NLK3Row22Coeff43_spec :
    mulCoeffTwo KData X4NLK2Data 22 43 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 43 0 := by
  decide

private theorem x4NLK3Row22Coeff44_spec :
    mulCoeffTwo KData X4NLK2Data 22 44 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 44 0 := by
  decide

private theorem x4NLK3Row22Coeff45_spec :
    mulCoeffTwo KData X4NLK2Data 22 45 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 45 0 := by
  decide

private theorem x4NLK3Row22Coeff46_spec :
    mulCoeffTwo KData X4NLK2Data 22 46 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 46 0 := by
  decide

private theorem x4NLK3Row22Coeff47_spec :
    mulCoeffTwo KData X4NLK2Data 22 47 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 47 0 := by
  decide

private theorem x4NLK3Row22Coeff48_spec :
    mulCoeffTwo KData X4NLK2Data 22 48 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 48 0 := by
  decide

private theorem x4NLK3Row22Coeff49_spec :
    mulCoeffTwo KData X4NLK2Data 22 49 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 49 0 := by
  decide

private theorem x4NLK3Row22Coeff50_spec :
    mulCoeffTwo KData X4NLK2Data 22 50 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 50 0 := by
  decide

private theorem x4NLK3Row22Coeff51_spec :
    mulCoeffTwo KData X4NLK2Data 22 51 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 51 0 := by
  decide

private theorem x4NLK3Row22Coeff52_spec :
    mulCoeffTwo KData X4NLK2Data 22 52 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 52 0 := by
  decide

private theorem x4NLK3Row22Coeff53_spec :
    mulCoeffTwo KData X4NLK2Data 22 53 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 53 0 := by
  decide

private theorem x4NLK3Row22Coeff54_spec :
    mulCoeffTwo KData X4NLK2Data 22 54 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 54 0 := by
  decide

private theorem x4NLK3Row22Coeff55_spec :
    mulCoeffTwo KData X4NLK2Data 22 55 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 55 0 := by
  decide

private theorem x4NLK3Row22Coeff56_spec :
    mulCoeffTwo KData X4NLK2Data 22 56 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 56 0 := by
  decide

private theorem x4NLK3Row22Coeff57_spec :
    mulCoeffTwo KData X4NLK2Data 22 57 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 57 0 := by
  decide

private theorem x4NLK3Row22Coeff58_spec :
    mulCoeffTwo KData X4NLK2Data 22 58 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 58 0 := by
  decide

private theorem x4NLK3Row22Coeff59_spec :
    mulCoeffTwo KData X4NLK2Data 22 59 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 59 0 := by
  decide

private theorem x4NLK3Row22Coeff60_spec :
    mulCoeffTwo KData X4NLK2Data 22 60 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 60 0 := by
  decide

private theorem x4NLK3Row22Coeff61_spec :
    mulCoeffTwo KData X4NLK2Data 22 61 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 61 0 := by
  decide

private theorem x4NLK3Row22Coeff62_spec :
    mulCoeffTwo KData X4NLK2Data 22 62 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 62 0 := by
  decide

private theorem x4NLK3Row22Coeff63_spec :
    mulCoeffTwo KData X4NLK2Data 22 63 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 63 0 := by
  decide

private theorem x4NLK3Row22Coeff64_spec :
    mulCoeffTwo KData X4NLK2Data 22 64 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 64 0 := by
  decide

private theorem x4NLK3Row22Coeff65_spec :
    mulCoeffTwo KData X4NLK2Data 22 65 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 65 0 := by
  decide

private theorem x4NLK3Row22Coeff66_spec :
    mulCoeffTwo KData X4NLK2Data 22 66 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 66 0 := by
  decide

private theorem x4NLK3Row22Coeff67_spec :
    mulCoeffTwo KData X4NLK2Data 22 67 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 67 0 := by
  decide

private theorem x4NLK3Row22Coeff68_spec :
    mulCoeffTwo KData X4NLK2Data 22 68 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 68 0 := by
  decide

private theorem x4NLK3Row22Coeff69_spec :
    mulCoeffTwo KData X4NLK2Data 22 69 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 69 0 := by
  decide

private theorem x4NLK3Row22Coeff70_spec :
    mulCoeffTwo KData X4NLK2Data 22 70 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 70 0 := by
  decide

private theorem x4NLK3Row22Coeff71_spec :
    mulCoeffTwo KData X4NLK2Data 22 71 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 71 0 := by
  decide

private theorem x4NLK3Row22Coeff72_spec :
    mulCoeffTwo KData X4NLK2Data 22 72 =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD 72 0 := by
  decide

private theorem x4NLK3Row22Coeffs0To9_spec (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo KData X4NLK2Data 22 j =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row22Coeff0_spec
  · exact x4NLK3Row22Coeff1_spec
  · exact x4NLK3Row22Coeff2_spec
  · exact x4NLK3Row22Coeff3_spec
  · exact x4NLK3Row22Coeff4_spec
  · exact x4NLK3Row22Coeff5_spec
  · exact x4NLK3Row22Coeff6_spec
  · exact x4NLK3Row22Coeff7_spec
  · exact x4NLK3Row22Coeff8_spec
  · exact x4NLK3Row22Coeff9_spec

private theorem x4NLK3Row22Coeffs10To19_spec (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo KData X4NLK2Data 22 j =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row22Coeff10_spec
  · exact x4NLK3Row22Coeff11_spec
  · exact x4NLK3Row22Coeff12_spec
  · exact x4NLK3Row22Coeff13_spec
  · exact x4NLK3Row22Coeff14_spec
  · exact x4NLK3Row22Coeff15_spec
  · exact x4NLK3Row22Coeff16_spec
  · exact x4NLK3Row22Coeff17_spec
  · exact x4NLK3Row22Coeff18_spec
  · exact x4NLK3Row22Coeff19_spec

private theorem x4NLK3Row22Coeffs20To29_spec (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo KData X4NLK2Data 22 j =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row22Coeff20_spec
  · exact x4NLK3Row22Coeff21_spec
  · exact x4NLK3Row22Coeff22_spec
  · exact x4NLK3Row22Coeff23_spec
  · exact x4NLK3Row22Coeff24_spec
  · exact x4NLK3Row22Coeff25_spec
  · exact x4NLK3Row22Coeff26_spec
  · exact x4NLK3Row22Coeff27_spec
  · exact x4NLK3Row22Coeff28_spec
  · exact x4NLK3Row22Coeff29_spec

private theorem x4NLK3Row22Coeffs30To39_spec (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo KData X4NLK2Data 22 j =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row22Coeff30_spec
  · exact x4NLK3Row22Coeff31_spec
  · exact x4NLK3Row22Coeff32_spec
  · exact x4NLK3Row22Coeff33_spec
  · exact x4NLK3Row22Coeff34_spec
  · exact x4NLK3Row22Coeff35_spec
  · exact x4NLK3Row22Coeff36_spec
  · exact x4NLK3Row22Coeff37_spec
  · exact x4NLK3Row22Coeff38_spec
  · exact x4NLK3Row22Coeff39_spec

private theorem x4NLK3Row22Coeffs40To49_spec (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo KData X4NLK2Data 22 j =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row22Coeff40_spec
  · exact x4NLK3Row22Coeff41_spec
  · exact x4NLK3Row22Coeff42_spec
  · exact x4NLK3Row22Coeff43_spec
  · exact x4NLK3Row22Coeff44_spec
  · exact x4NLK3Row22Coeff45_spec
  · exact x4NLK3Row22Coeff46_spec
  · exact x4NLK3Row22Coeff47_spec
  · exact x4NLK3Row22Coeff48_spec
  · exact x4NLK3Row22Coeff49_spec

private theorem x4NLK3Row22Coeffs50To59_spec (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo KData X4NLK2Data 22 j =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row22Coeff50_spec
  · exact x4NLK3Row22Coeff51_spec
  · exact x4NLK3Row22Coeff52_spec
  · exact x4NLK3Row22Coeff53_spec
  · exact x4NLK3Row22Coeff54_spec
  · exact x4NLK3Row22Coeff55_spec
  · exact x4NLK3Row22Coeff56_spec
  · exact x4NLK3Row22Coeff57_spec
  · exact x4NLK3Row22Coeff58_spec
  · exact x4NLK3Row22Coeff59_spec

private theorem x4NLK3Row22Coeffs60To69_spec (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo KData X4NLK2Data 22 j =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row22Coeff60_spec
  · exact x4NLK3Row22Coeff61_spec
  · exact x4NLK3Row22Coeff62_spec
  · exact x4NLK3Row22Coeff63_spec
  · exact x4NLK3Row22Coeff64_spec
  · exact x4NLK3Row22Coeff65_spec
  · exact x4NLK3Row22Coeff66_spec
  · exact x4NLK3Row22Coeff67_spec
  · exact x4NLK3Row22Coeff68_spec
  · exact x4NLK3Row22Coeff69_spec

private theorem x4NLK3Row22Coeffs70To72_spec (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 73) :
    mulCoeffTwo KData X4NLK2Data 22 j =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 := by
    omega
  rcases hCases with
    rfl | rfl | rfl
  · exact x4NLK3Row22Coeff70_spec
  · exact x4NLK3Row22Coeff71_spec
  · exact x4NLK3Row22Coeff72_spec

private theorem x4NLK3Row22_coefficients (j : ℕ) (hj : j < 73) :
    mulCoeffTwo KData X4NLK2Data 22 j =
      ((rectangularize 53 73 X4NLK3Data).getD 22 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact x4NLK3Row22Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact x4NLK3Row22Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact x4NLK3Row22Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact x4NLK3Row22Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact x4NLK3Row22Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact x4NLK3Row22Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact x4NLK3Row22Coeffs60To69_spec j (by omega) h70
  exact x4NLK3Row22Coeffs70To72_spec j (by omega) hj

private theorem x4NLK3Row22_spec :
    padOne 73 (mulRow KData X4NLK2Data 22) =
      (rectangularize 53 73 X4NLK3Data).getD 22 [] := by
  apply padOne_mulRow_eq_of_coefficients 73 KData X4NLK2Data 22
    ((rectangularize 53 73 X4NLK3Data).getD 22 [])
  · decide
  · have hTargetSupport : (X4NLK3Data.getD 22 []).length ≤ 73 := by
      decide
    rw [getD_rectangularize 53 73 X4NLK3Data 22 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact x4NLK3Row22_coefficients

private theorem x4NLK3Row23Coeff0_spec :
    mulCoeffTwo KData X4NLK2Data 23 0 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 0 0 := by
  decide

private theorem x4NLK3Row23Coeff1_spec :
    mulCoeffTwo KData X4NLK2Data 23 1 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 1 0 := by
  decide

private theorem x4NLK3Row23Coeff2_spec :
    mulCoeffTwo KData X4NLK2Data 23 2 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 2 0 := by
  decide

private theorem x4NLK3Row23Coeff3_spec :
    mulCoeffTwo KData X4NLK2Data 23 3 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 3 0 := by
  decide

private theorem x4NLK3Row23Coeff4_spec :
    mulCoeffTwo KData X4NLK2Data 23 4 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 4 0 := by
  decide

private theorem x4NLK3Row23Coeff5_spec :
    mulCoeffTwo KData X4NLK2Data 23 5 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 5 0 := by
  decide

private theorem x4NLK3Row23Coeff6_spec :
    mulCoeffTwo KData X4NLK2Data 23 6 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 6 0 := by
  decide

private theorem x4NLK3Row23Coeff7_spec :
    mulCoeffTwo KData X4NLK2Data 23 7 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 7 0 := by
  decide

private theorem x4NLK3Row23Coeff8_spec :
    mulCoeffTwo KData X4NLK2Data 23 8 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 8 0 := by
  decide

private theorem x4NLK3Row23Coeff9_spec :
    mulCoeffTwo KData X4NLK2Data 23 9 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 9 0 := by
  decide

private theorem x4NLK3Row23Coeff10_spec :
    mulCoeffTwo KData X4NLK2Data 23 10 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 10 0 := by
  decide

private theorem x4NLK3Row23Coeff11_spec :
    mulCoeffTwo KData X4NLK2Data 23 11 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 11 0 := by
  decide

private theorem x4NLK3Row23Coeff12_spec :
    mulCoeffTwo KData X4NLK2Data 23 12 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 12 0 := by
  decide

private theorem x4NLK3Row23Coeff13_spec :
    mulCoeffTwo KData X4NLK2Data 23 13 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 13 0 := by
  decide

private theorem x4NLK3Row23Coeff14_spec :
    mulCoeffTwo KData X4NLK2Data 23 14 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 14 0 := by
  decide

private theorem x4NLK3Row23Coeff15_spec :
    mulCoeffTwo KData X4NLK2Data 23 15 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 15 0 := by
  decide

private theorem x4NLK3Row23Coeff16_spec :
    mulCoeffTwo KData X4NLK2Data 23 16 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 16 0 := by
  decide

private theorem x4NLK3Row23Coeff17_spec :
    mulCoeffTwo KData X4NLK2Data 23 17 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 17 0 := by
  decide

private theorem x4NLK3Row23Coeff18_spec :
    mulCoeffTwo KData X4NLK2Data 23 18 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 18 0 := by
  decide

private theorem x4NLK3Row23Coeff19_spec :
    mulCoeffTwo KData X4NLK2Data 23 19 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 19 0 := by
  decide

private theorem x4NLK3Row23Coeff20_spec :
    mulCoeffTwo KData X4NLK2Data 23 20 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 20 0 := by
  decide

private theorem x4NLK3Row23Coeff21_spec :
    mulCoeffTwo KData X4NLK2Data 23 21 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 21 0 := by
  decide

private theorem x4NLK3Row23Coeff22_spec :
    mulCoeffTwo KData X4NLK2Data 23 22 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 22 0 := by
  decide

private theorem x4NLK3Row23Coeff23_spec :
    mulCoeffTwo KData X4NLK2Data 23 23 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 23 0 := by
  decide

private theorem x4NLK3Row23Coeff24_spec :
    mulCoeffTwo KData X4NLK2Data 23 24 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 24 0 := by
  decide

private theorem x4NLK3Row23Coeff25_spec :
    mulCoeffTwo KData X4NLK2Data 23 25 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 25 0 := by
  decide

private theorem x4NLK3Row23Coeff26_spec :
    mulCoeffTwo KData X4NLK2Data 23 26 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 26 0 := by
  decide

private theorem x4NLK3Row23Coeff27_spec :
    mulCoeffTwo KData X4NLK2Data 23 27 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 27 0 := by
  decide

private theorem x4NLK3Row23Coeff28_spec :
    mulCoeffTwo KData X4NLK2Data 23 28 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 28 0 := by
  decide

private theorem x4NLK3Row23Coeff29_spec :
    mulCoeffTwo KData X4NLK2Data 23 29 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 29 0 := by
  decide

private theorem x4NLK3Row23Coeff30_spec :
    mulCoeffTwo KData X4NLK2Data 23 30 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 30 0 := by
  decide

private theorem x4NLK3Row23Coeff31_spec :
    mulCoeffTwo KData X4NLK2Data 23 31 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 31 0 := by
  decide

private theorem x4NLK3Row23Coeff32_spec :
    mulCoeffTwo KData X4NLK2Data 23 32 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 32 0 := by
  decide

private theorem x4NLK3Row23Coeff33_spec :
    mulCoeffTwo KData X4NLK2Data 23 33 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 33 0 := by
  decide

private theorem x4NLK3Row23Coeff34_spec :
    mulCoeffTwo KData X4NLK2Data 23 34 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 34 0 := by
  decide

private theorem x4NLK3Row23Coeff35_spec :
    mulCoeffTwo KData X4NLK2Data 23 35 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 35 0 := by
  decide

private theorem x4NLK3Row23Coeff36_spec :
    mulCoeffTwo KData X4NLK2Data 23 36 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 36 0 := by
  decide

private theorem x4NLK3Row23Coeff37_spec :
    mulCoeffTwo KData X4NLK2Data 23 37 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 37 0 := by
  decide

private theorem x4NLK3Row23Coeff38_spec :
    mulCoeffTwo KData X4NLK2Data 23 38 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 38 0 := by
  decide

private theorem x4NLK3Row23Coeff39_spec :
    mulCoeffTwo KData X4NLK2Data 23 39 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 39 0 := by
  decide

private theorem x4NLK3Row23Coeff40_spec :
    mulCoeffTwo KData X4NLK2Data 23 40 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 40 0 := by
  decide

private theorem x4NLK3Row23Coeff41_spec :
    mulCoeffTwo KData X4NLK2Data 23 41 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 41 0 := by
  decide

private theorem x4NLK3Row23Coeff42_spec :
    mulCoeffTwo KData X4NLK2Data 23 42 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 42 0 := by
  decide

private theorem x4NLK3Row23Coeff43_spec :
    mulCoeffTwo KData X4NLK2Data 23 43 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 43 0 := by
  decide

private theorem x4NLK3Row23Coeff44_spec :
    mulCoeffTwo KData X4NLK2Data 23 44 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 44 0 := by
  decide

private theorem x4NLK3Row23Coeff45_spec :
    mulCoeffTwo KData X4NLK2Data 23 45 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 45 0 := by
  decide

private theorem x4NLK3Row23Coeff46_spec :
    mulCoeffTwo KData X4NLK2Data 23 46 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 46 0 := by
  decide

private theorem x4NLK3Row23Coeff47_spec :
    mulCoeffTwo KData X4NLK2Data 23 47 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 47 0 := by
  decide

private theorem x4NLK3Row23Coeff48_spec :
    mulCoeffTwo KData X4NLK2Data 23 48 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 48 0 := by
  decide

private theorem x4NLK3Row23Coeff49_spec :
    mulCoeffTwo KData X4NLK2Data 23 49 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 49 0 := by
  decide

private theorem x4NLK3Row23Coeff50_spec :
    mulCoeffTwo KData X4NLK2Data 23 50 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 50 0 := by
  decide

private theorem x4NLK3Row23Coeff51_spec :
    mulCoeffTwo KData X4NLK2Data 23 51 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 51 0 := by
  decide

private theorem x4NLK3Row23Coeff52_spec :
    mulCoeffTwo KData X4NLK2Data 23 52 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 52 0 := by
  decide

private theorem x4NLK3Row23Coeff53_spec :
    mulCoeffTwo KData X4NLK2Data 23 53 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 53 0 := by
  decide

private theorem x4NLK3Row23Coeff54_spec :
    mulCoeffTwo KData X4NLK2Data 23 54 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 54 0 := by
  decide

private theorem x4NLK3Row23Coeff55_spec :
    mulCoeffTwo KData X4NLK2Data 23 55 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 55 0 := by
  decide

private theorem x4NLK3Row23Coeff56_spec :
    mulCoeffTwo KData X4NLK2Data 23 56 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 56 0 := by
  decide

private theorem x4NLK3Row23Coeff57_spec :
    mulCoeffTwo KData X4NLK2Data 23 57 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 57 0 := by
  decide

private theorem x4NLK3Row23Coeff58_spec :
    mulCoeffTwo KData X4NLK2Data 23 58 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 58 0 := by
  decide

private theorem x4NLK3Row23Coeff59_spec :
    mulCoeffTwo KData X4NLK2Data 23 59 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 59 0 := by
  decide

private theorem x4NLK3Row23Coeff60_spec :
    mulCoeffTwo KData X4NLK2Data 23 60 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 60 0 := by
  decide

private theorem x4NLK3Row23Coeff61_spec :
    mulCoeffTwo KData X4NLK2Data 23 61 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 61 0 := by
  decide

private theorem x4NLK3Row23Coeff62_spec :
    mulCoeffTwo KData X4NLK2Data 23 62 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 62 0 := by
  decide

private theorem x4NLK3Row23Coeff63_spec :
    mulCoeffTwo KData X4NLK2Data 23 63 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 63 0 := by
  decide

private theorem x4NLK3Row23Coeff64_spec :
    mulCoeffTwo KData X4NLK2Data 23 64 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 64 0 := by
  decide

private theorem x4NLK3Row23Coeff65_spec :
    mulCoeffTwo KData X4NLK2Data 23 65 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 65 0 := by
  decide

private theorem x4NLK3Row23Coeff66_spec :
    mulCoeffTwo KData X4NLK2Data 23 66 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 66 0 := by
  decide

private theorem x4NLK3Row23Coeff67_spec :
    mulCoeffTwo KData X4NLK2Data 23 67 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 67 0 := by
  decide

private theorem x4NLK3Row23Coeff68_spec :
    mulCoeffTwo KData X4NLK2Data 23 68 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 68 0 := by
  decide

private theorem x4NLK3Row23Coeff69_spec :
    mulCoeffTwo KData X4NLK2Data 23 69 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 69 0 := by
  decide

private theorem x4NLK3Row23Coeff70_spec :
    mulCoeffTwo KData X4NLK2Data 23 70 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 70 0 := by
  decide

private theorem x4NLK3Row23Coeff71_spec :
    mulCoeffTwo KData X4NLK2Data 23 71 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 71 0 := by
  decide

private theorem x4NLK3Row23Coeff72_spec :
    mulCoeffTwo KData X4NLK2Data 23 72 =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD 72 0 := by
  decide

private theorem x4NLK3Row23Coeffs0To9_spec (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo KData X4NLK2Data 23 j =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row23Coeff0_spec
  · exact x4NLK3Row23Coeff1_spec
  · exact x4NLK3Row23Coeff2_spec
  · exact x4NLK3Row23Coeff3_spec
  · exact x4NLK3Row23Coeff4_spec
  · exact x4NLK3Row23Coeff5_spec
  · exact x4NLK3Row23Coeff6_spec
  · exact x4NLK3Row23Coeff7_spec
  · exact x4NLK3Row23Coeff8_spec
  · exact x4NLK3Row23Coeff9_spec

private theorem x4NLK3Row23Coeffs10To19_spec (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo KData X4NLK2Data 23 j =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row23Coeff10_spec
  · exact x4NLK3Row23Coeff11_spec
  · exact x4NLK3Row23Coeff12_spec
  · exact x4NLK3Row23Coeff13_spec
  · exact x4NLK3Row23Coeff14_spec
  · exact x4NLK3Row23Coeff15_spec
  · exact x4NLK3Row23Coeff16_spec
  · exact x4NLK3Row23Coeff17_spec
  · exact x4NLK3Row23Coeff18_spec
  · exact x4NLK3Row23Coeff19_spec

private theorem x4NLK3Row23Coeffs20To29_spec (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo KData X4NLK2Data 23 j =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row23Coeff20_spec
  · exact x4NLK3Row23Coeff21_spec
  · exact x4NLK3Row23Coeff22_spec
  · exact x4NLK3Row23Coeff23_spec
  · exact x4NLK3Row23Coeff24_spec
  · exact x4NLK3Row23Coeff25_spec
  · exact x4NLK3Row23Coeff26_spec
  · exact x4NLK3Row23Coeff27_spec
  · exact x4NLK3Row23Coeff28_spec
  · exact x4NLK3Row23Coeff29_spec

private theorem x4NLK3Row23Coeffs30To39_spec (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo KData X4NLK2Data 23 j =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row23Coeff30_spec
  · exact x4NLK3Row23Coeff31_spec
  · exact x4NLK3Row23Coeff32_spec
  · exact x4NLK3Row23Coeff33_spec
  · exact x4NLK3Row23Coeff34_spec
  · exact x4NLK3Row23Coeff35_spec
  · exact x4NLK3Row23Coeff36_spec
  · exact x4NLK3Row23Coeff37_spec
  · exact x4NLK3Row23Coeff38_spec
  · exact x4NLK3Row23Coeff39_spec

private theorem x4NLK3Row23Coeffs40To49_spec (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo KData X4NLK2Data 23 j =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row23Coeff40_spec
  · exact x4NLK3Row23Coeff41_spec
  · exact x4NLK3Row23Coeff42_spec
  · exact x4NLK3Row23Coeff43_spec
  · exact x4NLK3Row23Coeff44_spec
  · exact x4NLK3Row23Coeff45_spec
  · exact x4NLK3Row23Coeff46_spec
  · exact x4NLK3Row23Coeff47_spec
  · exact x4NLK3Row23Coeff48_spec
  · exact x4NLK3Row23Coeff49_spec

private theorem x4NLK3Row23Coeffs50To59_spec (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo KData X4NLK2Data 23 j =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row23Coeff50_spec
  · exact x4NLK3Row23Coeff51_spec
  · exact x4NLK3Row23Coeff52_spec
  · exact x4NLK3Row23Coeff53_spec
  · exact x4NLK3Row23Coeff54_spec
  · exact x4NLK3Row23Coeff55_spec
  · exact x4NLK3Row23Coeff56_spec
  · exact x4NLK3Row23Coeff57_spec
  · exact x4NLK3Row23Coeff58_spec
  · exact x4NLK3Row23Coeff59_spec

private theorem x4NLK3Row23Coeffs60To69_spec (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo KData X4NLK2Data 23 j =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row23Coeff60_spec
  · exact x4NLK3Row23Coeff61_spec
  · exact x4NLK3Row23Coeff62_spec
  · exact x4NLK3Row23Coeff63_spec
  · exact x4NLK3Row23Coeff64_spec
  · exact x4NLK3Row23Coeff65_spec
  · exact x4NLK3Row23Coeff66_spec
  · exact x4NLK3Row23Coeff67_spec
  · exact x4NLK3Row23Coeff68_spec
  · exact x4NLK3Row23Coeff69_spec

private theorem x4NLK3Row23Coeffs70To72_spec (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 73) :
    mulCoeffTwo KData X4NLK2Data 23 j =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 := by
    omega
  rcases hCases with
    rfl | rfl | rfl
  · exact x4NLK3Row23Coeff70_spec
  · exact x4NLK3Row23Coeff71_spec
  · exact x4NLK3Row23Coeff72_spec

private theorem x4NLK3Row23_coefficients (j : ℕ) (hj : j < 73) :
    mulCoeffTwo KData X4NLK2Data 23 j =
      ((rectangularize 53 73 X4NLK3Data).getD 23 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact x4NLK3Row23Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact x4NLK3Row23Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact x4NLK3Row23Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact x4NLK3Row23Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact x4NLK3Row23Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact x4NLK3Row23Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact x4NLK3Row23Coeffs60To69_spec j (by omega) h70
  exact x4NLK3Row23Coeffs70To72_spec j (by omega) hj

private theorem x4NLK3Row23_spec :
    padOne 73 (mulRow KData X4NLK2Data 23) =
      (rectangularize 53 73 X4NLK3Data).getD 23 [] := by
  apply padOne_mulRow_eq_of_coefficients 73 KData X4NLK2Data 23
    ((rectangularize 53 73 X4NLK3Data).getD 23 [])
  · decide
  · have hTargetSupport : (X4NLK3Data.getD 23 []).length ≤ 73 := by
      decide
    rw [getD_rectangularize 53 73 X4NLK3Data 23 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact x4NLK3Row23_coefficients

private theorem x4NLK3Row24Coeff0_spec :
    mulCoeffTwo KData X4NLK2Data 24 0 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 0 0 := by
  decide

private theorem x4NLK3Row24Coeff1_spec :
    mulCoeffTwo KData X4NLK2Data 24 1 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 1 0 := by
  decide

private theorem x4NLK3Row24Coeff2_spec :
    mulCoeffTwo KData X4NLK2Data 24 2 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 2 0 := by
  decide

private theorem x4NLK3Row24Coeff3_spec :
    mulCoeffTwo KData X4NLK2Data 24 3 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 3 0 := by
  decide

private theorem x4NLK3Row24Coeff4_spec :
    mulCoeffTwo KData X4NLK2Data 24 4 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 4 0 := by
  decide

private theorem x4NLK3Row24Coeff5_spec :
    mulCoeffTwo KData X4NLK2Data 24 5 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 5 0 := by
  decide

private theorem x4NLK3Row24Coeff6_spec :
    mulCoeffTwo KData X4NLK2Data 24 6 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 6 0 := by
  decide

private theorem x4NLK3Row24Coeff7_spec :
    mulCoeffTwo KData X4NLK2Data 24 7 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 7 0 := by
  decide

private theorem x4NLK3Row24Coeff8_spec :
    mulCoeffTwo KData X4NLK2Data 24 8 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 8 0 := by
  decide

private theorem x4NLK3Row24Coeff9_spec :
    mulCoeffTwo KData X4NLK2Data 24 9 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 9 0 := by
  decide

private theorem x4NLK3Row24Coeff10_spec :
    mulCoeffTwo KData X4NLK2Data 24 10 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 10 0 := by
  decide

private theorem x4NLK3Row24Coeff11_spec :
    mulCoeffTwo KData X4NLK2Data 24 11 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 11 0 := by
  decide

private theorem x4NLK3Row24Coeff12_spec :
    mulCoeffTwo KData X4NLK2Data 24 12 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 12 0 := by
  decide

private theorem x4NLK3Row24Coeff13_spec :
    mulCoeffTwo KData X4NLK2Data 24 13 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 13 0 := by
  decide

private theorem x4NLK3Row24Coeff14_spec :
    mulCoeffTwo KData X4NLK2Data 24 14 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 14 0 := by
  decide

private theorem x4NLK3Row24Coeff15_spec :
    mulCoeffTwo KData X4NLK2Data 24 15 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 15 0 := by
  decide

private theorem x4NLK3Row24Coeff16_spec :
    mulCoeffTwo KData X4NLK2Data 24 16 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 16 0 := by
  decide

private theorem x4NLK3Row24Coeff17_spec :
    mulCoeffTwo KData X4NLK2Data 24 17 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 17 0 := by
  decide

private theorem x4NLK3Row24Coeff18_spec :
    mulCoeffTwo KData X4NLK2Data 24 18 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 18 0 := by
  decide

private theorem x4NLK3Row24Coeff19_spec :
    mulCoeffTwo KData X4NLK2Data 24 19 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 19 0 := by
  decide

private theorem x4NLK3Row24Coeff20_spec :
    mulCoeffTwo KData X4NLK2Data 24 20 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 20 0 := by
  decide

private theorem x4NLK3Row24Coeff21_spec :
    mulCoeffTwo KData X4NLK2Data 24 21 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 21 0 := by
  decide

private theorem x4NLK3Row24Coeff22_spec :
    mulCoeffTwo KData X4NLK2Data 24 22 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 22 0 := by
  decide

private theorem x4NLK3Row24Coeff23_spec :
    mulCoeffTwo KData X4NLK2Data 24 23 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 23 0 := by
  decide

private theorem x4NLK3Row24Coeff24_spec :
    mulCoeffTwo KData X4NLK2Data 24 24 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 24 0 := by
  decide

private theorem x4NLK3Row24Coeff25_spec :
    mulCoeffTwo KData X4NLK2Data 24 25 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 25 0 := by
  decide

private theorem x4NLK3Row24Coeff26_spec :
    mulCoeffTwo KData X4NLK2Data 24 26 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 26 0 := by
  decide

private theorem x4NLK3Row24Coeff27_spec :
    mulCoeffTwo KData X4NLK2Data 24 27 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 27 0 := by
  decide

private theorem x4NLK3Row24Coeff28_spec :
    mulCoeffTwo KData X4NLK2Data 24 28 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 28 0 := by
  decide

private theorem x4NLK3Row24Coeff29_spec :
    mulCoeffTwo KData X4NLK2Data 24 29 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 29 0 := by
  decide

private theorem x4NLK3Row24Coeff30_spec :
    mulCoeffTwo KData X4NLK2Data 24 30 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 30 0 := by
  decide

private theorem x4NLK3Row24Coeff31_spec :
    mulCoeffTwo KData X4NLK2Data 24 31 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 31 0 := by
  decide

private theorem x4NLK3Row24Coeff32_spec :
    mulCoeffTwo KData X4NLK2Data 24 32 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 32 0 := by
  decide

private theorem x4NLK3Row24Coeff33_spec :
    mulCoeffTwo KData X4NLK2Data 24 33 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 33 0 := by
  decide

private theorem x4NLK3Row24Coeff34_spec :
    mulCoeffTwo KData X4NLK2Data 24 34 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 34 0 := by
  decide

private theorem x4NLK3Row24Coeff35_spec :
    mulCoeffTwo KData X4NLK2Data 24 35 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 35 0 := by
  decide

private theorem x4NLK3Row24Coeff36_spec :
    mulCoeffTwo KData X4NLK2Data 24 36 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 36 0 := by
  decide

private theorem x4NLK3Row24Coeff37_spec :
    mulCoeffTwo KData X4NLK2Data 24 37 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 37 0 := by
  decide

private theorem x4NLK3Row24Coeff38_spec :
    mulCoeffTwo KData X4NLK2Data 24 38 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 38 0 := by
  decide

private theorem x4NLK3Row24Coeff39_spec :
    mulCoeffTwo KData X4NLK2Data 24 39 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 39 0 := by
  decide

private theorem x4NLK3Row24Coeff40_spec :
    mulCoeffTwo KData X4NLK2Data 24 40 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 40 0 := by
  decide

private theorem x4NLK3Row24Coeff41_spec :
    mulCoeffTwo KData X4NLK2Data 24 41 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 41 0 := by
  decide

private theorem x4NLK3Row24Coeff42_spec :
    mulCoeffTwo KData X4NLK2Data 24 42 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 42 0 := by
  decide

private theorem x4NLK3Row24Coeff43_spec :
    mulCoeffTwo KData X4NLK2Data 24 43 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 43 0 := by
  decide

private theorem x4NLK3Row24Coeff44_spec :
    mulCoeffTwo KData X4NLK2Data 24 44 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 44 0 := by
  decide

private theorem x4NLK3Row24Coeff45_spec :
    mulCoeffTwo KData X4NLK2Data 24 45 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 45 0 := by
  decide

private theorem x4NLK3Row24Coeff46_spec :
    mulCoeffTwo KData X4NLK2Data 24 46 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 46 0 := by
  decide

private theorem x4NLK3Row24Coeff47_spec :
    mulCoeffTwo KData X4NLK2Data 24 47 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 47 0 := by
  decide

private theorem x4NLK3Row24Coeff48_spec :
    mulCoeffTwo KData X4NLK2Data 24 48 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 48 0 := by
  decide

private theorem x4NLK3Row24Coeff49_spec :
    mulCoeffTwo KData X4NLK2Data 24 49 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 49 0 := by
  decide

private theorem x4NLK3Row24Coeff50_spec :
    mulCoeffTwo KData X4NLK2Data 24 50 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 50 0 := by
  decide

private theorem x4NLK3Row24Coeff51_spec :
    mulCoeffTwo KData X4NLK2Data 24 51 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 51 0 := by
  decide

private theorem x4NLK3Row24Coeff52_spec :
    mulCoeffTwo KData X4NLK2Data 24 52 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 52 0 := by
  decide

private theorem x4NLK3Row24Coeff53_spec :
    mulCoeffTwo KData X4NLK2Data 24 53 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 53 0 := by
  decide

private theorem x4NLK3Row24Coeff54_spec :
    mulCoeffTwo KData X4NLK2Data 24 54 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 54 0 := by
  decide

private theorem x4NLK3Row24Coeff55_spec :
    mulCoeffTwo KData X4NLK2Data 24 55 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 55 0 := by
  decide

private theorem x4NLK3Row24Coeff56_spec :
    mulCoeffTwo KData X4NLK2Data 24 56 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 56 0 := by
  decide

private theorem x4NLK3Row24Coeff57_spec :
    mulCoeffTwo KData X4NLK2Data 24 57 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 57 0 := by
  decide

private theorem x4NLK3Row24Coeff58_spec :
    mulCoeffTwo KData X4NLK2Data 24 58 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 58 0 := by
  decide

private theorem x4NLK3Row24Coeff59_spec :
    mulCoeffTwo KData X4NLK2Data 24 59 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 59 0 := by
  decide

private theorem x4NLK3Row24Coeff60_spec :
    mulCoeffTwo KData X4NLK2Data 24 60 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 60 0 := by
  decide

private theorem x4NLK3Row24Coeff61_spec :
    mulCoeffTwo KData X4NLK2Data 24 61 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 61 0 := by
  decide

private theorem x4NLK3Row24Coeff62_spec :
    mulCoeffTwo KData X4NLK2Data 24 62 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 62 0 := by
  decide

private theorem x4NLK3Row24Coeff63_spec :
    mulCoeffTwo KData X4NLK2Data 24 63 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 63 0 := by
  decide

private theorem x4NLK3Row24Coeff64_spec :
    mulCoeffTwo KData X4NLK2Data 24 64 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 64 0 := by
  decide

private theorem x4NLK3Row24Coeff65_spec :
    mulCoeffTwo KData X4NLK2Data 24 65 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 65 0 := by
  decide

private theorem x4NLK3Row24Coeff66_spec :
    mulCoeffTwo KData X4NLK2Data 24 66 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 66 0 := by
  decide

private theorem x4NLK3Row24Coeff67_spec :
    mulCoeffTwo KData X4NLK2Data 24 67 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 67 0 := by
  decide

private theorem x4NLK3Row24Coeff68_spec :
    mulCoeffTwo KData X4NLK2Data 24 68 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 68 0 := by
  decide

private theorem x4NLK3Row24Coeff69_spec :
    mulCoeffTwo KData X4NLK2Data 24 69 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 69 0 := by
  decide

private theorem x4NLK3Row24Coeff70_spec :
    mulCoeffTwo KData X4NLK2Data 24 70 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 70 0 := by
  decide

private theorem x4NLK3Row24Coeff71_spec :
    mulCoeffTwo KData X4NLK2Data 24 71 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 71 0 := by
  decide

private theorem x4NLK3Row24Coeff72_spec :
    mulCoeffTwo KData X4NLK2Data 24 72 =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD 72 0 := by
  decide

private theorem x4NLK3Row24Coeffs0To9_spec (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo KData X4NLK2Data 24 j =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row24Coeff0_spec
  · exact x4NLK3Row24Coeff1_spec
  · exact x4NLK3Row24Coeff2_spec
  · exact x4NLK3Row24Coeff3_spec
  · exact x4NLK3Row24Coeff4_spec
  · exact x4NLK3Row24Coeff5_spec
  · exact x4NLK3Row24Coeff6_spec
  · exact x4NLK3Row24Coeff7_spec
  · exact x4NLK3Row24Coeff8_spec
  · exact x4NLK3Row24Coeff9_spec

private theorem x4NLK3Row24Coeffs10To19_spec (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo KData X4NLK2Data 24 j =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row24Coeff10_spec
  · exact x4NLK3Row24Coeff11_spec
  · exact x4NLK3Row24Coeff12_spec
  · exact x4NLK3Row24Coeff13_spec
  · exact x4NLK3Row24Coeff14_spec
  · exact x4NLK3Row24Coeff15_spec
  · exact x4NLK3Row24Coeff16_spec
  · exact x4NLK3Row24Coeff17_spec
  · exact x4NLK3Row24Coeff18_spec
  · exact x4NLK3Row24Coeff19_spec

private theorem x4NLK3Row24Coeffs20To29_spec (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo KData X4NLK2Data 24 j =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row24Coeff20_spec
  · exact x4NLK3Row24Coeff21_spec
  · exact x4NLK3Row24Coeff22_spec
  · exact x4NLK3Row24Coeff23_spec
  · exact x4NLK3Row24Coeff24_spec
  · exact x4NLK3Row24Coeff25_spec
  · exact x4NLK3Row24Coeff26_spec
  · exact x4NLK3Row24Coeff27_spec
  · exact x4NLK3Row24Coeff28_spec
  · exact x4NLK3Row24Coeff29_spec

private theorem x4NLK3Row24Coeffs30To39_spec (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo KData X4NLK2Data 24 j =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row24Coeff30_spec
  · exact x4NLK3Row24Coeff31_spec
  · exact x4NLK3Row24Coeff32_spec
  · exact x4NLK3Row24Coeff33_spec
  · exact x4NLK3Row24Coeff34_spec
  · exact x4NLK3Row24Coeff35_spec
  · exact x4NLK3Row24Coeff36_spec
  · exact x4NLK3Row24Coeff37_spec
  · exact x4NLK3Row24Coeff38_spec
  · exact x4NLK3Row24Coeff39_spec

private theorem x4NLK3Row24Coeffs40To49_spec (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo KData X4NLK2Data 24 j =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row24Coeff40_spec
  · exact x4NLK3Row24Coeff41_spec
  · exact x4NLK3Row24Coeff42_spec
  · exact x4NLK3Row24Coeff43_spec
  · exact x4NLK3Row24Coeff44_spec
  · exact x4NLK3Row24Coeff45_spec
  · exact x4NLK3Row24Coeff46_spec
  · exact x4NLK3Row24Coeff47_spec
  · exact x4NLK3Row24Coeff48_spec
  · exact x4NLK3Row24Coeff49_spec

private theorem x4NLK3Row24Coeffs50To59_spec (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo KData X4NLK2Data 24 j =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row24Coeff50_spec
  · exact x4NLK3Row24Coeff51_spec
  · exact x4NLK3Row24Coeff52_spec
  · exact x4NLK3Row24Coeff53_spec
  · exact x4NLK3Row24Coeff54_spec
  · exact x4NLK3Row24Coeff55_spec
  · exact x4NLK3Row24Coeff56_spec
  · exact x4NLK3Row24Coeff57_spec
  · exact x4NLK3Row24Coeff58_spec
  · exact x4NLK3Row24Coeff59_spec

private theorem x4NLK3Row24Coeffs60To69_spec (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo KData X4NLK2Data 24 j =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row24Coeff60_spec
  · exact x4NLK3Row24Coeff61_spec
  · exact x4NLK3Row24Coeff62_spec
  · exact x4NLK3Row24Coeff63_spec
  · exact x4NLK3Row24Coeff64_spec
  · exact x4NLK3Row24Coeff65_spec
  · exact x4NLK3Row24Coeff66_spec
  · exact x4NLK3Row24Coeff67_spec
  · exact x4NLK3Row24Coeff68_spec
  · exact x4NLK3Row24Coeff69_spec

private theorem x4NLK3Row24Coeffs70To72_spec (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 73) :
    mulCoeffTwo KData X4NLK2Data 24 j =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 := by
    omega
  rcases hCases with
    rfl | rfl | rfl
  · exact x4NLK3Row24Coeff70_spec
  · exact x4NLK3Row24Coeff71_spec
  · exact x4NLK3Row24Coeff72_spec

private theorem x4NLK3Row24_coefficients (j : ℕ) (hj : j < 73) :
    mulCoeffTwo KData X4NLK2Data 24 j =
      ((rectangularize 53 73 X4NLK3Data).getD 24 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact x4NLK3Row24Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact x4NLK3Row24Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact x4NLK3Row24Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact x4NLK3Row24Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact x4NLK3Row24Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact x4NLK3Row24Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact x4NLK3Row24Coeffs60To69_spec j (by omega) h70
  exact x4NLK3Row24Coeffs70To72_spec j (by omega) hj

private theorem x4NLK3Row24_spec :
    padOne 73 (mulRow KData X4NLK2Data 24) =
      (rectangularize 53 73 X4NLK3Data).getD 24 [] := by
  apply padOne_mulRow_eq_of_coefficients 73 KData X4NLK2Data 24
    ((rectangularize 53 73 X4NLK3Data).getD 24 [])
  · decide
  · have hTargetSupport : (X4NLK3Data.getD 24 []).length ≤ 73 := by
      decide
    rw [getD_rectangularize 53 73 X4NLK3Data 24 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact x4NLK3Row24_coefficients

private theorem x4NLK3Row25Coeff0_spec :
    mulCoeffTwo KData X4NLK2Data 25 0 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 0 0 := by
  decide

private theorem x4NLK3Row25Coeff1_spec :
    mulCoeffTwo KData X4NLK2Data 25 1 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 1 0 := by
  decide

private theorem x4NLK3Row25Coeff2_spec :
    mulCoeffTwo KData X4NLK2Data 25 2 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 2 0 := by
  decide

private theorem x4NLK3Row25Coeff3_spec :
    mulCoeffTwo KData X4NLK2Data 25 3 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 3 0 := by
  decide

private theorem x4NLK3Row25Coeff4_spec :
    mulCoeffTwo KData X4NLK2Data 25 4 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 4 0 := by
  decide

private theorem x4NLK3Row25Coeff5_spec :
    mulCoeffTwo KData X4NLK2Data 25 5 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 5 0 := by
  decide

private theorem x4NLK3Row25Coeff6_spec :
    mulCoeffTwo KData X4NLK2Data 25 6 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 6 0 := by
  decide

private theorem x4NLK3Row25Coeff7_spec :
    mulCoeffTwo KData X4NLK2Data 25 7 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 7 0 := by
  decide

private theorem x4NLK3Row25Coeff8_spec :
    mulCoeffTwo KData X4NLK2Data 25 8 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 8 0 := by
  decide

private theorem x4NLK3Row25Coeff9_spec :
    mulCoeffTwo KData X4NLK2Data 25 9 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 9 0 := by
  decide

private theorem x4NLK3Row25Coeff10_spec :
    mulCoeffTwo KData X4NLK2Data 25 10 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 10 0 := by
  decide

private theorem x4NLK3Row25Coeff11_spec :
    mulCoeffTwo KData X4NLK2Data 25 11 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 11 0 := by
  decide

private theorem x4NLK3Row25Coeff12_spec :
    mulCoeffTwo KData X4NLK2Data 25 12 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 12 0 := by
  decide

private theorem x4NLK3Row25Coeff13_spec :
    mulCoeffTwo KData X4NLK2Data 25 13 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 13 0 := by
  decide

private theorem x4NLK3Row25Coeff14_spec :
    mulCoeffTwo KData X4NLK2Data 25 14 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 14 0 := by
  decide

private theorem x4NLK3Row25Coeff15_spec :
    mulCoeffTwo KData X4NLK2Data 25 15 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 15 0 := by
  decide

private theorem x4NLK3Row25Coeff16_spec :
    mulCoeffTwo KData X4NLK2Data 25 16 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 16 0 := by
  decide

private theorem x4NLK3Row25Coeff17_spec :
    mulCoeffTwo KData X4NLK2Data 25 17 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 17 0 := by
  decide

private theorem x4NLK3Row25Coeff18_spec :
    mulCoeffTwo KData X4NLK2Data 25 18 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 18 0 := by
  decide

private theorem x4NLK3Row25Coeff19_spec :
    mulCoeffTwo KData X4NLK2Data 25 19 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 19 0 := by
  decide

private theorem x4NLK3Row25Coeff20_spec :
    mulCoeffTwo KData X4NLK2Data 25 20 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 20 0 := by
  decide

private theorem x4NLK3Row25Coeff21_spec :
    mulCoeffTwo KData X4NLK2Data 25 21 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 21 0 := by
  decide

private theorem x4NLK3Row25Coeff22_spec :
    mulCoeffTwo KData X4NLK2Data 25 22 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 22 0 := by
  decide

private theorem x4NLK3Row25Coeff23_spec :
    mulCoeffTwo KData X4NLK2Data 25 23 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 23 0 := by
  decide

private theorem x4NLK3Row25Coeff24_spec :
    mulCoeffTwo KData X4NLK2Data 25 24 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 24 0 := by
  decide

private theorem x4NLK3Row25Coeff25_spec :
    mulCoeffTwo KData X4NLK2Data 25 25 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 25 0 := by
  decide

private theorem x4NLK3Row25Coeff26_spec :
    mulCoeffTwo KData X4NLK2Data 25 26 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 26 0 := by
  decide

private theorem x4NLK3Row25Coeff27_spec :
    mulCoeffTwo KData X4NLK2Data 25 27 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 27 0 := by
  decide

private theorem x4NLK3Row25Coeff28_spec :
    mulCoeffTwo KData X4NLK2Data 25 28 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 28 0 := by
  decide

private theorem x4NLK3Row25Coeff29_spec :
    mulCoeffTwo KData X4NLK2Data 25 29 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 29 0 := by
  decide

private theorem x4NLK3Row25Coeff30_spec :
    mulCoeffTwo KData X4NLK2Data 25 30 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 30 0 := by
  decide

private theorem x4NLK3Row25Coeff31_spec :
    mulCoeffTwo KData X4NLK2Data 25 31 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 31 0 := by
  decide

private theorem x4NLK3Row25Coeff32_spec :
    mulCoeffTwo KData X4NLK2Data 25 32 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 32 0 := by
  decide

private theorem x4NLK3Row25Coeff33_spec :
    mulCoeffTwo KData X4NLK2Data 25 33 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 33 0 := by
  decide

private theorem x4NLK3Row25Coeff34_spec :
    mulCoeffTwo KData X4NLK2Data 25 34 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 34 0 := by
  decide

private theorem x4NLK3Row25Coeff35_spec :
    mulCoeffTwo KData X4NLK2Data 25 35 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 35 0 := by
  decide

private theorem x4NLK3Row25Coeff36_spec :
    mulCoeffTwo KData X4NLK2Data 25 36 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 36 0 := by
  decide

private theorem x4NLK3Row25Coeff37_spec :
    mulCoeffTwo KData X4NLK2Data 25 37 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 37 0 := by
  decide

private theorem x4NLK3Row25Coeff38_spec :
    mulCoeffTwo KData X4NLK2Data 25 38 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 38 0 := by
  decide

private theorem x4NLK3Row25Coeff39_spec :
    mulCoeffTwo KData X4NLK2Data 25 39 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 39 0 := by
  decide

private theorem x4NLK3Row25Coeff40_spec :
    mulCoeffTwo KData X4NLK2Data 25 40 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 40 0 := by
  decide

private theorem x4NLK3Row25Coeff41_spec :
    mulCoeffTwo KData X4NLK2Data 25 41 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 41 0 := by
  decide

private theorem x4NLK3Row25Coeff42_spec :
    mulCoeffTwo KData X4NLK2Data 25 42 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 42 0 := by
  decide

private theorem x4NLK3Row25Coeff43_spec :
    mulCoeffTwo KData X4NLK2Data 25 43 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 43 0 := by
  decide

private theorem x4NLK3Row25Coeff44_spec :
    mulCoeffTwo KData X4NLK2Data 25 44 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 44 0 := by
  decide

private theorem x4NLK3Row25Coeff45_spec :
    mulCoeffTwo KData X4NLK2Data 25 45 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 45 0 := by
  decide

private theorem x4NLK3Row25Coeff46_spec :
    mulCoeffTwo KData X4NLK2Data 25 46 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 46 0 := by
  decide

private theorem x4NLK3Row25Coeff47_spec :
    mulCoeffTwo KData X4NLK2Data 25 47 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 47 0 := by
  decide

private theorem x4NLK3Row25Coeff48_spec :
    mulCoeffTwo KData X4NLK2Data 25 48 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 48 0 := by
  decide

private theorem x4NLK3Row25Coeff49_spec :
    mulCoeffTwo KData X4NLK2Data 25 49 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 49 0 := by
  decide

private theorem x4NLK3Row25Coeff50_spec :
    mulCoeffTwo KData X4NLK2Data 25 50 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 50 0 := by
  decide

private theorem x4NLK3Row25Coeff51_spec :
    mulCoeffTwo KData X4NLK2Data 25 51 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 51 0 := by
  decide

private theorem x4NLK3Row25Coeff52_spec :
    mulCoeffTwo KData X4NLK2Data 25 52 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 52 0 := by
  decide

private theorem x4NLK3Row25Coeff53_spec :
    mulCoeffTwo KData X4NLK2Data 25 53 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 53 0 := by
  decide

private theorem x4NLK3Row25Coeff54_spec :
    mulCoeffTwo KData X4NLK2Data 25 54 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 54 0 := by
  decide

private theorem x4NLK3Row25Coeff55_spec :
    mulCoeffTwo KData X4NLK2Data 25 55 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 55 0 := by
  decide

private theorem x4NLK3Row25Coeff56_spec :
    mulCoeffTwo KData X4NLK2Data 25 56 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 56 0 := by
  decide

private theorem x4NLK3Row25Coeff57_spec :
    mulCoeffTwo KData X4NLK2Data 25 57 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 57 0 := by
  decide

private theorem x4NLK3Row25Coeff58_spec :
    mulCoeffTwo KData X4NLK2Data 25 58 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 58 0 := by
  decide

private theorem x4NLK3Row25Coeff59_spec :
    mulCoeffTwo KData X4NLK2Data 25 59 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 59 0 := by
  decide

private theorem x4NLK3Row25Coeff60_spec :
    mulCoeffTwo KData X4NLK2Data 25 60 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 60 0 := by
  decide

private theorem x4NLK3Row25Coeff61_spec :
    mulCoeffTwo KData X4NLK2Data 25 61 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 61 0 := by
  decide

private theorem x4NLK3Row25Coeff62_spec :
    mulCoeffTwo KData X4NLK2Data 25 62 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 62 0 := by
  decide

private theorem x4NLK3Row25Coeff63_spec :
    mulCoeffTwo KData X4NLK2Data 25 63 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 63 0 := by
  decide

private theorem x4NLK3Row25Coeff64_spec :
    mulCoeffTwo KData X4NLK2Data 25 64 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 64 0 := by
  decide

private theorem x4NLK3Row25Coeff65_spec :
    mulCoeffTwo KData X4NLK2Data 25 65 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 65 0 := by
  decide

private theorem x4NLK3Row25Coeff66_spec :
    mulCoeffTwo KData X4NLK2Data 25 66 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 66 0 := by
  decide

private theorem x4NLK3Row25Coeff67_spec :
    mulCoeffTwo KData X4NLK2Data 25 67 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 67 0 := by
  decide

private theorem x4NLK3Row25Coeff68_spec :
    mulCoeffTwo KData X4NLK2Data 25 68 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 68 0 := by
  decide

private theorem x4NLK3Row25Coeff69_spec :
    mulCoeffTwo KData X4NLK2Data 25 69 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 69 0 := by
  decide

private theorem x4NLK3Row25Coeff70_spec :
    mulCoeffTwo KData X4NLK2Data 25 70 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 70 0 := by
  decide

private theorem x4NLK3Row25Coeff71_spec :
    mulCoeffTwo KData X4NLK2Data 25 71 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 71 0 := by
  decide

private theorem x4NLK3Row25Coeff72_spec :
    mulCoeffTwo KData X4NLK2Data 25 72 =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD 72 0 := by
  decide

private theorem x4NLK3Row25Coeffs0To9_spec (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo KData X4NLK2Data 25 j =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row25Coeff0_spec
  · exact x4NLK3Row25Coeff1_spec
  · exact x4NLK3Row25Coeff2_spec
  · exact x4NLK3Row25Coeff3_spec
  · exact x4NLK3Row25Coeff4_spec
  · exact x4NLK3Row25Coeff5_spec
  · exact x4NLK3Row25Coeff6_spec
  · exact x4NLK3Row25Coeff7_spec
  · exact x4NLK3Row25Coeff8_spec
  · exact x4NLK3Row25Coeff9_spec

private theorem x4NLK3Row25Coeffs10To19_spec (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo KData X4NLK2Data 25 j =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row25Coeff10_spec
  · exact x4NLK3Row25Coeff11_spec
  · exact x4NLK3Row25Coeff12_spec
  · exact x4NLK3Row25Coeff13_spec
  · exact x4NLK3Row25Coeff14_spec
  · exact x4NLK3Row25Coeff15_spec
  · exact x4NLK3Row25Coeff16_spec
  · exact x4NLK3Row25Coeff17_spec
  · exact x4NLK3Row25Coeff18_spec
  · exact x4NLK3Row25Coeff19_spec

private theorem x4NLK3Row25Coeffs20To29_spec (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo KData X4NLK2Data 25 j =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row25Coeff20_spec
  · exact x4NLK3Row25Coeff21_spec
  · exact x4NLK3Row25Coeff22_spec
  · exact x4NLK3Row25Coeff23_spec
  · exact x4NLK3Row25Coeff24_spec
  · exact x4NLK3Row25Coeff25_spec
  · exact x4NLK3Row25Coeff26_spec
  · exact x4NLK3Row25Coeff27_spec
  · exact x4NLK3Row25Coeff28_spec
  · exact x4NLK3Row25Coeff29_spec

private theorem x4NLK3Row25Coeffs30To39_spec (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo KData X4NLK2Data 25 j =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row25Coeff30_spec
  · exact x4NLK3Row25Coeff31_spec
  · exact x4NLK3Row25Coeff32_spec
  · exact x4NLK3Row25Coeff33_spec
  · exact x4NLK3Row25Coeff34_spec
  · exact x4NLK3Row25Coeff35_spec
  · exact x4NLK3Row25Coeff36_spec
  · exact x4NLK3Row25Coeff37_spec
  · exact x4NLK3Row25Coeff38_spec
  · exact x4NLK3Row25Coeff39_spec

private theorem x4NLK3Row25Coeffs40To49_spec (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo KData X4NLK2Data 25 j =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row25Coeff40_spec
  · exact x4NLK3Row25Coeff41_spec
  · exact x4NLK3Row25Coeff42_spec
  · exact x4NLK3Row25Coeff43_spec
  · exact x4NLK3Row25Coeff44_spec
  · exact x4NLK3Row25Coeff45_spec
  · exact x4NLK3Row25Coeff46_spec
  · exact x4NLK3Row25Coeff47_spec
  · exact x4NLK3Row25Coeff48_spec
  · exact x4NLK3Row25Coeff49_spec

private theorem x4NLK3Row25Coeffs50To59_spec (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo KData X4NLK2Data 25 j =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row25Coeff50_spec
  · exact x4NLK3Row25Coeff51_spec
  · exact x4NLK3Row25Coeff52_spec
  · exact x4NLK3Row25Coeff53_spec
  · exact x4NLK3Row25Coeff54_spec
  · exact x4NLK3Row25Coeff55_spec
  · exact x4NLK3Row25Coeff56_spec
  · exact x4NLK3Row25Coeff57_spec
  · exact x4NLK3Row25Coeff58_spec
  · exact x4NLK3Row25Coeff59_spec

private theorem x4NLK3Row25Coeffs60To69_spec (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo KData X4NLK2Data 25 j =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row25Coeff60_spec
  · exact x4NLK3Row25Coeff61_spec
  · exact x4NLK3Row25Coeff62_spec
  · exact x4NLK3Row25Coeff63_spec
  · exact x4NLK3Row25Coeff64_spec
  · exact x4NLK3Row25Coeff65_spec
  · exact x4NLK3Row25Coeff66_spec
  · exact x4NLK3Row25Coeff67_spec
  · exact x4NLK3Row25Coeff68_spec
  · exact x4NLK3Row25Coeff69_spec

private theorem x4NLK3Row25Coeffs70To72_spec (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 73) :
    mulCoeffTwo KData X4NLK2Data 25 j =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 := by
    omega
  rcases hCases with
    rfl | rfl | rfl
  · exact x4NLK3Row25Coeff70_spec
  · exact x4NLK3Row25Coeff71_spec
  · exact x4NLK3Row25Coeff72_spec

private theorem x4NLK3Row25_coefficients (j : ℕ) (hj : j < 73) :
    mulCoeffTwo KData X4NLK2Data 25 j =
      ((rectangularize 53 73 X4NLK3Data).getD 25 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact x4NLK3Row25Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact x4NLK3Row25Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact x4NLK3Row25Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact x4NLK3Row25Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact x4NLK3Row25Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact x4NLK3Row25Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact x4NLK3Row25Coeffs60To69_spec j (by omega) h70
  exact x4NLK3Row25Coeffs70To72_spec j (by omega) hj

private theorem x4NLK3Row25_spec :
    padOne 73 (mulRow KData X4NLK2Data 25) =
      (rectangularize 53 73 X4NLK3Data).getD 25 [] := by
  apply padOne_mulRow_eq_of_coefficients 73 KData X4NLK2Data 25
    ((rectangularize 53 73 X4NLK3Data).getD 25 [])
  · decide
  · have hTargetSupport : (X4NLK3Data.getD 25 []).length ≤ 73 := by
      decide
    rw [getD_rectangularize 53 73 X4NLK3Data 25 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact x4NLK3Row25_coefficients

private theorem x4NLK3Row26Coeff0_spec :
    mulCoeffTwo KData X4NLK2Data 26 0 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 0 0 := by
  decide

private theorem x4NLK3Row26Coeff1_spec :
    mulCoeffTwo KData X4NLK2Data 26 1 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 1 0 := by
  decide

private theorem x4NLK3Row26Coeff2_spec :
    mulCoeffTwo KData X4NLK2Data 26 2 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 2 0 := by
  decide

private theorem x4NLK3Row26Coeff3_spec :
    mulCoeffTwo KData X4NLK2Data 26 3 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 3 0 := by
  decide

private theorem x4NLK3Row26Coeff4_spec :
    mulCoeffTwo KData X4NLK2Data 26 4 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 4 0 := by
  decide

private theorem x4NLK3Row26Coeff5_spec :
    mulCoeffTwo KData X4NLK2Data 26 5 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 5 0 := by
  decide

private theorem x4NLK3Row26Coeff6_spec :
    mulCoeffTwo KData X4NLK2Data 26 6 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 6 0 := by
  decide

private theorem x4NLK3Row26Coeff7_spec :
    mulCoeffTwo KData X4NLK2Data 26 7 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 7 0 := by
  decide

private theorem x4NLK3Row26Coeff8_spec :
    mulCoeffTwo KData X4NLK2Data 26 8 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 8 0 := by
  decide

private theorem x4NLK3Row26Coeff9_spec :
    mulCoeffTwo KData X4NLK2Data 26 9 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 9 0 := by
  decide

private theorem x4NLK3Row26Coeff10_spec :
    mulCoeffTwo KData X4NLK2Data 26 10 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 10 0 := by
  decide

private theorem x4NLK3Row26Coeff11_spec :
    mulCoeffTwo KData X4NLK2Data 26 11 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 11 0 := by
  decide

private theorem x4NLK3Row26Coeff12_spec :
    mulCoeffTwo KData X4NLK2Data 26 12 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 12 0 := by
  decide

private theorem x4NLK3Row26Coeff13_spec :
    mulCoeffTwo KData X4NLK2Data 26 13 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 13 0 := by
  decide

private theorem x4NLK3Row26Coeff14_spec :
    mulCoeffTwo KData X4NLK2Data 26 14 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 14 0 := by
  decide

private theorem x4NLK3Row26Coeff15_spec :
    mulCoeffTwo KData X4NLK2Data 26 15 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 15 0 := by
  decide

private theorem x4NLK3Row26Coeff16_spec :
    mulCoeffTwo KData X4NLK2Data 26 16 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 16 0 := by
  decide

private theorem x4NLK3Row26Coeff17_spec :
    mulCoeffTwo KData X4NLK2Data 26 17 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 17 0 := by
  decide

private theorem x4NLK3Row26Coeff18_spec :
    mulCoeffTwo KData X4NLK2Data 26 18 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 18 0 := by
  decide

private theorem x4NLK3Row26Coeff19_spec :
    mulCoeffTwo KData X4NLK2Data 26 19 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 19 0 := by
  decide

private theorem x4NLK3Row26Coeff20_spec :
    mulCoeffTwo KData X4NLK2Data 26 20 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 20 0 := by
  decide

private theorem x4NLK3Row26Coeff21_spec :
    mulCoeffTwo KData X4NLK2Data 26 21 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 21 0 := by
  decide

private theorem x4NLK3Row26Coeff22_spec :
    mulCoeffTwo KData X4NLK2Data 26 22 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 22 0 := by
  decide

private theorem x4NLK3Row26Coeff23_spec :
    mulCoeffTwo KData X4NLK2Data 26 23 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 23 0 := by
  decide

private theorem x4NLK3Row26Coeff24_spec :
    mulCoeffTwo KData X4NLK2Data 26 24 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 24 0 := by
  decide

private theorem x4NLK3Row26Coeff25_spec :
    mulCoeffTwo KData X4NLK2Data 26 25 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 25 0 := by
  decide

private theorem x4NLK3Row26Coeff26_spec :
    mulCoeffTwo KData X4NLK2Data 26 26 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 26 0 := by
  decide

private theorem x4NLK3Row26Coeff27_spec :
    mulCoeffTwo KData X4NLK2Data 26 27 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 27 0 := by
  decide

private theorem x4NLK3Row26Coeff28_spec :
    mulCoeffTwo KData X4NLK2Data 26 28 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 28 0 := by
  decide

private theorem x4NLK3Row26Coeff29_spec :
    mulCoeffTwo KData X4NLK2Data 26 29 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 29 0 := by
  decide

private theorem x4NLK3Row26Coeff30_spec :
    mulCoeffTwo KData X4NLK2Data 26 30 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 30 0 := by
  decide

private theorem x4NLK3Row26Coeff31_spec :
    mulCoeffTwo KData X4NLK2Data 26 31 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 31 0 := by
  decide

private theorem x4NLK3Row26Coeff32_spec :
    mulCoeffTwo KData X4NLK2Data 26 32 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 32 0 := by
  decide

private theorem x4NLK3Row26Coeff33_spec :
    mulCoeffTwo KData X4NLK2Data 26 33 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 33 0 := by
  decide

private theorem x4NLK3Row26Coeff34_spec :
    mulCoeffTwo KData X4NLK2Data 26 34 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 34 0 := by
  decide

private theorem x4NLK3Row26Coeff35_spec :
    mulCoeffTwo KData X4NLK2Data 26 35 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 35 0 := by
  decide

private theorem x4NLK3Row26Coeff36_spec :
    mulCoeffTwo KData X4NLK2Data 26 36 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 36 0 := by
  decide

private theorem x4NLK3Row26Coeff37_spec :
    mulCoeffTwo KData X4NLK2Data 26 37 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 37 0 := by
  decide

private theorem x4NLK3Row26Coeff38_spec :
    mulCoeffTwo KData X4NLK2Data 26 38 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 38 0 := by
  decide

private theorem x4NLK3Row26Coeff39_spec :
    mulCoeffTwo KData X4NLK2Data 26 39 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 39 0 := by
  decide

private theorem x4NLK3Row26Coeff40_spec :
    mulCoeffTwo KData X4NLK2Data 26 40 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 40 0 := by
  decide

private theorem x4NLK3Row26Coeff41_spec :
    mulCoeffTwo KData X4NLK2Data 26 41 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 41 0 := by
  decide

private theorem x4NLK3Row26Coeff42_spec :
    mulCoeffTwo KData X4NLK2Data 26 42 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 42 0 := by
  decide

private theorem x4NLK3Row26Coeff43_spec :
    mulCoeffTwo KData X4NLK2Data 26 43 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 43 0 := by
  decide

private theorem x4NLK3Row26Coeff44_spec :
    mulCoeffTwo KData X4NLK2Data 26 44 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 44 0 := by
  decide

private theorem x4NLK3Row26Coeff45_spec :
    mulCoeffTwo KData X4NLK2Data 26 45 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 45 0 := by
  decide

private theorem x4NLK3Row26Coeff46_spec :
    mulCoeffTwo KData X4NLK2Data 26 46 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 46 0 := by
  decide

private theorem x4NLK3Row26Coeff47_spec :
    mulCoeffTwo KData X4NLK2Data 26 47 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 47 0 := by
  decide

private theorem x4NLK3Row26Coeff48_spec :
    mulCoeffTwo KData X4NLK2Data 26 48 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 48 0 := by
  decide

private theorem x4NLK3Row26Coeff49_spec :
    mulCoeffTwo KData X4NLK2Data 26 49 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 49 0 := by
  decide

private theorem x4NLK3Row26Coeff50_spec :
    mulCoeffTwo KData X4NLK2Data 26 50 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 50 0 := by
  decide

private theorem x4NLK3Row26Coeff51_spec :
    mulCoeffTwo KData X4NLK2Data 26 51 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 51 0 := by
  decide

private theorem x4NLK3Row26Coeff52_spec :
    mulCoeffTwo KData X4NLK2Data 26 52 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 52 0 := by
  decide

private theorem x4NLK3Row26Coeff53_spec :
    mulCoeffTwo KData X4NLK2Data 26 53 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 53 0 := by
  decide

private theorem x4NLK3Row26Coeff54_spec :
    mulCoeffTwo KData X4NLK2Data 26 54 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 54 0 := by
  decide

private theorem x4NLK3Row26Coeff55_spec :
    mulCoeffTwo KData X4NLK2Data 26 55 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 55 0 := by
  decide

private theorem x4NLK3Row26Coeff56_spec :
    mulCoeffTwo KData X4NLK2Data 26 56 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 56 0 := by
  decide

private theorem x4NLK3Row26Coeff57_spec :
    mulCoeffTwo KData X4NLK2Data 26 57 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 57 0 := by
  decide

private theorem x4NLK3Row26Coeff58_spec :
    mulCoeffTwo KData X4NLK2Data 26 58 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 58 0 := by
  decide

private theorem x4NLK3Row26Coeff59_spec :
    mulCoeffTwo KData X4NLK2Data 26 59 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 59 0 := by
  decide

private theorem x4NLK3Row26Coeff60_spec :
    mulCoeffTwo KData X4NLK2Data 26 60 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 60 0 := by
  decide

private theorem x4NLK3Row26Coeff61_spec :
    mulCoeffTwo KData X4NLK2Data 26 61 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 61 0 := by
  decide

private theorem x4NLK3Row26Coeff62_spec :
    mulCoeffTwo KData X4NLK2Data 26 62 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 62 0 := by
  decide

private theorem x4NLK3Row26Coeff63_spec :
    mulCoeffTwo KData X4NLK2Data 26 63 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 63 0 := by
  decide

private theorem x4NLK3Row26Coeff64_spec :
    mulCoeffTwo KData X4NLK2Data 26 64 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 64 0 := by
  decide

private theorem x4NLK3Row26Coeff65_spec :
    mulCoeffTwo KData X4NLK2Data 26 65 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 65 0 := by
  decide

private theorem x4NLK3Row26Coeff66_spec :
    mulCoeffTwo KData X4NLK2Data 26 66 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 66 0 := by
  decide

private theorem x4NLK3Row26Coeff67_spec :
    mulCoeffTwo KData X4NLK2Data 26 67 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 67 0 := by
  decide

private theorem x4NLK3Row26Coeff68_spec :
    mulCoeffTwo KData X4NLK2Data 26 68 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 68 0 := by
  decide

private theorem x4NLK3Row26Coeff69_spec :
    mulCoeffTwo KData X4NLK2Data 26 69 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 69 0 := by
  decide

private theorem x4NLK3Row26Coeff70_spec :
    mulCoeffTwo KData X4NLK2Data 26 70 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 70 0 := by
  decide

private theorem x4NLK3Row26Coeff71_spec :
    mulCoeffTwo KData X4NLK2Data 26 71 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 71 0 := by
  decide

private theorem x4NLK3Row26Coeff72_spec :
    mulCoeffTwo KData X4NLK2Data 26 72 =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD 72 0 := by
  decide

private theorem x4NLK3Row26Coeffs0To9_spec (j : ℕ) (hHi : j < 10) :
    mulCoeffTwo KData X4NLK2Data 26 j =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD j 0 := by
  have hCases :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
    j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row26Coeff0_spec
  · exact x4NLK3Row26Coeff1_spec
  · exact x4NLK3Row26Coeff2_spec
  · exact x4NLK3Row26Coeff3_spec
  · exact x4NLK3Row26Coeff4_spec
  · exact x4NLK3Row26Coeff5_spec
  · exact x4NLK3Row26Coeff6_spec
  · exact x4NLK3Row26Coeff7_spec
  · exact x4NLK3Row26Coeff8_spec
  · exact x4NLK3Row26Coeff9_spec

private theorem x4NLK3Row26Coeffs10To19_spec (j : ℕ) (hLo : 10 ≤ j) (hHi : j < 20) :
    mulCoeffTwo KData X4NLK2Data 26 j =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD j 0 := by
  have hCases :
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨
    j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row26Coeff10_spec
  · exact x4NLK3Row26Coeff11_spec
  · exact x4NLK3Row26Coeff12_spec
  · exact x4NLK3Row26Coeff13_spec
  · exact x4NLK3Row26Coeff14_spec
  · exact x4NLK3Row26Coeff15_spec
  · exact x4NLK3Row26Coeff16_spec
  · exact x4NLK3Row26Coeff17_spec
  · exact x4NLK3Row26Coeff18_spec
  · exact x4NLK3Row26Coeff19_spec

private theorem x4NLK3Row26Coeffs20To29_spec (j : ℕ) (hLo : 20 ≤ j) (hHi : j < 30) :
    mulCoeffTwo KData X4NLK2Data 26 j =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD j 0 := by
  have hCases :
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨
    j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row26Coeff20_spec
  · exact x4NLK3Row26Coeff21_spec
  · exact x4NLK3Row26Coeff22_spec
  · exact x4NLK3Row26Coeff23_spec
  · exact x4NLK3Row26Coeff24_spec
  · exact x4NLK3Row26Coeff25_spec
  · exact x4NLK3Row26Coeff26_spec
  · exact x4NLK3Row26Coeff27_spec
  · exact x4NLK3Row26Coeff28_spec
  · exact x4NLK3Row26Coeff29_spec

private theorem x4NLK3Row26Coeffs30To39_spec (j : ℕ) (hLo : 30 ≤ j) (hHi : j < 40) :
    mulCoeffTwo KData X4NLK2Data 26 j =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD j 0 := by
  have hCases :
    j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨
    j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row26Coeff30_spec
  · exact x4NLK3Row26Coeff31_spec
  · exact x4NLK3Row26Coeff32_spec
  · exact x4NLK3Row26Coeff33_spec
  · exact x4NLK3Row26Coeff34_spec
  · exact x4NLK3Row26Coeff35_spec
  · exact x4NLK3Row26Coeff36_spec
  · exact x4NLK3Row26Coeff37_spec
  · exact x4NLK3Row26Coeff38_spec
  · exact x4NLK3Row26Coeff39_spec

private theorem x4NLK3Row26Coeffs40To49_spec (j : ℕ) (hLo : 40 ≤ j) (hHi : j < 50) :
    mulCoeffTwo KData X4NLK2Data 26 j =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD j 0 := by
  have hCases :
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨
    j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row26Coeff40_spec
  · exact x4NLK3Row26Coeff41_spec
  · exact x4NLK3Row26Coeff42_spec
  · exact x4NLK3Row26Coeff43_spec
  · exact x4NLK3Row26Coeff44_spec
  · exact x4NLK3Row26Coeff45_spec
  · exact x4NLK3Row26Coeff46_spec
  · exact x4NLK3Row26Coeff47_spec
  · exact x4NLK3Row26Coeff48_spec
  · exact x4NLK3Row26Coeff49_spec

private theorem x4NLK3Row26Coeffs50To59_spec (j : ℕ) (hLo : 50 ≤ j) (hHi : j < 60) :
    mulCoeffTwo KData X4NLK2Data 26 j =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD j 0 := by
  have hCases :
    j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨
    j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row26Coeff50_spec
  · exact x4NLK3Row26Coeff51_spec
  · exact x4NLK3Row26Coeff52_spec
  · exact x4NLK3Row26Coeff53_spec
  · exact x4NLK3Row26Coeff54_spec
  · exact x4NLK3Row26Coeff55_spec
  · exact x4NLK3Row26Coeff56_spec
  · exact x4NLK3Row26Coeff57_spec
  · exact x4NLK3Row26Coeff58_spec
  · exact x4NLK3Row26Coeff59_spec

private theorem x4NLK3Row26Coeffs60To69_spec (j : ℕ) (hLo : 60 ≤ j) (hHi : j < 70) :
    mulCoeffTwo KData X4NLK2Data 26 j =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD j 0 := by
  have hCases :
    j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨
    j = 65 ∨ j = 66 ∨ j = 67 ∨ j = 68 ∨ j = 69 := by
    omega
  rcases hCases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact x4NLK3Row26Coeff60_spec
  · exact x4NLK3Row26Coeff61_spec
  · exact x4NLK3Row26Coeff62_spec
  · exact x4NLK3Row26Coeff63_spec
  · exact x4NLK3Row26Coeff64_spec
  · exact x4NLK3Row26Coeff65_spec
  · exact x4NLK3Row26Coeff66_spec
  · exact x4NLK3Row26Coeff67_spec
  · exact x4NLK3Row26Coeff68_spec
  · exact x4NLK3Row26Coeff69_spec

private theorem x4NLK3Row26Coeffs70To72_spec (j : ℕ) (hLo : 70 ≤ j) (hHi : j < 73) :
    mulCoeffTwo KData X4NLK2Data 26 j =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD j 0 := by
  have hCases :
    j = 70 ∨ j = 71 ∨ j = 72 := by
    omega
  rcases hCases with
    rfl | rfl | rfl
  · exact x4NLK3Row26Coeff70_spec
  · exact x4NLK3Row26Coeff71_spec
  · exact x4NLK3Row26Coeff72_spec

private theorem x4NLK3Row26_coefficients (j : ℕ) (hj : j < 73) :
    mulCoeffTwo KData X4NLK2Data 26 j =
      ((rectangularize 53 73 X4NLK3Data).getD 26 []).getD j 0 := by
  by_cases h10 : j < 10
  · exact x4NLK3Row26Coeffs0To9_spec j h10
  by_cases h20 : j < 20
  · exact x4NLK3Row26Coeffs10To19_spec j (by omega) h20
  by_cases h30 : j < 30
  · exact x4NLK3Row26Coeffs20To29_spec j (by omega) h30
  by_cases h40 : j < 40
  · exact x4NLK3Row26Coeffs30To39_spec j (by omega) h40
  by_cases h50 : j < 50
  · exact x4NLK3Row26Coeffs40To49_spec j (by omega) h50
  by_cases h60 : j < 60
  · exact x4NLK3Row26Coeffs50To59_spec j (by omega) h60
  by_cases h70 : j < 70
  · exact x4NLK3Row26Coeffs60To69_spec j (by omega) h70
  exact x4NLK3Row26Coeffs70To72_spec j (by omega) hj

private theorem x4NLK3Row26_spec :
    padOne 73 (mulRow KData X4NLK2Data 26) =
      (rectangularize 53 73 X4NLK3Data).getD 26 [] := by
  apply padOne_mulRow_eq_of_coefficients 73 KData X4NLK2Data 26
    ((rectangularize 53 73 X4NLK3Data).getD 26 [])
  · decide
  · have hTargetSupport : (X4NLK3Data.getD 26 []).length ≤ 73 := by
      decide
    rw [getD_rectangularize 53 73 X4NLK3Data 26 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact x4NLK3Row26_coefficients

private theorem x4NLK3Row27_spec :
    padOne 73 (mulRow KData X4NLK2Data 27) =
      (rectangularize 53 73 X4NLK3Data).getD 27 [] := by
  decide

private theorem x4NLK3Row28_spec :
    padOne 73 (mulRow KData X4NLK2Data 28) =
      (rectangularize 53 73 X4NLK3Data).getD 28 [] := by
  decide

private theorem x4NLK3Row29_spec :
    padOne 73 (mulRow KData X4NLK2Data 29) =
      (rectangularize 53 73 X4NLK3Data).getD 29 [] := by
  decide

private theorem x4NLK3Row30_spec :
    padOne 73 (mulRow KData X4NLK2Data 30) =
      (rectangularize 53 73 X4NLK3Data).getD 30 [] := by
  decide

private theorem x4NLK3Row31_spec :
    padOne 73 (mulRow KData X4NLK2Data 31) =
      (rectangularize 53 73 X4NLK3Data).getD 31 [] := by
  decide

private theorem x4NLK3Row32_spec :
    padOne 73 (mulRow KData X4NLK2Data 32) =
      (rectangularize 53 73 X4NLK3Data).getD 32 [] := by
  decide

private theorem x4NLK3Row33_spec :
    padOne 73 (mulRow KData X4NLK2Data 33) =
      (rectangularize 53 73 X4NLK3Data).getD 33 [] := by
  decide

private theorem x4NLK3Row34_spec :
    padOne 73 (mulRow KData X4NLK2Data 34) =
      (rectangularize 53 73 X4NLK3Data).getD 34 [] := by
  decide

private theorem x4NLK3Row35_spec :
    padOne 73 (mulRow KData X4NLK2Data 35) =
      (rectangularize 53 73 X4NLK3Data).getD 35 [] := by
  decide

private theorem x4NLK3Row36_spec :
    padOne 73 (mulRow KData X4NLK2Data 36) =
      (rectangularize 53 73 X4NLK3Data).getD 36 [] := by
  decide

private theorem x4NLK3Row37_spec :
    padOne 73 (mulRow KData X4NLK2Data 37) =
      (rectangularize 53 73 X4NLK3Data).getD 37 [] := by
  decide

private theorem x4NLK3Row38_spec :
    padOne 73 (mulRow KData X4NLK2Data 38) =
      (rectangularize 53 73 X4NLK3Data).getD 38 [] := by
  decide

private theorem x4NLK3Row39_spec :
    padOne 73 (mulRow KData X4NLK2Data 39) =
      (rectangularize 53 73 X4NLK3Data).getD 39 [] := by
  decide

private theorem x4NLK3Row40_spec :
    padOne 73 (mulRow KData X4NLK2Data 40) =
      (rectangularize 53 73 X4NLK3Data).getD 40 [] := by
  decide

private theorem x4NLK3Row41_spec :
    padOne 73 (mulRow KData X4NLK2Data 41) =
      (rectangularize 53 73 X4NLK3Data).getD 41 [] := by
  decide

private theorem x4NLK3Row42_spec :
    padOne 73 (mulRow KData X4NLK2Data 42) =
      (rectangularize 53 73 X4NLK3Data).getD 42 [] := by
  decide

private theorem x4NLK3Row43_spec :
    padOne 73 (mulRow KData X4NLK2Data 43) =
      (rectangularize 53 73 X4NLK3Data).getD 43 [] := by
  decide

private theorem x4NLK3Row44_spec :
    padOne 73 (mulRow KData X4NLK2Data 44) =
      (rectangularize 53 73 X4NLK3Data).getD 44 [] := by
  decide

private theorem x4NLK3Row45_spec :
    padOne 73 (mulRow KData X4NLK2Data 45) =
      (rectangularize 53 73 X4NLK3Data).getD 45 [] := by
  decide

private theorem x4NLK3Row46_spec :
    padOne 73 (mulRow KData X4NLK2Data 46) =
      (rectangularize 53 73 X4NLK3Data).getD 46 [] := by
  decide

private theorem x4NLK3Row47_spec :
    padOne 73 (mulRow KData X4NLK2Data 47) =
      (rectangularize 53 73 X4NLK3Data).getD 47 [] := by
  decide

private theorem x4NLK3Row48_spec :
    padOne 73 (mulRow KData X4NLK2Data 48) =
      (rectangularize 53 73 X4NLK3Data).getD 48 [] := by
  decide

private theorem x4NLK3Row49_spec :
    padOne 73 (mulRow KData X4NLK2Data 49) =
      (rectangularize 53 73 X4NLK3Data).getD 49 [] := by
  decide

private theorem x4NLK3Row50_spec :
    padOne 73 (mulRow KData X4NLK2Data 50) =
      (rectangularize 53 73 X4NLK3Data).getD 50 [] := by
  decide

private theorem x4NLK3Row51_spec :
    padOne 73 (mulRow KData X4NLK2Data 51) =
      (rectangularize 53 73 X4NLK3Data).getD 51 [] := by
  decide

private theorem x4NLK3Row52_spec :
    padOne 73 (mulRow KData X4NLK2Data 52) =
      (rectangularize 53 73 X4NLK3Data).getD 52 [] := by
  decide

private theorem x4NLK3Rows_spec (n : ℕ) (hn : n < 53) :
    padOne 73 (mulRow KData X4NLK2Data n) =
      (rectangularize 53 73 X4NLK3Data).getD n [] := by
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
  · exact x4NLK3Row0_spec
  · exact x4NLK3Row1_spec
  · exact x4NLK3Row2_spec
  · exact x4NLK3Row3_spec
  · exact x4NLK3Row4_spec
  · exact x4NLK3Row5_spec
  · exact x4NLK3Row6_spec
  · exact x4NLK3Row7_spec
  · exact x4NLK3Row8_spec
  · exact x4NLK3Row9_spec
  · exact x4NLK3Row10_spec
  · exact x4NLK3Row11_spec
  · exact x4NLK3Row12_spec
  · exact x4NLK3Row13_spec
  · exact x4NLK3Row14_spec
  · exact x4NLK3Row15_spec
  · exact x4NLK3Row16_spec
  · exact x4NLK3Row17_spec
  · exact x4NLK3Row18_spec
  · exact x4NLK3Row19_spec
  · exact x4NLK3Row20_spec
  · exact x4NLK3Row21_spec
  · exact x4NLK3Row22_spec
  · exact x4NLK3Row23_spec
  · exact x4NLK3Row24_spec
  · exact x4NLK3Row25_spec
  · exact x4NLK3Row26_spec
  · exact x4NLK3Row27_spec
  · exact x4NLK3Row28_spec
  · exact x4NLK3Row29_spec
  · exact x4NLK3Row30_spec
  · exact x4NLK3Row31_spec
  · exact x4NLK3Row32_spec
  · exact x4NLK3Row33_spec
  · exact x4NLK3Row34_spec
  · exact x4NLK3Row35_spec
  · exact x4NLK3Row36_spec
  · exact x4NLK3Row37_spec
  · exact x4NLK3Row38_spec
  · exact x4NLK3Row39_spec
  · exact x4NLK3Row40_spec
  · exact x4NLK3Row41_spec
  · exact x4NLK3Row42_spec
  · exact x4NLK3Row43_spec
  · exact x4NLK3Row44_spec
  · exact x4NLK3Row45_spec
  · exact x4NLK3Row46_spec
  · exact x4NLK3Row47_spec
  · exact x4NLK3Row48_spec
  · exact x4NLK3Row49_spec
  · exact x4NLK3Row50_spec
  · exact x4NLK3Row51_spec
  · exact x4NLK3Row52_spec

private theorem x4NLK3Left_length :
    (rectangularize 53 73 (Two.mul KData X4NLK2Data)).length = 53 := by
  decide

private theorem x4NLK3Right_length :
    (rectangularize 53 73 X4NLK3Data).length = 53 := by
  decide

-- Exact bidegree bound (52, 72); no row or column is discarded.
theorem x4NLK3Data_spec :
    rectangularize 53 73 (Two.mul KData X4NLK2Data) =
      rectangularize 53 73 X4NLK3Data := by
  apply List.ext_getElem (x4NLK3Left_length.trans x4NLK3Right_length.symm)
  intro n hn _
  rw [List.getElem_eq_getD [], List.getElem_eq_getD []]
  rw [x4NLK3Left_length] at hn
  rw [getD_rectangularize 53 73 (Two.mul KData X4NLK2Data) n hn,
    ← mulRow_eq_getD]
  exact x4NLK3Rows_spec n hn

/-- Evaluation of the checked `R * A * K^3` branch of the canonical `N`. -/
theorem eval_x4NLeftData (r s : ℚ) :
    Two.eval X4NLK3Data r s =
      Two.eval KData r s ^ 3 * Two.eval AData r s *
        Two.eval RData r s * Two.eval X4MData r s := by
  have hR := congrArg (fun p => Two.eval p r s) x4NLRData_spec
  have hA := congrArg (fun p => Two.eval p r s) x4NLAData_spec
  have hK1 := congrArg (fun p => Two.eval p r s) x4NLK1Data_spec
  have hK2 := congrArg (fun p => Two.eval p r s) x4NLK2Data_spec
  have hK3 := congrArg (fun p => Two.eval p r s) x4NLK3Data_spec
  simp only [eval_rectangularize, Two.eval_mul] at hR hA hK1 hK2 hK3
  calc
    Two.eval X4NLK3Data r s =
        Two.eval KData r s * Two.eval X4NLK2Data r s := hK3.symm
    _ = Two.eval KData r s *
        (Two.eval KData r s * Two.eval X4NLK1Data r s) := by rw [← hK2]
    _ = Two.eval KData r s *
        (Two.eval KData r s *
          (Two.eval KData r s * Two.eval X4NLAData r s)) := by rw [← hK1]
    _ = Two.eval KData r s *
        (Two.eval KData r s *
          (Two.eval KData r s *
            (Two.eval AData r s * Two.eval X4NLRData r s))) := by rw [← hA]
    _ = Two.eval KData r s ^ 3 * Two.eval AData r s *
        Two.eval RData r s * Two.eval X4MData r s := by rw [← hR]; ring

end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
