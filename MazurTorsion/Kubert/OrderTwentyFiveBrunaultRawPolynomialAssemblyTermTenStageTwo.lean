/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialAssemblyTermTenStageOne

/-!
# The second staged product for raw Brunault numerator term ten

This leaf checks the literal dense table for `B (D⁸ E)`, reusing the checked
first-stage table rather than unfolding its construction.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveDensePolynomialRectangular
open OrderTwentyFiveDensePolynomialRowCertificate
open OrderTwentyFiveDensePolynomialMulCertificate
open OrderTwentyFiveRelationZeroCertificate.Dense

def termTenTailThreeRow0 : One :=
  [0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 1, -1]

def termTenTailThreeRow1 : One :=
  [0, 0, 0, 0, 0, 0, 0, 0, -35, 58, -63, 64, -32, 8]

def termTenTailThreeRow2 : One :=
  [0, 0, 0, 0, 0, 0, 0, 8, 539, -1252, 1629, -1756, 1336, -672, 196,
    -28]

def termTenTailThreeRow3 : One :=
  [0, 0, 0, 0, 0, 0, 0, -248, -4616, 14320, -22412, 26544, -24424,
    16856, -8260, 2744, -560, 56]

def termTenTailThreeRow4 : One :=
  [0, 0, 0, 0, 0, 0, 28, 3356, 22340, -97012, 182868, -241752, 251454,
    -208670, 134582, -65618, 23394, -5810, 910, -70]

def termTenTailThreeRow5 : One :=
  [0, 0, 0, 0, 0, 0, -756, -25424, -46060, 392448, -919408, 1375752,
    -1578626, 1477028, -1130766, 696976, -338814, 126980, -35546, 7056,
    -896, 56]

def termTenTailThreeRow6 : One :=
  [0, 0, 0, 0, 0, 56, 8764, 113792, -101136, -828380, 2782864, -4883424,
    6164438, -6265644, 5339334, -3826284, 2275742, -1104376, 429254,
    -130648, 30128, -4984, 532, -28]

def termTenTailThreeRow7 : One :=
  [0, 0, 0, 0, 0, -1288, -55944, -278656, 911452, 133144, -4350224,
    10243104, -14692580, 15953280, -14344820, 11103984, -7445448, 4275400,
    -2066480, 825720, -267568, 68656, -13476, 1912, -176, 8]

def termTenTailThreeRow8 : One :=
  [0, 0, 0, 0, 70, 12418, 207886, 193018, -2348556, 3683840, 448868,
    -10194916, 19875032, -24008772, 21964880, -16671452, 11090477,
    -6636133, 3565229, -1686445, 685114, -233394, 65142, -14506, 2485,
    -309, 25, -1]

def termTenTailThreeRow9 : One :=
  [0, 0, 0, 0, -1330, -63980, -422562, 796456, 2114840, -8060112,
    10174228, -2733728, -10646828, 20623120, -21778964, 16140376, -8959815,
    3766946, -1158875, 224648, -4102, -15436, 6426, -1520, 233, -22, 1]

def termTenTailThreeRow10 : One :=
  [0, 0, 0, 56, 10234, 184296, 302218, -2173684, 1917144, 4727304,
    -14616624, 18386060, -11192968, -1934268, 12123844, -14925024, 11977799,
    -7254164, 3483221, -1352088, 426258, -108476, 21906, -3400, 383, -28, 1]

def termTenTailThreeRow11 : One :=
  [0, 0, 0, -840, -40152, -272272, 445228, 1564320, -5191688, 5385152,
    1596700, -12526136, 20197156, -20609960, 15485696, -9042360, 4197952,
    -1560552, 462560, -107632, 19068, -2432, 200, -8]

def termTenTailThreeRow12 : One :=
  [0, 0, 28, 4844, 82068, 111916, -945700, 1031912, 1642046, -6548038,
    10478790, -10939922, 8349278, -4873946, 2216718, -787486, 216104,
    -44576, 6552, -616, 28]

def termTenTailThreeRow13 : One :=
  [0, 0, -308, -13216, -74620, 180656, 271040, -1511608, 2801246,
    -3189060, 2550058, -1507912, 672154, -225540, 55790, -9688, 1064, -56]

def termTenTailThreeRow14 : One :=
  [0, 8, 1196, 16640, 1448, -168532, 424928, -563416, 486710, -294868,
    128282, -39816, 8470, -1120, 70]

def termTenTailThreeRow15 : One :=
  [0, -56, -1944, -6496, 35204, -60904, 59648, -37576, 15820, -4368, 728,
    -56]

def termTenTailThreeRow16 : One :=
  [1, 119, 1177, -3761, 4572, -3088, 1232, -280, 28]

def termTenTailThreeRow17 : One :=
  [-3, -94, 201, -152, 56, -8]

def termTenTailThreeRow18 : One :=
  [3, -4, 1]

/-- Literal dense coefficient table for the staged product `B (D⁸ E)`. -/
def termTenTailThreeData : Two :=
  [termTenTailThreeRow0, termTenTailThreeRow1, termTenTailThreeRow2,
    termTenTailThreeRow3, termTenTailThreeRow4, termTenTailThreeRow5,
    termTenTailThreeRow6, termTenTailThreeRow7, termTenTailThreeRow8,
    termTenTailThreeRow9, termTenTailThreeRow10, termTenTailThreeRow11,
    termTenTailThreeRow12, termTenTailThreeRow13, termTenTailThreeRow14,
    termTenTailThreeRow15, termTenTailThreeRow16, termTenTailThreeRow17,
    termTenTailThreeRow18]

private theorem termTenTailThreeRow0_spec :
    padOne 28 (mulRow BData termTenTailTwoData 0) =
      (rectangularize 19 28 termTenTailThreeData).getD 0 [] := by decide

private theorem termTenTailThreeRow1_spec :
    padOne 28 (mulRow BData termTenTailTwoData 1) =
      (rectangularize 19 28 termTenTailThreeData).getD 1 [] := by decide

private theorem termTenTailThreeRow2_spec :
    padOne 28 (mulRow BData termTenTailTwoData 2) =
      (rectangularize 19 28 termTenTailThreeData).getD 2 [] := by decide

private theorem termTenTailThreeRow3_spec :
    padOne 28 (mulRow BData termTenTailTwoData 3) =
      (rectangularize 19 28 termTenTailThreeData).getD 3 [] := by decide

private theorem termTenTailThreeRow4_spec :
    padOne 28 (mulRow BData termTenTailTwoData 4) =
      (rectangularize 19 28 termTenTailThreeData).getD 4 [] := by decide

private theorem termTenTailThreeRow5_spec :
    padOne 28 (mulRow BData termTenTailTwoData 5) =
      (rectangularize 19 28 termTenTailThreeData).getD 5 [] := by decide

private theorem termTenTailThreeRow6_spec :
    padOne 28 (mulRow BData termTenTailTwoData 6) =
      (rectangularize 19 28 termTenTailThreeData).getD 6 [] := by decide

private theorem termTenTailThreeRow7_spec :
    padOne 28 (mulRow BData termTenTailTwoData 7) =
      (rectangularize 19 28 termTenTailThreeData).getD 7 [] := by decide

private theorem termTenTailThreeRow8_spec :
    padOne 28 (mulRow BData termTenTailTwoData 8) =
      (rectangularize 19 28 termTenTailThreeData).getD 8 [] := by decide

private theorem termTenTailThreeRow9_spec :
    padOne 28 (mulRow BData termTenTailTwoData 9) =
      (rectangularize 19 28 termTenTailThreeData).getD 9 [] := by decide

private theorem termTenTailThreeRow10_spec :
    padOne 28 (mulRow BData termTenTailTwoData 10) =
      (rectangularize 19 28 termTenTailThreeData).getD 10 [] := by decide

private theorem termTenTailThreeRow11_spec :
    padOne 28 (mulRow BData termTenTailTwoData 11) =
      (rectangularize 19 28 termTenTailThreeData).getD 11 [] := by decide

private theorem termTenTailThreeRow12_spec :
    padOne 28 (mulRow BData termTenTailTwoData 12) =
      (rectangularize 19 28 termTenTailThreeData).getD 12 [] := by decide

private theorem termTenTailThreeRow13_spec :
    padOne 28 (mulRow BData termTenTailTwoData 13) =
      (rectangularize 19 28 termTenTailThreeData).getD 13 [] := by decide

private theorem termTenTailThreeRow14_spec :
    padOne 28 (mulRow BData termTenTailTwoData 14) =
      (rectangularize 19 28 termTenTailThreeData).getD 14 [] := by decide

private theorem termTenTailThreeRow15_spec :
    padOne 28 (mulRow BData termTenTailTwoData 15) =
      (rectangularize 19 28 termTenTailThreeData).getD 15 [] := by decide

private theorem termTenTailThreeRow16_spec :
    padOne 28 (mulRow BData termTenTailTwoData 16) =
      (rectangularize 19 28 termTenTailThreeData).getD 16 [] := by decide

private theorem termTenTailThreeRow17_spec :
    padOne 28 (mulRow BData termTenTailTwoData 17) =
      (rectangularize 19 28 termTenTailThreeData).getD 17 [] := by decide

private theorem termTenTailThreeRow18_spec :
    padOne 28 (mulRow BData termTenTailTwoData 18) =
      (rectangularize 19 28 termTenTailThreeData).getD 18 [] := by decide

private theorem termTenTailThreeRows_spec (n : ℕ) (hn : n < 19) :
    padOne 28 (mulRow BData termTenTailTwoData n) =
      (rectangularize 19 28 termTenTailThreeData).getD n [] := by
  interval_cases n
  · exact termTenTailThreeRow0_spec
  · exact termTenTailThreeRow1_spec
  · exact termTenTailThreeRow2_spec
  · exact termTenTailThreeRow3_spec
  · exact termTenTailThreeRow4_spec
  · exact termTenTailThreeRow5_spec
  · exact termTenTailThreeRow6_spec
  · exact termTenTailThreeRow7_spec
  · exact termTenTailThreeRow8_spec
  · exact termTenTailThreeRow9_spec
  · exact termTenTailThreeRow10_spec
  · exact termTenTailThreeRow11_spec
  · exact termTenTailThreeRow12_spec
  · exact termTenTailThreeRow13_spec
  · exact termTenTailThreeRow14_spec
  · exact termTenTailThreeRow15_spec
  · exact termTenTailThreeRow16_spec
  · exact termTenTailThreeRow17_spec
  · exact termTenTailThreeRow18_spec

private theorem termTenTailThree_mul_outer :
    (Two.mul BData termTenTailTwoData).length ≤ 19 := by
  change
    (mulWith [] One.add One.mul BData termTenTailTwoData).length ≤ 19
  rw [length_mulWith_of_ne_nil [] One.add One.mul BData termTenTailTwoData
    (by decide) (by decide)]
  decide

private theorem termTenTailThree_data_outer :
    termTenTailThreeData.length ≤ 19 := by
  decide

/-- Evaluation of the kernel-checked second staged product in term ten. -/
theorem eval_termTenTailThreeData (r s : ℚ) :
    Two.eval termTenTailThreeData r s =
      Two.eval BData r s * Two.eval termTenTailTwoData r s := by
  exact eval_mulData_eq_mul_of_rows 19 28 BData termTenTailTwoData
    termTenTailThreeData termTenTailThree_mul_outer
    termTenTailThree_data_outer termTenTailThreeRows_spec r s

end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
