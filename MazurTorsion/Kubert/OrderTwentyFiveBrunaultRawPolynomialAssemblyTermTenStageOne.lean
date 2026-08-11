/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialPowerCertificate
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialWindow
import MazurTorsion.Kubert.OrderTwentyFiveDensePolynomialMulCertificate
import Mathlib.Tactic.IntervalCases

/-!
# The first staged product for raw Brunault numerator term ten

This leaf records the literal dense table for `D⁸ E` and checks it one padded
row at a time.  The generic multiplication-certificate facade then exposes its
evaluation without asking Lean to normalize the complete product at once.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveDensePolynomialRectangular
open OrderTwentyFiveDensePolynomialRowCertificate
open OrderTwentyFiveDensePolynomialMulCertificate
open OrderTwentyFiveRelationZeroCertificate.Dense

def termTenTailTwoRow0 : One :=
  [0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1]

def termTenTailTwoRow1 : One :=
  [0, 0, 0, 0, 0, 0, 0, 0, 35, -23, 40, -24, 8]

def termTenTailTwoRow2 : One :=
  [0, 0, 0, 0, 0, 0, 0, -8, -547, 705, -924, 832, -504, 168, -28]

def termTenTailTwoRow3 : One :=
  [0, 0, 0, 0, 0, 0, 0, 248, 4864, -9456, 12956, -13588, 10836, -6020,
    2240, -504, 56]

def termTenTailTwoRow4 : One :=
  [0, 0, 0, 0, 0, 0, -28, -3384, -25724, 71288, -111580, 130172,
    -121282, 87388, -47194, 18424, -4970, 840, -70]

def termTenTailTwoRow5 : One :=
  [0, 0, 0, 0, 0, 0, 756, 26180, 72240, -320208, 599200, -776552,
    802074, -674954, 455812, -241164, 97650, -29330, 6216, -840, 56]

def termTenTailTwoRow6 : One :=
  [0, 0, 0, 0, 0, -56, -8820, -122612, -21476, 806904, -1975960, 2907464,
    -3256974, 3008670, -2330664, 1495620, -780122, 324254, -105000, 25648,
    -4480, 504, -28]

def termTenTailTwoRow7 : One :=
  [0, 0, 0, 0, 0, 1288, 57232, 335888, -575564, -708708, 3641516, -6601588,
    8090992, -7862288, 6482532, -4621452, 2823996, -1451404, 615076, -210644,
    56924, -11732, 1744, -168, 8]

def termTenTailTwoRow8 : One :=
  [0, 0, 0, 0, -70, -12488, -220374, -413392, 1935164, -1748676, -2197544,
    7997372, -11877660, 12131112, -9833768, 6837684, -4252793, 2383340,
    -1181889, 504556, -180558, 52836, -12306, 2200, -285, 24, -1]

def termTenTailTwoRow9 : One :=
  [0, 0, 0, 0, 1330, 65310, 487872, -308584, -2423424, 5636688, -4537540,
    -1803812, 8843016, -11780104, 9998860, -6141516, 2818299, -948647,
    210228, -14420, -10318, 5118, -1308, 212, -21, 1]

def termTenTailTwoRow10 : One :=
  [0, 0, 0, -56, -10290, -194586, -496804, 1676880, -240264, -4967568,
    9649056, -8737004, 2455964, 4390232, -7733612, 7191412, -4786387,
    2467777, -1015444, 336644, -89614, 18862, -3044, 356, -27, 1]

def termTenTailTwoRow11 : One :=
  [0, 0, 0, 840, 40992, 313264, -131964, -1696284, 3495404, -1889748,
    -3486448, 9039688, -11157468, 9452492, -6033204, 3009156, -1188796,
    371756, -90804, 16828, -2240, 192, -8]

def termTenTailTwoRow12 : One :=
  [0, 0, -28, -4872, -86940, -198856, 746844, -285068, -1927114, 4620924,
    -5857866, 5082056, -3267222, 1606724, -609994, 177492, -38612, 5964,
    -588, 28]

def termTenTailTwoRow13 : One :=
  [0, 0, 308, 13524, 88144, -92512, -363552, 1148056, -1653190, 1535870,
    -1014188, 493724, -178430, 47110, -8680, 1008, -56]

def termTenTailTwoRow14 : One :=
  [0, -8, -1204, -17844, -19292, 149240, -275688, 287728, -198982, 95886,
    -32396, 7420, -1050, 70]

def termTenTailTwoRow15 : One :=
  [0, 56, 2000, 8496, -26708, 34196, -25452, 12124, -3696, 672, -56]

def termTenTailTwoRow16 : One :=
  [-1, -120, -1297, 2464, -2108, 980, -252, 28]

def termTenTailTwoRow17 : One :=
  [3, 97, -104, 48, -8]

def termTenTailTwoRow18 : One :=
  [-3, 1]

/-- Literal dense coefficient table for the staged product `D⁸ E`. -/
def termTenTailTwoData : Two :=
  [termTenTailTwoRow0, termTenTailTwoRow1, termTenTailTwoRow2,
    termTenTailTwoRow3, termTenTailTwoRow4, termTenTailTwoRow5,
    termTenTailTwoRow6, termTenTailTwoRow7, termTenTailTwoRow8,
    termTenTailTwoRow9, termTenTailTwoRow10, termTenTailTwoRow11,
    termTenTailTwoRow12, termTenTailTwoRow13, termTenTailTwoRow14,
    termTenTailTwoRow15, termTenTailTwoRow16, termTenTailTwoRow17,
    termTenTailTwoRow18]

private theorem termTenTailTwoRow0_spec :
    padOne 27 (mulRow D8Data EData 0) =
      (rectangularize 19 27 termTenTailTwoData).getD 0 [] := by decide

private theorem termTenTailTwoRow1_spec :
    padOne 27 (mulRow D8Data EData 1) =
      (rectangularize 19 27 termTenTailTwoData).getD 1 [] := by decide

private theorem termTenTailTwoRow2_spec :
    padOne 27 (mulRow D8Data EData 2) =
      (rectangularize 19 27 termTenTailTwoData).getD 2 [] := by decide

private theorem termTenTailTwoRow3_spec :
    padOne 27 (mulRow D8Data EData 3) =
      (rectangularize 19 27 termTenTailTwoData).getD 3 [] := by decide

private theorem termTenTailTwoRow4_spec :
    padOne 27 (mulRow D8Data EData 4) =
      (rectangularize 19 27 termTenTailTwoData).getD 4 [] := by decide

private theorem termTenTailTwoRow5_spec :
    padOne 27 (mulRow D8Data EData 5) =
      (rectangularize 19 27 termTenTailTwoData).getD 5 [] := by decide

private theorem termTenTailTwoRow6_spec :
    padOne 27 (mulRow D8Data EData 6) =
      (rectangularize 19 27 termTenTailTwoData).getD 6 [] := by decide

private theorem termTenTailTwoRow7_spec :
    padOne 27 (mulRow D8Data EData 7) =
      (rectangularize 19 27 termTenTailTwoData).getD 7 [] := by decide

private theorem termTenTailTwoRow8_spec :
    padOne 27 (mulRow D8Data EData 8) =
      (rectangularize 19 27 termTenTailTwoData).getD 8 [] := by decide

private theorem termTenTailTwoRow9_spec :
    padOne 27 (mulRow D8Data EData 9) =
      (rectangularize 19 27 termTenTailTwoData).getD 9 [] := by decide

private theorem termTenTailTwoRow10_spec :
    padOne 27 (mulRow D8Data EData 10) =
      (rectangularize 19 27 termTenTailTwoData).getD 10 [] := by decide

private theorem termTenTailTwoRow11_spec :
    padOne 27 (mulRow D8Data EData 11) =
      (rectangularize 19 27 termTenTailTwoData).getD 11 [] := by decide

private theorem termTenTailTwoRow12_spec :
    padOne 27 (mulRow D8Data EData 12) =
      (rectangularize 19 27 termTenTailTwoData).getD 12 [] := by decide

private theorem termTenTailTwoRow13_spec :
    padOne 27 (mulRow D8Data EData 13) =
      (rectangularize 19 27 termTenTailTwoData).getD 13 [] := by decide

private theorem termTenTailTwoRow14_spec :
    padOne 27 (mulRow D8Data EData 14) =
      (rectangularize 19 27 termTenTailTwoData).getD 14 [] := by decide

private theorem termTenTailTwoRow15_spec :
    padOne 27 (mulRow D8Data EData 15) =
      (rectangularize 19 27 termTenTailTwoData).getD 15 [] := by decide

private theorem termTenTailTwoRow16_spec :
    padOne 27 (mulRow D8Data EData 16) =
      (rectangularize 19 27 termTenTailTwoData).getD 16 [] := by decide

private theorem termTenTailTwoRow17_spec :
    padOne 27 (mulRow D8Data EData 17) =
      (rectangularize 19 27 termTenTailTwoData).getD 17 [] := by decide

private theorem termTenTailTwoRow18_spec :
    padOne 27 (mulRow D8Data EData 18) =
      (rectangularize 19 27 termTenTailTwoData).getD 18 [] := by decide

private theorem termTenTailTwoRows_spec (n : ℕ) (hn : n < 19) :
    padOne 27 (mulRow D8Data EData n) =
      (rectangularize 19 27 termTenTailTwoData).getD n [] := by
  interval_cases n
  · exact termTenTailTwoRow0_spec
  · exact termTenTailTwoRow1_spec
  · exact termTenTailTwoRow2_spec
  · exact termTenTailTwoRow3_spec
  · exact termTenTailTwoRow4_spec
  · exact termTenTailTwoRow5_spec
  · exact termTenTailTwoRow6_spec
  · exact termTenTailTwoRow7_spec
  · exact termTenTailTwoRow8_spec
  · exact termTenTailTwoRow9_spec
  · exact termTenTailTwoRow10_spec
  · exact termTenTailTwoRow11_spec
  · exact termTenTailTwoRow12_spec
  · exact termTenTailTwoRow13_spec
  · exact termTenTailTwoRow14_spec
  · exact termTenTailTwoRow15_spec
  · exact termTenTailTwoRow16_spec
  · exact termTenTailTwoRow17_spec
  · exact termTenTailTwoRow18_spec

private theorem termTenTailTwo_mul_outer :
    (Two.mul D8Data EData).length ≤ 19 := by
  change
    (mulWith [] One.add One.mul D8Data EData).length ≤ 19
  rw [length_mulWith_of_ne_nil [] One.add One.mul D8Data EData
    (by decide) (by decide)]
  decide

private theorem termTenTailTwo_data_outer : termTenTailTwoData.length ≤ 19 := by
  decide

/-- Evaluation of the kernel-checked first staged product in term ten. -/
theorem eval_termTenTailTwoData (r s : ℚ) :
    Two.eval termTenTailTwoData r s =
      Two.eval D8Data r s * Two.eval EData r s := by
  exact eval_mulData_eq_mul_of_rows 19 27 D8Data EData termTenTailTwoData
    termTenTailTwo_mul_outer termTenTailTwo_data_outer
    termTenTailTwoRows_spec r s

end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
