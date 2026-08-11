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
# The first staged product for raw Brunault numerator term eleven

This leaf records the literal dense table for `E⁵ T²` and checks it one padded
row at a time.  The generic multiplication-certificate facade then exposes its
evaluation without asking Lean to normalize the complete product at once.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveDensePolynomialRectangular
open OrderTwentyFiveDensePolynomialRowCertificate
open OrderTwentyFiveDensePolynomialMulCertificate
open OrderTwentyFiveRelationZeroCertificate.Dense

def termElevenTailTwoRow0 : One :=
  [0, 0, -1, 0, -5, 0, -10, 0, -10, 0, -5, 0, -1]

def termElevenTailTwoRow1 : One :=
  [0, -2, 29, -17, 136, -62, 260, -120, 260, -130, 145, -77, 44, -22, 6,
    -2]

def termElevenTailTwoRow2 : One :=
  [-1, 46, -383, 355, -1627, 1170, -2871, 2046, -2781, 2040, -1686, 1191,
    -693, 410, -187, 80, -26, 6, -1]

def termElevenTailTwoRow3 : One :=
  [17, -471, 3001, -3255, 11102, -9304, 16891, -13497, 13840, -10450, 6717,
    -4211, 1856, -770, 207, -29, 1, 3]

def termElevenTailTwoRow4 : One :=
  [-136, 2917, -15821, 18297, -49932, 45310, -64216, 54255, -44535, 33200,
    -18596, 10577, -4671, 1872, -687, 175, -46, 5]

def termElevenTailTwoRow5 : One :=
  [675, -12335, 60193, -71895, 160185, -153785, 173650, -149324, 102565,
    -69835, 35050, -15780, 5775, -1355, 285, 5, -10]

def termElevenTailTwoRow6 : One :=
  [-2310, 37841, -172147, 211121, -384733, 386101, -357063, 298536, -183918,
    108199, -52248, 20530, -7675, 2085, -520, 115, -10]

def termElevenTailTwoRow7 : One :=
  [5733, -86943, 378489, -480115, 715341, -735629, 584632, -445020, 258883,
    -126613, 54465, -17099, 4539, -879, 30, 10]

def termElevenTailTwoRow8 : One :=
  [-10566, 151773, -645643, 858985, -1058406, 1073565, -782062, 512500,
    -284080, 123243, -47141, 14409, -3268, 715, -130, 10]

def termElevenTailTwoRow9 : One :=
  [14553, -201501, 852453, -1208771, 1276336, -1204254, 845696, -475324,
    234193, -91553, 28615, -7709, 1450, -120]

def termElevenTailTwoRow10 : One :=
  [-14850, 201015, -858393, 1317025, -1270510, 1050680, -711025, 366396,
    -154750, 54135, -14045, 2695, -470, 70, -5]

def termElevenTailTwoRow11 : One :=
  [10935, -146421, 639117, -1073871, 1025453, -734541, 446572, -217884,
    82367, -25561, 6567, -1205, 125, -5]

def termElevenTailTwoRow12 : One :=
  [-5508, 73683, -332154, 616065, -626261, 420361, -216739, 91936, -30463,
    7227, -1195, 151, -16, 1]

def termElevenTailTwoRow13 : One :=
  [1701, -22923, 107568, -220950, 250536, -178074, 86759, -31547, 9215,
    -2177, 379, -41, 2]

def termElevenTailTwoRow14 : One :=
  [-243, 3321, -16308, 37026, -47616, 38476, -20565, 7411, -1787, 277, -25,
    1]

/-- Literal dense coefficient table for the staged product `E⁵ T²`. -/
def termElevenTailTwoData : Two :=
  [termElevenTailTwoRow0, termElevenTailTwoRow1, termElevenTailTwoRow2,
    termElevenTailTwoRow3, termElevenTailTwoRow4, termElevenTailTwoRow5,
    termElevenTailTwoRow6, termElevenTailTwoRow7, termElevenTailTwoRow8,
    termElevenTailTwoRow9, termElevenTailTwoRow10, termElevenTailTwoRow11,
    termElevenTailTwoRow12, termElevenTailTwoRow13, termElevenTailTwoRow14]

private theorem termElevenTailTwoRow0_spec :
    padOne 19 (mulRow E5Data T2Data 0) =
      (rectangularize 15 19 termElevenTailTwoData).getD 0 [] := by decide

private theorem termElevenTailTwoRow1_spec :
    padOne 19 (mulRow E5Data T2Data 1) =
      (rectangularize 15 19 termElevenTailTwoData).getD 1 [] := by decide

private theorem termElevenTailTwoRow2_spec :
    padOne 19 (mulRow E5Data T2Data 2) =
      (rectangularize 15 19 termElevenTailTwoData).getD 2 [] := by decide

private theorem termElevenTailTwoRow3_spec :
    padOne 19 (mulRow E5Data T2Data 3) =
      (rectangularize 15 19 termElevenTailTwoData).getD 3 [] := by decide

private theorem termElevenTailTwoRow4_spec :
    padOne 19 (mulRow E5Data T2Data 4) =
      (rectangularize 15 19 termElevenTailTwoData).getD 4 [] := by decide

private theorem termElevenTailTwoRow5_spec :
    padOne 19 (mulRow E5Data T2Data 5) =
      (rectangularize 15 19 termElevenTailTwoData).getD 5 [] := by decide

private theorem termElevenTailTwoRow6_spec :
    padOne 19 (mulRow E5Data T2Data 6) =
      (rectangularize 15 19 termElevenTailTwoData).getD 6 [] := by decide

private theorem termElevenTailTwoRow7_spec :
    padOne 19 (mulRow E5Data T2Data 7) =
      (rectangularize 15 19 termElevenTailTwoData).getD 7 [] := by decide

private theorem termElevenTailTwoRow8_spec :
    padOne 19 (mulRow E5Data T2Data 8) =
      (rectangularize 15 19 termElevenTailTwoData).getD 8 [] := by decide

private theorem termElevenTailTwoRow9_spec :
    padOne 19 (mulRow E5Data T2Data 9) =
      (rectangularize 15 19 termElevenTailTwoData).getD 9 [] := by decide

private theorem termElevenTailTwoRow10_spec :
    padOne 19 (mulRow E5Data T2Data 10) =
      (rectangularize 15 19 termElevenTailTwoData).getD 10 [] := by decide

private theorem termElevenTailTwoRow11_spec :
    padOne 19 (mulRow E5Data T2Data 11) =
      (rectangularize 15 19 termElevenTailTwoData).getD 11 [] := by decide

private theorem termElevenTailTwoRow12_spec :
    padOne 19 (mulRow E5Data T2Data 12) =
      (rectangularize 15 19 termElevenTailTwoData).getD 12 [] := by decide

private theorem termElevenTailTwoRow13_spec :
    padOne 19 (mulRow E5Data T2Data 13) =
      (rectangularize 15 19 termElevenTailTwoData).getD 13 [] := by decide

private theorem termElevenTailTwoRow14_spec :
    padOne 19 (mulRow E5Data T2Data 14) =
      (rectangularize 15 19 termElevenTailTwoData).getD 14 [] := by decide

private theorem termElevenTailTwoRows_spec (n : ℕ) (hn : n < 15) :
    padOne 19 (mulRow E5Data T2Data n) =
      (rectangularize 15 19 termElevenTailTwoData).getD n [] := by
  interval_cases n
  · exact termElevenTailTwoRow0_spec
  · exact termElevenTailTwoRow1_spec
  · exact termElevenTailTwoRow2_spec
  · exact termElevenTailTwoRow3_spec
  · exact termElevenTailTwoRow4_spec
  · exact termElevenTailTwoRow5_spec
  · exact termElevenTailTwoRow6_spec
  · exact termElevenTailTwoRow7_spec
  · exact termElevenTailTwoRow8_spec
  · exact termElevenTailTwoRow9_spec
  · exact termElevenTailTwoRow10_spec
  · exact termElevenTailTwoRow11_spec
  · exact termElevenTailTwoRow12_spec
  · exact termElevenTailTwoRow13_spec
  · exact termElevenTailTwoRow14_spec

private theorem termElevenTailTwo_mul_outer :
    (Two.mul E5Data T2Data).length ≤ 15 := by
  change
    (mulWith [] One.add One.mul E5Data T2Data).length ≤ 15
  rw [length_mulWith_of_ne_nil [] One.add One.mul E5Data T2Data
    (by decide) (by decide)]
  decide

private theorem termElevenTailTwo_data_outer :
    termElevenTailTwoData.length ≤ 15 := by
  decide

/-- Evaluation of the kernel-checked first staged product in term eleven. -/
theorem eval_termElevenTailTwoData (r s : ℚ) :
    Two.eval termElevenTailTwoData r s =
      Two.eval E5Data r s * Two.eval T2Data r s := by
  exact eval_mulData_eq_mul_of_rows 15 19 E5Data T2Data
    termElevenTailTwoData termElevenTailTwo_mul_outer
    termElevenTailTwo_data_outer termElevenTailTwoRows_spec r s

end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
