/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroDenseFactors

/-!
# Dense multiplication stages 1 through 10 for cleared term two

Each closed integer-table multiplication is checked by Lean.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Dense

open OrderTwentyFiveDensePolynomial

def T2Stage1 : Two :=
  [[], [0, 1]]

theorem t2_stage1_spec :
    Two.mul RData SData = T2Stage1 := by
  decide

def T2Stage2 : Two :=
  [[], [0, -1, 1]]

theorem t2_stage2_spec :
    Two.mul T2Stage1 BData = T2Stage2 := by
  decide

def T2Stage3 : Two :=
  [[], [0, 1, -2, 1]]

theorem t2_stage3_spec :
    Two.mul T2Stage2 BData = T2Stage3 := by
  decide

def T2Stage4 : Two :=
  [[], [0, 1, -2, 1], [0, -2, 5, -4, 1]]

theorem t2_stage4_spec :
    Two.mul T2Stage3 CData = T2Stage4 := by
  decide

def T2Stage5 : Two :=
  [[], [0, 1, -2, 1], [0, -4, 10, -8, 2], [0, 4, -12, 13, -6, 1]]

theorem t2_stage5_spec :
    Two.mul T2Stage4 CData = T2Stage5 := by
  decide

def T2Stage6 : Two :=
  [[], [0, 1, -2, 1], [0, -6, 15, -12, 3], [0, 12, -36, 39, -18, 3], [0, -8, 28, -38, 25, -8,
    1]]

theorem t2_stage6_spec :
    Two.mul T2Stage5 CData = T2Stage6 := by
  decide

def T2Stage7 : Two :=
  [[], [0, -1, 3, -4, 3, -1], [0, 7, -23, 34, -30, 15, -3], [0, -18, 63, -99, 96, -60, 21, -3],
    [0, 20, -72, 113, -109, 74, -34, 9, -1], [0, -8, 28, -38, 25, -8, 1]]

theorem t2_stage7_spec :
    Two.mul T2Stage6 KData = T2Stage7 := by
  decide

def T2Stage8 : Two :=
  [[], [0, 1, -4, 8, -10, 8, -4, 1], [0, -8, 33, -68, 90, -80, 48, -18, 3], [0, 25, -104, 214,
    -288, 270, -180, 84, -24, 3], [0, -38, 155, -304, 390, -356, 238, -120, 44, -10, 1], [0, 28,
    -108, 187, -200, 145, -68, 18, -2], [0, -8, 28, -38, 25, -8, 1]]

theorem t2_stage8_spec :
    Two.mul T2Stage7 KData = T2Stage8 := by
  decide

def T2Stage9 : Two :=
  [[], [0, -1, 4, -9, 14, -16, 14, -9, 4, -1], [0, 11, -44, 96, -145, 162, -142, 97, -50, 18,
    -3], [0, -52, 208, -438, 632, -668, 552, -367, 196, -84, 24, -3], [0, 137, -549, 1117,
    -1533, 1512, -1122, 650, -297, 118, -42, 10, -1], [0, -217, 872, -1718, 2252, -2108, 1436,
    -717, 238, -37, -2, 1], [0, 206, -827, 1566, -1940, 1739, -1155, 592, -241, 72, -13, 1], [0,
    -108, 428, -755, 824, -634, 344, -121, 24, -2], [0, 24, -92, 142, -113, 49, -11, 1]]

theorem t2_stage9_spec :
    Two.mul T2Stage8 EData = T2Stage9 := by
  decide

def T2Stage10 : Two :=
  [[], [0, 1, -4, 10, -18, 25, -28, 25, -18, 10, -4, 1], [0, -14, 55, -130, 222, -292, 313,
    -272, 195, -114, 52, -18, 3], [0, 88, -342, 765, -1230, 1509, -1506, 1225, -822, 462, -212,
    84, -24, 3], [0, -326, 1264, -2692, 4071, -4632, 4231, -3144, 1887, -928, 354, -116, 40,
    -10, 1], [0, 784, -3058, 6259, -8940, 9465, -7866, 5306, -2870, 1259, -400, 57, 6, -2], [0,
    -1268, 5010, -9954, 13521, -13446, 10173, -6118, 2934, -1188, 455, -144, 27, -2], [0, 1377,
    -5536, 10760, -13980, 13242, -9310, 4963, -1930, 447, -22, -13, 2], [0, -966, 3955, -7528,
    9308, -8426, 5726, -3000, 1277, -440, 109, -16, 1], [0, 396, -1644, 3027, -3424, 2760,
    -1650, 699, -192, 30, -2], [0, -72, 300, -518, 481, -260, 82, -14, 1]]

theorem t2_stage10_spec :
    Two.mul T2Stage9 EData = T2Stage10 := by
  decide

end MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Dense
