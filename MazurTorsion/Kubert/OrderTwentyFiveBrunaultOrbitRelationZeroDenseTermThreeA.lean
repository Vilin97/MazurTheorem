/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroDenseFactors

/-!
# Dense multiplication stages 1 through 5 for cleared term three

Each closed integer-table multiplication is checked by Lean.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Dense

open OrderTwentyFiveDensePolynomial

def T3Stage1 : Two :=
  [[0, 1], [0, -2, 1]]

theorem t3_stage1_spec :
    Two.mul SData CData = T3Stage1 := by
  decide

def T3Stage2 : Two :=
  [[0, 1], [0, -4, 2], [0, 4, -4, 1]]

theorem t3_stage2_spec :
    Two.mul T3Stage1 CData = T3Stage2 := by
  decide

def T3Stage3 : Two :=
  [[0, 1], [0, -6, 3], [0, 12, -12, 3], [0, -8, 12, -6, 1]]

theorem t3_stage3_spec :
    Two.mul T3Stage2 CData = T3Stage3 := by
  decide

def T3Stage4 : Two :=
  [[0, 0, 0, 0, 0, 1], [0, 1, -3, 6, -10, -2, 2], [0, -8, 23, -42, 78, -42, 6, 0], [0, 26, -70,
    100, -192, 178, -78, 18, -2], [0, -44, 114, -102, 144, -182, 122, -46, 10, -1], [0, 40,
    -112, 78, -2, -13, 3], [0, -16, 56, -68, 38, -10, 1]]

theorem t3_stage4_spec :
    Two.mul T3Stage3 JData = T3Stage4 := by
  decide

def T3Stage5 : Two :=
  [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, -1, 4, -9, 16, -25, 1, 2], [0, 0,
    -1, 6, -21, 56, -102, 134, -133, 63, 164, -128, 33, -6, 1], [0, 0, 15, -86, 280, -706, 1332,
    -1946, 2429, -2599, 1204, -52, -139, 62, -16, 2], [0, 0, -103, 567, -1694, 3906, -7001,
    9737, -11760, 14348, -12041, 6201, -2084, 488, -74, 5, 0], [0, 0, 429, -2305, 6370, -13230,
    21833, -27083, 26070, -29054, 30501, -22515, 11476, -4250, 1169, -231, 30, -2], [0, -1,
    -1191, 6386, -16731, 31605, -48776, 57232, -42033, 24425, -21354, 20694, -14399, 7021,
    -2506, 664, -127, 16, -1], [0, 9, 2264, -12390, 31555, -54677, 79198, -98042, 81707, -36917,
    4368, 3710, -1869, 259, 56, -26, 3], [0, -34, -2919, 16734, -42456, 67324, -84117, 102409,
    -107070, 79026, -37695, 10619, -1120, -344, 165, -29, 2], [0, 70, 2432, -15226, 40084,
    -60842, 60067, -49955, 46578, -42318, 29343, -14413, 4998, -1222, 204, -21, 1], [0, -84,
    -1134, 8460, -24546, 40499, -40225, 23186, -5945, -1189, 1461, -490, 78, -5], [0, 56, 152,
    -2078, 7120, -13911, 17700, -15312, 9165, -3799, 1071, -196, 21, -1], [0, -16, 56, -68, 38,
    -10, 1]]

theorem t3_stage5_spec :
    Two.mul T3Stage4 P6Data = T3Stage5 := by
  decide

end MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Dense
