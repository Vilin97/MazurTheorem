/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroDenseFactors

/-!
# Dense multiplication stages 1 through 8 for cleared term one

Each closed integer-table multiplication is checked by Lean.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Dense

open OrderTwentyFiveDensePolynomial

def T1Stage1 : Two :=
  [[], [-1]]

theorem t1_stage1_spec :
    Two.mul NegData RData = T1Stage1 := by
  decide

def T1Stage2 : Two :=
  [[], [1, -1]]

theorem t1_stage2_spec :
    Two.mul T1Stage1 BData = T1Stage2 := by
  decide

def T1Stage3 : Two :=
  [[], [-1, 2, -1]]

theorem t1_stage3_spec :
    Two.mul T1Stage2 BData = T1Stage3 := by
  decide

def T1Stage4 : Two :=
  [[], [1, -3, 4, -3, 1], [-1, 2, -1]]

theorem t1_stage4_spec :
    Two.mul T1Stage3 KData = T1Stage4 := by
  decide

def T1Stage5 : Two :=
  [[], [-1, 4, -8, 10, -8, 4, -1], [2, -6, 8, -6, 2], [-1, 2, -1]]

theorem t1_stage5_spec :
    Two.mul T1Stage4 KData = T1Stage5 := by
  decide

def T1Stage6 : Two :=
  [[], [0, -1, 4, -8, 10, -8, 4, -1], [0, 6, -25, 53, -74, 72, -50, 24, -7, 1], [-1, -5, 24,
    -43, 46, -30, 11, -2], [2, -2, -3, 5, -3, 1], [-1, 2, -1]]

theorem t1_stage6_spec :
    Two.mul T1Stage5 DData = T1Stage6 := by
  decide

def T1Stage7 : Two :=
  [[], [0, 1, -4, 9, -14, 16, -14, 9, -4, 1], [0, -9, 36, -79, 121, -139, 128, -95, 56, -25, 7,
    -1], [1, 26, -105, 210, -277, 249, -155, 61, -9, -2, 1], [-5, -32, 149, -292, 376, -340,
    228, -118, 43, -10, 1], [10, 8, -86, 163, -184, 136, -62, 17, -2], [-9, 13, 6, -19, 14, -6,
    1], [3, -7, 5, -1]]

theorem t1_stage7_spec :
    Two.mul T1Stage6 EData = T1Stage7 := by
  decide

def T1Stage8 : Two :=
  [[], [0, -1, 4, -10, 18, -25, 28, -25, 18, -10, 4, -1], [0, 12, -47, 111, -190, 252, -275,
    247, -187, 119, -62, 26, -7, 1], [-1, -56, 216, -468, 717, -817, 735, -508, 258, -85, 5, 6,
    -2], [8, 138, -550, 1122, -1588, 1640, -1343, 899, -500, 244, -89, 21, -2], [-28, -186, 832,
    -1633, 2147, -1967, 1304, -617, 163, -7, -10, 2], [54, 112, -726, 1434, -1829, 1645, -1089,
    577, -237, 71, -13, 1], [-60, 23, 289, -618, 733, -595, 319, -112, 23, -2], [36, -66, 3, 65,
    -62, 32, -9, 1], [-9, 24, -22, 8, -1]]

theorem t1_stage8_spec :
    Two.mul T1Stage7 EData = T1Stage8 := by
  decide

end MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Dense
