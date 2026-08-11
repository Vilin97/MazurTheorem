/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationFourCertificateDenseFactors

/-! # Dense multiplication stages 1 through 9 for RelationFour term three -/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Dense

open OrderTwentyFiveDensePolynomial

def TermThreeStage1 : Two :=
  [
    [1, -1]
  ]

theorem termThree_stage1_spec :
    Two.mul NegData BData = TermThreeStage1 := by
  decide

def TermThreeStage2 : Two :=
  [
    [-1, 2, -1]
  ]

theorem termThree_stage2_spec :
    Two.mul TermThreeStage1 BData = TermThreeStage2 := by
  decide

def TermThreeStage3 : Two :=
  [
    [0, -1, 2, -1],
    [0, 4, -11, 11, -5, 1],
    [-1, 2, -1]
  ]

theorem termThree_stage3_spec :
    Two.mul TermThreeStage2 DData = TermThreeStage3 := by
  decide

def TermThreeStage4 : Two :=
  [
    [0, 1, -2, 2, -2, 1],
    [0, -7, 16, -16, 15, -12, 5, -1],
    [1, 13, -34, 25, -4, -2, 1],
    [-3, -7, 36, -45, 26, -8, 1],
    [3, -7, 5, -1]
  ]

theorem termThree_stage4_spec :
    Two.mul TermThreeStage3 EData = TermThreeStage4 := by
  decide

def TermThreeStage5 : Two :=
  [
    [0, -1, 2, -3, 4, -3, 2, -1],
    [0, 10, -21, 27, -35, 29, -19, 13, -5, 1],
    [-1, -37, 81, -78, 75, -49, 7, 4, -2],
    [6, 68, -177, 157, -110, 94, -53, 17, -2],
    [-15, -55, 208, -200, 65, 5, -10, 2],
    [18, 0, -107, 173, -124, 50, -11, 1],
    [-9, 24, -22, 8, -1]
  ]

theorem termThree_stage5_spec :
    Two.mul TermThreeStage4 EData = TermThreeStage5 := by
  decide

def TermThreeStage6 : Two :=
  [
    [0, 1, -3, 6, -9, 10, -9, 6, -3, 1],
    [0, -11, 33, -61, 87, -94, 85, -62, 37, -19, 6, -1],
    [1, 46, -138, 223, -269, 231, -150, 65, -6, -5, 2],
    [-7, -99, 320, -480, 519, -410, 264, -160, 70, -19, 2],
    [21, 108, -425, 620, -583, 354, -103, 0, 10, -2],
    [-33, -37, 297, -480, 469, -342, 175, -60, 12, -1],
    [27, -33, -52, 119, -93, 41, -10, 1],
    [-9, 24, -22, 8, -1]
  ]

theorem termThree_stage6_spec :
    Two.mul TermThreeStage5 KData = TermThreeStage6 := by
  decide

def TermThreeStage7 : Two :=
  [
    [0, -1, 4, -10, 18, -25, 28, -25, 18, -10, 4, -1],
    [0, 12, -47, 111, -190, 252, -275, 247, -187, 119, -62, 26, -7, 1],
    [-1, -56, 216, -468, 717, -817, 735, -508, 258, -85, 5, 6, -2],
    [8, 138, -550, 1122, -1588, 1640, -1343, 899, -500, 244, -89, 21, -2],
    [-28, -186, 832, -1633, 2147, -1967, 1304, -617, 163, -7, -10, 2],
    [54, 112, -726, 1434, -1829, 1645, -1089, 577, -237, 71, -13, 1],
    [-60, 23, 289, -618, 733, -595, 319, -112, 23, -2],
    [36, -66, 3, 65, -62, 32, -9, 1],
    [-9, 24, -22, 8, -1]
  ]

theorem termThree_stage7_spec :
    Two.mul TermThreeStage6 KData = TermThreeStage7 := by
  decide

def TermThreeStage8 : Two :=
  [
    [0, 1, -5, 15, -32, 53, -71, 78, -71, 53, -32, 15, -5, 1],
    [0, -13, 63, -180, 366, -578, 745, -799, 727, -563, 372, -208, 95, -34, 8, -1],
    [1, 67, -318, 851, -1591, 2254, -2544, 2307, -1688, 970, -410, 110, -4, -7, 2],
    [-9, -186, 896, -2278, 3977, -5167, 5306, -4390, 3000, -1728, 838, -348, 110, -23, 2],
    [36, 296, -1540, 3773, -6200, 7387, -6761, 4787, -2584, 1031, -249, 16, 10, -2],
    [-82, -244, 1616, -3905, 6136, -6875, 5867, -3928, 2066, -892, 311, -83, 14, -1],
    [114, 29, -932, 2318, -3469, 3591, -2736, 1603, -691, 208, -38, 3],
    [-96, 125, 184, -614, 857, -754, 422, -154, 33, -3],
    [45, -99, 58, 11, -31, 23, -8, 1],
    [-9, 24, -22, 8, -1]
  ]

theorem termThree_stage8_spec :
    Two.mul TermThreeStage7 KData = TermThreeStage8 := by
  decide

def TermThreeStage9 : Two :=
  [
    [0, -1, 6, -21, 52, -100, 156, -202, 220, -202, 156, -100, 52, -21, 6, -1],
    [0, 14, -81, 271, -641, 1177, -1760, 2200, -2342, 2142, -1694, 1158, -680, 338, -137, 43, -9,
      1],
    [-1, -79, 447, -1416, 3126, -5274, 7134, -7904, 7266, -5528, 3440, -1698, 619, -141, 3, 8, -2],
    [10, 244, -1391, 4211, -8742, 13676, -16994, 17170, -14384, 10088, -5976, 3024, -1300, 474,
      -133, 25, -2],
    [-45, -446, 2696, -7887, 15490, -22527, 25654, -23325, 17132, -10130, 4702, -1644, 365, -27,
      -10, 2],
    [118, 458, -3318, 9538, -17857, 24303, -25639, 21457, -14445, 7917, -3518, 1302, -398, 96,
      -15, 1],
    [-196, -159, 2463, -7184, 12855, -16253, 15663, -11858, 7096, -3394, 1248, -332, 55, -4],
    [210, -192, -895, 2991, -5124, 5816, -4769, 2933, -1300, 398, -74, 6],
    [-141, 269, -18, -468, 841, -819, 484, -186, 42, -4],
    [54, -132, 113, -43, 0, 14, -7, 1],
    [-9, 24, -22, 8, -1]
  ]

theorem termThree_stage9_spec :
    Two.mul TermThreeStage8 KData = TermThreeStage9 := by
  decide

end MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Dense
