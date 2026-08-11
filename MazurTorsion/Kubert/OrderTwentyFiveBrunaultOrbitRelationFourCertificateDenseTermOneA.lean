/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationFourCertificateDenseFactors

/-! # Dense multiplication stages 1 through 8 for RelationFour term one -/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Dense

open OrderTwentyFiveDensePolynomial

def TermOneStage1 : Two :=
  [[0, 0, 1], [0, -2], [1]]

theorem termOne_stage1_spec :
    Two.mul AData AData = TermOneStage1 := by
  decide

def TermOneStage2 : Two :=
  [[0, 0, -1, 1], [0, 2, -2], [-1, 1]]

theorem termOne_stage2_spec :
    Two.mul TermOneStage1 BData = TermOneStage2 := by
  decide

def TermOneStage3 : Two :=
  [[0, 0, 1, -2, 1], [0, -2, 4, -2], [1, -2, 1]]

theorem termOne_stage3_spec :
    Two.mul TermOneStage2 BData = TermOneStage3 := by
  decide

def TermOneStage4 : Two :=
  [[0, 0, 1, -2, 1], [0, -2, 2, 3, -4, 1], [1, 2, -9, 8, -2], [-2, 5, -4, 1]]

theorem termOne_stage4_spec :
    Two.mul TermOneStage3 CData = TermOneStage4 := by
  decide

def TermOneStage5 : Two :=
  [[0, 0, 1, -2, 1], [0, -2, 0, 8, -8, 2], [1, 6, -15, 4, 9, -6, 1], [-4, 2, 16, -24, 12, -2],
   [4, -12, 13, -6, 1]]

theorem termOne_stage5_spec :
    Two.mul TermOneStage4 CData = TermOneStage5 := by
  decide

def TermOneStage6 : Two :=
  [[0, 0, 1, -2, 1], [0, -2, -2, 13, -12, 3], [1, 10, -17, -12, 33, -18, 3],
   [-6, -9, 52, -47, -2, 19, -8, 1], [12, -20, -17, 58, -47, 16, -2], [-8, 28, -38, 25, -8, 1]]

theorem termOne_stage6_spec :
    Two.mul TermOneStage5 CData = TermOneStage6 := by
  decide

def TermOneStage7 : Two :=
  [[0, 0, 1, -2, 1], [0, -2, -4, 18, -16, 4], [1, 14, -15, -40, 70, -36, 6],
   [-8, -28, 96, -40, -80, 88, -32, 4], [24, -8, -130, 204, -90, -24, 33, -10, 1],
   [-32, 80, -24, -108, 144, -78, 20, -2], [16, -64, 104, -88, 41, -10, 1]]

theorem termOne_stage7_spec :
    Two.mul TermOneStage6 CData = TermOneStage7 := by
  decide

def TermOneStage8 : Two :=
  [[0, 0, 1, -2, 1], [0, -2, -6, 23, -20, 5], [1, 18, -9, -80, 120, -60, 10],
   [-10, -55, 140, 25, -260, 230, -80, 10], [40, 40, -350, 380, 30, -280, 185, -50, 5],
   [-80, 120, 228, -646, 528, -120, -70, 51, -12, 1],
   [80, -256, 232, 104, -355, 290, -117, 24, -2], [-32, 144, -272, 280, -170, 61, -12, 1]]

theorem termOne_stage8_spec :
    Two.mul TermOneStage7 CData = TermOneStage8 := by
  decide

end MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Dense
