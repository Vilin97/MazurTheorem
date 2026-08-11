/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationFourCertificateDenseFactors

/-! # Dense multiplication stages 1 through 7 for RelationFour term zero -/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Dense

open OrderTwentyFiveDensePolynomial

def TermZeroStage1 : Two :=
  [[1, -1]]

theorem termZero_stage1_spec :
    Two.mul NegData BData = TermZeroStage1 := by
  decide

def TermZeroStage2 : Two :=
  [[1, -1], [-2, 3, -1]]

theorem termZero_stage2_spec :
    Two.mul TermZeroStage1 CData = TermZeroStage2 := by
  decide

def TermZeroStage3 : Two :=
  [[1, -1], [-4, 6, -2], [4, -8, 5, -1]]

theorem termZero_stage3_spec :
    Two.mul TermZeroStage2 CData = TermZeroStage3 := by
  decide

def TermZeroStage4 : Two :=
  [[1, -1], [-6, 9, -3], [12, -24, 15, -3], [-8, 20, -18, 7, -1]]

theorem termZero_stage4_spec :
    Two.mul TermZeroStage3 CData = TermZeroStage4 := by
  decide

def TermZeroStage5 : Two :=
  [[0, 1, -1], [0, -10, 16, -7, 1], [1, 35, -78, 60, -21, 3], [-6, -47, 149, -162, 88, -25, 3],
   [12, 8, -89, 137, -102, 43, -10, 1], [-8, 20, -18, 7, -1]]

theorem termZero_stage5_spec :
    Two.mul TermZeroStage4 DData = TermZeroStage5 := by
  decide

def TermZeroStage6 : Two :=
  [[0, 0, 1, -1], [0, 0, -14, 23, -11, 2], [0, 2, 74, -172, 146, -62, 13, -1],
   [0, -20, -168, 558, -670, 430, -160, 33, -3],
   [1, 71, 100, -760, 1258, -1086, 569, -185, 35, -3],
   [-6, -103, 173, 188, -728, 882, -612, 271, -77, 13, -1],
   [12, 40, -193, 277, -204, 86, -20, 2], [-8, 20, -18, 7, -1]]

theorem termZero_stage6_spec :
    Two.mul TermZeroStage5 DData = TermZeroStage6 := by
  decide

def TermZeroStage7 : Two :=
  [[0, 0, -1, 1, -1, 1], [0, 0, 17, -25, 24, -25, 11, -2],
   [0, -2, -119, 229, -231, 229, -157, 63, -13, 1],
   [0, 26, 434, -1063, 1160, -1045, 809, -453, 162, -33, 3],
   [-1, -137, -845, 2785, -3420, 2798, -1978, 1226, -581, 185, -35, 3],
   [9, 377, 688, -4107, 6137, -5030, 2871, -1398, 651, -261, 75, -13, 1],
   [-33, -567, 368, 2800, -6133, 6071, -3523, 1237, -230, 4, 7, -1],
   [62, 415, -1135, 220, 2056, -3327, 2745, -1439, 504, -116, 16, -1],
   [-60, -56, 585, -1021, 893, -463, 146, -26, 2], [24, -68, 74, -39, 10, -1]]

theorem termZero_stage7_spec :
    Two.mul TermZeroStage6 EData = TermZeroStage7 := by
  decide

end MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Dense
