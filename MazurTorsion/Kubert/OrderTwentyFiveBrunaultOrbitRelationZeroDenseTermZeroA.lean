/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroDenseFactors

/-!
# Dense multiplication stages 1 through 7 for cleared term zero

Each exact integer-table multiplication is reduced and checked by Lean.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Dense

open OrderTwentyFiveDensePolynomial

def T0Stage1 : Two :=
  [[], [-1]]

theorem t0_stage1_spec :
    Two.mul NegData RData = T0Stage1 := by
  norm_num [Two.mul, One.mul, One.add, mulWith, scaleWith, addWith,
    NegData, RData, T0Stage1]

def T0Stage2 : Two :=
  [[], [0, -1]]

theorem t0_stage2_spec :
    Two.mul T0Stage1 SData = T0Stage2 := by
  norm_num [Two.mul, One.mul, One.add, mulWith, scaleWith, addWith,
    T0Stage1, SData, T0Stage2]

def T0Stage3 : Two :=
  [[], [0, 1, -1]]

theorem t0_stage3_spec :
    Two.mul T0Stage2 BData = T0Stage3 := by
  norm_num [Two.mul, One.mul, One.add, mulWith, scaleWith, addWith,
    T0Stage2, BData, T0Stage3]

def T0Stage4 : Two :=
  [[], [0, 1, -1], [0, -2, 3, -1]]

theorem t0_stage4_spec :
    Two.mul T0Stage3 CData = T0Stage4 := by
  norm_num [Two.mul, One.mul, One.add, mulWith, scaleWith, addWith,
    T0Stage3, CData, T0Stage4]

def T0Stage5 : Two :=
  [[], [0, 1, -1], [0, -4, 6, -2], [0, 4, -8, 5, -1]]

theorem t0_stage5_spec :
    Two.mul T0Stage4 CData = T0Stage5 := by
  norm_num [Two.mul, One.mul, One.add, mulWith, scaleWith, addWith,
    T0Stage4, CData, T0Stage5]

def T0Stage6 : Two :=
  [[], [0, 1, -1], [0, -6, 9, -3], [0, 12, -24, 15, -3], [0, -8, 20, -18, 7, -1]]

theorem t0_stage6_spec :
    Two.mul T0Stage5 CData = T0Stage6 := by
  norm_num [Two.mul, One.mul, One.add, mulWith, scaleWith, addWith,
    T0Stage5, CData, T0Stage6]

def T0Stage7 : Two :=
  [[], [0, -1, 2, -2, 1], [0, 7, -16, 18, -12, 3], [0, -18, 45, -54, 42, -18, 3], [0, 20, -52,
    61, -48, 26, -8, 1], [0, -8, 20, -18, 7, -1]]

theorem t0_stage7_spec :
    Two.mul T0Stage6 KData = T0Stage7 := by
  norm_num [Two.mul, One.mul, One.add, mulWith, scaleWith, addWith,
    T0Stage6, KData, T0Stage7]

end MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Dense
