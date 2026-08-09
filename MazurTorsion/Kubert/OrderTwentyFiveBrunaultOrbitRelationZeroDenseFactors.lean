/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroCertificateData
import MazurTorsion.Kubert.OrderTwentyFiveDensePolynomial
import Mathlib.Tactic.NormNum

/-!
# Dense factor data for the first order-twenty-five orbit relation

The lists below are exact bivariate integer coefficient tables in ascending
`r`- then `s`-degree.  Lean checks their evaluations against the public
certificate factors before any generated multiplication stage consumes them.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Dense

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveRelationZeroCertificate.Internal

def NegData : Two :=
  [[-1]]

def RData : Two :=
  [[], [1]]

def SData : Two :=
  [[0, 1]]

def AData : Two :=
  [[0, -1], [1]]

def BData : Two :=
  [[-1, 1]]

def CData : Two :=
  [[1], [-2, 1]]

def KData : Two :=
  [[-1, 1, -1], [1]]

def DData : Two :=
  [[0, 1], [0, -4, 3, -1], [1]]

def EData : Two :=
  [[-1, 0, -1], [3, 1], [-3, 1]]

def LData : Two :=
  [[0, 0, 0, -1], [1, -3, 6, -1], [-2, 4, -9, 5, -1], [1]]

def JData : Two :=
  [[0, 0, 0, 0, 1], [1, -3, 6, -10, 4, -1], [-2, 2, 3], [2, -4, 1]]

def TData : Two :=
  [[0, 1], [1, -7, 6, -3, 1], [-1, 6, -5, 1]]

def MData : Two :=
  [[0, 0, 1, 1, 1], [0, 0, -8, -5, 1], [0, 0, 28, -11, 1], [1, -8, -19, 20, -7, 1], [-1, 9, -6,
    1]]

def NData : Two :=
  [[0, 0, 0, -1], [0, 0, 0, 11, -10, 6, -3, 1], [-1, 6, -21, 1, 9, -3, -1], [3, -15, 54, -46,
    12, 3, -1], [-3, 10, -39, 50, -31, 9, -1], [1]]

def P6Data : Two :=
  [[0, 0, 0, 0, 0, 0, 1], [0, -1, 3, -6, 10, -15, 3], [0, 7, -18, 25, -31, 66, -50, 21, -6, 1],
    [0, -21, 51, -41, -30, 21, 3, -3], [0, 35, -105, 144, -60, -9, 12, -2], [-1, -20, 69, -121,
    105, -48, 11, -1], [1]]

def P9Data : Two :=
  [[0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 21, -21, 15, -10, 6, -3, 1], [0, -1, 6, -21, 56,
    -126, 42, 28, -24, -1, 13, -9, 1], [0, 9, -48, 145, -351, 837, -833, 402, -45, -84, 66, -15,
    1], [0, -36, 171, -415, 780, -2046, 2957, -2562, 1530, -650, 165, -21, 1], [0, 84, -369,
    686, -480, 1095, -2296, 2553, -1827, 970, -370, 93, -14, 1], [0, -126, 576, -1130, 570, 324,
    -357, 24, 45, -10], [1, 105, -525, 1256, -1341, 597, 28, -120, 39, -4], [-2, -35, 189, -520,
    756, -636, 319, -94, 15, -1], [1]]

theorem eval_NegData (r s : ℚ) :
    Two.eval NegData r s = (-1 : ℚ) := by
  norm_num [Two.eval, One.eval, evalWith, NegData]

theorem eval_RData (r s : ℚ) :
    Two.eval RData r s = r := by
  norm_num [Two.eval, One.eval, evalWith, RData]

theorem eval_SData (r s : ℚ) :
    Two.eval SData r s = s := by
  norm_num [Two.eval, One.eval, evalWith, SData]

theorem eval_AData (r s : ℚ) :
    Two.eval AData r s = A r s := by
  norm_num [Two.eval, One.eval, evalWith, AData, A]
  ring

theorem eval_BData (r s : ℚ) :
    Two.eval BData r s = B r s := by
  norm_num [Two.eval, One.eval, evalWith, BData, B]
  ring

theorem eval_CData (r s : ℚ) :
    Two.eval CData r s = C r s := by
  norm_num [Two.eval, One.eval, evalWith, CData, C]
  ring

theorem eval_KData (r s : ℚ) :
    Two.eval KData r s = K r s := by
  norm_num [Two.eval, One.eval, evalWith, KData, K]
  ring

theorem eval_DData (r s : ℚ) :
    Two.eval DData r s = D r s := by
  norm_num [Two.eval, One.eval, evalWith, DData, D]
  ring

theorem eval_EData (r s : ℚ) :
    Two.eval EData r s = E r s := by
  norm_num [Two.eval, One.eval, evalWith, EData, E]
  ring

theorem eval_LData (r s : ℚ) :
    Two.eval LData r s = L r s := by
  norm_num [Two.eval, One.eval, evalWith, LData, L]
  ring

theorem eval_JData (r s : ℚ) :
    Two.eval JData r s = J r s := by
  norm_num [Two.eval, One.eval, evalWith, JData, J]
  ring

theorem eval_TData (r s : ℚ) :
    Two.eval TData r s = T r s := by
  norm_num [Two.eval, One.eval, evalWith, TData, T]
  ring

theorem eval_MData (r s : ℚ) :
    Two.eval MData r s = M r s := by
  norm_num [Two.eval, One.eval, evalWith, MData, M]
  ring

theorem eval_NData (r s : ℚ) :
    Two.eval NData r s = N r s := by
  norm_num [Two.eval, One.eval, evalWith, NData, N]
  ring

theorem eval_P6Data (r s : ℚ) :
    Two.eval P6Data r s = P6 r s := by
  norm_num [Two.eval, One.eval, evalWith, P6Data, P6]
  ring

theorem eval_P9Data (r s : ℚ) :
    Two.eval P9Data r s = P9 r s := by
  norm_num [Two.eval, One.eval, evalWith, P9Data, P9]
  ring

end MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Dense
