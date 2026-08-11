/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationFourCertificateData
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroBridge
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroDenseFactors

/-!
# Checked dense factors for RelationFour term zero

The integer tables are shared with the independently checked RelationZero
factor library.  The small evaluation bridges below check that those tables
denote the RelationFour implementation factors before any generated product
stage consumes them.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Dense

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveRelationFourCertificate.Internal


def NegData : Two := OrderTwentyFiveRelationZeroCertificate.Dense.NegData
def SData : Two := OrderTwentyFiveRelationZeroCertificate.Dense.SData
def AData : Two := OrderTwentyFiveRelationZeroCertificate.Dense.AData
def BData : Two := OrderTwentyFiveRelationZeroCertificate.Dense.BData
def CData : Two := OrderTwentyFiveRelationZeroCertificate.Dense.CData
def DData : Two := OrderTwentyFiveRelationZeroCertificate.Dense.DData
def EData : Two := OrderTwentyFiveRelationZeroCertificate.Dense.EData
def JData : Two := OrderTwentyFiveRelationZeroCertificate.Dense.JData
def KData : Two := OrderTwentyFiveRelationZeroCertificate.Dense.KData
def LData : Two := OrderTwentyFiveRelationZeroCertificate.Dense.LData
def MData : Two := OrderTwentyFiveRelationZeroCertificate.Dense.MData
def NData : Two := OrderTwentyFiveRelationZeroCertificate.Dense.NData
def P9Data : Two := OrderTwentyFiveRelationZeroCertificate.Dense.P9Data

theorem eval_NegData (r s : ℚ) :
    Two.eval NegData r s = (-1 : ℚ) := by
  rw [NegData, OrderTwentyFiveRelationZeroCertificate.Dense.eval_NegData]

theorem eval_SData (r s : ℚ) :
    Two.eval SData r s = s := by
  rw [SData, OrderTwentyFiveRelationZeroCertificate.Dense.eval_SData]

theorem eval_AData (r s : ℚ) :
    Two.eval AData r s = A r s := by
  rw [AData, OrderTwentyFiveRelationZeroCertificate.Dense.eval_AData]
  rfl

theorem eval_BData (r s : ℚ) :
    Two.eval BData r s = B r s := by
  rw [BData, OrderTwentyFiveRelationZeroCertificate.Dense.eval_BData]
  rfl

theorem eval_CData (r s : ℚ) :
    Two.eval CData r s = C r s := by
  rw [CData, OrderTwentyFiveRelationZeroCertificate.Dense.eval_CData]
  rfl

theorem eval_DData (r s : ℚ) :
    Two.eval DData r s = D r s := by
  rw [DData, OrderTwentyFiveRelationZeroCertificate.Dense.eval_DData]
  rfl

theorem eval_EData (r s : ℚ) :
    Two.eval EData r s = E r s := by
  rw [EData, OrderTwentyFiveRelationZeroCertificate.Dense.eval_EData]
  rfl

theorem eval_JData (r s : ℚ) :
    Two.eval JData r s = J r s := by
  rw [JData, OrderTwentyFiveRelationZeroCertificate.Dense.eval_JData]
  rfl

theorem eval_KData (r s : ℚ) :
    Two.eval KData r s = K r s := by
  rw [KData, OrderTwentyFiveRelationZeroCertificate.Dense.eval_KData]
  rfl

theorem eval_LData (r s : ℚ) :
    Two.eval LData r s = L r s := by
  rw [LData, OrderTwentyFiveRelationZeroCertificate.Dense.eval_LData]
  rfl

theorem eval_MData (r s : ℚ) :
    Two.eval MData r s = M r s := by
  rw [MData, OrderTwentyFiveRelationZeroCertificate.Dense.eval_MData]
  rfl

theorem eval_NData (r s : ℚ) :
    Two.eval NData r s = N r s := by
  rw [NData, OrderTwentyFiveRelationZeroCertificate.Dense.eval_NData]
  rfl

theorem eval_P9Data (r s : ℚ) :
    Two.eval P9Data r s = P9 r s := by
  rw [P9Data, OrderTwentyFiveRelationZeroCertificate.Dense.eval_P9Data,
    OrderTwentyFiveRelationZeroCertificate.Internal.P9_eq_factor]
  rfl

end MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Dense
