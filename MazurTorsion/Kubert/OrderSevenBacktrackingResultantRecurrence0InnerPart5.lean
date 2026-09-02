/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData0
import Mathlib.Tactic.Ring

/-!
# Initial resultant recurrence certificates for order-seven branch zero

This internal proof shard checks a balanced subset of the independent
coefficient identities used by the initial pseudo-remainder recurrence.
-/

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

public theorem recurrence0Inner30 :
    Internal.selectionCofactorCoefficient30 =
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient26 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient25 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient24 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient23 := by
  unfold Internal.selectionCofactorCoefficient30
    Internal.selectionCofactorCoefficient30Chunk1
    Internal.selectionCofactorCoefficient30Chunk0
    Internal.divisionCofactor0Coefficient4
    Internal.divisionCofactor0Coefficient4Chunk0
    quotient0Coefficient26
    quotient0Coefficient26Block0
    quotient0Coefficient26Chunk0
    Internal.divisionCofactor0Coefficient5
    Internal.divisionCofactor0Coefficient5Chunk0
    quotient0Coefficient25
    quotient0Coefficient25Block0
    quotient0Coefficient25Chunk0
    Internal.divisionCofactor0Coefficient6
    Internal.divisionCofactor0Coefficient6Chunk0
    quotient0Coefficient24
    quotient0Coefficient24Block0
    quotient0Coefficient24Chunk1
    quotient0Coefficient24Chunk0
    Internal.divisionCofactor0Coefficient7
    Internal.divisionCofactor0Coefficient7Chunk0
    quotient0Coefficient23
    quotient0Coefficient23Block0
    quotient0Coefficient23Chunk1
    quotient0Coefficient23Chunk0
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_neg, Polynomial.C_ofNat]
  ring
public theorem recurrence0Inner31 :
    Internal.selectionCofactorCoefficient31 =
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient26 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient25 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient24 := by
  unfold Internal.selectionCofactorCoefficient31
    Internal.selectionCofactorCoefficient31Chunk0
    Internal.divisionCofactor0Coefficient5
    Internal.divisionCofactor0Coefficient5Chunk0
    quotient0Coefficient26
    quotient0Coefficient26Block0
    quotient0Coefficient26Chunk0
    Internal.divisionCofactor0Coefficient6
    Internal.divisionCofactor0Coefficient6Chunk0
    quotient0Coefficient25
    quotient0Coefficient25Block0
    quotient0Coefficient25Chunk0
    Internal.divisionCofactor0Coefficient7
    Internal.divisionCofactor0Coefficient7Chunk0
    quotient0Coefficient24
    quotient0Coefficient24Block0
    quotient0Coefficient24Chunk1
    quotient0Coefficient24Chunk0
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_neg, Polynomial.C_ofNat]
  ring
public theorem recurrence0Inner32 :
    Internal.selectionCofactorCoefficient32 =
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient26 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient25 := by
  unfold Internal.selectionCofactorCoefficient32
    Internal.selectionCofactorCoefficient32Chunk0
    Internal.divisionCofactor0Coefficient6
    Internal.divisionCofactor0Coefficient6Chunk0
    quotient0Coefficient26
    quotient0Coefficient26Block0
    quotient0Coefficient26Chunk0
    Internal.divisionCofactor0Coefficient7
    Internal.divisionCofactor0Coefficient7Chunk0
    quotient0Coefficient25
    quotient0Coefficient25Block0
    quotient0Coefficient25Chunk0
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_neg, Polynomial.C_ofNat]
  ring
public theorem recurrence0Inner33 :
    Internal.selectionCofactorCoefficient33 =
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient26 := by
  unfold Internal.selectionCofactorCoefficient33
    Internal.selectionCofactorCoefficient33Chunk0
    Internal.divisionCofactor0Coefficient7
    Internal.divisionCofactor0Coefficient7Chunk0
    quotient0Coefficient26
    quotient0Coefficient26Block0
    quotient0Coefficient26Chunk0
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_neg, Polynomial.C_ofNat]
  ring
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate
