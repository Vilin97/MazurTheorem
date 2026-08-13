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

public theorem recurrence0Inner24 :
    Internal.selectionCofactorCoefficient24 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient24 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient23 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient22 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient21 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient20 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient19 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient18 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient17 := by
  unfold Internal.selectionCofactorCoefficient24
    Internal.selectionCofactorCoefficient24Chunk3
    Internal.selectionCofactorCoefficient24Chunk2
    Internal.selectionCofactorCoefficient24Chunk1
    Internal.selectionCofactorCoefficient24Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
    quotient0Coefficient24
    quotient0Coefficient24Block0
    quotient0Coefficient24Chunk1
    quotient0Coefficient24Chunk0
    Internal.divisionCofactor0Coefficient1
    Internal.divisionCofactor0Coefficient1Chunk1
    Internal.divisionCofactor0Coefficient1Chunk0
    quotient0Coefficient23
    quotient0Coefficient23Block0
    quotient0Coefficient23Chunk1
    quotient0Coefficient23Chunk0
    Internal.divisionCofactor0Coefficient2
    Internal.divisionCofactor0Coefficient2Chunk1
    Internal.divisionCofactor0Coefficient2Chunk0
    quotient0Coefficient22
    quotient0Coefficient22Block0
    quotient0Coefficient22Chunk2
    quotient0Coefficient22Chunk1
    quotient0Coefficient22Chunk0
    Internal.divisionCofactor0Coefficient3
    Internal.divisionCofactor0Coefficient3Chunk1
    Internal.divisionCofactor0Coefficient3Chunk0
    quotient0Coefficient21
    quotient0Coefficient21Block0
    quotient0Coefficient21Chunk2
    quotient0Coefficient21Chunk1
    quotient0Coefficient21Chunk0
    Internal.divisionCofactor0Coefficient4
    Internal.divisionCofactor0Coefficient4Chunk0
    quotient0Coefficient20
    quotient0Coefficient20Block0
    quotient0Coefficient20Chunk3
    quotient0Coefficient20Chunk2
    quotient0Coefficient20Chunk1
    quotient0Coefficient20Chunk0
    Internal.divisionCofactor0Coefficient5
    Internal.divisionCofactor0Coefficient5Chunk0
    quotient0Coefficient19
    quotient0Coefficient19Block0
    quotient0Coefficient19Chunk3
    quotient0Coefficient19Chunk2
    quotient0Coefficient19Chunk1
    quotient0Coefficient19Chunk0
    Internal.divisionCofactor0Coefficient6
    Internal.divisionCofactor0Coefficient6Chunk0
    quotient0Coefficient18
    quotient0Coefficient18Block0
    quotient0Coefficient18Chunk4
    quotient0Coefficient18Chunk3
    quotient0Coefficient18Chunk2
    quotient0Coefficient18Chunk1
    quotient0Coefficient18Chunk0
    Internal.divisionCofactor0Coefficient7
    Internal.divisionCofactor0Coefficient7Chunk0
    quotient0Coefficient17
    quotient0Coefficient17Block0
    quotient0Coefficient17Chunk4
    quotient0Coefficient17Chunk3
    quotient0Coefficient17Chunk2
    quotient0Coefficient17Chunk1
    quotient0Coefficient17Chunk0
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring
public theorem recurrence0Inner25 :
    Internal.selectionCofactorCoefficient25 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient25 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient24 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient23 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient22 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient21 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient20 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient19 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient18 := by
  unfold Internal.selectionCofactorCoefficient25
    Internal.selectionCofactorCoefficient25Chunk2
    Internal.selectionCofactorCoefficient25Chunk1
    Internal.selectionCofactorCoefficient25Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
    quotient0Coefficient25
    quotient0Coefficient25Block0
    quotient0Coefficient25Chunk0
    Internal.divisionCofactor0Coefficient1
    Internal.divisionCofactor0Coefficient1Chunk1
    Internal.divisionCofactor0Coefficient1Chunk0
    quotient0Coefficient24
    quotient0Coefficient24Block0
    quotient0Coefficient24Chunk1
    quotient0Coefficient24Chunk0
    Internal.divisionCofactor0Coefficient2
    Internal.divisionCofactor0Coefficient2Chunk1
    Internal.divisionCofactor0Coefficient2Chunk0
    quotient0Coefficient23
    quotient0Coefficient23Block0
    quotient0Coefficient23Chunk1
    quotient0Coefficient23Chunk0
    Internal.divisionCofactor0Coefficient3
    Internal.divisionCofactor0Coefficient3Chunk1
    Internal.divisionCofactor0Coefficient3Chunk0
    quotient0Coefficient22
    quotient0Coefficient22Block0
    quotient0Coefficient22Chunk2
    quotient0Coefficient22Chunk1
    quotient0Coefficient22Chunk0
    Internal.divisionCofactor0Coefficient4
    Internal.divisionCofactor0Coefficient4Chunk0
    quotient0Coefficient21
    quotient0Coefficient21Block0
    quotient0Coefficient21Chunk2
    quotient0Coefficient21Chunk1
    quotient0Coefficient21Chunk0
    Internal.divisionCofactor0Coefficient5
    Internal.divisionCofactor0Coefficient5Chunk0
    quotient0Coefficient20
    quotient0Coefficient20Block0
    quotient0Coefficient20Chunk3
    quotient0Coefficient20Chunk2
    quotient0Coefficient20Chunk1
    quotient0Coefficient20Chunk0
    Internal.divisionCofactor0Coefficient6
    Internal.divisionCofactor0Coefficient6Chunk0
    quotient0Coefficient19
    quotient0Coefficient19Block0
    quotient0Coefficient19Chunk3
    quotient0Coefficient19Chunk2
    quotient0Coefficient19Chunk1
    quotient0Coefficient19Chunk0
    Internal.divisionCofactor0Coefficient7
    Internal.divisionCofactor0Coefficient7Chunk0
    quotient0Coefficient18
    quotient0Coefficient18Block0
    quotient0Coefficient18Chunk4
    quotient0Coefficient18Chunk3
    quotient0Coefficient18Chunk2
    quotient0Coefficient18Chunk1
    quotient0Coefficient18Chunk0
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring
public theorem recurrence0Inner26 :
    Internal.selectionCofactorCoefficient26 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient26 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient25 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient24 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient23 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient22 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient21 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient20 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient19 := by
  unfold Internal.selectionCofactorCoefficient26
    Internal.selectionCofactorCoefficient26Chunk2
    Internal.selectionCofactorCoefficient26Chunk1
    Internal.selectionCofactorCoefficient26Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
    quotient0Coefficient26
    quotient0Coefficient26Block0
    quotient0Coefficient26Chunk0
    Internal.divisionCofactor0Coefficient1
    Internal.divisionCofactor0Coefficient1Chunk1
    Internal.divisionCofactor0Coefficient1Chunk0
    quotient0Coefficient25
    quotient0Coefficient25Block0
    quotient0Coefficient25Chunk0
    Internal.divisionCofactor0Coefficient2
    Internal.divisionCofactor0Coefficient2Chunk1
    Internal.divisionCofactor0Coefficient2Chunk0
    quotient0Coefficient24
    quotient0Coefficient24Block0
    quotient0Coefficient24Chunk1
    quotient0Coefficient24Chunk0
    Internal.divisionCofactor0Coefficient3
    Internal.divisionCofactor0Coefficient3Chunk1
    Internal.divisionCofactor0Coefficient3Chunk0
    quotient0Coefficient23
    quotient0Coefficient23Block0
    quotient0Coefficient23Chunk1
    quotient0Coefficient23Chunk0
    Internal.divisionCofactor0Coefficient4
    Internal.divisionCofactor0Coefficient4Chunk0
    quotient0Coefficient22
    quotient0Coefficient22Block0
    quotient0Coefficient22Chunk2
    quotient0Coefficient22Chunk1
    quotient0Coefficient22Chunk0
    Internal.divisionCofactor0Coefficient5
    Internal.divisionCofactor0Coefficient5Chunk0
    quotient0Coefficient21
    quotient0Coefficient21Block0
    quotient0Coefficient21Chunk2
    quotient0Coefficient21Chunk1
    quotient0Coefficient21Chunk0
    Internal.divisionCofactor0Coefficient6
    Internal.divisionCofactor0Coefficient6Chunk0
    quotient0Coefficient20
    quotient0Coefficient20Block0
    quotient0Coefficient20Chunk3
    quotient0Coefficient20Chunk2
    quotient0Coefficient20Chunk1
    quotient0Coefficient20Chunk0
    Internal.divisionCofactor0Coefficient7
    Internal.divisionCofactor0Coefficient7Chunk0
    quotient0Coefficient19
    quotient0Coefficient19Block0
    quotient0Coefficient19Chunk3
    quotient0Coefficient19Chunk2
    quotient0Coefficient19Chunk1
    quotient0Coefficient19Chunk0
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring
public theorem recurrence0Inner27 :
    Internal.selectionCofactorCoefficient27 =
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient26 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient25 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient24 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient23 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient22 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient21 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient20 := by
  unfold Internal.selectionCofactorCoefficient27
    Internal.selectionCofactorCoefficient27Chunk2
    Internal.selectionCofactorCoefficient27Chunk1
    Internal.selectionCofactorCoefficient27Chunk0
    Internal.divisionCofactor0Coefficient1
    Internal.divisionCofactor0Coefficient1Chunk1
    Internal.divisionCofactor0Coefficient1Chunk0
    quotient0Coefficient26
    quotient0Coefficient26Block0
    quotient0Coefficient26Chunk0
    Internal.divisionCofactor0Coefficient2
    Internal.divisionCofactor0Coefficient2Chunk1
    Internal.divisionCofactor0Coefficient2Chunk0
    quotient0Coefficient25
    quotient0Coefficient25Block0
    quotient0Coefficient25Chunk0
    Internal.divisionCofactor0Coefficient3
    Internal.divisionCofactor0Coefficient3Chunk1
    Internal.divisionCofactor0Coefficient3Chunk0
    quotient0Coefficient24
    quotient0Coefficient24Block0
    quotient0Coefficient24Chunk1
    quotient0Coefficient24Chunk0
    Internal.divisionCofactor0Coefficient4
    Internal.divisionCofactor0Coefficient4Chunk0
    quotient0Coefficient23
    quotient0Coefficient23Block0
    quotient0Coefficient23Chunk1
    quotient0Coefficient23Chunk0
    Internal.divisionCofactor0Coefficient5
    Internal.divisionCofactor0Coefficient5Chunk0
    quotient0Coefficient22
    quotient0Coefficient22Block0
    quotient0Coefficient22Chunk2
    quotient0Coefficient22Chunk1
    quotient0Coefficient22Chunk0
    Internal.divisionCofactor0Coefficient6
    Internal.divisionCofactor0Coefficient6Chunk0
    quotient0Coefficient21
    quotient0Coefficient21Block0
    quotient0Coefficient21Chunk2
    quotient0Coefficient21Chunk1
    quotient0Coefficient21Chunk0
    Internal.divisionCofactor0Coefficient7
    Internal.divisionCofactor0Coefficient7Chunk0
    quotient0Coefficient20
    quotient0Coefficient20Block0
    quotient0Coefficient20Chunk3
    quotient0Coefficient20Chunk2
    quotient0Coefficient20Chunk1
    quotient0Coefficient20Chunk0
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring
public theorem recurrence0Inner28 :
    Internal.selectionCofactorCoefficient28 =
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient26 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient25 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient24 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient23 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient22 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient21 := by
  unfold Internal.selectionCofactorCoefficient28
    Internal.selectionCofactorCoefficient28Chunk1
    Internal.selectionCofactorCoefficient28Chunk0
    Internal.divisionCofactor0Coefficient2
    Internal.divisionCofactor0Coefficient2Chunk1
    Internal.divisionCofactor0Coefficient2Chunk0
    quotient0Coefficient26
    quotient0Coefficient26Block0
    quotient0Coefficient26Chunk0
    Internal.divisionCofactor0Coefficient3
    Internal.divisionCofactor0Coefficient3Chunk1
    Internal.divisionCofactor0Coefficient3Chunk0
    quotient0Coefficient25
    quotient0Coefficient25Block0
    quotient0Coefficient25Chunk0
    Internal.divisionCofactor0Coefficient4
    Internal.divisionCofactor0Coefficient4Chunk0
    quotient0Coefficient24
    quotient0Coefficient24Block0
    quotient0Coefficient24Chunk1
    quotient0Coefficient24Chunk0
    Internal.divisionCofactor0Coefficient5
    Internal.divisionCofactor0Coefficient5Chunk0
    quotient0Coefficient23
    quotient0Coefficient23Block0
    quotient0Coefficient23Chunk1
    quotient0Coefficient23Chunk0
    Internal.divisionCofactor0Coefficient6
    Internal.divisionCofactor0Coefficient6Chunk0
    quotient0Coefficient22
    quotient0Coefficient22Block0
    quotient0Coefficient22Chunk2
    quotient0Coefficient22Chunk1
    quotient0Coefficient22Chunk0
    Internal.divisionCofactor0Coefficient7
    Internal.divisionCofactor0Coefficient7Chunk0
    quotient0Coefficient21
    quotient0Coefficient21Block0
    quotient0Coefficient21Chunk2
    quotient0Coefficient21Chunk1
    quotient0Coefficient21Chunk0
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_neg, Polynomial.C_ofNat]
  ring
public theorem recurrence0Inner29 :
    Internal.selectionCofactorCoefficient29 =
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient26 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient25 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient24 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient23 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient22 := by
  unfold Internal.selectionCofactorCoefficient29
    Internal.selectionCofactorCoefficient29Chunk1
    Internal.selectionCofactorCoefficient29Chunk0
    Internal.divisionCofactor0Coefficient3
    Internal.divisionCofactor0Coefficient3Chunk1
    Internal.divisionCofactor0Coefficient3Chunk0
    quotient0Coefficient26
    quotient0Coefficient26Block0
    quotient0Coefficient26Chunk0
    Internal.divisionCofactor0Coefficient4
    Internal.divisionCofactor0Coefficient4Chunk0
    quotient0Coefficient25
    quotient0Coefficient25Block0
    quotient0Coefficient25Chunk0
    Internal.divisionCofactor0Coefficient5
    Internal.divisionCofactor0Coefficient5Chunk0
    quotient0Coefficient24
    quotient0Coefficient24Block0
    quotient0Coefficient24Chunk1
    quotient0Coefficient24Chunk0
    Internal.divisionCofactor0Coefficient6
    Internal.divisionCofactor0Coefficient6Chunk0
    quotient0Coefficient23
    quotient0Coefficient23Block0
    quotient0Coefficient23Chunk1
    quotient0Coefficient23Chunk0
    Internal.divisionCofactor0Coefficient7
    Internal.divisionCofactor0Coefficient7Chunk0
    quotient0Coefficient22
    quotient0Coefficient22Block0
    quotient0Coefficient22Chunk2
    quotient0Coefficient22Chunk1
    quotient0Coefficient22Chunk0
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_neg, Polynomial.C_ofNat]
  ring
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate
