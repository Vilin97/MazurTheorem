/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData0
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Initial resultant recurrence for order-seven branch zero

This file checks the first primitive pseudo-remainder recurrence over
the bivariate polynomial ring. The private coefficient identities are
exact ring certificates for the thirty-four outer coefficients.
-/

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

private theorem recurrence0Inner0 :
    Internal.selectionCofactorCoefficient0 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient0 +
      exceptional0 * remainder2Coefficient0 := by
  unfold Internal.selectionCofactorCoefficient0
    Internal.selectionCofactorCoefficient0Chunk10
    Internal.selectionCofactorCoefficient0Chunk9
    Internal.selectionCofactorCoefficient0Chunk8
    Internal.selectionCofactorCoefficient0Chunk7
    Internal.selectionCofactorCoefficient0Chunk6
    Internal.selectionCofactorCoefficient0Chunk5
    Internal.selectionCofactorCoefficient0Chunk4
    Internal.selectionCofactorCoefficient0Chunk3
    Internal.selectionCofactorCoefficient0Chunk2
    Internal.selectionCofactorCoefficient0Chunk1
    Internal.selectionCofactorCoefficient0Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
    quotient0Coefficient0
    quotient0Coefficient0Block1
    quotient0Coefficient0Block0
    quotient0Coefficient0Chunk12
    quotient0Coefficient0Chunk11
    quotient0Coefficient0Chunk10
    quotient0Coefficient0Chunk9
    quotient0Coefficient0Chunk8
    quotient0Coefficient0Chunk7
    quotient0Coefficient0Chunk6
    quotient0Coefficient0Chunk5
    quotient0Coefficient0Chunk4
    quotient0Coefficient0Chunk3
    quotient0Coefficient0Chunk2
    quotient0Coefficient0Chunk1
    quotient0Coefficient0Chunk0
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    exceptional0
    exceptionalUnit0
    parameter
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow,
    Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring

private theorem recurrence0Inner1 :
    Internal.selectionCofactorCoefficient1 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient1 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient0 +
      exceptional0 * remainder2Coefficient1 := by
  unfold Internal.selectionCofactorCoefficient1
    Internal.selectionCofactorCoefficient1Chunk10
    Internal.selectionCofactorCoefficient1Chunk9
    Internal.selectionCofactorCoefficient1Chunk8
    Internal.selectionCofactorCoefficient1Chunk7
    Internal.selectionCofactorCoefficient1Chunk6
    Internal.selectionCofactorCoefficient1Chunk5
    Internal.selectionCofactorCoefficient1Chunk4
    Internal.selectionCofactorCoefficient1Chunk3
    Internal.selectionCofactorCoefficient1Chunk2
    Internal.selectionCofactorCoefficient1Chunk1
    Internal.selectionCofactorCoefficient1Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
    quotient0Coefficient1
    quotient0Coefficient1Block0
    quotient0Coefficient1Chunk11
    quotient0Coefficient1Chunk10
    quotient0Coefficient1Chunk9
    quotient0Coefficient1Chunk8
    quotient0Coefficient1Chunk7
    quotient0Coefficient1Chunk6
    quotient0Coefficient1Chunk5
    quotient0Coefficient1Chunk4
    quotient0Coefficient1Chunk3
    quotient0Coefficient1Chunk2
    quotient0Coefficient1Chunk1
    quotient0Coefficient1Chunk0
    Internal.divisionCofactor0Coefficient1
    Internal.divisionCofactor0Coefficient1Chunk1
    Internal.divisionCofactor0Coefficient1Chunk0
    quotient0Coefficient0
    quotient0Coefficient0Block1
    quotient0Coefficient0Block0
    quotient0Coefficient0Chunk12
    quotient0Coefficient0Chunk11
    quotient0Coefficient0Chunk10
    quotient0Coefficient0Chunk9
    quotient0Coefficient0Chunk8
    quotient0Coefficient0Chunk7
    quotient0Coefficient0Chunk6
    quotient0Coefficient0Chunk5
    quotient0Coefficient0Chunk4
    quotient0Coefficient0Chunk3
    quotient0Coefficient0Chunk2
    quotient0Coefficient0Chunk1
    quotient0Coefficient0Chunk0
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    exceptional0
    exceptionalUnit0
    parameter
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow,
    Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring

private theorem recurrence0Inner2 :
    Internal.selectionCofactorCoefficient2 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient2 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient1 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient0 +
      exceptional0 * remainder2Coefficient2 := by
  unfold Internal.selectionCofactorCoefficient2
    Internal.selectionCofactorCoefficient2Chunk9
    Internal.selectionCofactorCoefficient2Chunk8
    Internal.selectionCofactorCoefficient2Chunk7
    Internal.selectionCofactorCoefficient2Chunk6
    Internal.selectionCofactorCoefficient2Chunk5
    Internal.selectionCofactorCoefficient2Chunk4
    Internal.selectionCofactorCoefficient2Chunk3
    Internal.selectionCofactorCoefficient2Chunk2
    Internal.selectionCofactorCoefficient2Chunk1
    Internal.selectionCofactorCoefficient2Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
    quotient0Coefficient2
    quotient0Coefficient2Block0
    quotient0Coefficient2Chunk11
    quotient0Coefficient2Chunk10
    quotient0Coefficient2Chunk9
    quotient0Coefficient2Chunk8
    quotient0Coefficient2Chunk7
    quotient0Coefficient2Chunk6
    quotient0Coefficient2Chunk5
    quotient0Coefficient2Chunk4
    quotient0Coefficient2Chunk3
    quotient0Coefficient2Chunk2
    quotient0Coefficient2Chunk1
    quotient0Coefficient2Chunk0
    Internal.divisionCofactor0Coefficient1
    Internal.divisionCofactor0Coefficient1Chunk1
    Internal.divisionCofactor0Coefficient1Chunk0
    quotient0Coefficient1
    quotient0Coefficient1Block0
    quotient0Coefficient1Chunk11
    quotient0Coefficient1Chunk10
    quotient0Coefficient1Chunk9
    quotient0Coefficient1Chunk8
    quotient0Coefficient1Chunk7
    quotient0Coefficient1Chunk6
    quotient0Coefficient1Chunk5
    quotient0Coefficient1Chunk4
    quotient0Coefficient1Chunk3
    quotient0Coefficient1Chunk2
    quotient0Coefficient1Chunk1
    quotient0Coefficient1Chunk0
    Internal.divisionCofactor0Coefficient2
    Internal.divisionCofactor0Coefficient2Chunk1
    Internal.divisionCofactor0Coefficient2Chunk0
    quotient0Coefficient0
    quotient0Coefficient0Block1
    quotient0Coefficient0Block0
    quotient0Coefficient0Chunk12
    quotient0Coefficient0Chunk11
    quotient0Coefficient0Chunk10
    quotient0Coefficient0Chunk9
    quotient0Coefficient0Chunk8
    quotient0Coefficient0Chunk7
    quotient0Coefficient0Chunk6
    quotient0Coefficient0Chunk5
    quotient0Coefficient0Chunk4
    quotient0Coefficient0Chunk3
    quotient0Coefficient0Chunk2
    quotient0Coefficient0Chunk1
    quotient0Coefficient0Chunk0
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    exceptional0
    exceptionalUnit0
    parameter
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow,
    Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring

private theorem recurrence0Inner3 :
    Internal.selectionCofactorCoefficient3 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient3 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient2 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient1 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient0 +
      exceptional0 * remainder2Coefficient3 := by
  unfold Internal.selectionCofactorCoefficient3
    Internal.selectionCofactorCoefficient3Chunk9
    Internal.selectionCofactorCoefficient3Chunk8
    Internal.selectionCofactorCoefficient3Chunk7
    Internal.selectionCofactorCoefficient3Chunk6
    Internal.selectionCofactorCoefficient3Chunk5
    Internal.selectionCofactorCoefficient3Chunk4
    Internal.selectionCofactorCoefficient3Chunk3
    Internal.selectionCofactorCoefficient3Chunk2
    Internal.selectionCofactorCoefficient3Chunk1
    Internal.selectionCofactorCoefficient3Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
    quotient0Coefficient3
    quotient0Coefficient3Block0
    quotient0Coefficient3Chunk10
    quotient0Coefficient3Chunk9
    quotient0Coefficient3Chunk8
    quotient0Coefficient3Chunk7
    quotient0Coefficient3Chunk6
    quotient0Coefficient3Chunk5
    quotient0Coefficient3Chunk4
    quotient0Coefficient3Chunk3
    quotient0Coefficient3Chunk2
    quotient0Coefficient3Chunk1
    quotient0Coefficient3Chunk0
    Internal.divisionCofactor0Coefficient1
    Internal.divisionCofactor0Coefficient1Chunk1
    Internal.divisionCofactor0Coefficient1Chunk0
    quotient0Coefficient2
    quotient0Coefficient2Block0
    quotient0Coefficient2Chunk11
    quotient0Coefficient2Chunk10
    quotient0Coefficient2Chunk9
    quotient0Coefficient2Chunk8
    quotient0Coefficient2Chunk7
    quotient0Coefficient2Chunk6
    quotient0Coefficient2Chunk5
    quotient0Coefficient2Chunk4
    quotient0Coefficient2Chunk3
    quotient0Coefficient2Chunk2
    quotient0Coefficient2Chunk1
    quotient0Coefficient2Chunk0
    Internal.divisionCofactor0Coefficient2
    Internal.divisionCofactor0Coefficient2Chunk1
    Internal.divisionCofactor0Coefficient2Chunk0
    quotient0Coefficient1
    quotient0Coefficient1Block0
    quotient0Coefficient1Chunk11
    quotient0Coefficient1Chunk10
    quotient0Coefficient1Chunk9
    quotient0Coefficient1Chunk8
    quotient0Coefficient1Chunk7
    quotient0Coefficient1Chunk6
    quotient0Coefficient1Chunk5
    quotient0Coefficient1Chunk4
    quotient0Coefficient1Chunk3
    quotient0Coefficient1Chunk2
    quotient0Coefficient1Chunk1
    quotient0Coefficient1Chunk0
    Internal.divisionCofactor0Coefficient3
    Internal.divisionCofactor0Coefficient3Chunk1
    Internal.divisionCofactor0Coefficient3Chunk0
    quotient0Coefficient0
    quotient0Coefficient0Block1
    quotient0Coefficient0Block0
    quotient0Coefficient0Chunk12
    quotient0Coefficient0Chunk11
    quotient0Coefficient0Chunk10
    quotient0Coefficient0Chunk9
    quotient0Coefficient0Chunk8
    quotient0Coefficient0Chunk7
    quotient0Coefficient0Chunk6
    quotient0Coefficient0Chunk5
    quotient0Coefficient0Chunk4
    quotient0Coefficient0Chunk3
    quotient0Coefficient0Chunk2
    quotient0Coefficient0Chunk1
    quotient0Coefficient0Chunk0
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    exceptional0
    exceptionalUnit0
    parameter
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow,
    Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring

private theorem recurrence0Inner4 :
    Internal.selectionCofactorCoefficient4 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient4 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient3 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient2 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient1 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient0 +
      exceptional0 * remainder2Coefficient4 := by
  unfold Internal.selectionCofactorCoefficient4
    Internal.selectionCofactorCoefficient4Chunk9
    Internal.selectionCofactorCoefficient4Chunk8
    Internal.selectionCofactorCoefficient4Chunk7
    Internal.selectionCofactorCoefficient4Chunk6
    Internal.selectionCofactorCoefficient4Chunk5
    Internal.selectionCofactorCoefficient4Chunk4
    Internal.selectionCofactorCoefficient4Chunk3
    Internal.selectionCofactorCoefficient4Chunk2
    Internal.selectionCofactorCoefficient4Chunk1
    Internal.selectionCofactorCoefficient4Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
    quotient0Coefficient4
    quotient0Coefficient4Block0
    quotient0Coefficient4Chunk10
    quotient0Coefficient4Chunk9
    quotient0Coefficient4Chunk8
    quotient0Coefficient4Chunk7
    quotient0Coefficient4Chunk6
    quotient0Coefficient4Chunk5
    quotient0Coefficient4Chunk4
    quotient0Coefficient4Chunk3
    quotient0Coefficient4Chunk2
    quotient0Coefficient4Chunk1
    quotient0Coefficient4Chunk0
    Internal.divisionCofactor0Coefficient1
    Internal.divisionCofactor0Coefficient1Chunk1
    Internal.divisionCofactor0Coefficient1Chunk0
    quotient0Coefficient3
    quotient0Coefficient3Block0
    quotient0Coefficient3Chunk10
    quotient0Coefficient3Chunk9
    quotient0Coefficient3Chunk8
    quotient0Coefficient3Chunk7
    quotient0Coefficient3Chunk6
    quotient0Coefficient3Chunk5
    quotient0Coefficient3Chunk4
    quotient0Coefficient3Chunk3
    quotient0Coefficient3Chunk2
    quotient0Coefficient3Chunk1
    quotient0Coefficient3Chunk0
    Internal.divisionCofactor0Coefficient2
    Internal.divisionCofactor0Coefficient2Chunk1
    Internal.divisionCofactor0Coefficient2Chunk0
    quotient0Coefficient2
    quotient0Coefficient2Block0
    quotient0Coefficient2Chunk11
    quotient0Coefficient2Chunk10
    quotient0Coefficient2Chunk9
    quotient0Coefficient2Chunk8
    quotient0Coefficient2Chunk7
    quotient0Coefficient2Chunk6
    quotient0Coefficient2Chunk5
    quotient0Coefficient2Chunk4
    quotient0Coefficient2Chunk3
    quotient0Coefficient2Chunk2
    quotient0Coefficient2Chunk1
    quotient0Coefficient2Chunk0
    Internal.divisionCofactor0Coefficient3
    Internal.divisionCofactor0Coefficient3Chunk1
    Internal.divisionCofactor0Coefficient3Chunk0
    quotient0Coefficient1
    quotient0Coefficient1Block0
    quotient0Coefficient1Chunk11
    quotient0Coefficient1Chunk10
    quotient0Coefficient1Chunk9
    quotient0Coefficient1Chunk8
    quotient0Coefficient1Chunk7
    quotient0Coefficient1Chunk6
    quotient0Coefficient1Chunk5
    quotient0Coefficient1Chunk4
    quotient0Coefficient1Chunk3
    quotient0Coefficient1Chunk2
    quotient0Coefficient1Chunk1
    quotient0Coefficient1Chunk0
    Internal.divisionCofactor0Coefficient4
    Internal.divisionCofactor0Coefficient4Chunk0
    quotient0Coefficient0
    quotient0Coefficient0Block1
    quotient0Coefficient0Block0
    quotient0Coefficient0Chunk12
    quotient0Coefficient0Chunk11
    quotient0Coefficient0Chunk10
    quotient0Coefficient0Chunk9
    quotient0Coefficient0Chunk8
    quotient0Coefficient0Chunk7
    quotient0Coefficient0Chunk6
    quotient0Coefficient0Chunk5
    quotient0Coefficient0Chunk4
    quotient0Coefficient0Chunk3
    quotient0Coefficient0Chunk2
    quotient0Coefficient0Chunk1
    quotient0Coefficient0Chunk0
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    exceptional0
    exceptionalUnit0
    parameter
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow,
    Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring

private theorem recurrence0Inner5 :
    Internal.selectionCofactorCoefficient5 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient5 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient4 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient3 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient2 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient1 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient0 +
      exceptional0 * remainder2Coefficient5 := by
  unfold Internal.selectionCofactorCoefficient5
    Internal.selectionCofactorCoefficient5Chunk9
    Internal.selectionCofactorCoefficient5Chunk8
    Internal.selectionCofactorCoefficient5Chunk7
    Internal.selectionCofactorCoefficient5Chunk6
    Internal.selectionCofactorCoefficient5Chunk5
    Internal.selectionCofactorCoefficient5Chunk4
    Internal.selectionCofactorCoefficient5Chunk3
    Internal.selectionCofactorCoefficient5Chunk2
    Internal.selectionCofactorCoefficient5Chunk1
    Internal.selectionCofactorCoefficient5Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
    quotient0Coefficient5
    quotient0Coefficient5Block0
    quotient0Coefficient5Chunk9
    quotient0Coefficient5Chunk8
    quotient0Coefficient5Chunk7
    quotient0Coefficient5Chunk6
    quotient0Coefficient5Chunk5
    quotient0Coefficient5Chunk4
    quotient0Coefficient5Chunk3
    quotient0Coefficient5Chunk2
    quotient0Coefficient5Chunk1
    quotient0Coefficient5Chunk0
    Internal.divisionCofactor0Coefficient1
    Internal.divisionCofactor0Coefficient1Chunk1
    Internal.divisionCofactor0Coefficient1Chunk0
    quotient0Coefficient4
    quotient0Coefficient4Block0
    quotient0Coefficient4Chunk10
    quotient0Coefficient4Chunk9
    quotient0Coefficient4Chunk8
    quotient0Coefficient4Chunk7
    quotient0Coefficient4Chunk6
    quotient0Coefficient4Chunk5
    quotient0Coefficient4Chunk4
    quotient0Coefficient4Chunk3
    quotient0Coefficient4Chunk2
    quotient0Coefficient4Chunk1
    quotient0Coefficient4Chunk0
    Internal.divisionCofactor0Coefficient2
    Internal.divisionCofactor0Coefficient2Chunk1
    Internal.divisionCofactor0Coefficient2Chunk0
    quotient0Coefficient3
    quotient0Coefficient3Block0
    quotient0Coefficient3Chunk10
    quotient0Coefficient3Chunk9
    quotient0Coefficient3Chunk8
    quotient0Coefficient3Chunk7
    quotient0Coefficient3Chunk6
    quotient0Coefficient3Chunk5
    quotient0Coefficient3Chunk4
    quotient0Coefficient3Chunk3
    quotient0Coefficient3Chunk2
    quotient0Coefficient3Chunk1
    quotient0Coefficient3Chunk0
    Internal.divisionCofactor0Coefficient3
    Internal.divisionCofactor0Coefficient3Chunk1
    Internal.divisionCofactor0Coefficient3Chunk0
    quotient0Coefficient2
    quotient0Coefficient2Block0
    quotient0Coefficient2Chunk11
    quotient0Coefficient2Chunk10
    quotient0Coefficient2Chunk9
    quotient0Coefficient2Chunk8
    quotient0Coefficient2Chunk7
    quotient0Coefficient2Chunk6
    quotient0Coefficient2Chunk5
    quotient0Coefficient2Chunk4
    quotient0Coefficient2Chunk3
    quotient0Coefficient2Chunk2
    quotient0Coefficient2Chunk1
    quotient0Coefficient2Chunk0
    Internal.divisionCofactor0Coefficient4
    Internal.divisionCofactor0Coefficient4Chunk0
    quotient0Coefficient1
    quotient0Coefficient1Block0
    quotient0Coefficient1Chunk11
    quotient0Coefficient1Chunk10
    quotient0Coefficient1Chunk9
    quotient0Coefficient1Chunk8
    quotient0Coefficient1Chunk7
    quotient0Coefficient1Chunk6
    quotient0Coefficient1Chunk5
    quotient0Coefficient1Chunk4
    quotient0Coefficient1Chunk3
    quotient0Coefficient1Chunk2
    quotient0Coefficient1Chunk1
    quotient0Coefficient1Chunk0
    Internal.divisionCofactor0Coefficient5
    Internal.divisionCofactor0Coefficient5Chunk0
    quotient0Coefficient0
    quotient0Coefficient0Block1
    quotient0Coefficient0Block0
    quotient0Coefficient0Chunk12
    quotient0Coefficient0Chunk11
    quotient0Coefficient0Chunk10
    quotient0Coefficient0Chunk9
    quotient0Coefficient0Chunk8
    quotient0Coefficient0Chunk7
    quotient0Coefficient0Chunk6
    quotient0Coefficient0Chunk5
    quotient0Coefficient0Chunk4
    quotient0Coefficient0Chunk3
    quotient0Coefficient0Chunk2
    quotient0Coefficient0Chunk1
    quotient0Coefficient0Chunk0
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    exceptional0
    exceptionalUnit0
    parameter
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow,
    Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring

private theorem recurrence0Inner6 :
    Internal.selectionCofactorCoefficient6 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient6 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient5 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient4 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient3 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient2 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient1 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient0 +
      exceptional0 * remainder2Coefficient6 := by
  unfold Internal.selectionCofactorCoefficient6
    Internal.selectionCofactorCoefficient6Chunk8
    Internal.selectionCofactorCoefficient6Chunk7
    Internal.selectionCofactorCoefficient6Chunk6
    Internal.selectionCofactorCoefficient6Chunk5
    Internal.selectionCofactorCoefficient6Chunk4
    Internal.selectionCofactorCoefficient6Chunk3
    Internal.selectionCofactorCoefficient6Chunk2
    Internal.selectionCofactorCoefficient6Chunk1
    Internal.selectionCofactorCoefficient6Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
    quotient0Coefficient6
    quotient0Coefficient6Block0
    quotient0Coefficient6Chunk9
    quotient0Coefficient6Chunk8
    quotient0Coefficient6Chunk7
    quotient0Coefficient6Chunk6
    quotient0Coefficient6Chunk5
    quotient0Coefficient6Chunk4
    quotient0Coefficient6Chunk3
    quotient0Coefficient6Chunk2
    quotient0Coefficient6Chunk1
    quotient0Coefficient6Chunk0
    Internal.divisionCofactor0Coefficient1
    Internal.divisionCofactor0Coefficient1Chunk1
    Internal.divisionCofactor0Coefficient1Chunk0
    quotient0Coefficient5
    quotient0Coefficient5Block0
    quotient0Coefficient5Chunk9
    quotient0Coefficient5Chunk8
    quotient0Coefficient5Chunk7
    quotient0Coefficient5Chunk6
    quotient0Coefficient5Chunk5
    quotient0Coefficient5Chunk4
    quotient0Coefficient5Chunk3
    quotient0Coefficient5Chunk2
    quotient0Coefficient5Chunk1
    quotient0Coefficient5Chunk0
    Internal.divisionCofactor0Coefficient2
    Internal.divisionCofactor0Coefficient2Chunk1
    Internal.divisionCofactor0Coefficient2Chunk0
    quotient0Coefficient4
    quotient0Coefficient4Block0
    quotient0Coefficient4Chunk10
    quotient0Coefficient4Chunk9
    quotient0Coefficient4Chunk8
    quotient0Coefficient4Chunk7
    quotient0Coefficient4Chunk6
    quotient0Coefficient4Chunk5
    quotient0Coefficient4Chunk4
    quotient0Coefficient4Chunk3
    quotient0Coefficient4Chunk2
    quotient0Coefficient4Chunk1
    quotient0Coefficient4Chunk0
    Internal.divisionCofactor0Coefficient3
    Internal.divisionCofactor0Coefficient3Chunk1
    Internal.divisionCofactor0Coefficient3Chunk0
    quotient0Coefficient3
    quotient0Coefficient3Block0
    quotient0Coefficient3Chunk10
    quotient0Coefficient3Chunk9
    quotient0Coefficient3Chunk8
    quotient0Coefficient3Chunk7
    quotient0Coefficient3Chunk6
    quotient0Coefficient3Chunk5
    quotient0Coefficient3Chunk4
    quotient0Coefficient3Chunk3
    quotient0Coefficient3Chunk2
    quotient0Coefficient3Chunk1
    quotient0Coefficient3Chunk0
    Internal.divisionCofactor0Coefficient4
    Internal.divisionCofactor0Coefficient4Chunk0
    quotient0Coefficient2
    quotient0Coefficient2Block0
    quotient0Coefficient2Chunk11
    quotient0Coefficient2Chunk10
    quotient0Coefficient2Chunk9
    quotient0Coefficient2Chunk8
    quotient0Coefficient2Chunk7
    quotient0Coefficient2Chunk6
    quotient0Coefficient2Chunk5
    quotient0Coefficient2Chunk4
    quotient0Coefficient2Chunk3
    quotient0Coefficient2Chunk2
    quotient0Coefficient2Chunk1
    quotient0Coefficient2Chunk0
    Internal.divisionCofactor0Coefficient5
    Internal.divisionCofactor0Coefficient5Chunk0
    quotient0Coefficient1
    quotient0Coefficient1Block0
    quotient0Coefficient1Chunk11
    quotient0Coefficient1Chunk10
    quotient0Coefficient1Chunk9
    quotient0Coefficient1Chunk8
    quotient0Coefficient1Chunk7
    quotient0Coefficient1Chunk6
    quotient0Coefficient1Chunk5
    quotient0Coefficient1Chunk4
    quotient0Coefficient1Chunk3
    quotient0Coefficient1Chunk2
    quotient0Coefficient1Chunk1
    quotient0Coefficient1Chunk0
    Internal.divisionCofactor0Coefficient6
    Internal.divisionCofactor0Coefficient6Chunk0
    quotient0Coefficient0
    quotient0Coefficient0Block1
    quotient0Coefficient0Block0
    quotient0Coefficient0Chunk12
    quotient0Coefficient0Chunk11
    quotient0Coefficient0Chunk10
    quotient0Coefficient0Chunk9
    quotient0Coefficient0Chunk8
    quotient0Coefficient0Chunk7
    quotient0Coefficient0Chunk6
    quotient0Coefficient0Chunk5
    quotient0Coefficient0Chunk4
    quotient0Coefficient0Chunk3
    quotient0Coefficient0Chunk2
    quotient0Coefficient0Chunk1
    quotient0Coefficient0Chunk0
    remainder2Coefficient6
    remainder2Coefficient6Block0
    remainder2Coefficient6Chunk11
    remainder2Coefficient6Chunk10
    remainder2Coefficient6Chunk9
    remainder2Coefficient6Chunk8
    remainder2Coefficient6Chunk7
    remainder2Coefficient6Chunk6
    remainder2Coefficient6Chunk5
    remainder2Coefficient6Chunk4
    remainder2Coefficient6Chunk3
    remainder2Coefficient6Chunk2
    remainder2Coefficient6Chunk1
    remainder2Coefficient6Chunk0
    exceptional0
    exceptionalUnit0
    parameter
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow,
    Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring

private theorem recurrence0Inner7 :
    Internal.selectionCofactorCoefficient7 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient7 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient6 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient5 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient4 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient3 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient2 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient1 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient0 := by
  unfold Internal.selectionCofactorCoefficient7
    Internal.selectionCofactorCoefficient7Chunk8
    Internal.selectionCofactorCoefficient7Chunk7
    Internal.selectionCofactorCoefficient7Chunk6
    Internal.selectionCofactorCoefficient7Chunk5
    Internal.selectionCofactorCoefficient7Chunk4
    Internal.selectionCofactorCoefficient7Chunk3
    Internal.selectionCofactorCoefficient7Chunk2
    Internal.selectionCofactorCoefficient7Chunk1
    Internal.selectionCofactorCoefficient7Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
    quotient0Coefficient7
    quotient0Coefficient7Block0
    quotient0Coefficient7Chunk9
    quotient0Coefficient7Chunk8
    quotient0Coefficient7Chunk7
    quotient0Coefficient7Chunk6
    quotient0Coefficient7Chunk5
    quotient0Coefficient7Chunk4
    quotient0Coefficient7Chunk3
    quotient0Coefficient7Chunk2
    quotient0Coefficient7Chunk1
    quotient0Coefficient7Chunk0
    Internal.divisionCofactor0Coefficient1
    Internal.divisionCofactor0Coefficient1Chunk1
    Internal.divisionCofactor0Coefficient1Chunk0
    quotient0Coefficient6
    quotient0Coefficient6Block0
    quotient0Coefficient6Chunk9
    quotient0Coefficient6Chunk8
    quotient0Coefficient6Chunk7
    quotient0Coefficient6Chunk6
    quotient0Coefficient6Chunk5
    quotient0Coefficient6Chunk4
    quotient0Coefficient6Chunk3
    quotient0Coefficient6Chunk2
    quotient0Coefficient6Chunk1
    quotient0Coefficient6Chunk0
    Internal.divisionCofactor0Coefficient2
    Internal.divisionCofactor0Coefficient2Chunk1
    Internal.divisionCofactor0Coefficient2Chunk0
    quotient0Coefficient5
    quotient0Coefficient5Block0
    quotient0Coefficient5Chunk9
    quotient0Coefficient5Chunk8
    quotient0Coefficient5Chunk7
    quotient0Coefficient5Chunk6
    quotient0Coefficient5Chunk5
    quotient0Coefficient5Chunk4
    quotient0Coefficient5Chunk3
    quotient0Coefficient5Chunk2
    quotient0Coefficient5Chunk1
    quotient0Coefficient5Chunk0
    Internal.divisionCofactor0Coefficient3
    Internal.divisionCofactor0Coefficient3Chunk1
    Internal.divisionCofactor0Coefficient3Chunk0
    quotient0Coefficient4
    quotient0Coefficient4Block0
    quotient0Coefficient4Chunk10
    quotient0Coefficient4Chunk9
    quotient0Coefficient4Chunk8
    quotient0Coefficient4Chunk7
    quotient0Coefficient4Chunk6
    quotient0Coefficient4Chunk5
    quotient0Coefficient4Chunk4
    quotient0Coefficient4Chunk3
    quotient0Coefficient4Chunk2
    quotient0Coefficient4Chunk1
    quotient0Coefficient4Chunk0
    Internal.divisionCofactor0Coefficient4
    Internal.divisionCofactor0Coefficient4Chunk0
    quotient0Coefficient3
    quotient0Coefficient3Block0
    quotient0Coefficient3Chunk10
    quotient0Coefficient3Chunk9
    quotient0Coefficient3Chunk8
    quotient0Coefficient3Chunk7
    quotient0Coefficient3Chunk6
    quotient0Coefficient3Chunk5
    quotient0Coefficient3Chunk4
    quotient0Coefficient3Chunk3
    quotient0Coefficient3Chunk2
    quotient0Coefficient3Chunk1
    quotient0Coefficient3Chunk0
    Internal.divisionCofactor0Coefficient5
    Internal.divisionCofactor0Coefficient5Chunk0
    quotient0Coefficient2
    quotient0Coefficient2Block0
    quotient0Coefficient2Chunk11
    quotient0Coefficient2Chunk10
    quotient0Coefficient2Chunk9
    quotient0Coefficient2Chunk8
    quotient0Coefficient2Chunk7
    quotient0Coefficient2Chunk6
    quotient0Coefficient2Chunk5
    quotient0Coefficient2Chunk4
    quotient0Coefficient2Chunk3
    quotient0Coefficient2Chunk2
    quotient0Coefficient2Chunk1
    quotient0Coefficient2Chunk0
    Internal.divisionCofactor0Coefficient6
    Internal.divisionCofactor0Coefficient6Chunk0
    quotient0Coefficient1
    quotient0Coefficient1Block0
    quotient0Coefficient1Chunk11
    quotient0Coefficient1Chunk10
    quotient0Coefficient1Chunk9
    quotient0Coefficient1Chunk8
    quotient0Coefficient1Chunk7
    quotient0Coefficient1Chunk6
    quotient0Coefficient1Chunk5
    quotient0Coefficient1Chunk4
    quotient0Coefficient1Chunk3
    quotient0Coefficient1Chunk2
    quotient0Coefficient1Chunk1
    quotient0Coefficient1Chunk0
    Internal.divisionCofactor0Coefficient7
    Internal.divisionCofactor0Coefficient7Chunk0
    quotient0Coefficient0
    quotient0Coefficient0Block1
    quotient0Coefficient0Block0
    quotient0Coefficient0Chunk12
    quotient0Coefficient0Chunk11
    quotient0Coefficient0Chunk10
    quotient0Coefficient0Chunk9
    quotient0Coefficient0Chunk8
    quotient0Coefficient0Chunk7
    quotient0Coefficient0Chunk6
    quotient0Coefficient0Chunk5
    quotient0Coefficient0Chunk4
    quotient0Coefficient0Chunk3
    quotient0Coefficient0Chunk2
    quotient0Coefficient0Chunk1
    quotient0Coefficient0Chunk0
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow,
    Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring

private theorem recurrence0Inner8 :
    Internal.selectionCofactorCoefficient8 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient8 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient7 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient6 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient5 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient4 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient3 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient2 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient1 := by
  unfold Internal.selectionCofactorCoefficient8
    Internal.selectionCofactorCoefficient8Chunk8
    Internal.selectionCofactorCoefficient8Chunk7
    Internal.selectionCofactorCoefficient8Chunk6
    Internal.selectionCofactorCoefficient8Chunk5
    Internal.selectionCofactorCoefficient8Chunk4
    Internal.selectionCofactorCoefficient8Chunk3
    Internal.selectionCofactorCoefficient8Chunk2
    Internal.selectionCofactorCoefficient8Chunk1
    Internal.selectionCofactorCoefficient8Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
    quotient0Coefficient8
    quotient0Coefficient8Block0
    quotient0Coefficient8Chunk8
    quotient0Coefficient8Chunk7
    quotient0Coefficient8Chunk6
    quotient0Coefficient8Chunk5
    quotient0Coefficient8Chunk4
    quotient0Coefficient8Chunk3
    quotient0Coefficient8Chunk2
    quotient0Coefficient8Chunk1
    quotient0Coefficient8Chunk0
    Internal.divisionCofactor0Coefficient1
    Internal.divisionCofactor0Coefficient1Chunk1
    Internal.divisionCofactor0Coefficient1Chunk0
    quotient0Coefficient7
    quotient0Coefficient7Block0
    quotient0Coefficient7Chunk9
    quotient0Coefficient7Chunk8
    quotient0Coefficient7Chunk7
    quotient0Coefficient7Chunk6
    quotient0Coefficient7Chunk5
    quotient0Coefficient7Chunk4
    quotient0Coefficient7Chunk3
    quotient0Coefficient7Chunk2
    quotient0Coefficient7Chunk1
    quotient0Coefficient7Chunk0
    Internal.divisionCofactor0Coefficient2
    Internal.divisionCofactor0Coefficient2Chunk1
    Internal.divisionCofactor0Coefficient2Chunk0
    quotient0Coefficient6
    quotient0Coefficient6Block0
    quotient0Coefficient6Chunk9
    quotient0Coefficient6Chunk8
    quotient0Coefficient6Chunk7
    quotient0Coefficient6Chunk6
    quotient0Coefficient6Chunk5
    quotient0Coefficient6Chunk4
    quotient0Coefficient6Chunk3
    quotient0Coefficient6Chunk2
    quotient0Coefficient6Chunk1
    quotient0Coefficient6Chunk0
    Internal.divisionCofactor0Coefficient3
    Internal.divisionCofactor0Coefficient3Chunk1
    Internal.divisionCofactor0Coefficient3Chunk0
    quotient0Coefficient5
    quotient0Coefficient5Block0
    quotient0Coefficient5Chunk9
    quotient0Coefficient5Chunk8
    quotient0Coefficient5Chunk7
    quotient0Coefficient5Chunk6
    quotient0Coefficient5Chunk5
    quotient0Coefficient5Chunk4
    quotient0Coefficient5Chunk3
    quotient0Coefficient5Chunk2
    quotient0Coefficient5Chunk1
    quotient0Coefficient5Chunk0
    Internal.divisionCofactor0Coefficient4
    Internal.divisionCofactor0Coefficient4Chunk0
    quotient0Coefficient4
    quotient0Coefficient4Block0
    quotient0Coefficient4Chunk10
    quotient0Coefficient4Chunk9
    quotient0Coefficient4Chunk8
    quotient0Coefficient4Chunk7
    quotient0Coefficient4Chunk6
    quotient0Coefficient4Chunk5
    quotient0Coefficient4Chunk4
    quotient0Coefficient4Chunk3
    quotient0Coefficient4Chunk2
    quotient0Coefficient4Chunk1
    quotient0Coefficient4Chunk0
    Internal.divisionCofactor0Coefficient5
    Internal.divisionCofactor0Coefficient5Chunk0
    quotient0Coefficient3
    quotient0Coefficient3Block0
    quotient0Coefficient3Chunk10
    quotient0Coefficient3Chunk9
    quotient0Coefficient3Chunk8
    quotient0Coefficient3Chunk7
    quotient0Coefficient3Chunk6
    quotient0Coefficient3Chunk5
    quotient0Coefficient3Chunk4
    quotient0Coefficient3Chunk3
    quotient0Coefficient3Chunk2
    quotient0Coefficient3Chunk1
    quotient0Coefficient3Chunk0
    Internal.divisionCofactor0Coefficient6
    Internal.divisionCofactor0Coefficient6Chunk0
    quotient0Coefficient2
    quotient0Coefficient2Block0
    quotient0Coefficient2Chunk11
    quotient0Coefficient2Chunk10
    quotient0Coefficient2Chunk9
    quotient0Coefficient2Chunk8
    quotient0Coefficient2Chunk7
    quotient0Coefficient2Chunk6
    quotient0Coefficient2Chunk5
    quotient0Coefficient2Chunk4
    quotient0Coefficient2Chunk3
    quotient0Coefficient2Chunk2
    quotient0Coefficient2Chunk1
    quotient0Coefficient2Chunk0
    Internal.divisionCofactor0Coefficient7
    Internal.divisionCofactor0Coefficient7Chunk0
    quotient0Coefficient1
    quotient0Coefficient1Block0
    quotient0Coefficient1Chunk11
    quotient0Coefficient1Chunk10
    quotient0Coefficient1Chunk9
    quotient0Coefficient1Chunk8
    quotient0Coefficient1Chunk7
    quotient0Coefficient1Chunk6
    quotient0Coefficient1Chunk5
    quotient0Coefficient1Chunk4
    quotient0Coefficient1Chunk3
    quotient0Coefficient1Chunk2
    quotient0Coefficient1Chunk1
    quotient0Coefficient1Chunk0
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow,
    Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring

private theorem recurrence0Inner9 :
    Internal.selectionCofactorCoefficient9 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient9 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient8 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient7 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient6 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient5 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient4 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient3 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient2 := by
  unfold Internal.selectionCofactorCoefficient9
    Internal.selectionCofactorCoefficient9Chunk7
    Internal.selectionCofactorCoefficient9Chunk6
    Internal.selectionCofactorCoefficient9Chunk5
    Internal.selectionCofactorCoefficient9Chunk4
    Internal.selectionCofactorCoefficient9Chunk3
    Internal.selectionCofactorCoefficient9Chunk2
    Internal.selectionCofactorCoefficient9Chunk1
    Internal.selectionCofactorCoefficient9Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
    quotient0Coefficient9
    quotient0Coefficient9Block0
    quotient0Coefficient9Chunk8
    quotient0Coefficient9Chunk7
    quotient0Coefficient9Chunk6
    quotient0Coefficient9Chunk5
    quotient0Coefficient9Chunk4
    quotient0Coefficient9Chunk3
    quotient0Coefficient9Chunk2
    quotient0Coefficient9Chunk1
    quotient0Coefficient9Chunk0
    Internal.divisionCofactor0Coefficient1
    Internal.divisionCofactor0Coefficient1Chunk1
    Internal.divisionCofactor0Coefficient1Chunk0
    quotient0Coefficient8
    quotient0Coefficient8Block0
    quotient0Coefficient8Chunk8
    quotient0Coefficient8Chunk7
    quotient0Coefficient8Chunk6
    quotient0Coefficient8Chunk5
    quotient0Coefficient8Chunk4
    quotient0Coefficient8Chunk3
    quotient0Coefficient8Chunk2
    quotient0Coefficient8Chunk1
    quotient0Coefficient8Chunk0
    Internal.divisionCofactor0Coefficient2
    Internal.divisionCofactor0Coefficient2Chunk1
    Internal.divisionCofactor0Coefficient2Chunk0
    quotient0Coefficient7
    quotient0Coefficient7Block0
    quotient0Coefficient7Chunk9
    quotient0Coefficient7Chunk8
    quotient0Coefficient7Chunk7
    quotient0Coefficient7Chunk6
    quotient0Coefficient7Chunk5
    quotient0Coefficient7Chunk4
    quotient0Coefficient7Chunk3
    quotient0Coefficient7Chunk2
    quotient0Coefficient7Chunk1
    quotient0Coefficient7Chunk0
    Internal.divisionCofactor0Coefficient3
    Internal.divisionCofactor0Coefficient3Chunk1
    Internal.divisionCofactor0Coefficient3Chunk0
    quotient0Coefficient6
    quotient0Coefficient6Block0
    quotient0Coefficient6Chunk9
    quotient0Coefficient6Chunk8
    quotient0Coefficient6Chunk7
    quotient0Coefficient6Chunk6
    quotient0Coefficient6Chunk5
    quotient0Coefficient6Chunk4
    quotient0Coefficient6Chunk3
    quotient0Coefficient6Chunk2
    quotient0Coefficient6Chunk1
    quotient0Coefficient6Chunk0
    Internal.divisionCofactor0Coefficient4
    Internal.divisionCofactor0Coefficient4Chunk0
    quotient0Coefficient5
    quotient0Coefficient5Block0
    quotient0Coefficient5Chunk9
    quotient0Coefficient5Chunk8
    quotient0Coefficient5Chunk7
    quotient0Coefficient5Chunk6
    quotient0Coefficient5Chunk5
    quotient0Coefficient5Chunk4
    quotient0Coefficient5Chunk3
    quotient0Coefficient5Chunk2
    quotient0Coefficient5Chunk1
    quotient0Coefficient5Chunk0
    Internal.divisionCofactor0Coefficient5
    Internal.divisionCofactor0Coefficient5Chunk0
    quotient0Coefficient4
    quotient0Coefficient4Block0
    quotient0Coefficient4Chunk10
    quotient0Coefficient4Chunk9
    quotient0Coefficient4Chunk8
    quotient0Coefficient4Chunk7
    quotient0Coefficient4Chunk6
    quotient0Coefficient4Chunk5
    quotient0Coefficient4Chunk4
    quotient0Coefficient4Chunk3
    quotient0Coefficient4Chunk2
    quotient0Coefficient4Chunk1
    quotient0Coefficient4Chunk0
    Internal.divisionCofactor0Coefficient6
    Internal.divisionCofactor0Coefficient6Chunk0
    quotient0Coefficient3
    quotient0Coefficient3Block0
    quotient0Coefficient3Chunk10
    quotient0Coefficient3Chunk9
    quotient0Coefficient3Chunk8
    quotient0Coefficient3Chunk7
    quotient0Coefficient3Chunk6
    quotient0Coefficient3Chunk5
    quotient0Coefficient3Chunk4
    quotient0Coefficient3Chunk3
    quotient0Coefficient3Chunk2
    quotient0Coefficient3Chunk1
    quotient0Coefficient3Chunk0
    Internal.divisionCofactor0Coefficient7
    Internal.divisionCofactor0Coefficient7Chunk0
    quotient0Coefficient2
    quotient0Coefficient2Block0
    quotient0Coefficient2Chunk11
    quotient0Coefficient2Chunk10
    quotient0Coefficient2Chunk9
    quotient0Coefficient2Chunk8
    quotient0Coefficient2Chunk7
    quotient0Coefficient2Chunk6
    quotient0Coefficient2Chunk5
    quotient0Coefficient2Chunk4
    quotient0Coefficient2Chunk3
    quotient0Coefficient2Chunk2
    quotient0Coefficient2Chunk1
    quotient0Coefficient2Chunk0
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow,
    Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring

private theorem recurrence0Inner10 :
    Internal.selectionCofactorCoefficient10 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient10 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient9 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient8 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient7 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient6 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient5 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient4 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient3 := by
  unfold Internal.selectionCofactorCoefficient10
    Internal.selectionCofactorCoefficient10Chunk7
    Internal.selectionCofactorCoefficient10Chunk6
    Internal.selectionCofactorCoefficient10Chunk5
    Internal.selectionCofactorCoefficient10Chunk4
    Internal.selectionCofactorCoefficient10Chunk3
    Internal.selectionCofactorCoefficient10Chunk2
    Internal.selectionCofactorCoefficient10Chunk1
    Internal.selectionCofactorCoefficient10Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
    quotient0Coefficient10
    quotient0Coefficient10Block0
    quotient0Coefficient10Chunk7
    quotient0Coefficient10Chunk6
    quotient0Coefficient10Chunk5
    quotient0Coefficient10Chunk4
    quotient0Coefficient10Chunk3
    quotient0Coefficient10Chunk2
    quotient0Coefficient10Chunk1
    quotient0Coefficient10Chunk0
    Internal.divisionCofactor0Coefficient1
    Internal.divisionCofactor0Coefficient1Chunk1
    Internal.divisionCofactor0Coefficient1Chunk0
    quotient0Coefficient9
    quotient0Coefficient9Block0
    quotient0Coefficient9Chunk8
    quotient0Coefficient9Chunk7
    quotient0Coefficient9Chunk6
    quotient0Coefficient9Chunk5
    quotient0Coefficient9Chunk4
    quotient0Coefficient9Chunk3
    quotient0Coefficient9Chunk2
    quotient0Coefficient9Chunk1
    quotient0Coefficient9Chunk0
    Internal.divisionCofactor0Coefficient2
    Internal.divisionCofactor0Coefficient2Chunk1
    Internal.divisionCofactor0Coefficient2Chunk0
    quotient0Coefficient8
    quotient0Coefficient8Block0
    quotient0Coefficient8Chunk8
    quotient0Coefficient8Chunk7
    quotient0Coefficient8Chunk6
    quotient0Coefficient8Chunk5
    quotient0Coefficient8Chunk4
    quotient0Coefficient8Chunk3
    quotient0Coefficient8Chunk2
    quotient0Coefficient8Chunk1
    quotient0Coefficient8Chunk0
    Internal.divisionCofactor0Coefficient3
    Internal.divisionCofactor0Coefficient3Chunk1
    Internal.divisionCofactor0Coefficient3Chunk0
    quotient0Coefficient7
    quotient0Coefficient7Block0
    quotient0Coefficient7Chunk9
    quotient0Coefficient7Chunk8
    quotient0Coefficient7Chunk7
    quotient0Coefficient7Chunk6
    quotient0Coefficient7Chunk5
    quotient0Coefficient7Chunk4
    quotient0Coefficient7Chunk3
    quotient0Coefficient7Chunk2
    quotient0Coefficient7Chunk1
    quotient0Coefficient7Chunk0
    Internal.divisionCofactor0Coefficient4
    Internal.divisionCofactor0Coefficient4Chunk0
    quotient0Coefficient6
    quotient0Coefficient6Block0
    quotient0Coefficient6Chunk9
    quotient0Coefficient6Chunk8
    quotient0Coefficient6Chunk7
    quotient0Coefficient6Chunk6
    quotient0Coefficient6Chunk5
    quotient0Coefficient6Chunk4
    quotient0Coefficient6Chunk3
    quotient0Coefficient6Chunk2
    quotient0Coefficient6Chunk1
    quotient0Coefficient6Chunk0
    Internal.divisionCofactor0Coefficient5
    Internal.divisionCofactor0Coefficient5Chunk0
    quotient0Coefficient5
    quotient0Coefficient5Block0
    quotient0Coefficient5Chunk9
    quotient0Coefficient5Chunk8
    quotient0Coefficient5Chunk7
    quotient0Coefficient5Chunk6
    quotient0Coefficient5Chunk5
    quotient0Coefficient5Chunk4
    quotient0Coefficient5Chunk3
    quotient0Coefficient5Chunk2
    quotient0Coefficient5Chunk1
    quotient0Coefficient5Chunk0
    Internal.divisionCofactor0Coefficient6
    Internal.divisionCofactor0Coefficient6Chunk0
    quotient0Coefficient4
    quotient0Coefficient4Block0
    quotient0Coefficient4Chunk10
    quotient0Coefficient4Chunk9
    quotient0Coefficient4Chunk8
    quotient0Coefficient4Chunk7
    quotient0Coefficient4Chunk6
    quotient0Coefficient4Chunk5
    quotient0Coefficient4Chunk4
    quotient0Coefficient4Chunk3
    quotient0Coefficient4Chunk2
    quotient0Coefficient4Chunk1
    quotient0Coefficient4Chunk0
    Internal.divisionCofactor0Coefficient7
    Internal.divisionCofactor0Coefficient7Chunk0
    quotient0Coefficient3
    quotient0Coefficient3Block0
    quotient0Coefficient3Chunk10
    quotient0Coefficient3Chunk9
    quotient0Coefficient3Chunk8
    quotient0Coefficient3Chunk7
    quotient0Coefficient3Chunk6
    quotient0Coefficient3Chunk5
    quotient0Coefficient3Chunk4
    quotient0Coefficient3Chunk3
    quotient0Coefficient3Chunk2
    quotient0Coefficient3Chunk1
    quotient0Coefficient3Chunk0
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow,
    Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring

private theorem recurrence0Inner11 :
    Internal.selectionCofactorCoefficient11 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient11 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient10 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient9 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient8 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient7 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient6 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient5 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient4 := by
  unfold Internal.selectionCofactorCoefficient11
    Internal.selectionCofactorCoefficient11Chunk7
    Internal.selectionCofactorCoefficient11Chunk6
    Internal.selectionCofactorCoefficient11Chunk5
    Internal.selectionCofactorCoefficient11Chunk4
    Internal.selectionCofactorCoefficient11Chunk3
    Internal.selectionCofactorCoefficient11Chunk2
    Internal.selectionCofactorCoefficient11Chunk1
    Internal.selectionCofactorCoefficient11Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
    quotient0Coefficient11
    quotient0Coefficient11Block0
    quotient0Coefficient11Chunk7
    quotient0Coefficient11Chunk6
    quotient0Coefficient11Chunk5
    quotient0Coefficient11Chunk4
    quotient0Coefficient11Chunk3
    quotient0Coefficient11Chunk2
    quotient0Coefficient11Chunk1
    quotient0Coefficient11Chunk0
    Internal.divisionCofactor0Coefficient1
    Internal.divisionCofactor0Coefficient1Chunk1
    Internal.divisionCofactor0Coefficient1Chunk0
    quotient0Coefficient10
    quotient0Coefficient10Block0
    quotient0Coefficient10Chunk7
    quotient0Coefficient10Chunk6
    quotient0Coefficient10Chunk5
    quotient0Coefficient10Chunk4
    quotient0Coefficient10Chunk3
    quotient0Coefficient10Chunk2
    quotient0Coefficient10Chunk1
    quotient0Coefficient10Chunk0
    Internal.divisionCofactor0Coefficient2
    Internal.divisionCofactor0Coefficient2Chunk1
    Internal.divisionCofactor0Coefficient2Chunk0
    quotient0Coefficient9
    quotient0Coefficient9Block0
    quotient0Coefficient9Chunk8
    quotient0Coefficient9Chunk7
    quotient0Coefficient9Chunk6
    quotient0Coefficient9Chunk5
    quotient0Coefficient9Chunk4
    quotient0Coefficient9Chunk3
    quotient0Coefficient9Chunk2
    quotient0Coefficient9Chunk1
    quotient0Coefficient9Chunk0
    Internal.divisionCofactor0Coefficient3
    Internal.divisionCofactor0Coefficient3Chunk1
    Internal.divisionCofactor0Coefficient3Chunk0
    quotient0Coefficient8
    quotient0Coefficient8Block0
    quotient0Coefficient8Chunk8
    quotient0Coefficient8Chunk7
    quotient0Coefficient8Chunk6
    quotient0Coefficient8Chunk5
    quotient0Coefficient8Chunk4
    quotient0Coefficient8Chunk3
    quotient0Coefficient8Chunk2
    quotient0Coefficient8Chunk1
    quotient0Coefficient8Chunk0
    Internal.divisionCofactor0Coefficient4
    Internal.divisionCofactor0Coefficient4Chunk0
    quotient0Coefficient7
    quotient0Coefficient7Block0
    quotient0Coefficient7Chunk9
    quotient0Coefficient7Chunk8
    quotient0Coefficient7Chunk7
    quotient0Coefficient7Chunk6
    quotient0Coefficient7Chunk5
    quotient0Coefficient7Chunk4
    quotient0Coefficient7Chunk3
    quotient0Coefficient7Chunk2
    quotient0Coefficient7Chunk1
    quotient0Coefficient7Chunk0
    Internal.divisionCofactor0Coefficient5
    Internal.divisionCofactor0Coefficient5Chunk0
    quotient0Coefficient6
    quotient0Coefficient6Block0
    quotient0Coefficient6Chunk9
    quotient0Coefficient6Chunk8
    quotient0Coefficient6Chunk7
    quotient0Coefficient6Chunk6
    quotient0Coefficient6Chunk5
    quotient0Coefficient6Chunk4
    quotient0Coefficient6Chunk3
    quotient0Coefficient6Chunk2
    quotient0Coefficient6Chunk1
    quotient0Coefficient6Chunk0
    Internal.divisionCofactor0Coefficient6
    Internal.divisionCofactor0Coefficient6Chunk0
    quotient0Coefficient5
    quotient0Coefficient5Block0
    quotient0Coefficient5Chunk9
    quotient0Coefficient5Chunk8
    quotient0Coefficient5Chunk7
    quotient0Coefficient5Chunk6
    quotient0Coefficient5Chunk5
    quotient0Coefficient5Chunk4
    quotient0Coefficient5Chunk3
    quotient0Coefficient5Chunk2
    quotient0Coefficient5Chunk1
    quotient0Coefficient5Chunk0
    Internal.divisionCofactor0Coefficient7
    Internal.divisionCofactor0Coefficient7Chunk0
    quotient0Coefficient4
    quotient0Coefficient4Block0
    quotient0Coefficient4Chunk10
    quotient0Coefficient4Chunk9
    quotient0Coefficient4Chunk8
    quotient0Coefficient4Chunk7
    quotient0Coefficient4Chunk6
    quotient0Coefficient4Chunk5
    quotient0Coefficient4Chunk4
    quotient0Coefficient4Chunk3
    quotient0Coefficient4Chunk2
    quotient0Coefficient4Chunk1
    quotient0Coefficient4Chunk0
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow,
    Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring

private theorem recurrence0Inner12 :
    Internal.selectionCofactorCoefficient12 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient12 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient11 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient10 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient9 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient8 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient7 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient6 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient5 := by
  unfold Internal.selectionCofactorCoefficient12
    Internal.selectionCofactorCoefficient12Chunk6
    Internal.selectionCofactorCoefficient12Chunk5
    Internal.selectionCofactorCoefficient12Chunk4
    Internal.selectionCofactorCoefficient12Chunk3
    Internal.selectionCofactorCoefficient12Chunk2
    Internal.selectionCofactorCoefficient12Chunk1
    Internal.selectionCofactorCoefficient12Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
    quotient0Coefficient12
    quotient0Coefficient12Block0
    quotient0Coefficient12Chunk6
    quotient0Coefficient12Chunk5
    quotient0Coefficient12Chunk4
    quotient0Coefficient12Chunk3
    quotient0Coefficient12Chunk2
    quotient0Coefficient12Chunk1
    quotient0Coefficient12Chunk0
    Internal.divisionCofactor0Coefficient1
    Internal.divisionCofactor0Coefficient1Chunk1
    Internal.divisionCofactor0Coefficient1Chunk0
    quotient0Coefficient11
    quotient0Coefficient11Block0
    quotient0Coefficient11Chunk7
    quotient0Coefficient11Chunk6
    quotient0Coefficient11Chunk5
    quotient0Coefficient11Chunk4
    quotient0Coefficient11Chunk3
    quotient0Coefficient11Chunk2
    quotient0Coefficient11Chunk1
    quotient0Coefficient11Chunk0
    Internal.divisionCofactor0Coefficient2
    Internal.divisionCofactor0Coefficient2Chunk1
    Internal.divisionCofactor0Coefficient2Chunk0
    quotient0Coefficient10
    quotient0Coefficient10Block0
    quotient0Coefficient10Chunk7
    quotient0Coefficient10Chunk6
    quotient0Coefficient10Chunk5
    quotient0Coefficient10Chunk4
    quotient0Coefficient10Chunk3
    quotient0Coefficient10Chunk2
    quotient0Coefficient10Chunk1
    quotient0Coefficient10Chunk0
    Internal.divisionCofactor0Coefficient3
    Internal.divisionCofactor0Coefficient3Chunk1
    Internal.divisionCofactor0Coefficient3Chunk0
    quotient0Coefficient9
    quotient0Coefficient9Block0
    quotient0Coefficient9Chunk8
    quotient0Coefficient9Chunk7
    quotient0Coefficient9Chunk6
    quotient0Coefficient9Chunk5
    quotient0Coefficient9Chunk4
    quotient0Coefficient9Chunk3
    quotient0Coefficient9Chunk2
    quotient0Coefficient9Chunk1
    quotient0Coefficient9Chunk0
    Internal.divisionCofactor0Coefficient4
    Internal.divisionCofactor0Coefficient4Chunk0
    quotient0Coefficient8
    quotient0Coefficient8Block0
    quotient0Coefficient8Chunk8
    quotient0Coefficient8Chunk7
    quotient0Coefficient8Chunk6
    quotient0Coefficient8Chunk5
    quotient0Coefficient8Chunk4
    quotient0Coefficient8Chunk3
    quotient0Coefficient8Chunk2
    quotient0Coefficient8Chunk1
    quotient0Coefficient8Chunk0
    Internal.divisionCofactor0Coefficient5
    Internal.divisionCofactor0Coefficient5Chunk0
    quotient0Coefficient7
    quotient0Coefficient7Block0
    quotient0Coefficient7Chunk9
    quotient0Coefficient7Chunk8
    quotient0Coefficient7Chunk7
    quotient0Coefficient7Chunk6
    quotient0Coefficient7Chunk5
    quotient0Coefficient7Chunk4
    quotient0Coefficient7Chunk3
    quotient0Coefficient7Chunk2
    quotient0Coefficient7Chunk1
    quotient0Coefficient7Chunk0
    Internal.divisionCofactor0Coefficient6
    Internal.divisionCofactor0Coefficient6Chunk0
    quotient0Coefficient6
    quotient0Coefficient6Block0
    quotient0Coefficient6Chunk9
    quotient0Coefficient6Chunk8
    quotient0Coefficient6Chunk7
    quotient0Coefficient6Chunk6
    quotient0Coefficient6Chunk5
    quotient0Coefficient6Chunk4
    quotient0Coefficient6Chunk3
    quotient0Coefficient6Chunk2
    quotient0Coefficient6Chunk1
    quotient0Coefficient6Chunk0
    Internal.divisionCofactor0Coefficient7
    Internal.divisionCofactor0Coefficient7Chunk0
    quotient0Coefficient5
    quotient0Coefficient5Block0
    quotient0Coefficient5Chunk9
    quotient0Coefficient5Chunk8
    quotient0Coefficient5Chunk7
    quotient0Coefficient5Chunk6
    quotient0Coefficient5Chunk5
    quotient0Coefficient5Chunk4
    quotient0Coefficient5Chunk3
    quotient0Coefficient5Chunk2
    quotient0Coefficient5Chunk1
    quotient0Coefficient5Chunk0
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow,
    Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring

private theorem recurrence0Inner13 :
    Internal.selectionCofactorCoefficient13 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient13 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient12 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient11 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient10 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient9 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient8 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient7 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient6 := by
  unfold Internal.selectionCofactorCoefficient13
    Internal.selectionCofactorCoefficient13Chunk6
    Internal.selectionCofactorCoefficient13Chunk5
    Internal.selectionCofactorCoefficient13Chunk4
    Internal.selectionCofactorCoefficient13Chunk3
    Internal.selectionCofactorCoefficient13Chunk2
    Internal.selectionCofactorCoefficient13Chunk1
    Internal.selectionCofactorCoefficient13Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
    quotient0Coefficient13
    quotient0Coefficient13Block0
    quotient0Coefficient13Chunk6
    quotient0Coefficient13Chunk5
    quotient0Coefficient13Chunk4
    quotient0Coefficient13Chunk3
    quotient0Coefficient13Chunk2
    quotient0Coefficient13Chunk1
    quotient0Coefficient13Chunk0
    Internal.divisionCofactor0Coefficient1
    Internal.divisionCofactor0Coefficient1Chunk1
    Internal.divisionCofactor0Coefficient1Chunk0
    quotient0Coefficient12
    quotient0Coefficient12Block0
    quotient0Coefficient12Chunk6
    quotient0Coefficient12Chunk5
    quotient0Coefficient12Chunk4
    quotient0Coefficient12Chunk3
    quotient0Coefficient12Chunk2
    quotient0Coefficient12Chunk1
    quotient0Coefficient12Chunk0
    Internal.divisionCofactor0Coefficient2
    Internal.divisionCofactor0Coefficient2Chunk1
    Internal.divisionCofactor0Coefficient2Chunk0
    quotient0Coefficient11
    quotient0Coefficient11Block0
    quotient0Coefficient11Chunk7
    quotient0Coefficient11Chunk6
    quotient0Coefficient11Chunk5
    quotient0Coefficient11Chunk4
    quotient0Coefficient11Chunk3
    quotient0Coefficient11Chunk2
    quotient0Coefficient11Chunk1
    quotient0Coefficient11Chunk0
    Internal.divisionCofactor0Coefficient3
    Internal.divisionCofactor0Coefficient3Chunk1
    Internal.divisionCofactor0Coefficient3Chunk0
    quotient0Coefficient10
    quotient0Coefficient10Block0
    quotient0Coefficient10Chunk7
    quotient0Coefficient10Chunk6
    quotient0Coefficient10Chunk5
    quotient0Coefficient10Chunk4
    quotient0Coefficient10Chunk3
    quotient0Coefficient10Chunk2
    quotient0Coefficient10Chunk1
    quotient0Coefficient10Chunk0
    Internal.divisionCofactor0Coefficient4
    Internal.divisionCofactor0Coefficient4Chunk0
    quotient0Coefficient9
    quotient0Coefficient9Block0
    quotient0Coefficient9Chunk8
    quotient0Coefficient9Chunk7
    quotient0Coefficient9Chunk6
    quotient0Coefficient9Chunk5
    quotient0Coefficient9Chunk4
    quotient0Coefficient9Chunk3
    quotient0Coefficient9Chunk2
    quotient0Coefficient9Chunk1
    quotient0Coefficient9Chunk0
    Internal.divisionCofactor0Coefficient5
    Internal.divisionCofactor0Coefficient5Chunk0
    quotient0Coefficient8
    quotient0Coefficient8Block0
    quotient0Coefficient8Chunk8
    quotient0Coefficient8Chunk7
    quotient0Coefficient8Chunk6
    quotient0Coefficient8Chunk5
    quotient0Coefficient8Chunk4
    quotient0Coefficient8Chunk3
    quotient0Coefficient8Chunk2
    quotient0Coefficient8Chunk1
    quotient0Coefficient8Chunk0
    Internal.divisionCofactor0Coefficient6
    Internal.divisionCofactor0Coefficient6Chunk0
    quotient0Coefficient7
    quotient0Coefficient7Block0
    quotient0Coefficient7Chunk9
    quotient0Coefficient7Chunk8
    quotient0Coefficient7Chunk7
    quotient0Coefficient7Chunk6
    quotient0Coefficient7Chunk5
    quotient0Coefficient7Chunk4
    quotient0Coefficient7Chunk3
    quotient0Coefficient7Chunk2
    quotient0Coefficient7Chunk1
    quotient0Coefficient7Chunk0
    Internal.divisionCofactor0Coefficient7
    Internal.divisionCofactor0Coefficient7Chunk0
    quotient0Coefficient6
    quotient0Coefficient6Block0
    quotient0Coefficient6Chunk9
    quotient0Coefficient6Chunk8
    quotient0Coefficient6Chunk7
    quotient0Coefficient6Chunk6
    quotient0Coefficient6Chunk5
    quotient0Coefficient6Chunk4
    quotient0Coefficient6Chunk3
    quotient0Coefficient6Chunk2
    quotient0Coefficient6Chunk1
    quotient0Coefficient6Chunk0
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow,
    Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring

private theorem recurrence0Inner14 :
    Internal.selectionCofactorCoefficient14 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient14 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient13 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient12 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient11 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient10 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient9 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient8 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient7 := by
  unfold Internal.selectionCofactorCoefficient14
    Internal.selectionCofactorCoefficient14Chunk6
    Internal.selectionCofactorCoefficient14Chunk5
    Internal.selectionCofactorCoefficient14Chunk4
    Internal.selectionCofactorCoefficient14Chunk3
    Internal.selectionCofactorCoefficient14Chunk2
    Internal.selectionCofactorCoefficient14Chunk1
    Internal.selectionCofactorCoefficient14Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
    quotient0Coefficient14
    quotient0Coefficient14Block0
    quotient0Coefficient14Chunk6
    quotient0Coefficient14Chunk5
    quotient0Coefficient14Chunk4
    quotient0Coefficient14Chunk3
    quotient0Coefficient14Chunk2
    quotient0Coefficient14Chunk1
    quotient0Coefficient14Chunk0
    Internal.divisionCofactor0Coefficient1
    Internal.divisionCofactor0Coefficient1Chunk1
    Internal.divisionCofactor0Coefficient1Chunk0
    quotient0Coefficient13
    quotient0Coefficient13Block0
    quotient0Coefficient13Chunk6
    quotient0Coefficient13Chunk5
    quotient0Coefficient13Chunk4
    quotient0Coefficient13Chunk3
    quotient0Coefficient13Chunk2
    quotient0Coefficient13Chunk1
    quotient0Coefficient13Chunk0
    Internal.divisionCofactor0Coefficient2
    Internal.divisionCofactor0Coefficient2Chunk1
    Internal.divisionCofactor0Coefficient2Chunk0
    quotient0Coefficient12
    quotient0Coefficient12Block0
    quotient0Coefficient12Chunk6
    quotient0Coefficient12Chunk5
    quotient0Coefficient12Chunk4
    quotient0Coefficient12Chunk3
    quotient0Coefficient12Chunk2
    quotient0Coefficient12Chunk1
    quotient0Coefficient12Chunk0
    Internal.divisionCofactor0Coefficient3
    Internal.divisionCofactor0Coefficient3Chunk1
    Internal.divisionCofactor0Coefficient3Chunk0
    quotient0Coefficient11
    quotient0Coefficient11Block0
    quotient0Coefficient11Chunk7
    quotient0Coefficient11Chunk6
    quotient0Coefficient11Chunk5
    quotient0Coefficient11Chunk4
    quotient0Coefficient11Chunk3
    quotient0Coefficient11Chunk2
    quotient0Coefficient11Chunk1
    quotient0Coefficient11Chunk0
    Internal.divisionCofactor0Coefficient4
    Internal.divisionCofactor0Coefficient4Chunk0
    quotient0Coefficient10
    quotient0Coefficient10Block0
    quotient0Coefficient10Chunk7
    quotient0Coefficient10Chunk6
    quotient0Coefficient10Chunk5
    quotient0Coefficient10Chunk4
    quotient0Coefficient10Chunk3
    quotient0Coefficient10Chunk2
    quotient0Coefficient10Chunk1
    quotient0Coefficient10Chunk0
    Internal.divisionCofactor0Coefficient5
    Internal.divisionCofactor0Coefficient5Chunk0
    quotient0Coefficient9
    quotient0Coefficient9Block0
    quotient0Coefficient9Chunk8
    quotient0Coefficient9Chunk7
    quotient0Coefficient9Chunk6
    quotient0Coefficient9Chunk5
    quotient0Coefficient9Chunk4
    quotient0Coefficient9Chunk3
    quotient0Coefficient9Chunk2
    quotient0Coefficient9Chunk1
    quotient0Coefficient9Chunk0
    Internal.divisionCofactor0Coefficient6
    Internal.divisionCofactor0Coefficient6Chunk0
    quotient0Coefficient8
    quotient0Coefficient8Block0
    quotient0Coefficient8Chunk8
    quotient0Coefficient8Chunk7
    quotient0Coefficient8Chunk6
    quotient0Coefficient8Chunk5
    quotient0Coefficient8Chunk4
    quotient0Coefficient8Chunk3
    quotient0Coefficient8Chunk2
    quotient0Coefficient8Chunk1
    quotient0Coefficient8Chunk0
    Internal.divisionCofactor0Coefficient7
    Internal.divisionCofactor0Coefficient7Chunk0
    quotient0Coefficient7
    quotient0Coefficient7Block0
    quotient0Coefficient7Chunk9
    quotient0Coefficient7Chunk8
    quotient0Coefficient7Chunk7
    quotient0Coefficient7Chunk6
    quotient0Coefficient7Chunk5
    quotient0Coefficient7Chunk4
    quotient0Coefficient7Chunk3
    quotient0Coefficient7Chunk2
    quotient0Coefficient7Chunk1
    quotient0Coefficient7Chunk0
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow,
    Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring

private theorem recurrence0Inner15 :
    Internal.selectionCofactorCoefficient15 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient15 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient14 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient13 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient12 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient11 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient10 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient9 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient8 := by
  unfold Internal.selectionCofactorCoefficient15
    Internal.selectionCofactorCoefficient15Chunk6
    Internal.selectionCofactorCoefficient15Chunk5
    Internal.selectionCofactorCoefficient15Chunk4
    Internal.selectionCofactorCoefficient15Chunk3
    Internal.selectionCofactorCoefficient15Chunk2
    Internal.selectionCofactorCoefficient15Chunk1
    Internal.selectionCofactorCoefficient15Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
    quotient0Coefficient15
    quotient0Coefficient15Block0
    quotient0Coefficient15Chunk5
    quotient0Coefficient15Chunk4
    quotient0Coefficient15Chunk3
    quotient0Coefficient15Chunk2
    quotient0Coefficient15Chunk1
    quotient0Coefficient15Chunk0
    Internal.divisionCofactor0Coefficient1
    Internal.divisionCofactor0Coefficient1Chunk1
    Internal.divisionCofactor0Coefficient1Chunk0
    quotient0Coefficient14
    quotient0Coefficient14Block0
    quotient0Coefficient14Chunk6
    quotient0Coefficient14Chunk5
    quotient0Coefficient14Chunk4
    quotient0Coefficient14Chunk3
    quotient0Coefficient14Chunk2
    quotient0Coefficient14Chunk1
    quotient0Coefficient14Chunk0
    Internal.divisionCofactor0Coefficient2
    Internal.divisionCofactor0Coefficient2Chunk1
    Internal.divisionCofactor0Coefficient2Chunk0
    quotient0Coefficient13
    quotient0Coefficient13Block0
    quotient0Coefficient13Chunk6
    quotient0Coefficient13Chunk5
    quotient0Coefficient13Chunk4
    quotient0Coefficient13Chunk3
    quotient0Coefficient13Chunk2
    quotient0Coefficient13Chunk1
    quotient0Coefficient13Chunk0
    Internal.divisionCofactor0Coefficient3
    Internal.divisionCofactor0Coefficient3Chunk1
    Internal.divisionCofactor0Coefficient3Chunk0
    quotient0Coefficient12
    quotient0Coefficient12Block0
    quotient0Coefficient12Chunk6
    quotient0Coefficient12Chunk5
    quotient0Coefficient12Chunk4
    quotient0Coefficient12Chunk3
    quotient0Coefficient12Chunk2
    quotient0Coefficient12Chunk1
    quotient0Coefficient12Chunk0
    Internal.divisionCofactor0Coefficient4
    Internal.divisionCofactor0Coefficient4Chunk0
    quotient0Coefficient11
    quotient0Coefficient11Block0
    quotient0Coefficient11Chunk7
    quotient0Coefficient11Chunk6
    quotient0Coefficient11Chunk5
    quotient0Coefficient11Chunk4
    quotient0Coefficient11Chunk3
    quotient0Coefficient11Chunk2
    quotient0Coefficient11Chunk1
    quotient0Coefficient11Chunk0
    Internal.divisionCofactor0Coefficient5
    Internal.divisionCofactor0Coefficient5Chunk0
    quotient0Coefficient10
    quotient0Coefficient10Block0
    quotient0Coefficient10Chunk7
    quotient0Coefficient10Chunk6
    quotient0Coefficient10Chunk5
    quotient0Coefficient10Chunk4
    quotient0Coefficient10Chunk3
    quotient0Coefficient10Chunk2
    quotient0Coefficient10Chunk1
    quotient0Coefficient10Chunk0
    Internal.divisionCofactor0Coefficient6
    Internal.divisionCofactor0Coefficient6Chunk0
    quotient0Coefficient9
    quotient0Coefficient9Block0
    quotient0Coefficient9Chunk8
    quotient0Coefficient9Chunk7
    quotient0Coefficient9Chunk6
    quotient0Coefficient9Chunk5
    quotient0Coefficient9Chunk4
    quotient0Coefficient9Chunk3
    quotient0Coefficient9Chunk2
    quotient0Coefficient9Chunk1
    quotient0Coefficient9Chunk0
    Internal.divisionCofactor0Coefficient7
    Internal.divisionCofactor0Coefficient7Chunk0
    quotient0Coefficient8
    quotient0Coefficient8Block0
    quotient0Coefficient8Chunk8
    quotient0Coefficient8Chunk7
    quotient0Coefficient8Chunk6
    quotient0Coefficient8Chunk5
    quotient0Coefficient8Chunk4
    quotient0Coefficient8Chunk3
    quotient0Coefficient8Chunk2
    quotient0Coefficient8Chunk1
    quotient0Coefficient8Chunk0
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring

private theorem recurrence0Inner16 :
    Internal.selectionCofactorCoefficient16 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient16 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient15 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient14 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient13 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient12 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient11 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient10 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient9 := by
  unfold Internal.selectionCofactorCoefficient16
    Internal.selectionCofactorCoefficient16Chunk5
    Internal.selectionCofactorCoefficient16Chunk4
    Internal.selectionCofactorCoefficient16Chunk3
    Internal.selectionCofactorCoefficient16Chunk2
    Internal.selectionCofactorCoefficient16Chunk1
    Internal.selectionCofactorCoefficient16Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
    quotient0Coefficient16
    quotient0Coefficient16Block0
    quotient0Coefficient16Chunk5
    quotient0Coefficient16Chunk4
    quotient0Coefficient16Chunk3
    quotient0Coefficient16Chunk2
    quotient0Coefficient16Chunk1
    quotient0Coefficient16Chunk0
    Internal.divisionCofactor0Coefficient1
    Internal.divisionCofactor0Coefficient1Chunk1
    Internal.divisionCofactor0Coefficient1Chunk0
    quotient0Coefficient15
    quotient0Coefficient15Block0
    quotient0Coefficient15Chunk5
    quotient0Coefficient15Chunk4
    quotient0Coefficient15Chunk3
    quotient0Coefficient15Chunk2
    quotient0Coefficient15Chunk1
    quotient0Coefficient15Chunk0
    Internal.divisionCofactor0Coefficient2
    Internal.divisionCofactor0Coefficient2Chunk1
    Internal.divisionCofactor0Coefficient2Chunk0
    quotient0Coefficient14
    quotient0Coefficient14Block0
    quotient0Coefficient14Chunk6
    quotient0Coefficient14Chunk5
    quotient0Coefficient14Chunk4
    quotient0Coefficient14Chunk3
    quotient0Coefficient14Chunk2
    quotient0Coefficient14Chunk1
    quotient0Coefficient14Chunk0
    Internal.divisionCofactor0Coefficient3
    Internal.divisionCofactor0Coefficient3Chunk1
    Internal.divisionCofactor0Coefficient3Chunk0
    quotient0Coefficient13
    quotient0Coefficient13Block0
    quotient0Coefficient13Chunk6
    quotient0Coefficient13Chunk5
    quotient0Coefficient13Chunk4
    quotient0Coefficient13Chunk3
    quotient0Coefficient13Chunk2
    quotient0Coefficient13Chunk1
    quotient0Coefficient13Chunk0
    Internal.divisionCofactor0Coefficient4
    Internal.divisionCofactor0Coefficient4Chunk0
    quotient0Coefficient12
    quotient0Coefficient12Block0
    quotient0Coefficient12Chunk6
    quotient0Coefficient12Chunk5
    quotient0Coefficient12Chunk4
    quotient0Coefficient12Chunk3
    quotient0Coefficient12Chunk2
    quotient0Coefficient12Chunk1
    quotient0Coefficient12Chunk0
    Internal.divisionCofactor0Coefficient5
    Internal.divisionCofactor0Coefficient5Chunk0
    quotient0Coefficient11
    quotient0Coefficient11Block0
    quotient0Coefficient11Chunk7
    quotient0Coefficient11Chunk6
    quotient0Coefficient11Chunk5
    quotient0Coefficient11Chunk4
    quotient0Coefficient11Chunk3
    quotient0Coefficient11Chunk2
    quotient0Coefficient11Chunk1
    quotient0Coefficient11Chunk0
    Internal.divisionCofactor0Coefficient6
    Internal.divisionCofactor0Coefficient6Chunk0
    quotient0Coefficient10
    quotient0Coefficient10Block0
    quotient0Coefficient10Chunk7
    quotient0Coefficient10Chunk6
    quotient0Coefficient10Chunk5
    quotient0Coefficient10Chunk4
    quotient0Coefficient10Chunk3
    quotient0Coefficient10Chunk2
    quotient0Coefficient10Chunk1
    quotient0Coefficient10Chunk0
    Internal.divisionCofactor0Coefficient7
    Internal.divisionCofactor0Coefficient7Chunk0
    quotient0Coefficient9
    quotient0Coefficient9Block0
    quotient0Coefficient9Chunk8
    quotient0Coefficient9Chunk7
    quotient0Coefficient9Chunk6
    quotient0Coefficient9Chunk5
    quotient0Coefficient9Chunk4
    quotient0Coefficient9Chunk3
    quotient0Coefficient9Chunk2
    quotient0Coefficient9Chunk1
    quotient0Coefficient9Chunk0
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring

private theorem recurrence0Inner17 :
    Internal.selectionCofactorCoefficient17 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient17 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient16 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient15 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient14 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient13 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient12 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient11 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient10 := by
  unfold Internal.selectionCofactorCoefficient17
    Internal.selectionCofactorCoefficient17Chunk5
    Internal.selectionCofactorCoefficient17Chunk4
    Internal.selectionCofactorCoefficient17Chunk3
    Internal.selectionCofactorCoefficient17Chunk2
    Internal.selectionCofactorCoefficient17Chunk1
    Internal.selectionCofactorCoefficient17Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
    quotient0Coefficient17
    quotient0Coefficient17Block0
    quotient0Coefficient17Chunk4
    quotient0Coefficient17Chunk3
    quotient0Coefficient17Chunk2
    quotient0Coefficient17Chunk1
    quotient0Coefficient17Chunk0
    Internal.divisionCofactor0Coefficient1
    Internal.divisionCofactor0Coefficient1Chunk1
    Internal.divisionCofactor0Coefficient1Chunk0
    quotient0Coefficient16
    quotient0Coefficient16Block0
    quotient0Coefficient16Chunk5
    quotient0Coefficient16Chunk4
    quotient0Coefficient16Chunk3
    quotient0Coefficient16Chunk2
    quotient0Coefficient16Chunk1
    quotient0Coefficient16Chunk0
    Internal.divisionCofactor0Coefficient2
    Internal.divisionCofactor0Coefficient2Chunk1
    Internal.divisionCofactor0Coefficient2Chunk0
    quotient0Coefficient15
    quotient0Coefficient15Block0
    quotient0Coefficient15Chunk5
    quotient0Coefficient15Chunk4
    quotient0Coefficient15Chunk3
    quotient0Coefficient15Chunk2
    quotient0Coefficient15Chunk1
    quotient0Coefficient15Chunk0
    Internal.divisionCofactor0Coefficient3
    Internal.divisionCofactor0Coefficient3Chunk1
    Internal.divisionCofactor0Coefficient3Chunk0
    quotient0Coefficient14
    quotient0Coefficient14Block0
    quotient0Coefficient14Chunk6
    quotient0Coefficient14Chunk5
    quotient0Coefficient14Chunk4
    quotient0Coefficient14Chunk3
    quotient0Coefficient14Chunk2
    quotient0Coefficient14Chunk1
    quotient0Coefficient14Chunk0
    Internal.divisionCofactor0Coefficient4
    Internal.divisionCofactor0Coefficient4Chunk0
    quotient0Coefficient13
    quotient0Coefficient13Block0
    quotient0Coefficient13Chunk6
    quotient0Coefficient13Chunk5
    quotient0Coefficient13Chunk4
    quotient0Coefficient13Chunk3
    quotient0Coefficient13Chunk2
    quotient0Coefficient13Chunk1
    quotient0Coefficient13Chunk0
    Internal.divisionCofactor0Coefficient5
    Internal.divisionCofactor0Coefficient5Chunk0
    quotient0Coefficient12
    quotient0Coefficient12Block0
    quotient0Coefficient12Chunk6
    quotient0Coefficient12Chunk5
    quotient0Coefficient12Chunk4
    quotient0Coefficient12Chunk3
    quotient0Coefficient12Chunk2
    quotient0Coefficient12Chunk1
    quotient0Coefficient12Chunk0
    Internal.divisionCofactor0Coefficient6
    Internal.divisionCofactor0Coefficient6Chunk0
    quotient0Coefficient11
    quotient0Coefficient11Block0
    quotient0Coefficient11Chunk7
    quotient0Coefficient11Chunk6
    quotient0Coefficient11Chunk5
    quotient0Coefficient11Chunk4
    quotient0Coefficient11Chunk3
    quotient0Coefficient11Chunk2
    quotient0Coefficient11Chunk1
    quotient0Coefficient11Chunk0
    Internal.divisionCofactor0Coefficient7
    Internal.divisionCofactor0Coefficient7Chunk0
    quotient0Coefficient10
    quotient0Coefficient10Block0
    quotient0Coefficient10Chunk7
    quotient0Coefficient10Chunk6
    quotient0Coefficient10Chunk5
    quotient0Coefficient10Chunk4
    quotient0Coefficient10Chunk3
    quotient0Coefficient10Chunk2
    quotient0Coefficient10Chunk1
    quotient0Coefficient10Chunk0
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring

private theorem recurrence0Inner18 :
    Internal.selectionCofactorCoefficient18 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient18 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient17 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient16 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient15 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient14 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient13 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient12 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient11 := by
  unfold Internal.selectionCofactorCoefficient18
    Internal.selectionCofactorCoefficient18Chunk5
    Internal.selectionCofactorCoefficient18Chunk4
    Internal.selectionCofactorCoefficient18Chunk3
    Internal.selectionCofactorCoefficient18Chunk2
    Internal.selectionCofactorCoefficient18Chunk1
    Internal.selectionCofactorCoefficient18Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
    quotient0Coefficient18
    quotient0Coefficient18Block0
    quotient0Coefficient18Chunk4
    quotient0Coefficient18Chunk3
    quotient0Coefficient18Chunk2
    quotient0Coefficient18Chunk1
    quotient0Coefficient18Chunk0
    Internal.divisionCofactor0Coefficient1
    Internal.divisionCofactor0Coefficient1Chunk1
    Internal.divisionCofactor0Coefficient1Chunk0
    quotient0Coefficient17
    quotient0Coefficient17Block0
    quotient0Coefficient17Chunk4
    quotient0Coefficient17Chunk3
    quotient0Coefficient17Chunk2
    quotient0Coefficient17Chunk1
    quotient0Coefficient17Chunk0
    Internal.divisionCofactor0Coefficient2
    Internal.divisionCofactor0Coefficient2Chunk1
    Internal.divisionCofactor0Coefficient2Chunk0
    quotient0Coefficient16
    quotient0Coefficient16Block0
    quotient0Coefficient16Chunk5
    quotient0Coefficient16Chunk4
    quotient0Coefficient16Chunk3
    quotient0Coefficient16Chunk2
    quotient0Coefficient16Chunk1
    quotient0Coefficient16Chunk0
    Internal.divisionCofactor0Coefficient3
    Internal.divisionCofactor0Coefficient3Chunk1
    Internal.divisionCofactor0Coefficient3Chunk0
    quotient0Coefficient15
    quotient0Coefficient15Block0
    quotient0Coefficient15Chunk5
    quotient0Coefficient15Chunk4
    quotient0Coefficient15Chunk3
    quotient0Coefficient15Chunk2
    quotient0Coefficient15Chunk1
    quotient0Coefficient15Chunk0
    Internal.divisionCofactor0Coefficient4
    Internal.divisionCofactor0Coefficient4Chunk0
    quotient0Coefficient14
    quotient0Coefficient14Block0
    quotient0Coefficient14Chunk6
    quotient0Coefficient14Chunk5
    quotient0Coefficient14Chunk4
    quotient0Coefficient14Chunk3
    quotient0Coefficient14Chunk2
    quotient0Coefficient14Chunk1
    quotient0Coefficient14Chunk0
    Internal.divisionCofactor0Coefficient5
    Internal.divisionCofactor0Coefficient5Chunk0
    quotient0Coefficient13
    quotient0Coefficient13Block0
    quotient0Coefficient13Chunk6
    quotient0Coefficient13Chunk5
    quotient0Coefficient13Chunk4
    quotient0Coefficient13Chunk3
    quotient0Coefficient13Chunk2
    quotient0Coefficient13Chunk1
    quotient0Coefficient13Chunk0
    Internal.divisionCofactor0Coefficient6
    Internal.divisionCofactor0Coefficient6Chunk0
    quotient0Coefficient12
    quotient0Coefficient12Block0
    quotient0Coefficient12Chunk6
    quotient0Coefficient12Chunk5
    quotient0Coefficient12Chunk4
    quotient0Coefficient12Chunk3
    quotient0Coefficient12Chunk2
    quotient0Coefficient12Chunk1
    quotient0Coefficient12Chunk0
    Internal.divisionCofactor0Coefficient7
    Internal.divisionCofactor0Coefficient7Chunk0
    quotient0Coefficient11
    quotient0Coefficient11Block0
    quotient0Coefficient11Chunk7
    quotient0Coefficient11Chunk6
    quotient0Coefficient11Chunk5
    quotient0Coefficient11Chunk4
    quotient0Coefficient11Chunk3
    quotient0Coefficient11Chunk2
    quotient0Coefficient11Chunk1
    quotient0Coefficient11Chunk0
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring

private theorem recurrence0Inner19 :
    Internal.selectionCofactorCoefficient19 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient19 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient18 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient17 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient16 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient15 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient14 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient13 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient12 := by
  unfold Internal.selectionCofactorCoefficient19
    Internal.selectionCofactorCoefficient19Chunk4
    Internal.selectionCofactorCoefficient19Chunk3
    Internal.selectionCofactorCoefficient19Chunk2
    Internal.selectionCofactorCoefficient19Chunk1
    Internal.selectionCofactorCoefficient19Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
    quotient0Coefficient19
    quotient0Coefficient19Block0
    quotient0Coefficient19Chunk3
    quotient0Coefficient19Chunk2
    quotient0Coefficient19Chunk1
    quotient0Coefficient19Chunk0
    Internal.divisionCofactor0Coefficient1
    Internal.divisionCofactor0Coefficient1Chunk1
    Internal.divisionCofactor0Coefficient1Chunk0
    quotient0Coefficient18
    quotient0Coefficient18Block0
    quotient0Coefficient18Chunk4
    quotient0Coefficient18Chunk3
    quotient0Coefficient18Chunk2
    quotient0Coefficient18Chunk1
    quotient0Coefficient18Chunk0
    Internal.divisionCofactor0Coefficient2
    Internal.divisionCofactor0Coefficient2Chunk1
    Internal.divisionCofactor0Coefficient2Chunk0
    quotient0Coefficient17
    quotient0Coefficient17Block0
    quotient0Coefficient17Chunk4
    quotient0Coefficient17Chunk3
    quotient0Coefficient17Chunk2
    quotient0Coefficient17Chunk1
    quotient0Coefficient17Chunk0
    Internal.divisionCofactor0Coefficient3
    Internal.divisionCofactor0Coefficient3Chunk1
    Internal.divisionCofactor0Coefficient3Chunk0
    quotient0Coefficient16
    quotient0Coefficient16Block0
    quotient0Coefficient16Chunk5
    quotient0Coefficient16Chunk4
    quotient0Coefficient16Chunk3
    quotient0Coefficient16Chunk2
    quotient0Coefficient16Chunk1
    quotient0Coefficient16Chunk0
    Internal.divisionCofactor0Coefficient4
    Internal.divisionCofactor0Coefficient4Chunk0
    quotient0Coefficient15
    quotient0Coefficient15Block0
    quotient0Coefficient15Chunk5
    quotient0Coefficient15Chunk4
    quotient0Coefficient15Chunk3
    quotient0Coefficient15Chunk2
    quotient0Coefficient15Chunk1
    quotient0Coefficient15Chunk0
    Internal.divisionCofactor0Coefficient5
    Internal.divisionCofactor0Coefficient5Chunk0
    quotient0Coefficient14
    quotient0Coefficient14Block0
    quotient0Coefficient14Chunk6
    quotient0Coefficient14Chunk5
    quotient0Coefficient14Chunk4
    quotient0Coefficient14Chunk3
    quotient0Coefficient14Chunk2
    quotient0Coefficient14Chunk1
    quotient0Coefficient14Chunk0
    Internal.divisionCofactor0Coefficient6
    Internal.divisionCofactor0Coefficient6Chunk0
    quotient0Coefficient13
    quotient0Coefficient13Block0
    quotient0Coefficient13Chunk6
    quotient0Coefficient13Chunk5
    quotient0Coefficient13Chunk4
    quotient0Coefficient13Chunk3
    quotient0Coefficient13Chunk2
    quotient0Coefficient13Chunk1
    quotient0Coefficient13Chunk0
    Internal.divisionCofactor0Coefficient7
    Internal.divisionCofactor0Coefficient7Chunk0
    quotient0Coefficient12
    quotient0Coefficient12Block0
    quotient0Coefficient12Chunk6
    quotient0Coefficient12Chunk5
    quotient0Coefficient12Chunk4
    quotient0Coefficient12Chunk3
    quotient0Coefficient12Chunk2
    quotient0Coefficient12Chunk1
    quotient0Coefficient12Chunk0
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring

private theorem recurrence0Inner20 :
    Internal.selectionCofactorCoefficient20 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient20 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient19 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient18 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient17 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient16 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient15 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient14 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient13 := by
  unfold Internal.selectionCofactorCoefficient20
    Internal.selectionCofactorCoefficient20Chunk4
    Internal.selectionCofactorCoefficient20Chunk3
    Internal.selectionCofactorCoefficient20Chunk2
    Internal.selectionCofactorCoefficient20Chunk1
    Internal.selectionCofactorCoefficient20Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
    quotient0Coefficient20
    quotient0Coefficient20Block0
    quotient0Coefficient20Chunk3
    quotient0Coefficient20Chunk2
    quotient0Coefficient20Chunk1
    quotient0Coefficient20Chunk0
    Internal.divisionCofactor0Coefficient1
    Internal.divisionCofactor0Coefficient1Chunk1
    Internal.divisionCofactor0Coefficient1Chunk0
    quotient0Coefficient19
    quotient0Coefficient19Block0
    quotient0Coefficient19Chunk3
    quotient0Coefficient19Chunk2
    quotient0Coefficient19Chunk1
    quotient0Coefficient19Chunk0
    Internal.divisionCofactor0Coefficient2
    Internal.divisionCofactor0Coefficient2Chunk1
    Internal.divisionCofactor0Coefficient2Chunk0
    quotient0Coefficient18
    quotient0Coefficient18Block0
    quotient0Coefficient18Chunk4
    quotient0Coefficient18Chunk3
    quotient0Coefficient18Chunk2
    quotient0Coefficient18Chunk1
    quotient0Coefficient18Chunk0
    Internal.divisionCofactor0Coefficient3
    Internal.divisionCofactor0Coefficient3Chunk1
    Internal.divisionCofactor0Coefficient3Chunk0
    quotient0Coefficient17
    quotient0Coefficient17Block0
    quotient0Coefficient17Chunk4
    quotient0Coefficient17Chunk3
    quotient0Coefficient17Chunk2
    quotient0Coefficient17Chunk1
    quotient0Coefficient17Chunk0
    Internal.divisionCofactor0Coefficient4
    Internal.divisionCofactor0Coefficient4Chunk0
    quotient0Coefficient16
    quotient0Coefficient16Block0
    quotient0Coefficient16Chunk5
    quotient0Coefficient16Chunk4
    quotient0Coefficient16Chunk3
    quotient0Coefficient16Chunk2
    quotient0Coefficient16Chunk1
    quotient0Coefficient16Chunk0
    Internal.divisionCofactor0Coefficient5
    Internal.divisionCofactor0Coefficient5Chunk0
    quotient0Coefficient15
    quotient0Coefficient15Block0
    quotient0Coefficient15Chunk5
    quotient0Coefficient15Chunk4
    quotient0Coefficient15Chunk3
    quotient0Coefficient15Chunk2
    quotient0Coefficient15Chunk1
    quotient0Coefficient15Chunk0
    Internal.divisionCofactor0Coefficient6
    Internal.divisionCofactor0Coefficient6Chunk0
    quotient0Coefficient14
    quotient0Coefficient14Block0
    quotient0Coefficient14Chunk6
    quotient0Coefficient14Chunk5
    quotient0Coefficient14Chunk4
    quotient0Coefficient14Chunk3
    quotient0Coefficient14Chunk2
    quotient0Coefficient14Chunk1
    quotient0Coefficient14Chunk0
    Internal.divisionCofactor0Coefficient7
    Internal.divisionCofactor0Coefficient7Chunk0
    quotient0Coefficient13
    quotient0Coefficient13Block0
    quotient0Coefficient13Chunk6
    quotient0Coefficient13Chunk5
    quotient0Coefficient13Chunk4
    quotient0Coefficient13Chunk3
    quotient0Coefficient13Chunk2
    quotient0Coefficient13Chunk1
    quotient0Coefficient13Chunk0
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring

private theorem recurrence0Inner21 :
    Internal.selectionCofactorCoefficient21 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient21 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient20 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient19 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient18 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient17 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient16 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient15 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient14 := by
  unfold Internal.selectionCofactorCoefficient21
    Internal.selectionCofactorCoefficient21Chunk4
    Internal.selectionCofactorCoefficient21Chunk3
    Internal.selectionCofactorCoefficient21Chunk2
    Internal.selectionCofactorCoefficient21Chunk1
    Internal.selectionCofactorCoefficient21Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
    quotient0Coefficient21
    quotient0Coefficient21Block0
    quotient0Coefficient21Chunk2
    quotient0Coefficient21Chunk1
    quotient0Coefficient21Chunk0
    Internal.divisionCofactor0Coefficient1
    Internal.divisionCofactor0Coefficient1Chunk1
    Internal.divisionCofactor0Coefficient1Chunk0
    quotient0Coefficient20
    quotient0Coefficient20Block0
    quotient0Coefficient20Chunk3
    quotient0Coefficient20Chunk2
    quotient0Coefficient20Chunk1
    quotient0Coefficient20Chunk0
    Internal.divisionCofactor0Coefficient2
    Internal.divisionCofactor0Coefficient2Chunk1
    Internal.divisionCofactor0Coefficient2Chunk0
    quotient0Coefficient19
    quotient0Coefficient19Block0
    quotient0Coefficient19Chunk3
    quotient0Coefficient19Chunk2
    quotient0Coefficient19Chunk1
    quotient0Coefficient19Chunk0
    Internal.divisionCofactor0Coefficient3
    Internal.divisionCofactor0Coefficient3Chunk1
    Internal.divisionCofactor0Coefficient3Chunk0
    quotient0Coefficient18
    quotient0Coefficient18Block0
    quotient0Coefficient18Chunk4
    quotient0Coefficient18Chunk3
    quotient0Coefficient18Chunk2
    quotient0Coefficient18Chunk1
    quotient0Coefficient18Chunk0
    Internal.divisionCofactor0Coefficient4
    Internal.divisionCofactor0Coefficient4Chunk0
    quotient0Coefficient17
    quotient0Coefficient17Block0
    quotient0Coefficient17Chunk4
    quotient0Coefficient17Chunk3
    quotient0Coefficient17Chunk2
    quotient0Coefficient17Chunk1
    quotient0Coefficient17Chunk0
    Internal.divisionCofactor0Coefficient5
    Internal.divisionCofactor0Coefficient5Chunk0
    quotient0Coefficient16
    quotient0Coefficient16Block0
    quotient0Coefficient16Chunk5
    quotient0Coefficient16Chunk4
    quotient0Coefficient16Chunk3
    quotient0Coefficient16Chunk2
    quotient0Coefficient16Chunk1
    quotient0Coefficient16Chunk0
    Internal.divisionCofactor0Coefficient6
    Internal.divisionCofactor0Coefficient6Chunk0
    quotient0Coefficient15
    quotient0Coefficient15Block0
    quotient0Coefficient15Chunk5
    quotient0Coefficient15Chunk4
    quotient0Coefficient15Chunk3
    quotient0Coefficient15Chunk2
    quotient0Coefficient15Chunk1
    quotient0Coefficient15Chunk0
    Internal.divisionCofactor0Coefficient7
    Internal.divisionCofactor0Coefficient7Chunk0
    quotient0Coefficient14
    quotient0Coefficient14Block0
    quotient0Coefficient14Chunk6
    quotient0Coefficient14Chunk5
    quotient0Coefficient14Chunk4
    quotient0Coefficient14Chunk3
    quotient0Coefficient14Chunk2
    quotient0Coefficient14Chunk1
    quotient0Coefficient14Chunk0
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring

private theorem recurrence0Inner22 :
    Internal.selectionCofactorCoefficient22 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient22 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient21 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient20 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient19 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient18 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient17 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient16 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient15 := by
  unfold Internal.selectionCofactorCoefficient22
    Internal.selectionCofactorCoefficient22Chunk3
    Internal.selectionCofactorCoefficient22Chunk2
    Internal.selectionCofactorCoefficient22Chunk1
    Internal.selectionCofactorCoefficient22Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
    quotient0Coefficient22
    quotient0Coefficient22Block0
    quotient0Coefficient22Chunk2
    quotient0Coefficient22Chunk1
    quotient0Coefficient22Chunk0
    Internal.divisionCofactor0Coefficient1
    Internal.divisionCofactor0Coefficient1Chunk1
    Internal.divisionCofactor0Coefficient1Chunk0
    quotient0Coefficient21
    quotient0Coefficient21Block0
    quotient0Coefficient21Chunk2
    quotient0Coefficient21Chunk1
    quotient0Coefficient21Chunk0
    Internal.divisionCofactor0Coefficient2
    Internal.divisionCofactor0Coefficient2Chunk1
    Internal.divisionCofactor0Coefficient2Chunk0
    quotient0Coefficient20
    quotient0Coefficient20Block0
    quotient0Coefficient20Chunk3
    quotient0Coefficient20Chunk2
    quotient0Coefficient20Chunk1
    quotient0Coefficient20Chunk0
    Internal.divisionCofactor0Coefficient3
    Internal.divisionCofactor0Coefficient3Chunk1
    Internal.divisionCofactor0Coefficient3Chunk0
    quotient0Coefficient19
    quotient0Coefficient19Block0
    quotient0Coefficient19Chunk3
    quotient0Coefficient19Chunk2
    quotient0Coefficient19Chunk1
    quotient0Coefficient19Chunk0
    Internal.divisionCofactor0Coefficient4
    Internal.divisionCofactor0Coefficient4Chunk0
    quotient0Coefficient18
    quotient0Coefficient18Block0
    quotient0Coefficient18Chunk4
    quotient0Coefficient18Chunk3
    quotient0Coefficient18Chunk2
    quotient0Coefficient18Chunk1
    quotient0Coefficient18Chunk0
    Internal.divisionCofactor0Coefficient5
    Internal.divisionCofactor0Coefficient5Chunk0
    quotient0Coefficient17
    quotient0Coefficient17Block0
    quotient0Coefficient17Chunk4
    quotient0Coefficient17Chunk3
    quotient0Coefficient17Chunk2
    quotient0Coefficient17Chunk1
    quotient0Coefficient17Chunk0
    Internal.divisionCofactor0Coefficient6
    Internal.divisionCofactor0Coefficient6Chunk0
    quotient0Coefficient16
    quotient0Coefficient16Block0
    quotient0Coefficient16Chunk5
    quotient0Coefficient16Chunk4
    quotient0Coefficient16Chunk3
    quotient0Coefficient16Chunk2
    quotient0Coefficient16Chunk1
    quotient0Coefficient16Chunk0
    Internal.divisionCofactor0Coefficient7
    Internal.divisionCofactor0Coefficient7Chunk0
    quotient0Coefficient15
    quotient0Coefficient15Block0
    quotient0Coefficient15Chunk5
    quotient0Coefficient15Chunk4
    quotient0Coefficient15Chunk3
    quotient0Coefficient15Chunk2
    quotient0Coefficient15Chunk1
    quotient0Coefficient15Chunk0
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring

private theorem recurrence0Inner23 :
    Internal.selectionCofactorCoefficient23 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient23 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient22 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient21 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient20 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient19 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient18 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient17 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient16 := by
  unfold Internal.selectionCofactorCoefficient23
    Internal.selectionCofactorCoefficient23Chunk3
    Internal.selectionCofactorCoefficient23Chunk2
    Internal.selectionCofactorCoefficient23Chunk1
    Internal.selectionCofactorCoefficient23Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
    quotient0Coefficient23
    quotient0Coefficient23Block0
    quotient0Coefficient23Chunk1
    quotient0Coefficient23Chunk0
    Internal.divisionCofactor0Coefficient1
    Internal.divisionCofactor0Coefficient1Chunk1
    Internal.divisionCofactor0Coefficient1Chunk0
    quotient0Coefficient22
    quotient0Coefficient22Block0
    quotient0Coefficient22Chunk2
    quotient0Coefficient22Chunk1
    quotient0Coefficient22Chunk0
    Internal.divisionCofactor0Coefficient2
    Internal.divisionCofactor0Coefficient2Chunk1
    Internal.divisionCofactor0Coefficient2Chunk0
    quotient0Coefficient21
    quotient0Coefficient21Block0
    quotient0Coefficient21Chunk2
    quotient0Coefficient21Chunk1
    quotient0Coefficient21Chunk0
    Internal.divisionCofactor0Coefficient3
    Internal.divisionCofactor0Coefficient3Chunk1
    Internal.divisionCofactor0Coefficient3Chunk0
    quotient0Coefficient20
    quotient0Coefficient20Block0
    quotient0Coefficient20Chunk3
    quotient0Coefficient20Chunk2
    quotient0Coefficient20Chunk1
    quotient0Coefficient20Chunk0
    Internal.divisionCofactor0Coefficient4
    Internal.divisionCofactor0Coefficient4Chunk0
    quotient0Coefficient19
    quotient0Coefficient19Block0
    quotient0Coefficient19Chunk3
    quotient0Coefficient19Chunk2
    quotient0Coefficient19Chunk1
    quotient0Coefficient19Chunk0
    Internal.divisionCofactor0Coefficient5
    Internal.divisionCofactor0Coefficient5Chunk0
    quotient0Coefficient18
    quotient0Coefficient18Block0
    quotient0Coefficient18Chunk4
    quotient0Coefficient18Chunk3
    quotient0Coefficient18Chunk2
    quotient0Coefficient18Chunk1
    quotient0Coefficient18Chunk0
    Internal.divisionCofactor0Coefficient6
    Internal.divisionCofactor0Coefficient6Chunk0
    quotient0Coefficient17
    quotient0Coefficient17Block0
    quotient0Coefficient17Chunk4
    quotient0Coefficient17Chunk3
    quotient0Coefficient17Chunk2
    quotient0Coefficient17Chunk1
    quotient0Coefficient17Chunk0
    Internal.divisionCofactor0Coefficient7
    Internal.divisionCofactor0Coefficient7Chunk0
    quotient0Coefficient16
    quotient0Coefficient16Block0
    quotient0Coefficient16Chunk5
    quotient0Coefficient16Chunk4
    quotient0Coefficient16Chunk3
    quotient0Coefficient16Chunk2
    quotient0Coefficient16Chunk1
    quotient0Coefficient16Chunk0
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring

private theorem recurrence0Inner24 :
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

private theorem recurrence0Inner25 :
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

private theorem recurrence0Inner26 :
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

private theorem recurrence0Inner27 :
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

private theorem recurrence0Inner28 :
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

private theorem recurrence0Inner29 :
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

private theorem recurrence0Inner30 :
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

private theorem recurrence0Inner31 :
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

private theorem recurrence0Inner32 :
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

private theorem recurrence0Inner33 :
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

@[simp] private theorem remainder0_coeff_0 :
    remainder0.coeff 0 = Internal.selectionCofactorCoefficient0 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_0 :
    remainder1.coeff 0 = Internal.divisionCofactor0Coefficient0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_0 :
    quotient0.coeff 0 = quotient0Coefficient0 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_0 :
    remainder2.coeff 0 = remainder2Coefficient0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_1 :
    remainder0.coeff 1 = Internal.selectionCofactorCoefficient1 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_1 :
    remainder1.coeff 1 = Internal.divisionCofactor0Coefficient1 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_1 :
    quotient0.coeff 1 = quotient0Coefficient1 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_1 :
    remainder2.coeff 1 = remainder2Coefficient1 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_2 :
    remainder0.coeff 2 = Internal.selectionCofactorCoefficient2 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_2 :
    remainder1.coeff 2 = Internal.divisionCofactor0Coefficient2 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_2 :
    quotient0.coeff 2 = quotient0Coefficient2 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_2 :
    remainder2.coeff 2 = remainder2Coefficient2 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_3 :
    remainder0.coeff 3 = Internal.selectionCofactorCoefficient3 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_3 :
    remainder1.coeff 3 = Internal.divisionCofactor0Coefficient3 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_3 :
    quotient0.coeff 3 = quotient0Coefficient3 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_3 :
    remainder2.coeff 3 = remainder2Coefficient3 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_4 :
    remainder0.coeff 4 = Internal.selectionCofactorCoefficient4 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_4 :
    remainder1.coeff 4 = Internal.divisionCofactor0Coefficient4 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_4 :
    quotient0.coeff 4 = quotient0Coefficient4 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_4 :
    remainder2.coeff 4 = remainder2Coefficient4 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_5 :
    remainder0.coeff 5 = Internal.selectionCofactorCoefficient5 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_5 :
    remainder1.coeff 5 = Internal.divisionCofactor0Coefficient5 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_5 :
    quotient0.coeff 5 = quotient0Coefficient5 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_5 :
    remainder2.coeff 5 = remainder2Coefficient5 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_6 :
    remainder0.coeff 6 = Internal.selectionCofactorCoefficient6 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_6 :
    remainder1.coeff 6 = Internal.divisionCofactor0Coefficient6 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_6 :
    quotient0.coeff 6 = quotient0Coefficient6 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_6 :
    remainder2.coeff 6 = remainder2Coefficient6 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_7 :
    remainder0.coeff 7 = Internal.selectionCofactorCoefficient7 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_7 :
    remainder1.coeff 7 = Internal.divisionCofactor0Coefficient7 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_7 :
    quotient0.coeff 7 = quotient0Coefficient7 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_7 :
    remainder2.coeff 7 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_8 :
    remainder0.coeff 8 = Internal.selectionCofactorCoefficient8 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_8 :
    remainder1.coeff 8 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_8 :
    quotient0.coeff 8 = quotient0Coefficient8 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_8 :
    remainder2.coeff 8 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_9 :
    remainder0.coeff 9 = Internal.selectionCofactorCoefficient9 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_9 :
    remainder1.coeff 9 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_9 :
    quotient0.coeff 9 = quotient0Coefficient9 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_9 :
    remainder2.coeff 9 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_10 :
    remainder0.coeff 10 = Internal.selectionCofactorCoefficient10 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_10 :
    remainder1.coeff 10 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_10 :
    quotient0.coeff 10 = quotient0Coefficient10 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_10 :
    remainder2.coeff 10 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_11 :
    remainder0.coeff 11 = Internal.selectionCofactorCoefficient11 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_11 :
    remainder1.coeff 11 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_11 :
    quotient0.coeff 11 = quotient0Coefficient11 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_11 :
    remainder2.coeff 11 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_12 :
    remainder0.coeff 12 = Internal.selectionCofactorCoefficient12 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_12 :
    remainder1.coeff 12 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_12 :
    quotient0.coeff 12 = quotient0Coefficient12 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_12 :
    remainder2.coeff 12 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_13 :
    remainder0.coeff 13 = Internal.selectionCofactorCoefficient13 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_13 :
    remainder1.coeff 13 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_13 :
    quotient0.coeff 13 = quotient0Coefficient13 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_13 :
    remainder2.coeff 13 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_14 :
    remainder0.coeff 14 = Internal.selectionCofactorCoefficient14 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_14 :
    remainder1.coeff 14 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_14 :
    quotient0.coeff 14 = quotient0Coefficient14 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_14 :
    remainder2.coeff 14 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_15 :
    remainder0.coeff 15 = Internal.selectionCofactorCoefficient15 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_15 :
    remainder1.coeff 15 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_15 :
    quotient0.coeff 15 = quotient0Coefficient15 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_15 :
    remainder2.coeff 15 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_16 :
    remainder0.coeff 16 = Internal.selectionCofactorCoefficient16 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_16 :
    remainder1.coeff 16 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_16 :
    quotient0.coeff 16 = quotient0Coefficient16 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_16 :
    remainder2.coeff 16 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_17 :
    remainder0.coeff 17 = Internal.selectionCofactorCoefficient17 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_17 :
    remainder1.coeff 17 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_17 :
    quotient0.coeff 17 = quotient0Coefficient17 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_17 :
    remainder2.coeff 17 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_18 :
    remainder0.coeff 18 = Internal.selectionCofactorCoefficient18 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_18 :
    remainder1.coeff 18 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_18 :
    quotient0.coeff 18 = quotient0Coefficient18 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_18 :
    remainder2.coeff 18 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_19 :
    remainder0.coeff 19 = Internal.selectionCofactorCoefficient19 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_19 :
    remainder1.coeff 19 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_19 :
    quotient0.coeff 19 = quotient0Coefficient19 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_19 :
    remainder2.coeff 19 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_20 :
    remainder0.coeff 20 = Internal.selectionCofactorCoefficient20 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_20 :
    remainder1.coeff 20 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_20 :
    quotient0.coeff 20 = quotient0Coefficient20 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_20 :
    remainder2.coeff 20 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_21 :
    remainder0.coeff 21 = Internal.selectionCofactorCoefficient21 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_21 :
    remainder1.coeff 21 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_21 :
    quotient0.coeff 21 = quotient0Coefficient21 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_21 :
    remainder2.coeff 21 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_22 :
    remainder0.coeff 22 = Internal.selectionCofactorCoefficient22 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_22 :
    remainder1.coeff 22 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_22 :
    quotient0.coeff 22 = quotient0Coefficient22 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_22 :
    remainder2.coeff 22 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_23 :
    remainder0.coeff 23 = Internal.selectionCofactorCoefficient23 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_23 :
    remainder1.coeff 23 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_23 :
    quotient0.coeff 23 = quotient0Coefficient23 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_23 :
    remainder2.coeff 23 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_24 :
    remainder0.coeff 24 = Internal.selectionCofactorCoefficient24 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_24 :
    remainder1.coeff 24 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_24 :
    quotient0.coeff 24 = quotient0Coefficient24 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_24 :
    remainder2.coeff 24 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_25 :
    remainder0.coeff 25 = Internal.selectionCofactorCoefficient25 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_25 :
    remainder1.coeff 25 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_25 :
    quotient0.coeff 25 = quotient0Coefficient25 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_25 :
    remainder2.coeff 25 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_26 :
    remainder0.coeff 26 = Internal.selectionCofactorCoefficient26 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_26 :
    remainder1.coeff 26 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_26 :
    quotient0.coeff 26 = quotient0Coefficient26 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_26 :
    remainder2.coeff 26 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_27 :
    remainder0.coeff 27 = Internal.selectionCofactorCoefficient27 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_27 :
    remainder1.coeff 27 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_27 :
    quotient0.coeff 27 = 0 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_27 :
    remainder2.coeff 27 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_28 :
    remainder0.coeff 28 = Internal.selectionCofactorCoefficient28 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_28 :
    remainder1.coeff 28 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_28 :
    quotient0.coeff 28 = 0 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_28 :
    remainder2.coeff 28 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_29 :
    remainder0.coeff 29 = Internal.selectionCofactorCoefficient29 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_29 :
    remainder1.coeff 29 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_29 :
    quotient0.coeff 29 = 0 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_29 :
    remainder2.coeff 29 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_30 :
    remainder0.coeff 30 = Internal.selectionCofactorCoefficient30 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_30 :
    remainder1.coeff 30 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_30 :
    quotient0.coeff 30 = 0 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_30 :
    remainder2.coeff 30 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_31 :
    remainder0.coeff 31 = Internal.selectionCofactorCoefficient31 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_31 :
    remainder1.coeff 31 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_31 :
    quotient0.coeff 31 = 0 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_31 :
    remainder2.coeff 31 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_32 :
    remainder0.coeff 32 = Internal.selectionCofactorCoefficient32 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_32 :
    remainder1.coeff 32 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_32 :
    quotient0.coeff 32 = 0 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_32 :
    remainder2.coeff 32 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_33 :
    remainder0.coeff 33 = Internal.selectionCofactorCoefficient33 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_33 :
    remainder1.coeff 33 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_33 :
    quotient0.coeff 33 = 0 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_33 :
    remainder2.coeff 33 = 0 := by
  simp [remainder2, outerTerm]


private lemma quotient0_degree : quotient0.natDegree ≤ 26 := by
  unfold quotient0 outerTerm
  compute_degree

private lemma remainder2_degree : remainder2.natDegree ≤ 6 := by
  unfold remainder2 outerTerm
  compute_degree

private lemma recurrence0_left_degree :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).natDegree ≤ 33 := by
  unfold remainder0
  compute_degree
  exact selectionCofactorData_degree

private lemma recurrence0_right_degree :
    (remainder1 * quotient0 +
      Polynomial.C exceptional0 * remainder2).natDegree ≤ 33 := by
  have hdivision := divisionCofactorData0_degree
  have hquotient := quotient0_degree
  have hremainder := remainder2_degree
  unfold remainder1
  compute_degree
  omega

private theorem recurrence0Coefficient0 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 0 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 0 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner0]

private theorem recurrence0Coefficient1 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 1 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 1 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner1]

private theorem recurrence0Coefficient2 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 2 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 2 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner2]
  ring

private theorem recurrence0Coefficient3 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 3 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 3 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner3]
  ring

private theorem recurrence0Coefficient4 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 4 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 4 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner4]
  ring

private theorem recurrence0Coefficient5 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 5 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 5 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner5]
  ring

private theorem recurrence0Coefficient6 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 6 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 6 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner6]
  ring

private theorem recurrence0Coefficient7 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 7 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 7 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner7]
  ring

private theorem recurrence0Coefficient8 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 8 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 8 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner8]
  ring

private theorem recurrence0Coefficient9 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 9 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 9 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner9]
  ring

private theorem recurrence0Coefficient10 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 10 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 10 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner10]
  ring

private theorem recurrence0Coefficient11 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 11 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 11 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner11]
  ring

private theorem recurrence0Coefficient12 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 12 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 12 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner12]
  ring

private theorem recurrence0Coefficient13 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 13 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 13 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner13]
  ring

private theorem recurrence0Coefficient14 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 14 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 14 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner14]
  ring

private theorem recurrence0Coefficient15 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 15 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 15 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner15]
  ring

private theorem recurrence0Coefficient16 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 16 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 16 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner16]
  ring

private theorem recurrence0Coefficient17 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 17 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 17 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner17]
  ring

private theorem recurrence0Coefficient18 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 18 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 18 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner18]
  ring

private theorem recurrence0Coefficient19 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 19 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 19 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner19]
  ring

private theorem recurrence0Coefficient20 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 20 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 20 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner20]
  ring

private theorem recurrence0Coefficient21 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 21 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 21 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner21]
  ring

private theorem recurrence0Coefficient22 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 22 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 22 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner22]
  ring

private theorem recurrence0Coefficient23 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 23 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 23 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner23]
  ring

private theorem recurrence0Coefficient24 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 24 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 24 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner24]
  ring

private theorem recurrence0Coefficient25 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 25 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 25 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner25]
  ring

private theorem recurrence0Coefficient26 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 26 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 26 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner26]
  ring

private theorem recurrence0Coefficient27 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 27 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 27 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner27]
  ring

private theorem recurrence0Coefficient28 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 28 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 28 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner28]
  ring

private theorem recurrence0Coefficient29 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 29 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 29 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner29]
  ring

private theorem recurrence0Coefficient30 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 30 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 30 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner30]
  ring

private theorem recurrence0Coefficient31 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 31 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 31 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner31]
  ring

private theorem recurrence0Coefficient32 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 32 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 32 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner32]

private theorem recurrence0Coefficient33 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 33 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 33 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner33]


theorem recurrence0_checked : recurrence0 := by
  unfold recurrence0
  apply Polynomial.ext
  intro degree
  by_cases hdegree : degree ≤ 33
  · interval_cases degree
    · exact recurrence0Coefficient0
    · exact recurrence0Coefficient1
    · exact recurrence0Coefficient2
    · exact recurrence0Coefficient3
    · exact recurrence0Coefficient4
    · exact recurrence0Coefficient5
    · exact recurrence0Coefficient6
    · exact recurrence0Coefficient7
    · exact recurrence0Coefficient8
    · exact recurrence0Coefficient9
    · exact recurrence0Coefficient10
    · exact recurrence0Coefficient11
    · exact recurrence0Coefficient12
    · exact recurrence0Coefficient13
    · exact recurrence0Coefficient14
    · exact recurrence0Coefficient15
    · exact recurrence0Coefficient16
    · exact recurrence0Coefficient17
    · exact recurrence0Coefficient18
    · exact recurrence0Coefficient19
    · exact recurrence0Coefficient20
    · exact recurrence0Coefficient21
    · exact recurrence0Coefficient22
    · exact recurrence0Coefficient23
    · exact recurrence0Coefficient24
    · exact recurrence0Coefficient25
    · exact recurrence0Coefficient26
    · exact recurrence0Coefficient27
    · exact recurrence0Coefficient28
    · exact recurrence0Coefficient29
    · exact recurrence0Coefficient30
    · exact recurrence0Coefficient31
    · exact recurrence0Coefficient32
    · exact recurrence0Coefficient33
  · have hdegree' : 33 < degree := Nat.lt_of_not_ge hdegree
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt recurrence0_left_degree hdegree')]
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt recurrence0_right_degree hdegree')]

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate
