/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6ActualScalar

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# The sixth order-seven branch-zero resultant recurrence

This file turns the checked scalar resultant identity into the bivariate
pseudo-division recurrence required by the backtracking certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

private def quadratic
    (a0 a1 a2 : Coefficient) : Bivariate :=
  C a2 * X ^ 2 + C a1 * X + C a0

private def linear
    (b0 b1 : Coefficient) : Bivariate :=
  C b1 * X + C b0

private def quotientDerived
    (a1 a2 b0 b1 : Coefficient) : Bivariate :=
  C (b1 * a2) * X +
    C (b1 * a1 - b0 * a2)

private theorem quadratic_linear_pseudodivision
    (a0 a1 a2 b0 b1 exceptional : Coefficient)
    (residual :
      b1 ^ 2 * a0 =
        b0 * (b1 * a1 - b0 * a2) -
          a2 ^ 2 * exceptional) :
    C (b1 ^ 2) * quadratic a0 a1 a2 =
      linear b0 b1 * quotientDerived a1 a2 b0 b1 +
        C (a2 ^ 2 * exceptional) * (-1) := by
  unfold quadratic linear quotientDerived
  have mappedResidual := congrArg C residual
  simp only [map_mul, map_pow, map_sub] at mappedResidual
  simp only [map_mul, map_pow, map_sub]
  linear_combination mappedResidual

private theorem remainder6_coefficient0 :
    remainder6.coeff 0 = remainder6Coefficient0 := by
  unfold remainder6 outerTerm
  simp

private theorem remainder6_coefficient1 :
    remainder6.coeff 1 = remainder6Coefficient1 := by
  unfold remainder6 outerTerm
  simp

private theorem remainder6_coefficient2 :
    remainder6.coeff 2 = remainder6Coefficient2 := by
  unfold remainder6 outerTerm
  simp

private theorem remainder7_coefficient0 :
    remainder7.coeff 0 = remainder7Coefficient0 := by
  unfold remainder7 outerTerm
  simp

private theorem remainder7_coefficient1 :
    remainder7.coeff 1 = remainder7Coefficient1 := by
  unfold remainder7 outerTerm
  simp

private theorem remainder8_eq :
    remainder8 = (-1 : Bivariate) := by
  unfold remainder8 remainder8Coefficient0
  unfold remainder8Coefficient0Block0 remainder8Coefficient0Chunk0
  unfold outerTerm
  rw [coefficientTerm_eq_C_mul_X_pow]
  norm_num

theorem recurrence6_checked : recurrence6 := by
  have division := quadratic_linear_pseudodivision
    remainder6Coefficient0
    remainder6Coefficient1
    remainder6Coefficient2
    remainder7Coefficient0
    remainder7Coefficient1
    exceptional6
    scalarResidual6
  unfold recurrence6
  rw [remainder6_coefficient2, remainder7_coefficient1]
  rw [remainder8_eq]
  unfold quotient6 linearPseudoQuotient
  rw [remainder6_coefficient1, remainder6_coefficient2]
  rw [remainder7_coefficient0, remainder7_coefficient1]
  unfold outerTerm
  unfold quadratic linear quotientDerived at division
  unfold remainder6 remainder7 outerTerm
  linear_combination division

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
