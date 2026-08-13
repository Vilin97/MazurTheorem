/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupScalar
import Mathlib.Tactic.LinearCombination

/-!
# Recurrence 5 lookup certificate: terminal recurrence theorem

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

private def cubic
    (a0 a1 a2 a3 : Coefficient) : Bivariate :=
  C a3 * X ^ 3 + C a2 * X ^ 2 + C a1 * X + C a0

private def quadratic
    (b0 b1 b2 : Coefficient) : Bivariate :=
  C b2 * X ^ 2 + C b1 * X + C b0

private def linear
    (c0 c1 : Coefficient) : Bivariate :=
  C c1 * X + C c0

private def quotientDerived
    (a2 a3 b1 b2 : Coefficient) : Bivariate :=
  C (b2 * a3) * X + C (b2 * a2 - b1 * a3)

private theorem cubic_quadratic_pseudodivision
    (a0 a1 a2 a3 b0 b1 b2 c0 c1 exceptional : Coefficient)
    (residual0 : b2 ^ 2 * a0 =
      b0 * (b2 * a2 - b1 * a3) + a3 ^ 2 * exceptional * c0)
    (residual1 : b2 ^ 2 * a1 =
      b0 * b2 * a3 + b1 * (b2 * a2 - b1 * a3) +
        a3 ^ 2 * exceptional * c1) :
    C (b2 ^ 2) * cubic a0 a1 a2 a3 =
      quadratic b0 b1 b2 * quotientDerived a2 a3 b1 b2 +
        C (a3 ^ 2 * exceptional) * linear c0 c1 := by
  unfold cubic quadratic linear quotientDerived
  have mapped0 := congrArg C residual0
  have mapped1 := congrArg C residual1
  simp only [map_mul, map_pow, map_add, map_sub] at mapped0 mapped1
  simp only [map_mul, map_pow, map_sub]
  linear_combination mapped0 + mapped1 * X

private theorem remainder5_coefficient0 :
    remainder5.coeff 0 =
      remainder5Coefficient0 := by
  unfold remainder5 outerTerm
  simp

private theorem remainder5_coefficient1 :
    remainder5.coeff 1 =
      remainder5Coefficient1 := by
  unfold remainder5 outerTerm
  simp

private theorem remainder5_coefficient2 :
    remainder5.coeff 2 =
      remainder5Coefficient2 := by
  unfold remainder5 outerTerm
  simp

private theorem remainder5_coefficient3 :
    remainder5.coeff 3 =
      remainder5Coefficient3 := by
  unfold remainder5 outerTerm
  simp

private theorem remainder6_coefficient0 :
    remainder6.coeff 0 =
      remainder6Coefficient0 := by
  unfold remainder6 outerTerm
  simp

private theorem remainder6_coefficient1 :
    remainder6.coeff 1 =
      remainder6Coefficient1 := by
  unfold remainder6 outerTerm
  simp

private theorem remainder6_coefficient2 :
    remainder6.coeff 2 =
      remainder6Coefficient2 := by
  unfold remainder6 outerTerm
  simp

private theorem remainder7_coefficient0 :
    remainder7.coeff 0 =
      remainder7Coefficient0 := by
  unfold remainder7 outerTerm
  simp

private theorem remainder7_coefficient1 :
    remainder7.coeff 1 =
      remainder7Coefficient1 := by
  unfold remainder7 outerTerm
  simp

theorem recurrence5_checked : recurrence5 := by
  have division := cubic_quadratic_pseudodivision
    remainder5Coefficient0 remainder5Coefficient1
    remainder5Coefficient2 remainder5Coefficient3
    remainder6Coefficient0 remainder6Coefficient1
    remainder6Coefficient2 remainder7Coefficient0
    remainder7Coefficient1 exceptional5
    scalarResidual5Coefficient0 scalarResidual5Coefficient1
  unfold recurrence5
  rw [remainder5_coefficient3, remainder6_coefficient2]
  unfold quotient5 linearPseudoQuotient
  rw [remainder5_coefficient2, remainder5_coefficient3]
  rw [remainder6_coefficient1, remainder6_coefficient2]
  unfold outerTerm
  unfold cubic quadratic linear quotientDerived at division
  unfold remainder5 remainder6 remainder7 outerTerm
  linear_combination division

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
