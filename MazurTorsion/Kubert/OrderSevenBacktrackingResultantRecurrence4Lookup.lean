/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar
import Mathlib.Tactic.LinearCombination

/-!
# Recurrence 4 lookup certificate: terminal recurrence theorem

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

private def quartic
    (a0 a1 a2 a3 a4 : Coefficient) : Bivariate :=
  C a4 * X ^ 4 + C a3 * X ^ 3 + C a2 * X ^ 2 +
    C a1 * X + C a0

private def cubic
    (b0 b1 b2 b3 : Coefficient) : Bivariate :=
  C b3 * X ^ 3 + C b2 * X ^ 2 + C b1 * X + C b0

private def quadratic
    (c0 c1 c2 : Coefficient) : Bivariate :=
  C c2 * X ^ 2 + C c1 * X + C c0

private def quotientDerived
    (a3 a4 b2 b3 : Coefficient) : Bivariate :=
  C (b3 * a4) * X + C (b3 * a3 - b2 * a4)

private theorem quartic_cubic_pseudodivision
    (a0 a1 a2 a3 a4 b0 b1 b2 b3 : Coefficient)
    (c0 c1 c2 exceptional : Coefficient)
    (residual0 : b3 ^ 2 * a0 =
      b0 * (b3 * a3 - b2 * a4) + a4 ^ 2 * exceptional * c0)
    (residual1 : b3 ^ 2 * a1 =
      b0 * b3 * a4 + b1 * (b3 * a3 - b2 * a4) +
        a4 ^ 2 * exceptional * c1)
    (residual2 : b3 ^ 2 * a2 =
      b1 * b3 * a4 + b2 * (b3 * a3 - b2 * a4) +
        a4 ^ 2 * exceptional * c2) :
    C (b3 ^ 2) * quartic a0 a1 a2 a3 a4 =
      cubic b0 b1 b2 b3 * quotientDerived a3 a4 b2 b3 +
        C (a4 ^ 2 * exceptional) * quadratic c0 c1 c2 := by
  unfold quartic cubic quadratic quotientDerived
  have mapped0 := congrArg C residual0
  have mapped1 := congrArg C residual1
  have mapped2 := congrArg C residual2
  simp only [map_mul, map_pow, map_add, map_sub] at mapped0 mapped1 mapped2
  simp only [map_mul, map_pow, map_sub]
  linear_combination mapped0 + mapped1 * X + mapped2 * X ^ 2

private theorem remainder4_coefficient0 :
    remainder4.coeff 0 =
      remainder4Coefficient0 := by
  unfold remainder4 outerTerm
  simp

private theorem remainder4_coefficient1 :
    remainder4.coeff 1 =
      remainder4Coefficient1 := by
  unfold remainder4 outerTerm
  simp

private theorem remainder4_coefficient2 :
    remainder4.coeff 2 =
      remainder4Coefficient2 := by
  unfold remainder4 outerTerm
  simp

private theorem remainder4_coefficient3 :
    remainder4.coeff 3 =
      remainder4Coefficient3 := by
  unfold remainder4 outerTerm
  simp

private theorem remainder4_coefficient4 :
    remainder4.coeff 4 =
      remainder4Coefficient4 := by
  unfold remainder4 outerTerm
  simp

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

theorem recurrence4_checked : recurrence4 := by
  have division := quartic_cubic_pseudodivision
    remainder4Coefficient0 remainder4Coefficient1
    remainder4Coefficient2 remainder4Coefficient3
    remainder4Coefficient4
    remainder5Coefficient0 remainder5Coefficient1
    remainder5Coefficient2 remainder5Coefficient3
    remainder6Coefficient0 remainder6Coefficient1
    remainder6Coefficient2 exceptional4
    scalarResidual4Coefficient0 scalarResidual4Coefficient1
    scalarResidual4Coefficient2
  unfold recurrence4
  rw [remainder4_coefficient4, remainder5_coefficient3]
  unfold quotient4 linearPseudoQuotient
  rw [remainder4_coefficient3, remainder4_coefficient4]
  rw [remainder5_coefficient2, remainder5_coefficient3]
  unfold outerTerm
  unfold quartic cubic quadratic quotientDerived at division
  unfold remainder4 remainder5 remainder6 outerTerm
  linear_combination division

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
