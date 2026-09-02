/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalarResidual0
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalarResidual1
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalarResidual2
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalarResidual3
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalarResidual4
import Mathlib.Tactic.LinearCombination

/-!
# Recurrence 2 lookup certificate: terminal recurrence theorem

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

private def sextic
    (a0 a1 a2 a3 a4 a5 a6 : Coefficient) : Bivariate :=
  C a6 * X ^ 6 + C a5 * X ^ 5 + C a4 * X ^ 4 +
    C a3 * X ^ 3 + C a2 * X ^ 2 + C a1 * X + C a0

private def quintic
    (b0 b1 b2 b3 b4 b5 : Coefficient) : Bivariate :=
  C b5 * X ^ 5 + C b4 * X ^ 4 + C b3 * X ^ 3 +
    C b2 * X ^ 2 + C b1 * X + C b0

private def quartic
    (c0 c1 c2 c3 c4 : Coefficient) : Bivariate :=
  C c4 * X ^ 4 + C c3 * X ^ 3 + C c2 * X ^ 2 +
    C c1 * X + C c0

private def quotientDerived
    (a5 a6 b4 b5 : Coefficient) : Bivariate :=
  C (b5 * a6) * X + C (b5 * a5 - b4 * a6)

private theorem sextic_quintic_pseudodivision
    (a0 a1 a2 a3 a4 a5 a6 : Coefficient)
    (b0 b1 b2 b3 b4 b5 : Coefficient)
    (c0 c1 c2 c3 c4 exceptional : Coefficient)
    (residual0 : b5 ^ 2 * a0 =
      b0 * (b5 * a5 - b4 * a6) +
        a6 ^ 2 * exceptional * c0)
    (residual1 : b5 ^ 2 * a1 =
      b0 * (b5 * a6) +
      b1 * (b5 * a5 - b4 * a6) +
        a6 ^ 2 * exceptional * c1)
    (residual2 : b5 ^ 2 * a2 =
      b1 * (b5 * a6) +
      b2 * (b5 * a5 - b4 * a6) +
        a6 ^ 2 * exceptional * c2)
    (residual3 : b5 ^ 2 * a3 =
      b2 * (b5 * a6) +
      b3 * (b5 * a5 - b4 * a6) +
        a6 ^ 2 * exceptional * c3)
    (residual4 : b5 ^ 2 * a4 =
      b3 * (b5 * a6) +
      b4 * (b5 * a5 - b4 * a6) +
        a6 ^ 2 * exceptional * c4)
    : C (b5 ^ 2) * sextic a0 a1 a2 a3 a4 a5 a6 =
      quintic b0 b1 b2 b3 b4 b5 *
          quotientDerived a5 a6 b4 b5 +
        C (a6 ^ 2 * exceptional) * quartic c0 c1 c2 c3 c4 := by
  unfold sextic quintic quartic quotientDerived
  have mapped0 := congrArg C residual0
  have mapped1 := congrArg C residual1
  have mapped2 := congrArg C residual2
  have mapped3 := congrArg C residual3
  have mapped4 := congrArg C residual4
  simp only [map_mul, map_pow, map_add, map_sub] at mapped0 mapped1 mapped2 mapped3 mapped4
  simp only [map_mul, map_pow, map_sub]
  linear_combination mapped0 + mapped1 * X + mapped2 * X ^ 2 +
    mapped3 * X ^ 3 + mapped4 * X ^ 4

private theorem remainder2_coefficient0 :
    remainder2.coeff 0 =
      remainder2Coefficient0 := by
  unfold remainder2 outerTerm
  simp

private theorem remainder2_coefficient1 :
    remainder2.coeff 1 =
      remainder2Coefficient1 := by
  unfold remainder2 outerTerm
  simp

private theorem remainder2_coefficient2 :
    remainder2.coeff 2 =
      remainder2Coefficient2 := by
  unfold remainder2 outerTerm
  simp

private theorem remainder2_coefficient3 :
    remainder2.coeff 3 =
      remainder2Coefficient3 := by
  unfold remainder2 outerTerm
  simp

private theorem remainder2_coefficient4 :
    remainder2.coeff 4 =
      remainder2Coefficient4 := by
  unfold remainder2 outerTerm
  simp

private theorem remainder2_coefficient5 :
    remainder2.coeff 5 =
      remainder2Coefficient5 := by
  unfold remainder2 outerTerm
  simp

private theorem remainder2_coefficient6 :
    remainder2.coeff 6 =
      remainder2Coefficient6 := by
  unfold remainder2 outerTerm
  simp

private theorem remainder3_coefficient0 :
    remainder3.coeff 0 =
      remainder3Coefficient0 := by
  unfold remainder3 outerTerm
  simp

private theorem remainder3_coefficient1 :
    remainder3.coeff 1 =
      remainder3Coefficient1 := by
  unfold remainder3 outerTerm
  simp

private theorem remainder3_coefficient2 :
    remainder3.coeff 2 =
      remainder3Coefficient2 := by
  unfold remainder3 outerTerm
  simp

private theorem remainder3_coefficient3 :
    remainder3.coeff 3 =
      remainder3Coefficient3 := by
  unfold remainder3 outerTerm
  simp

private theorem remainder3_coefficient4 :
    remainder3.coeff 4 =
      remainder3Coefficient4 := by
  unfold remainder3 outerTerm
  simp

private theorem remainder3_coefficient5 :
    remainder3.coeff 5 =
      remainder3Coefficient5 := by
  unfold remainder3 outerTerm
  simp

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

theorem recurrence2_checked : recurrence2 := by
  have division := sextic_quintic_pseudodivision
    remainder2Coefficient0 remainder2Coefficient1
    remainder2Coefficient2 remainder2Coefficient3
    remainder2Coefficient4 remainder2Coefficient5
    remainder2Coefficient6 remainder3Coefficient0
    remainder3Coefficient1 remainder3Coefficient2
    remainder3Coefficient3 remainder3Coefficient4
    remainder3Coefficient5 remainder4Coefficient0
    remainder4Coefficient1 remainder4Coefficient2
    remainder4Coefficient3 remainder4Coefficient4 exceptional2
    scalarResidual2Coefficient0 scalarResidual2Coefficient1
    scalarResidual2Coefficient2 scalarResidual2Coefficient3
    scalarResidual2Coefficient4
  unfold recurrence2
  rw [remainder3_coefficient5, remainder2_coefficient6]
  unfold quotient2 linearPseudoQuotient
  rw [remainder2_coefficient5, remainder2_coefficient6]
  rw [remainder3_coefficient4, remainder3_coefficient5]
  unfold outerTerm
  unfold sextic quintic quartic quotientDerived at division
  unfold remainder2 remainder3 remainder4 outerTerm
  linear_combination division

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
