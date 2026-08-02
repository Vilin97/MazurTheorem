/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B1Square
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B1A1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B0A2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Inner
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6A2Square
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term3
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Residual

import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Recurrence 6 certificate: NormalizedScalar

This file is a checked arithmetic shard for the sixth pseudo-division
recurrence in the order-seven branch-zero resultant certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem normalizedScalarResidual6 :
    remainder7Coefficient1Normalized ^ 2 *
        remainder6Coefficient0Normalized =
      remainder7Coefficient0Normalized *
          (remainder7Coefficient1Normalized *
              remainder6Coefficient1Normalized -
            remainder7Coefficient0Normalized *
              remainder6Coefficient2Normalized) -
        remainder6Coefficient2Normalized ^ 2 *
          normalizedExceptional6 := by
  calc
    remainder7Coefficient1Normalized ^ 2 *
          remainder6Coefficient0Normalized =
        remainder7Coefficient1Square *
          remainder6Coefficient0Normalized := by
            rw [pow_two, remainder7Coefficient1Square_eq]
    _ = normalizedResidual6Term1 := by
          simpa only [mul_comm] using normalizedResidual6Term1_eq
    _ = normalizedResidual6Term2 -
          normalizedResidual6Term3 := by
            linear_combination normalizedResidual6_eq_zero
    _ = remainder7Coefficient0Normalized *
          normalizedResidual6Inner -
        remainder6Coefficient2Square *
          normalizedExceptional6 := by
            rw [← normalizedResidual6Term2_eq]
            rw [← normalizedResidual6Term3_eq]
            ring
    _ = remainder7Coefficient0Normalized *
          (remainder7Coefficient1TimesRemainder6Coefficient1 -
            remainder7Coefficient0TimesRemainder6Coefficient2) -
        remainder6Coefficient2Square *
          normalizedExceptional6 := by
            rw [← normalizedResidual6Inner_eq]
            ring
    _ = remainder7Coefficient0Normalized *
          (remainder7Coefficient1Normalized *
              remainder6Coefficient1Normalized -
            remainder7Coefficient0Normalized *
              remainder6Coefficient2Normalized) -
        remainder6Coefficient2Square *
          normalizedExceptional6 := by
            rw [remainder7Coefficient1TimesRemainder6Coefficient1_eq]
            rw [remainder7Coefficient0TimesRemainder6Coefficient2_eq]
    _ = remainder7Coefficient0Normalized *
          (remainder7Coefficient1Normalized *
              remainder6Coefficient1Normalized -
            remainder7Coefficient0Normalized *
              remainder6Coefficient2Normalized) -
        remainder6Coefficient2Normalized ^ 2 *
          normalizedExceptional6 := by
            rw [pow_two, remainder6Coefficient2Square_eq]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
