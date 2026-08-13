/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6BlockData.Base
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6BlockData.Remainder7Coefficient1Square
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6BlockData.NormalizedResidualTerm1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6BlockData.Coefficient1Product
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6BlockData.Coefficient0Coefficient2Product
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6BlockData.NormalizedResidualInner
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6BlockData.NormalizedResidualTerm2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6BlockData.Coefficient2Square
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6BlockData.NormalizedResidualTerm3
import Mathlib.Tactic.Ring

/-!
# Recurrence 6 certificate: BlockData

This compatibility module re-exports the independently checked literal-data
shards for the sixth pseudo-division recurrence.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem normalizedExceptional6_eq :
    normalizedExceptional6 =
      (parameter - 1) * discriminantFactor ^ 6 * cmTwelve := by
  unfold normalizedExceptional6 normalizedExceptional6Block0 normalizedExceptional6Block1
  unfold normalizedExceptional6Block2 normalizedExceptional6Block3 discriminantFactor cmTwelve
  unfold parameter
  ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
