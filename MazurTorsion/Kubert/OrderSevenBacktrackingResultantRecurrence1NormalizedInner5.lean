/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1B6Square
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1QuotientConstant
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1Left5
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1QuotientTerm5
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1ExceptionalTerm5
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1Residual5
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1ShiftTerm5

import Mathlib.Tactic.Ring

/-!
# Recurrence 1 certificate: NormalizedInner5

This file is a checked bounded-band arithmetic shard for the first
pseudo-division recurrence in the order-seven branch-zero resultant certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence1NormalizedInner5 :
    recurrence1Remainder26 ^ 2 *
      recurrence1Source5 =
      recurrence1Remainder24 * recurrence1Remainder26 +
        recurrence1Remainder25 *
          recurrence1QuotientConstant +
        recurrence1Exceptional *
          recurrence1Remainder35 := by
  calc
    recurrence1Remainder26 ^ 2 *
        recurrence1Source5 =
      recurrence1Left5 := by
        rw [pow_two, recurrence1B6Square_eq]
        rw [mul_comm, recurrence1Left5_eq]
    _ =
        recurrence1ShiftTerm5 +
        recurrence1QuotientTerm5 +
        recurrence1ExceptionalTerm5 := recurrence1Residual5
    _ = _ := by
      rw [← recurrence1ShiftTerm5_eq]
      rw [← recurrence1QuotientTerm5_eq]
      rw [← recurrence1ExceptionalTerm5_eq]
      ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
