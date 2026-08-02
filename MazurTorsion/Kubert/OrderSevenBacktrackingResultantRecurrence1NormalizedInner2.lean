/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1B6Square
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1QuotientConstant
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1Left2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1QuotientTerm2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1ExceptionalTerm2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1Residual2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1ShiftTerm2

import Mathlib.Tactic.Ring

/-!
# Recurrence 1 certificate: NormalizedInner2

This file is a checked bounded-band arithmetic shard for the first
pseudo-division recurrence in the order-seven branch-zero resultant certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence1NormalizedInner2 :
    recurrence1Remainder26 ^ 2 *
      recurrence1Source2 =
      recurrence1Remainder21 * recurrence1Remainder26 +
        recurrence1Remainder22 *
          recurrence1QuotientConstant +
        recurrence1Exceptional *
          recurrence1Remainder32 := by
  calc
    recurrence1Remainder26 ^ 2 *
        recurrence1Source2 =
      recurrence1Left2 := by
        rw [pow_two, recurrence1B6Square_eq]
        rw [mul_comm, recurrence1Left2_eq]
    _ =
        recurrence1ShiftTerm2 +
        recurrence1QuotientTerm2 +
        recurrence1ExceptionalTerm2 := recurrence1Residual2
    _ = _ := by
      rw [← recurrence1ShiftTerm2_eq]
      rw [← recurrence1QuotientTerm2_eq]
      rw [← recurrence1ExceptionalTerm2_eq]
      ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
