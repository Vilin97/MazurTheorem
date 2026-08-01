/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1B6Square
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1QuotientConstant
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1Left4
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1QuotientTerm4
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1ExceptionalTerm4
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1Residual4
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1ShiftTerm4

import Mathlib.Tactic.Ring

/-!
# Recurrence 1 certificate: NormalizedInner4

This file is a checked bounded-band arithmetic shard for the first
pseudo-division recurrence in the order-seven branch-zero resultant certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence1NormalizedInner4 :
    recurrence1Remainder26 ^ 2 *
      recurrence1Source4 =
      recurrence1Remainder23 * recurrence1Remainder26 +
        recurrence1Remainder24 *
          recurrence1QuotientConstant +
        recurrence1Exceptional *
          recurrence1Remainder34 := by
  calc
    recurrence1Remainder26 ^ 2 *
        recurrence1Source4 =
      recurrence1Left4 := by
        rw [pow_two, recurrence1B6Square_eq]
        rw [mul_comm, recurrence1Left4_eq]
    _ =
        recurrence1ShiftTerm4 +
        recurrence1QuotientTerm4 +
        recurrence1ExceptionalTerm4 := recurrence1Residual4
    _ = _ := by
      rw [← recurrence1ShiftTerm4_eq]
      rw [← recurrence1QuotientTerm4_eq]
      rw [← recurrence1ExceptionalTerm4_eq]
      ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
