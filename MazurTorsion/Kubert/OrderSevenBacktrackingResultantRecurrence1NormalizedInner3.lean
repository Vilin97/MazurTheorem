/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1B6Square
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1QuotientConstant
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1Left3
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1QuotientTerm3
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1ExceptionalTerm3
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1Residual3
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1ShiftTerm3

import Mathlib.Tactic.Ring

/-!
# Recurrence 1 certificate: NormalizedInner3

This file is a checked bounded-band arithmetic shard for the first
pseudo-division recurrence in the order-seven branch-zero resultant certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence1NormalizedInner3 :
    recurrence1Remainder26 ^ 2 *
      recurrence1Source3 =
      recurrence1Remainder22 * recurrence1Remainder26 +
        recurrence1Remainder23 *
          recurrence1QuotientConstant +
        recurrence1Exceptional *
          recurrence1Remainder33 := by
  calc
    recurrence1Remainder26 ^ 2 *
        recurrence1Source3 =
      recurrence1Left3 := by
        rw [pow_two, recurrence1B6Square_eq]
        rw [mul_comm, recurrence1Left3_eq]
    _ =
        recurrence1ShiftTerm3 +
        recurrence1QuotientTerm3 +
        recurrence1ExceptionalTerm3 := recurrence1Residual3
    _ = _ := by
      rw [← recurrence1ShiftTerm3_eq]
      rw [← recurrence1QuotientTerm3_eq]
      rw [← recurrence1ExceptionalTerm3_eq]
      ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
