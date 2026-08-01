/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1B6Square
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1QuotientConstant
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1Left1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1QuotientTerm1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1ExceptionalTerm1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1Residual1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1ShiftTerm1

import Mathlib.Tactic.Ring

/-!
# Recurrence 1 certificate: NormalizedInner1

This file is a checked bounded-band arithmetic shard for the first
pseudo-division recurrence in the order-seven branch-zero resultant certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence1NormalizedInner1 :
    recurrence1Remainder26 ^ 2 *
      recurrence1Source1 =
      recurrence1Remainder20 * recurrence1Remainder26 +
        recurrence1Remainder21 *
          recurrence1QuotientConstant +
        recurrence1Exceptional *
          recurrence1Remainder31 := by
  calc
    recurrence1Remainder26 ^ 2 *
        recurrence1Source1 =
      recurrence1Left1 := by
        rw [pow_two, recurrence1B6Square_eq]
        rw [mul_comm, recurrence1Left1_eq]
    _ =
        recurrence1ShiftTerm1 +
        recurrence1QuotientTerm1 +
        recurrence1ExceptionalTerm1 := recurrence1Residual1
    _ = _ := by
      rw [← recurrence1ShiftTerm1_eq]
      rw [← recurrence1QuotientTerm1_eq]
      rw [← recurrence1ExceptionalTerm1_eq]
      ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
