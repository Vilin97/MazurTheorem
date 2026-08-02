/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1B6Square
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1QuotientConstant
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1Left0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1QuotientTerm0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1ExceptionalTerm0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1Residual0

import Mathlib.Tactic.Ring

/-!
# Recurrence 1 certificate: NormalizedInner0

This file is a checked bounded-band arithmetic shard for the first
pseudo-division recurrence in the order-seven branch-zero resultant certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence1NormalizedInner0 :
    recurrence1Remainder26 ^ 2 *
      recurrence1Source0 =
      recurrence1Remainder20 *
          recurrence1QuotientConstant +
        recurrence1Exceptional *
          recurrence1Remainder30 := by
  calc
    recurrence1Remainder26 ^ 2 *
        recurrence1Source0 =
      recurrence1Left0 := by
        rw [pow_two, recurrence1B6Square_eq]
        rw [mul_comm, recurrence1Left0_eq]
    _ =
        recurrence1QuotientTerm0 +
        recurrence1ExceptionalTerm0 := recurrence1Residual0
    _ = _ := by
      rw [← recurrence1QuotientTerm0_eq]
      rw [← recurrence1ExceptionalTerm0_eq]
      ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
