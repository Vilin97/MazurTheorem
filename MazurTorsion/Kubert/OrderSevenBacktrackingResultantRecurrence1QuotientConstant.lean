/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1B6A6
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1CommonData

import Mathlib.Tactic.Ring

/-!
# Recurrence 1 certificate: QuotientConstant

This file is a checked bounded-band arithmetic shard for the first
pseudo-division recurrence in the order-seven branch-zero resultant certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence1QuotientConstant_eq :
    recurrence1Remainder26 * recurrence1Source6 -
      recurrence1Remainder25 * recurrence1Source7 =
        recurrence1QuotientConstant := by
  rw [mul_comm recurrence1Remainder26, recurrence1B6A6_eq]
  unfold recurrence1B6A6 recurrence1Remainder25 recurrence1Source7 recurrence1QuotientConstant
  unfold recurrence1B6A6Block0 recurrence1B6A6Block1 recurrence1B6A6Block2 recurrence1B6A6Block3
  unfold recurrence1B6A6Block4 recurrence1B6A6Block5 recurrence1B6A6Block6 recurrence1B6A6Block7
  unfold recurrence1B6A6Block8 recurrence1B6A6Block9 recurrence1B6A6Block10
  unfold recurrence1Remainder25Block0 recurrence1Remainder25Block1 recurrence1Remainder25Block2
  unfold recurrence1Remainder25Block3 recurrence1Remainder25Block4 recurrence1Remainder25Block5
  unfold recurrence1Remainder25Block6 recurrence1Remainder25Block7 recurrence1Remainder25Block8
  unfold recurrence1Remainder25Block9 recurrence1Remainder25Block10 recurrence1Source7Block0
  unfold recurrence1QuotientConstantBlock0 recurrence1QuotientConstantBlock1
  unfold recurrence1QuotientConstantBlock2 recurrence1QuotientConstantBlock3
  unfold recurrence1QuotientConstantBlock4 recurrence1QuotientConstantBlock5
  unfold recurrence1QuotientConstantBlock6 recurrence1QuotientConstantBlock7
  unfold recurrence1QuotientConstantBlock8 recurrence1QuotientConstantBlock9
  unfold recurrence1QuotientConstantBlock10
  ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
