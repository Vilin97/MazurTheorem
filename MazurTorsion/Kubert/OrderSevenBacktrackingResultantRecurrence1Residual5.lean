/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1RowData5

import Mathlib.Tactic.Ring

/-!
# Recurrence 1 certificate: Residual5

This file is a checked bounded-band arithmetic shard for the first
pseudo-division recurrence in the order-seven branch-zero resultant certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

private theorem recurrence1Residual5Band0 :
    recurrence1ShiftTerm5Block0 +
    recurrence1QuotientTerm5Block0 +
    recurrence1ExceptionalTerm5Block0 =
      recurrence1Left5Block0 := by
  unfold recurrence1Left5Block0 recurrence1ShiftTerm5Block0 recurrence1QuotientTerm5Block0
  unfold recurrence1ExceptionalTerm5Block0
  ring

private theorem recurrence1Residual5Band1 :
    recurrence1ShiftTerm5Block1 +
    recurrence1QuotientTerm5Block1 +
    recurrence1ExceptionalTerm5Block1 =
      recurrence1Left5Block1 := by
  unfold recurrence1Left5Block1 recurrence1ShiftTerm5Block1 recurrence1QuotientTerm5Block1
  unfold recurrence1ExceptionalTerm5Block1
  ring

private theorem recurrence1Residual5Band2 :
    recurrence1ShiftTerm5Block2 +
    recurrence1QuotientTerm5Block2 +
    recurrence1ExceptionalTerm5Block2 =
      recurrence1Left5Block2 := by
  unfold recurrence1Left5Block2 recurrence1ShiftTerm5Block2 recurrence1QuotientTerm5Block2
  unfold recurrence1ExceptionalTerm5Block2
  ring

private theorem recurrence1Residual5Band3 :
    recurrence1ShiftTerm5Block3 +
    recurrence1QuotientTerm5Block3 +
    recurrence1ExceptionalTerm5Block3 =
      recurrence1Left5Block3 := by
  unfold recurrence1Left5Block3 recurrence1ShiftTerm5Block3 recurrence1QuotientTerm5Block3
  unfold recurrence1ExceptionalTerm5Block3
  ring

private theorem recurrence1Residual5Band4 :
    recurrence1ShiftTerm5Block4 +
    recurrence1QuotientTerm5Block4 +
    recurrence1ExceptionalTerm5Block4 =
      recurrence1Left5Block4 := by
  unfold recurrence1Left5Block4 recurrence1ShiftTerm5Block4 recurrence1QuotientTerm5Block4
  unfold recurrence1ExceptionalTerm5Block4
  ring

private theorem recurrence1Residual5Band5 :
    recurrence1ShiftTerm5Block5 +
    recurrence1QuotientTerm5Block5 +
    recurrence1ExceptionalTerm5Block5 =
      recurrence1Left5Block5 := by
  unfold recurrence1Left5Block5 recurrence1ShiftTerm5Block5 recurrence1QuotientTerm5Block5
  unfold recurrence1ExceptionalTerm5Block5
  ring

private theorem recurrence1Residual5Band6 :
    recurrence1ShiftTerm5Block6 +
    recurrence1QuotientTerm5Block6 +
    recurrence1ExceptionalTerm5Block6 =
      recurrence1Left5Block6 := by
  unfold recurrence1Left5Block6 recurrence1ShiftTerm5Block6 recurrence1QuotientTerm5Block6
  unfold recurrence1ExceptionalTerm5Block6
  ring

private theorem recurrence1Residual5Band7 :
    recurrence1ShiftTerm5Block7 +
    recurrence1QuotientTerm5Block7 +
    recurrence1ExceptionalTerm5Block7 =
      recurrence1Left5Block7 := by
  unfold recurrence1Left5Block7 recurrence1ShiftTerm5Block7 recurrence1QuotientTerm5Block7
  unfold recurrence1ExceptionalTerm5Block7
  ring

private theorem recurrence1Residual5Band8 :
    recurrence1ShiftTerm5Block8 +
    recurrence1QuotientTerm5Block8 +
    recurrence1ExceptionalTerm5Block8 =
      recurrence1Left5Block8 := by
  unfold recurrence1Left5Block8 recurrence1ShiftTerm5Block8 recurrence1QuotientTerm5Block8
  unfold recurrence1ExceptionalTerm5Block8
  ring

private theorem recurrence1Residual5Band9 :
    recurrence1ShiftTerm5Block9 +
    recurrence1QuotientTerm5Block9 +
    recurrence1ExceptionalTerm5Block9 =
      recurrence1Left5Block9 := by
  unfold recurrence1Left5Block9 recurrence1ShiftTerm5Block9 recurrence1QuotientTerm5Block9
  unfold recurrence1ExceptionalTerm5Block9
  ring

private theorem recurrence1Residual5Band10 :
    recurrence1ShiftTerm5Block10 +
    recurrence1QuotientTerm5Block10 +
    recurrence1ExceptionalTerm5Block10 =
      recurrence1Left5Block10 := by
  unfold recurrence1Left5Block10 recurrence1ShiftTerm5Block10 recurrence1QuotientTerm5Block10
  unfold recurrence1ExceptionalTerm5Block10
  ring

private theorem recurrence1Residual5Band11 :
    recurrence1ShiftTerm5Block11 +
    recurrence1QuotientTerm5Block11 +
    recurrence1ExceptionalTerm5Block11 =
      recurrence1Left5Block11 := by
  unfold recurrence1Left5Block11 recurrence1ShiftTerm5Block11 recurrence1QuotientTerm5Block11
  unfold recurrence1ExceptionalTerm5Block11
  ring

private theorem recurrence1Residual5Band12 :
    recurrence1ShiftTerm5Block12 +
    recurrence1QuotientTerm5Block12 +
    recurrence1ExceptionalTerm5Block12 =
      recurrence1Left5Block12 := by
  unfold recurrence1Left5Block12 recurrence1ShiftTerm5Block12 recurrence1QuotientTerm5Block12
  unfold recurrence1ExceptionalTerm5Block12
  ring

private theorem recurrence1Residual5Band13 :
    recurrence1ShiftTerm5Block13 +
    recurrence1QuotientTerm5Block13 +
    recurrence1ExceptionalTerm5Block13 =
      recurrence1Left5Block13 := by
  unfold recurrence1Left5Block13 recurrence1ShiftTerm5Block13 recurrence1QuotientTerm5Block13
  unfold recurrence1ExceptionalTerm5Block13
  ring

private theorem recurrence1Residual5Band14 :
    recurrence1ShiftTerm5Block14 +
    recurrence1QuotientTerm5Block14 +
    recurrence1ExceptionalTerm5Block14 =
      recurrence1Left5Block14 := by
  unfold recurrence1Left5Block14 recurrence1ShiftTerm5Block14 recurrence1QuotientTerm5Block14
  unfold recurrence1ExceptionalTerm5Block14
  ring

private theorem recurrence1Residual5Band15 :
    recurrence1ShiftTerm5Block15 +
    recurrence1QuotientTerm5Block15 +
    recurrence1ExceptionalTerm5Block15 =
      recurrence1Left5Block15 := by
  unfold recurrence1Left5Block15 recurrence1ShiftTerm5Block15 recurrence1QuotientTerm5Block15
  unfold recurrence1ExceptionalTerm5Block15
  ring

private theorem recurrence1Residual5Band16 :
    recurrence1ShiftTerm5Block16 +
    recurrence1QuotientTerm5Block16 +
    recurrence1ExceptionalTerm5Block16 =
      recurrence1Left5Block16 := by
  unfold recurrence1Left5Block16 recurrence1ShiftTerm5Block16 recurrence1QuotientTerm5Block16
  unfold recurrence1ExceptionalTerm5Block16
  ring

private theorem recurrence1Residual5Band17 :
    recurrence1ShiftTerm5Block17 +
    recurrence1QuotientTerm5Block17 +
    recurrence1ExceptionalTerm5Block17 =
      recurrence1Left5Block17 := by
  unfold recurrence1Left5Block17 recurrence1ShiftTerm5Block17 recurrence1QuotientTerm5Block17
  unfold recurrence1ExceptionalTerm5Block17
  ring

private theorem recurrence1Residual5Band18 :
    recurrence1ShiftTerm5Block18 +
    recurrence1QuotientTerm5Block18 +
    recurrence1ExceptionalTerm5Block18 =
      recurrence1Left5Block18 := by
  unfold recurrence1Left5Block18 recurrence1ShiftTerm5Block18 recurrence1QuotientTerm5Block18
  unfold recurrence1ExceptionalTerm5Block18
  ring

private theorem recurrence1Residual5Band19 :
    recurrence1ShiftTerm5Block19 +
    recurrence1QuotientTerm5Block19 +
    recurrence1ExceptionalTerm5Block19 =
      recurrence1Left5Block19 := by
  unfold recurrence1Left5Block19 recurrence1ShiftTerm5Block19 recurrence1QuotientTerm5Block19
  unfold recurrence1ExceptionalTerm5Block19
  ring

private theorem recurrence1Residual5Band20 :
    recurrence1ShiftTerm5Block20 +
    recurrence1QuotientTerm5Block20 +
    recurrence1ExceptionalTerm5Block20 =
      recurrence1Left5Block20 := by
  unfold recurrence1Left5Block20 recurrence1ShiftTerm5Block20 recurrence1QuotientTerm5Block20
  unfold recurrence1ExceptionalTerm5Block20
  ring

private theorem recurrence1Residual5Band21 :
    recurrence1ShiftTerm5Block21 +
    recurrence1QuotientTerm5Block21 +
    recurrence1ExceptionalTerm5Block21 =
      recurrence1Left5Block21 := by
  unfold recurrence1Left5Block21 recurrence1ShiftTerm5Block21 recurrence1QuotientTerm5Block21
  unfold recurrence1ExceptionalTerm5Block21
  ring

theorem recurrence1Residual5 :
    recurrence1Left5 =
      recurrence1ShiftTerm5 +
      recurrence1QuotientTerm5 +
      recurrence1ExceptionalTerm5 := by
  unfold recurrence1Left5 recurrence1ShiftTerm5 recurrence1QuotientTerm5 recurrence1ExceptionalTerm5
  rw [← recurrence1Residual5Band0]
  rw [← recurrence1Residual5Band1]
  rw [← recurrence1Residual5Band2]
  rw [← recurrence1Residual5Band3]
  rw [← recurrence1Residual5Band4]
  rw [← recurrence1Residual5Band5]
  rw [← recurrence1Residual5Band6]
  rw [← recurrence1Residual5Band7]
  rw [← recurrence1Residual5Band8]
  rw [← recurrence1Residual5Band9]
  rw [← recurrence1Residual5Band10]
  rw [← recurrence1Residual5Band11]
  rw [← recurrence1Residual5Band12]
  rw [← recurrence1Residual5Band13]
  rw [← recurrence1Residual5Band14]
  rw [← recurrence1Residual5Band15]
  rw [← recurrence1Residual5Band16]
  rw [← recurrence1Residual5Band17]
  rw [← recurrence1Residual5Band18]
  rw [← recurrence1Residual5Band19]
  rw [← recurrence1Residual5Band20]
  rw [← recurrence1Residual5Band21]
  ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
