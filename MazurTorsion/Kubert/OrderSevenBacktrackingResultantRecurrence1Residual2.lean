/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1RowData2

import Mathlib.Tactic.Ring

/-!
# Recurrence 1 certificate: Residual2

This file is a checked bounded-band arithmetic shard for the first
pseudo-division recurrence in the order-seven branch-zero resultant certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

private theorem recurrence1Residual2Band0 :
    recurrence1ShiftTerm2Block0 +
    recurrence1QuotientTerm2Block0 +
    recurrence1ExceptionalTerm2Block0 =
      recurrence1Left2Block0 := by
  unfold recurrence1Left2Block0 recurrence1ShiftTerm2Block0 recurrence1QuotientTerm2Block0
  unfold recurrence1ExceptionalTerm2Block0
  ring

private theorem recurrence1Residual2Band1 :
    recurrence1ShiftTerm2Block1 +
    recurrence1QuotientTerm2Block1 +
    recurrence1ExceptionalTerm2Block1 =
      recurrence1Left2Block1 := by
  unfold recurrence1Left2Block1 recurrence1ShiftTerm2Block1 recurrence1QuotientTerm2Block1
  unfold recurrence1ExceptionalTerm2Block1
  ring

private theorem recurrence1Residual2Band2 :
    recurrence1ShiftTerm2Block2 +
    recurrence1QuotientTerm2Block2 +
    recurrence1ExceptionalTerm2Block2 =
      recurrence1Left2Block2 := by
  unfold recurrence1Left2Block2 recurrence1ShiftTerm2Block2 recurrence1QuotientTerm2Block2
  unfold recurrence1ExceptionalTerm2Block2
  ring

private theorem recurrence1Residual2Band3 :
    recurrence1ShiftTerm2Block3 +
    recurrence1QuotientTerm2Block3 +
    recurrence1ExceptionalTerm2Block3 =
      recurrence1Left2Block3 := by
  unfold recurrence1Left2Block3 recurrence1ShiftTerm2Block3 recurrence1QuotientTerm2Block3
  unfold recurrence1ExceptionalTerm2Block3
  ring

private theorem recurrence1Residual2Band4 :
    recurrence1ShiftTerm2Block4 +
    recurrence1QuotientTerm2Block4 +
    recurrence1ExceptionalTerm2Block4 =
      recurrence1Left2Block4 := by
  unfold recurrence1Left2Block4 recurrence1ShiftTerm2Block4 recurrence1QuotientTerm2Block4
  unfold recurrence1ExceptionalTerm2Block4
  ring

private theorem recurrence1Residual2Band5 :
    recurrence1ShiftTerm2Block5 +
    recurrence1QuotientTerm2Block5 +
    recurrence1ExceptionalTerm2Block5 =
      recurrence1Left2Block5 := by
  unfold recurrence1Left2Block5 recurrence1ShiftTerm2Block5 recurrence1QuotientTerm2Block5
  unfold recurrence1ExceptionalTerm2Block5
  ring

private theorem recurrence1Residual2Band6 :
    recurrence1ShiftTerm2Block6 +
    recurrence1QuotientTerm2Block6 +
    recurrence1ExceptionalTerm2Block6 =
      recurrence1Left2Block6 := by
  unfold recurrence1Left2Block6 recurrence1ShiftTerm2Block6 recurrence1QuotientTerm2Block6
  unfold recurrence1ExceptionalTerm2Block6
  ring

private theorem recurrence1Residual2Band7 :
    recurrence1ShiftTerm2Block7 +
    recurrence1QuotientTerm2Block7 +
    recurrence1ExceptionalTerm2Block7 =
      recurrence1Left2Block7 := by
  unfold recurrence1Left2Block7 recurrence1ShiftTerm2Block7 recurrence1QuotientTerm2Block7
  unfold recurrence1ExceptionalTerm2Block7
  ring

private theorem recurrence1Residual2Band8 :
    recurrence1ShiftTerm2Block8 +
    recurrence1QuotientTerm2Block8 +
    recurrence1ExceptionalTerm2Block8 =
      recurrence1Left2Block8 := by
  unfold recurrence1Left2Block8 recurrence1ShiftTerm2Block8 recurrence1QuotientTerm2Block8
  unfold recurrence1ExceptionalTerm2Block8
  ring

private theorem recurrence1Residual2Band9 :
    recurrence1ShiftTerm2Block9 +
    recurrence1QuotientTerm2Block9 +
    recurrence1ExceptionalTerm2Block9 =
      recurrence1Left2Block9 := by
  unfold recurrence1Left2Block9 recurrence1ShiftTerm2Block9 recurrence1QuotientTerm2Block9
  unfold recurrence1ExceptionalTerm2Block9
  ring

private theorem recurrence1Residual2Band10 :
    recurrence1ShiftTerm2Block10 +
    recurrence1QuotientTerm2Block10 +
    recurrence1ExceptionalTerm2Block10 =
      recurrence1Left2Block10 := by
  unfold recurrence1Left2Block10 recurrence1ShiftTerm2Block10 recurrence1QuotientTerm2Block10
  unfold recurrence1ExceptionalTerm2Block10
  ring

private theorem recurrence1Residual2Band11 :
    recurrence1ShiftTerm2Block11 +
    recurrence1QuotientTerm2Block11 +
    recurrence1ExceptionalTerm2Block11 =
      recurrence1Left2Block11 := by
  unfold recurrence1Left2Block11 recurrence1ShiftTerm2Block11 recurrence1QuotientTerm2Block11
  unfold recurrence1ExceptionalTerm2Block11
  ring

private theorem recurrence1Residual2Band12 :
    recurrence1ShiftTerm2Block12 +
    recurrence1QuotientTerm2Block12 +
    recurrence1ExceptionalTerm2Block12 =
      recurrence1Left2Block12 := by
  unfold recurrence1Left2Block12 recurrence1ShiftTerm2Block12 recurrence1QuotientTerm2Block12
  unfold recurrence1ExceptionalTerm2Block12
  ring

private theorem recurrence1Residual2Band13 :
    recurrence1ShiftTerm2Block13 +
    recurrence1QuotientTerm2Block13 +
    recurrence1ExceptionalTerm2Block13 =
      recurrence1Left2Block13 := by
  unfold recurrence1Left2Block13 recurrence1ShiftTerm2Block13 recurrence1QuotientTerm2Block13
  unfold recurrence1ExceptionalTerm2Block13
  ring

private theorem recurrence1Residual2Band14 :
    recurrence1ShiftTerm2Block14 +
    recurrence1QuotientTerm2Block14 +
    recurrence1ExceptionalTerm2Block14 =
      recurrence1Left2Block14 := by
  unfold recurrence1Left2Block14 recurrence1ShiftTerm2Block14 recurrence1QuotientTerm2Block14
  unfold recurrence1ExceptionalTerm2Block14
  ring

private theorem recurrence1Residual2Band15 :
    recurrence1ShiftTerm2Block15 +
    recurrence1QuotientTerm2Block15 +
    recurrence1ExceptionalTerm2Block15 =
      recurrence1Left2Block15 := by
  unfold recurrence1Left2Block15 recurrence1ShiftTerm2Block15 recurrence1QuotientTerm2Block15
  unfold recurrence1ExceptionalTerm2Block15
  ring

private theorem recurrence1Residual2Band16 :
    recurrence1ShiftTerm2Block16 +
    recurrence1QuotientTerm2Block16 +
    recurrence1ExceptionalTerm2Block16 =
      recurrence1Left2Block16 := by
  unfold recurrence1Left2Block16 recurrence1ShiftTerm2Block16 recurrence1QuotientTerm2Block16
  unfold recurrence1ExceptionalTerm2Block16
  ring

private theorem recurrence1Residual2Band17 :
    recurrence1ShiftTerm2Block17 +
    recurrence1QuotientTerm2Block17 +
    recurrence1ExceptionalTerm2Block17 =
      recurrence1Left2Block17 := by
  unfold recurrence1Left2Block17 recurrence1ShiftTerm2Block17 recurrence1QuotientTerm2Block17
  unfold recurrence1ExceptionalTerm2Block17
  ring

private theorem recurrence1Residual2Band18 :
    recurrence1ShiftTerm2Block18 +
    recurrence1QuotientTerm2Block18 +
    recurrence1ExceptionalTerm2Block18 =
      recurrence1Left2Block18 := by
  unfold recurrence1Left2Block18 recurrence1ShiftTerm2Block18 recurrence1QuotientTerm2Block18
  unfold recurrence1ExceptionalTerm2Block18
  ring

private theorem recurrence1Residual2Band19 :
    recurrence1ShiftTerm2Block19 +
    recurrence1QuotientTerm2Block19 +
    recurrence1ExceptionalTerm2Block19 =
      recurrence1Left2Block19 := by
  unfold recurrence1Left2Block19 recurrence1ShiftTerm2Block19 recurrence1QuotientTerm2Block19
  unfold recurrence1ExceptionalTerm2Block19
  ring

private theorem recurrence1Residual2Band20 :
    recurrence1ShiftTerm2Block20 +
    recurrence1QuotientTerm2Block20 +
    recurrence1ExceptionalTerm2Block20 =
      recurrence1Left2Block20 := by
  unfold recurrence1Left2Block20 recurrence1ShiftTerm2Block20 recurrence1QuotientTerm2Block20
  unfold recurrence1ExceptionalTerm2Block20
  ring

private theorem recurrence1Residual2Band21 :
    recurrence1ShiftTerm2Block21 +
    recurrence1QuotientTerm2Block21 +
    recurrence1ExceptionalTerm2Block21 =
      recurrence1Left2Block21 := by
  unfold recurrence1Left2Block21 recurrence1ShiftTerm2Block21 recurrence1QuotientTerm2Block21
  unfold recurrence1ExceptionalTerm2Block21
  ring

private theorem recurrence1Residual2Band22 :
    recurrence1ShiftTerm2Block22 +
    recurrence1QuotientTerm2Block22 +
    recurrence1ExceptionalTerm2Block22 =
      recurrence1Left2Block22 := by
  unfold recurrence1Left2Block22 recurrence1ShiftTerm2Block22 recurrence1QuotientTerm2Block22
  unfold recurrence1ExceptionalTerm2Block22
  ring

private theorem recurrence1Residual2Band23 :
    recurrence1ShiftTerm2Block23 +
    recurrence1QuotientTerm2Block23 +
    recurrence1ExceptionalTerm2Block23 =
      recurrence1Left2Block23 := by
  unfold recurrence1Left2Block23 recurrence1ShiftTerm2Block23 recurrence1QuotientTerm2Block23
  unfold recurrence1ExceptionalTerm2Block23
  ring

theorem recurrence1Residual2 :
    recurrence1Left2 =
      recurrence1ShiftTerm2 +
      recurrence1QuotientTerm2 +
      recurrence1ExceptionalTerm2 := by
  unfold recurrence1Left2 recurrence1ShiftTerm2 recurrence1QuotientTerm2 recurrence1ExceptionalTerm2
  rw [← recurrence1Residual2Band0]
  rw [← recurrence1Residual2Band1]
  rw [← recurrence1Residual2Band2]
  rw [← recurrence1Residual2Band3]
  rw [← recurrence1Residual2Band4]
  rw [← recurrence1Residual2Band5]
  rw [← recurrence1Residual2Band6]
  rw [← recurrence1Residual2Band7]
  rw [← recurrence1Residual2Band8]
  rw [← recurrence1Residual2Band9]
  rw [← recurrence1Residual2Band10]
  rw [← recurrence1Residual2Band11]
  rw [← recurrence1Residual2Band12]
  rw [← recurrence1Residual2Band13]
  rw [← recurrence1Residual2Band14]
  rw [← recurrence1Residual2Band15]
  rw [← recurrence1Residual2Band16]
  rw [← recurrence1Residual2Band17]
  rw [← recurrence1Residual2Band18]
  rw [← recurrence1Residual2Band19]
  rw [← recurrence1Residual2Band20]
  rw [← recurrence1Residual2Band21]
  rw [← recurrence1Residual2Band22]
  rw [← recurrence1Residual2Band23]
  ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
