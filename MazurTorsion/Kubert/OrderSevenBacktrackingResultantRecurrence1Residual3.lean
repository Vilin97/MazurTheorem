/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1RowData3

import Mathlib.Tactic.Ring

/-!
# Recurrence 1 certificate: Residual3

This file is a checked bounded-band arithmetic shard for the first
pseudo-division recurrence in the order-seven branch-zero resultant certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

private theorem recurrence1Residual3Band0 :
    recurrence1ShiftTerm3Block0 +
    recurrence1QuotientTerm3Block0 +
    recurrence1ExceptionalTerm3Block0 =
      recurrence1Left3Block0 := by
  unfold recurrence1Left3Block0 recurrence1ShiftTerm3Block0 recurrence1QuotientTerm3Block0
  unfold recurrence1ExceptionalTerm3Block0
  ring

private theorem recurrence1Residual3Band1 :
    recurrence1ShiftTerm3Block1 +
    recurrence1QuotientTerm3Block1 +
    recurrence1ExceptionalTerm3Block1 =
      recurrence1Left3Block1 := by
  unfold recurrence1Left3Block1 recurrence1ShiftTerm3Block1 recurrence1QuotientTerm3Block1
  unfold recurrence1ExceptionalTerm3Block1
  ring

private theorem recurrence1Residual3Band2 :
    recurrence1ShiftTerm3Block2 +
    recurrence1QuotientTerm3Block2 +
    recurrence1ExceptionalTerm3Block2 =
      recurrence1Left3Block2 := by
  unfold recurrence1Left3Block2 recurrence1ShiftTerm3Block2 recurrence1QuotientTerm3Block2
  unfold recurrence1ExceptionalTerm3Block2
  ring

private theorem recurrence1Residual3Band3 :
    recurrence1ShiftTerm3Block3 +
    recurrence1QuotientTerm3Block3 +
    recurrence1ExceptionalTerm3Block3 =
      recurrence1Left3Block3 := by
  unfold recurrence1Left3Block3 recurrence1ShiftTerm3Block3 recurrence1QuotientTerm3Block3
  unfold recurrence1ExceptionalTerm3Block3
  ring

private theorem recurrence1Residual3Band4 :
    recurrence1ShiftTerm3Block4 +
    recurrence1QuotientTerm3Block4 +
    recurrence1ExceptionalTerm3Block4 =
      recurrence1Left3Block4 := by
  unfold recurrence1Left3Block4 recurrence1ShiftTerm3Block4 recurrence1QuotientTerm3Block4
  unfold recurrence1ExceptionalTerm3Block4
  ring

private theorem recurrence1Residual3Band5 :
    recurrence1ShiftTerm3Block5 +
    recurrence1QuotientTerm3Block5 +
    recurrence1ExceptionalTerm3Block5 =
      recurrence1Left3Block5 := by
  unfold recurrence1Left3Block5 recurrence1ShiftTerm3Block5 recurrence1QuotientTerm3Block5
  unfold recurrence1ExceptionalTerm3Block5
  ring

private theorem recurrence1Residual3Band6 :
    recurrence1ShiftTerm3Block6 +
    recurrence1QuotientTerm3Block6 +
    recurrence1ExceptionalTerm3Block6 =
      recurrence1Left3Block6 := by
  unfold recurrence1Left3Block6 recurrence1ShiftTerm3Block6 recurrence1QuotientTerm3Block6
  unfold recurrence1ExceptionalTerm3Block6
  ring

private theorem recurrence1Residual3Band7 :
    recurrence1ShiftTerm3Block7 +
    recurrence1QuotientTerm3Block7 +
    recurrence1ExceptionalTerm3Block7 =
      recurrence1Left3Block7 := by
  unfold recurrence1Left3Block7 recurrence1ShiftTerm3Block7 recurrence1QuotientTerm3Block7
  unfold recurrence1ExceptionalTerm3Block7
  ring

private theorem recurrence1Residual3Band8 :
    recurrence1ShiftTerm3Block8 +
    recurrence1QuotientTerm3Block8 +
    recurrence1ExceptionalTerm3Block8 =
      recurrence1Left3Block8 := by
  unfold recurrence1Left3Block8 recurrence1ShiftTerm3Block8 recurrence1QuotientTerm3Block8
  unfold recurrence1ExceptionalTerm3Block8
  ring

private theorem recurrence1Residual3Band9 :
    recurrence1ShiftTerm3Block9 +
    recurrence1QuotientTerm3Block9 +
    recurrence1ExceptionalTerm3Block9 =
      recurrence1Left3Block9 := by
  unfold recurrence1Left3Block9 recurrence1ShiftTerm3Block9 recurrence1QuotientTerm3Block9
  unfold recurrence1ExceptionalTerm3Block9
  ring

private theorem recurrence1Residual3Band10 :
    recurrence1ShiftTerm3Block10 +
    recurrence1QuotientTerm3Block10 +
    recurrence1ExceptionalTerm3Block10 =
      recurrence1Left3Block10 := by
  unfold recurrence1Left3Block10 recurrence1ShiftTerm3Block10 recurrence1QuotientTerm3Block10
  unfold recurrence1ExceptionalTerm3Block10
  ring

private theorem recurrence1Residual3Band11 :
    recurrence1ShiftTerm3Block11 +
    recurrence1QuotientTerm3Block11 +
    recurrence1ExceptionalTerm3Block11 =
      recurrence1Left3Block11 := by
  unfold recurrence1Left3Block11 recurrence1ShiftTerm3Block11 recurrence1QuotientTerm3Block11
  unfold recurrence1ExceptionalTerm3Block11
  ring

private theorem recurrence1Residual3Band12 :
    recurrence1ShiftTerm3Block12 +
    recurrence1QuotientTerm3Block12 +
    recurrence1ExceptionalTerm3Block12 =
      recurrence1Left3Block12 := by
  unfold recurrence1Left3Block12 recurrence1ShiftTerm3Block12 recurrence1QuotientTerm3Block12
  unfold recurrence1ExceptionalTerm3Block12
  ring

private theorem recurrence1Residual3Band13 :
    recurrence1ShiftTerm3Block13 +
    recurrence1QuotientTerm3Block13 +
    recurrence1ExceptionalTerm3Block13 =
      recurrence1Left3Block13 := by
  unfold recurrence1Left3Block13 recurrence1ShiftTerm3Block13 recurrence1QuotientTerm3Block13
  unfold recurrence1ExceptionalTerm3Block13
  ring

private theorem recurrence1Residual3Band14 :
    recurrence1ShiftTerm3Block14 +
    recurrence1QuotientTerm3Block14 +
    recurrence1ExceptionalTerm3Block14 =
      recurrence1Left3Block14 := by
  unfold recurrence1Left3Block14 recurrence1ShiftTerm3Block14 recurrence1QuotientTerm3Block14
  unfold recurrence1ExceptionalTerm3Block14
  ring

private theorem recurrence1Residual3Band15 :
    recurrence1ShiftTerm3Block15 +
    recurrence1QuotientTerm3Block15 +
    recurrence1ExceptionalTerm3Block15 =
      recurrence1Left3Block15 := by
  unfold recurrence1Left3Block15 recurrence1ShiftTerm3Block15 recurrence1QuotientTerm3Block15
  unfold recurrence1ExceptionalTerm3Block15
  ring

private theorem recurrence1Residual3Band16 :
    recurrence1ShiftTerm3Block16 +
    recurrence1QuotientTerm3Block16 +
    recurrence1ExceptionalTerm3Block16 =
      recurrence1Left3Block16 := by
  unfold recurrence1Left3Block16 recurrence1ShiftTerm3Block16 recurrence1QuotientTerm3Block16
  unfold recurrence1ExceptionalTerm3Block16
  ring

private theorem recurrence1Residual3Band17 :
    recurrence1ShiftTerm3Block17 +
    recurrence1QuotientTerm3Block17 +
    recurrence1ExceptionalTerm3Block17 =
      recurrence1Left3Block17 := by
  unfold recurrence1Left3Block17 recurrence1ShiftTerm3Block17 recurrence1QuotientTerm3Block17
  unfold recurrence1ExceptionalTerm3Block17
  ring

private theorem recurrence1Residual3Band18 :
    recurrence1ShiftTerm3Block18 +
    recurrence1QuotientTerm3Block18 +
    recurrence1ExceptionalTerm3Block18 =
      recurrence1Left3Block18 := by
  unfold recurrence1Left3Block18 recurrence1ShiftTerm3Block18 recurrence1QuotientTerm3Block18
  unfold recurrence1ExceptionalTerm3Block18
  ring

private theorem recurrence1Residual3Band19 :
    recurrence1ShiftTerm3Block19 +
    recurrence1QuotientTerm3Block19 +
    recurrence1ExceptionalTerm3Block19 =
      recurrence1Left3Block19 := by
  unfold recurrence1Left3Block19 recurrence1ShiftTerm3Block19 recurrence1QuotientTerm3Block19
  unfold recurrence1ExceptionalTerm3Block19
  ring

private theorem recurrence1Residual3Band20 :
    recurrence1ShiftTerm3Block20 +
    recurrence1QuotientTerm3Block20 +
    recurrence1ExceptionalTerm3Block20 =
      recurrence1Left3Block20 := by
  unfold recurrence1Left3Block20 recurrence1ShiftTerm3Block20 recurrence1QuotientTerm3Block20
  unfold recurrence1ExceptionalTerm3Block20
  ring

private theorem recurrence1Residual3Band21 :
    recurrence1ShiftTerm3Block21 +
    recurrence1QuotientTerm3Block21 +
    recurrence1ExceptionalTerm3Block21 =
      recurrence1Left3Block21 := by
  unfold recurrence1Left3Block21 recurrence1ShiftTerm3Block21 recurrence1QuotientTerm3Block21
  unfold recurrence1ExceptionalTerm3Block21
  ring

private theorem recurrence1Residual3Band22 :
    recurrence1ShiftTerm3Block22 +
    recurrence1QuotientTerm3Block22 +
    recurrence1ExceptionalTerm3Block22 =
      recurrence1Left3Block22 := by
  unfold recurrence1Left3Block22 recurrence1ShiftTerm3Block22 recurrence1QuotientTerm3Block22
  unfold recurrence1ExceptionalTerm3Block22
  ring

theorem recurrence1Residual3 :
    recurrence1Left3 =
      recurrence1ShiftTerm3 +
      recurrence1QuotientTerm3 +
      recurrence1ExceptionalTerm3 := by
  unfold recurrence1Left3 recurrence1ShiftTerm3 recurrence1QuotientTerm3 recurrence1ExceptionalTerm3
  rw [← recurrence1Residual3Band0]
  rw [← recurrence1Residual3Band1]
  rw [← recurrence1Residual3Band2]
  rw [← recurrence1Residual3Band3]
  rw [← recurrence1Residual3Band4]
  rw [← recurrence1Residual3Band5]
  rw [← recurrence1Residual3Band6]
  rw [← recurrence1Residual3Band7]
  rw [← recurrence1Residual3Band8]
  rw [← recurrence1Residual3Band9]
  rw [← recurrence1Residual3Band10]
  rw [← recurrence1Residual3Band11]
  rw [← recurrence1Residual3Band12]
  rw [← recurrence1Residual3Band13]
  rw [← recurrence1Residual3Band14]
  rw [← recurrence1Residual3Band15]
  rw [← recurrence1Residual3Band16]
  rw [← recurrence1Residual3Band17]
  rw [← recurrence1Residual3Band18]
  rw [← recurrence1Residual3Band19]
  rw [← recurrence1Residual3Band20]
  rw [← recurrence1Residual3Band21]
  rw [← recurrence1Residual3Band22]
  ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
