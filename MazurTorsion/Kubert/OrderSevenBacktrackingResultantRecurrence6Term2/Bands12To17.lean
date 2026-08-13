/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term2.Rows0To1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term2.Rows2To3
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term2.Rows4To5
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term2.Rows6To7
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term2.Rows8To9
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6BlockData.NormalizedResidualTerm2
import Mathlib.Tactic.Ring

/-!
# Recurrence 6 Term2 bands 12–17

This file checks bands 12 through 17 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

def recurrence6Term2Band12 : Coefficient :=
  recurrence6Term2Row0Band12 +
  recurrence6Term2Row1Band12 +
  recurrence6Term2Row2Band12 +
  recurrence6Term2Row3Band12 +
  recurrence6Term2Row4Band12 +
  recurrence6Term2Row5Band12 +
  recurrence6Term2Row6Band12 +
  recurrence6Term2Row7Band12 +
  recurrence6Term2Row8Band12 +
  recurrence6Term2Row9Band12

theorem recurrence6Term2Band12_eq :
    recurrence6Term2Band12 = normalizedResidual6Term2Block12 := by
  unfold recurrence6Term2Band12 recurrence6Term2Row0Band12 recurrence6Term2Row1Band12
  unfold recurrence6Term2Row2Band12 recurrence6Term2Row3Band12 recurrence6Term2Row4Band12
  unfold recurrence6Term2Row5Band12 recurrence6Term2Row6Band12 recurrence6Term2Row7Band12
  unfold recurrence6Term2Row8Band12 recurrence6Term2Row9Band12 normalizedResidual6Term2Block12
  ring

def recurrence6Term2Band13 : Coefficient :=
  recurrence6Term2Row0Band13 +
  recurrence6Term2Row1Band13 +
  recurrence6Term2Row2Band13 +
  recurrence6Term2Row3Band13 +
  recurrence6Term2Row4Band13 +
  recurrence6Term2Row5Band13 +
  recurrence6Term2Row6Band13 +
  recurrence6Term2Row7Band13 +
  recurrence6Term2Row8Band13 +
  recurrence6Term2Row9Band13

theorem recurrence6Term2Band13_eq :
    recurrence6Term2Band13 = normalizedResidual6Term2Block13 := by
  unfold recurrence6Term2Band13 recurrence6Term2Row0Band13 recurrence6Term2Row1Band13
  unfold recurrence6Term2Row2Band13 recurrence6Term2Row3Band13 recurrence6Term2Row4Band13
  unfold recurrence6Term2Row5Band13 recurrence6Term2Row6Band13 recurrence6Term2Row7Band13
  unfold recurrence6Term2Row8Band13 recurrence6Term2Row9Band13 normalizedResidual6Term2Block13
  ring

def recurrence6Term2Band14 : Coefficient :=
  recurrence6Term2Row0Band14 +
  recurrence6Term2Row1Band14 +
  recurrence6Term2Row2Band14 +
  recurrence6Term2Row3Band14 +
  recurrence6Term2Row4Band14 +
  recurrence6Term2Row5Band14 +
  recurrence6Term2Row6Band14 +
  recurrence6Term2Row7Band14 +
  recurrence6Term2Row8Band14 +
  recurrence6Term2Row9Band14

theorem recurrence6Term2Band14_eq :
    recurrence6Term2Band14 = normalizedResidual6Term2Block14 := by
  unfold recurrence6Term2Band14 recurrence6Term2Row0Band14 recurrence6Term2Row1Band14
  unfold recurrence6Term2Row2Band14 recurrence6Term2Row3Band14 recurrence6Term2Row4Band14
  unfold recurrence6Term2Row5Band14 recurrence6Term2Row6Band14 recurrence6Term2Row7Band14
  unfold recurrence6Term2Row8Band14 recurrence6Term2Row9Band14 normalizedResidual6Term2Block14
  ring

def recurrence6Term2Band15 : Coefficient :=
  recurrence6Term2Row0Band15 +
  recurrence6Term2Row1Band15 +
  recurrence6Term2Row2Band15 +
  recurrence6Term2Row3Band15 +
  recurrence6Term2Row4Band15 +
  recurrence6Term2Row5Band15 +
  recurrence6Term2Row6Band15 +
  recurrence6Term2Row7Band15 +
  recurrence6Term2Row8Band15 +
  recurrence6Term2Row9Band15

theorem recurrence6Term2Band15_eq :
    recurrence6Term2Band15 = normalizedResidual6Term2Block15 := by
  unfold recurrence6Term2Band15 recurrence6Term2Row0Band15 recurrence6Term2Row1Band15
  unfold recurrence6Term2Row2Band15 recurrence6Term2Row3Band15 recurrence6Term2Row4Band15
  unfold recurrence6Term2Row5Band15 recurrence6Term2Row6Band15 recurrence6Term2Row7Band15
  unfold recurrence6Term2Row8Band15 recurrence6Term2Row9Band15 normalizedResidual6Term2Block15
  ring

def recurrence6Term2Band16 : Coefficient :=
  recurrence6Term2Row0Band16 +
  recurrence6Term2Row1Band16 +
  recurrence6Term2Row2Band16 +
  recurrence6Term2Row3Band16 +
  recurrence6Term2Row4Band16 +
  recurrence6Term2Row5Band16 +
  recurrence6Term2Row6Band16 +
  recurrence6Term2Row7Band16 +
  recurrence6Term2Row8Band16 +
  recurrence6Term2Row9Band16

theorem recurrence6Term2Band16_eq :
    recurrence6Term2Band16 = normalizedResidual6Term2Block16 := by
  unfold recurrence6Term2Band16 recurrence6Term2Row0Band16 recurrence6Term2Row1Band16
  unfold recurrence6Term2Row2Band16 recurrence6Term2Row3Band16 recurrence6Term2Row4Band16
  unfold recurrence6Term2Row5Band16 recurrence6Term2Row6Band16 recurrence6Term2Row7Band16
  unfold recurrence6Term2Row8Band16 recurrence6Term2Row9Band16 normalizedResidual6Term2Block16
  ring

def recurrence6Term2Band17 : Coefficient :=
  recurrence6Term2Row0Band17 +
  recurrence6Term2Row1Band17 +
  recurrence6Term2Row2Band17 +
  recurrence6Term2Row3Band17 +
  recurrence6Term2Row4Band17 +
  recurrence6Term2Row5Band17 +
  recurrence6Term2Row6Band17 +
  recurrence6Term2Row7Band17 +
  recurrence6Term2Row8Band17 +
  recurrence6Term2Row9Band17

theorem recurrence6Term2Band17_eq :
    recurrence6Term2Band17 = normalizedResidual6Term2Block17 := by
  unfold recurrence6Term2Band17 recurrence6Term2Row0Band17 recurrence6Term2Row1Band17
  unfold recurrence6Term2Row2Band17 recurrence6Term2Row3Band17 recurrence6Term2Row4Band17
  unfold recurrence6Term2Row5Band17 recurrence6Term2Row6Band17 recurrence6Term2Row7Band17
  unfold recurrence6Term2Row8Band17 recurrence6Term2Row9Band17 normalizedResidual6Term2Block17
  ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
