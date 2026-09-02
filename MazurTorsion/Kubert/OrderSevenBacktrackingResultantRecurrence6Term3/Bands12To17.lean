/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term3.Rows0To0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term3.Rows1To1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term3.Rows2To2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term3.Rows3To3
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6BlockData.NormalizedResidualTerm3
import Mathlib.Tactic.Ring

/-!
# Recurrence 6 Term3 bands 12–17

This file checks bands 12 through 17 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

def recurrence6Term3Band12 : Coefficient :=
  recurrence6Term3Row0Band12 +
  recurrence6Term3Row1Band12 +
  recurrence6Term3Row2Band12 +
  recurrence6Term3Row3Band12

theorem recurrence6Term3Band12_eq :
    recurrence6Term3Band12 = normalizedResidual6Term3Block12 := by
  unfold recurrence6Term3Band12 recurrence6Term3Row0Band12 recurrence6Term3Row1Band12
  unfold recurrence6Term3Row2Band12 recurrence6Term3Row3Band12 normalizedResidual6Term3Block12
  ring

def recurrence6Term3Band13 : Coefficient :=
  recurrence6Term3Row0Band13 +
  recurrence6Term3Row1Band13 +
  recurrence6Term3Row2Band13 +
  recurrence6Term3Row3Band13

theorem recurrence6Term3Band13_eq :
    recurrence6Term3Band13 = normalizedResidual6Term3Block13 := by
  unfold recurrence6Term3Band13 recurrence6Term3Row0Band13 recurrence6Term3Row1Band13
  unfold recurrence6Term3Row2Band13 recurrence6Term3Row3Band13 normalizedResidual6Term3Block13
  ring

def recurrence6Term3Band14 : Coefficient :=
  recurrence6Term3Row0Band14 +
  recurrence6Term3Row1Band14 +
  recurrence6Term3Row2Band14 +
  recurrence6Term3Row3Band14

theorem recurrence6Term3Band14_eq :
    recurrence6Term3Band14 = normalizedResidual6Term3Block14 := by
  unfold recurrence6Term3Band14 recurrence6Term3Row0Band14 recurrence6Term3Row1Band14
  unfold recurrence6Term3Row2Band14 recurrence6Term3Row3Band14 normalizedResidual6Term3Block14
  ring

def recurrence6Term3Band15 : Coefficient :=
  recurrence6Term3Row0Band15 +
  recurrence6Term3Row1Band15 +
  recurrence6Term3Row2Band15 +
  recurrence6Term3Row3Band15

theorem recurrence6Term3Band15_eq :
    recurrence6Term3Band15 = normalizedResidual6Term3Block15 := by
  unfold recurrence6Term3Band15 recurrence6Term3Row0Band15 recurrence6Term3Row1Band15
  unfold recurrence6Term3Row2Band15 recurrence6Term3Row3Band15 normalizedResidual6Term3Block15
  ring

def recurrence6Term3Band16 : Coefficient :=
  recurrence6Term3Row0Band16 +
  recurrence6Term3Row1Band16 +
  recurrence6Term3Row2Band16 +
  recurrence6Term3Row3Band16

theorem recurrence6Term3Band16_eq :
    recurrence6Term3Band16 = normalizedResidual6Term3Block16 := by
  unfold recurrence6Term3Band16 recurrence6Term3Row0Band16 recurrence6Term3Row1Band16
  unfold recurrence6Term3Row2Band16 recurrence6Term3Row3Band16 normalizedResidual6Term3Block16
  ring

def recurrence6Term3Band17 : Coefficient :=
  recurrence6Term3Row0Band17 +
  recurrence6Term3Row1Band17 +
  recurrence6Term3Row2Band17 +
  recurrence6Term3Row3Band17

theorem recurrence6Term3Band17_eq :
    recurrence6Term3Band17 = normalizedResidual6Term3Block17 := by
  unfold recurrence6Term3Band17 recurrence6Term3Row0Band17 recurrence6Term3Row1Band17
  unfold recurrence6Term3Row2Band17 recurrence6Term3Row3Band17 normalizedResidual6Term3Block17
  ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
