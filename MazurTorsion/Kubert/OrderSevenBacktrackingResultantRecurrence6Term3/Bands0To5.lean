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
# Recurrence 6 Term3 bands 0–5

This file checks bands 0 through 5 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

def recurrence6Term3Band0 : Coefficient :=
  recurrence6Term3Row0Band0

theorem recurrence6Term3Band0_eq :
    recurrence6Term3Band0 = normalizedResidual6Term3Block0 := by
  unfold recurrence6Term3Band0 recurrence6Term3Row0Band0 normalizedResidual6Term3Block0
  ring

def recurrence6Term3Band1 : Coefficient :=
  recurrence6Term3Row0Band1 +
  recurrence6Term3Row1Band1

theorem recurrence6Term3Band1_eq :
    recurrence6Term3Band1 = normalizedResidual6Term3Block1 := by
  unfold recurrence6Term3Band1 recurrence6Term3Row0Band1 recurrence6Term3Row1Band1
  unfold normalizedResidual6Term3Block1
  ring

def recurrence6Term3Band2 : Coefficient :=
  recurrence6Term3Row0Band2 +
  recurrence6Term3Row1Band2 +
  recurrence6Term3Row2Band2

theorem recurrence6Term3Band2_eq :
    recurrence6Term3Band2 = normalizedResidual6Term3Block2 := by
  unfold recurrence6Term3Band2 recurrence6Term3Row0Band2 recurrence6Term3Row1Band2
  unfold recurrence6Term3Row2Band2 normalizedResidual6Term3Block2
  ring

def recurrence6Term3Band3 : Coefficient :=
  recurrence6Term3Row0Band3 +
  recurrence6Term3Row1Band3 +
  recurrence6Term3Row2Band3 +
  recurrence6Term3Row3Band3

theorem recurrence6Term3Band3_eq :
    recurrence6Term3Band3 = normalizedResidual6Term3Block3 := by
  unfold recurrence6Term3Band3 recurrence6Term3Row0Band3 recurrence6Term3Row1Band3
  unfold recurrence6Term3Row2Band3 recurrence6Term3Row3Band3 normalizedResidual6Term3Block3
  ring

def recurrence6Term3Band4 : Coefficient :=
  recurrence6Term3Row0Band4 +
  recurrence6Term3Row1Band4 +
  recurrence6Term3Row2Band4 +
  recurrence6Term3Row3Band4

theorem recurrence6Term3Band4_eq :
    recurrence6Term3Band4 = normalizedResidual6Term3Block4 := by
  unfold recurrence6Term3Band4 recurrence6Term3Row0Band4 recurrence6Term3Row1Band4
  unfold recurrence6Term3Row2Band4 recurrence6Term3Row3Band4 normalizedResidual6Term3Block4
  ring

def recurrence6Term3Band5 : Coefficient :=
  recurrence6Term3Row0Band5 +
  recurrence6Term3Row1Band5 +
  recurrence6Term3Row2Band5 +
  recurrence6Term3Row3Band5

theorem recurrence6Term3Band5_eq :
    recurrence6Term3Band5 = normalizedResidual6Term3Block5 := by
  unfold recurrence6Term3Band5 recurrence6Term3Row0Band5 recurrence6Term3Row1Band5
  unfold recurrence6Term3Row2Band5 recurrence6Term3Row3Band5 normalizedResidual6Term3Block5
  ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
