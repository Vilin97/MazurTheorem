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
# Recurrence 6 Term3 bands 30–35

This file checks bands 30 through 35 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

def recurrence6Term3Band30 : Coefficient :=
  recurrence6Term3Row0Band30 +
  recurrence6Term3Row1Band30 +
  recurrence6Term3Row2Band30 +
  recurrence6Term3Row3Band30

theorem recurrence6Term3Band30_eq :
    recurrence6Term3Band30 = normalizedResidual6Term3Block30 := by
  unfold recurrence6Term3Band30 recurrence6Term3Row0Band30 recurrence6Term3Row1Band30
  unfold recurrence6Term3Row2Band30 recurrence6Term3Row3Band30 normalizedResidual6Term3Block30
  ring

def recurrence6Term3Band31 : Coefficient :=
  recurrence6Term3Row0Band31 +
  recurrence6Term3Row1Band31 +
  recurrence6Term3Row2Band31 +
  recurrence6Term3Row3Band31

theorem recurrence6Term3Band31_eq :
    recurrence6Term3Band31 = normalizedResidual6Term3Block31 := by
  unfold recurrence6Term3Band31 recurrence6Term3Row0Band31 recurrence6Term3Row1Band31
  unfold recurrence6Term3Row2Band31 recurrence6Term3Row3Band31 normalizedResidual6Term3Block31
  ring

def recurrence6Term3Band32 : Coefficient :=
  recurrence6Term3Row0Band32 +
  recurrence6Term3Row1Band32 +
  recurrence6Term3Row2Band32 +
  recurrence6Term3Row3Band32

theorem recurrence6Term3Band32_eq :
    recurrence6Term3Band32 = normalizedResidual6Term3Block32 := by
  unfold recurrence6Term3Band32 recurrence6Term3Row0Band32 recurrence6Term3Row1Band32
  unfold recurrence6Term3Row2Band32 recurrence6Term3Row3Band32 normalizedResidual6Term3Block32
  ring

def recurrence6Term3Band33 : Coefficient :=
  recurrence6Term3Row0Band33 +
  recurrence6Term3Row1Band33 +
  recurrence6Term3Row2Band33 +
  recurrence6Term3Row3Band33

theorem recurrence6Term3Band33_eq :
    recurrence6Term3Band33 = normalizedResidual6Term3Block33 := by
  unfold recurrence6Term3Band33 recurrence6Term3Row0Band33 recurrence6Term3Row1Band33
  unfold recurrence6Term3Row2Band33 recurrence6Term3Row3Band33 normalizedResidual6Term3Block33
  ring

def recurrence6Term3Band34 : Coefficient :=
  recurrence6Term3Row1Band34 +
  recurrence6Term3Row2Band34 +
  recurrence6Term3Row3Band34

theorem recurrence6Term3Band34_eq :
    recurrence6Term3Band34 = normalizedResidual6Term3Block34 := by
  unfold recurrence6Term3Band34 recurrence6Term3Row1Band34 recurrence6Term3Row2Band34
  unfold recurrence6Term3Row3Band34 normalizedResidual6Term3Block34
  ring

def recurrence6Term3Band35 : Coefficient :=
  recurrence6Term3Row2Band35 +
  recurrence6Term3Row3Band35

theorem recurrence6Term3Band35_eq :
    recurrence6Term3Band35 = normalizedResidual6Term3Block35 := by
  unfold recurrence6Term3Band35 recurrence6Term3Row2Band35 recurrence6Term3Row3Band35
  unfold normalizedResidual6Term3Block35
  ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
