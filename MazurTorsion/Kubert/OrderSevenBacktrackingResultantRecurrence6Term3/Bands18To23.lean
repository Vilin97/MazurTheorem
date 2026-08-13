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
# Recurrence 6 Term3 bands 18–23

This file checks bands 18 through 23 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

def recurrence6Term3Band18 : Coefficient :=
  recurrence6Term3Row0Band18 +
  recurrence6Term3Row1Band18 +
  recurrence6Term3Row2Band18 +
  recurrence6Term3Row3Band18

theorem recurrence6Term3Band18_eq :
    recurrence6Term3Band18 = normalizedResidual6Term3Block18 := by
  unfold recurrence6Term3Band18 recurrence6Term3Row0Band18 recurrence6Term3Row1Band18
  unfold recurrence6Term3Row2Band18 recurrence6Term3Row3Band18 normalizedResidual6Term3Block18
  ring

def recurrence6Term3Band19 : Coefficient :=
  recurrence6Term3Row0Band19 +
  recurrence6Term3Row1Band19 +
  recurrence6Term3Row2Band19 +
  recurrence6Term3Row3Band19

theorem recurrence6Term3Band19_eq :
    recurrence6Term3Band19 = normalizedResidual6Term3Block19 := by
  unfold recurrence6Term3Band19 recurrence6Term3Row0Band19 recurrence6Term3Row1Band19
  unfold recurrence6Term3Row2Band19 recurrence6Term3Row3Band19 normalizedResidual6Term3Block19
  ring

def recurrence6Term3Band20 : Coefficient :=
  recurrence6Term3Row0Band20 +
  recurrence6Term3Row1Band20 +
  recurrence6Term3Row2Band20 +
  recurrence6Term3Row3Band20

theorem recurrence6Term3Band20_eq :
    recurrence6Term3Band20 = normalizedResidual6Term3Block20 := by
  unfold recurrence6Term3Band20 recurrence6Term3Row0Band20 recurrence6Term3Row1Band20
  unfold recurrence6Term3Row2Band20 recurrence6Term3Row3Band20 normalizedResidual6Term3Block20
  ring

def recurrence6Term3Band21 : Coefficient :=
  recurrence6Term3Row0Band21 +
  recurrence6Term3Row1Band21 +
  recurrence6Term3Row2Band21 +
  recurrence6Term3Row3Band21

theorem recurrence6Term3Band21_eq :
    recurrence6Term3Band21 = normalizedResidual6Term3Block21 := by
  unfold recurrence6Term3Band21 recurrence6Term3Row0Band21 recurrence6Term3Row1Band21
  unfold recurrence6Term3Row2Band21 recurrence6Term3Row3Band21 normalizedResidual6Term3Block21
  ring

def recurrence6Term3Band22 : Coefficient :=
  recurrence6Term3Row0Band22 +
  recurrence6Term3Row1Band22 +
  recurrence6Term3Row2Band22 +
  recurrence6Term3Row3Band22

theorem recurrence6Term3Band22_eq :
    recurrence6Term3Band22 = normalizedResidual6Term3Block22 := by
  unfold recurrence6Term3Band22 recurrence6Term3Row0Band22 recurrence6Term3Row1Band22
  unfold recurrence6Term3Row2Band22 recurrence6Term3Row3Band22 normalizedResidual6Term3Block22
  ring

def recurrence6Term3Band23 : Coefficient :=
  recurrence6Term3Row0Band23 +
  recurrence6Term3Row1Band23 +
  recurrence6Term3Row2Band23 +
  recurrence6Term3Row3Band23

theorem recurrence6Term3Band23_eq :
    recurrence6Term3Band23 = normalizedResidual6Term3Block23 := by
  unfold recurrence6Term3Band23 recurrence6Term3Row0Band23 recurrence6Term3Row1Band23
  unfold recurrence6Term3Row2Band23 recurrence6Term3Row3Band23 normalizedResidual6Term3Block23
  ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
