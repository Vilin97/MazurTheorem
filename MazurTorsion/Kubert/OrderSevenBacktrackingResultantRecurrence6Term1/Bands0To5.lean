/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term1.Rows0To2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term1.Rows3To5
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6BlockData.NormalizedResidualTerm1
import Mathlib.Tactic.Ring

/-!
# Recurrence 6 Term1 bands 0–5

This file checks an independent group of band identities for Term1 of the sixth
pseudo-division recurrence.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

def recurrence6Term1Band0 : Coefficient :=
  recurrence6Term1Row0Band0

theorem recurrence6Term1Band0_eq :
    recurrence6Term1Band0 = normalizedResidual6Term1Block0 := by
  unfold recurrence6Term1Band0 recurrence6Term1Row0Band0 normalizedResidual6Term1Block0
  ring

def recurrence6Term1Band1 : Coefficient :=
  recurrence6Term1Row0Band1 +
  recurrence6Term1Row1Band1

theorem recurrence6Term1Band1_eq :
    recurrence6Term1Band1 = normalizedResidual6Term1Block1 := by
  unfold recurrence6Term1Band1 recurrence6Term1Row0Band1 recurrence6Term1Row1Band1
  unfold normalizedResidual6Term1Block1
  ring

def recurrence6Term1Band2 : Coefficient :=
  recurrence6Term1Row0Band2 +
  recurrence6Term1Row1Band2 +
  recurrence6Term1Row2Band2

theorem recurrence6Term1Band2_eq :
    recurrence6Term1Band2 = normalizedResidual6Term1Block2 := by
  unfold recurrence6Term1Band2 recurrence6Term1Row0Band2 recurrence6Term1Row1Band2
  unfold recurrence6Term1Row2Band2 normalizedResidual6Term1Block2
  ring

def recurrence6Term1Band3 : Coefficient :=
  recurrence6Term1Row0Band3 +
  recurrence6Term1Row1Band3 +
  recurrence6Term1Row2Band3 +
  recurrence6Term1Row3Band3

theorem recurrence6Term1Band3_eq :
    recurrence6Term1Band3 = normalizedResidual6Term1Block3 := by
  unfold recurrence6Term1Band3 recurrence6Term1Row0Band3 recurrence6Term1Row1Band3
  unfold recurrence6Term1Row2Band3 recurrence6Term1Row3Band3 normalizedResidual6Term1Block3
  ring

def recurrence6Term1Band4 : Coefficient :=
  recurrence6Term1Row0Band4 +
  recurrence6Term1Row1Band4 +
  recurrence6Term1Row2Band4 +
  recurrence6Term1Row3Band4 +
  recurrence6Term1Row4Band4

theorem recurrence6Term1Band4_eq :
    recurrence6Term1Band4 = normalizedResidual6Term1Block4 := by
  unfold recurrence6Term1Band4 recurrence6Term1Row0Band4 recurrence6Term1Row1Band4
  unfold recurrence6Term1Row2Band4 recurrence6Term1Row3Band4 recurrence6Term1Row4Band4
  unfold normalizedResidual6Term1Block4
  ring

def recurrence6Term1Band5 : Coefficient :=
  recurrence6Term1Row0Band5 +
  recurrence6Term1Row1Band5 +
  recurrence6Term1Row2Band5 +
  recurrence6Term1Row3Band5 +
  recurrence6Term1Row4Band5 +
  recurrence6Term1Row5Band5

theorem recurrence6Term1Band5_eq :
    recurrence6Term1Band5 = normalizedResidual6Term1Block5 := by
  unfold recurrence6Term1Band5 recurrence6Term1Row0Band5 recurrence6Term1Row1Band5
  unfold recurrence6Term1Row2Band5 recurrence6Term1Row3Band5 recurrence6Term1Row4Band5
  unfold recurrence6Term1Row5Band5 normalizedResidual6Term1Block5
  ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
