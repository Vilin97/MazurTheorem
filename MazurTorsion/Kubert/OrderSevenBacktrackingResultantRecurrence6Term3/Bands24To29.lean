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
# Recurrence 6 Term3 bands 24–29

This file checks bands 24 through 29 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

def recurrence6Term3Band24 : Coefficient :=
  recurrence6Term3Row0Band24 +
  recurrence6Term3Row1Band24 +
  recurrence6Term3Row2Band24 +
  recurrence6Term3Row3Band24

theorem recurrence6Term3Band24_eq :
    recurrence6Term3Band24 = normalizedResidual6Term3Block24 := by
  unfold recurrence6Term3Band24 recurrence6Term3Row0Band24 recurrence6Term3Row1Band24
  unfold recurrence6Term3Row2Band24 recurrence6Term3Row3Band24 normalizedResidual6Term3Block24
  ring

def recurrence6Term3Band25 : Coefficient :=
  recurrence6Term3Row0Band25 +
  recurrence6Term3Row1Band25 +
  recurrence6Term3Row2Band25 +
  recurrence6Term3Row3Band25

theorem recurrence6Term3Band25_eq :
    recurrence6Term3Band25 = normalizedResidual6Term3Block25 := by
  unfold recurrence6Term3Band25 recurrence6Term3Row0Band25 recurrence6Term3Row1Band25
  unfold recurrence6Term3Row2Band25 recurrence6Term3Row3Band25 normalizedResidual6Term3Block25
  ring

def recurrence6Term3Band26 : Coefficient :=
  recurrence6Term3Row0Band26 +
  recurrence6Term3Row1Band26 +
  recurrence6Term3Row2Band26 +
  recurrence6Term3Row3Band26

theorem recurrence6Term3Band26_eq :
    recurrence6Term3Band26 = normalizedResidual6Term3Block26 := by
  unfold recurrence6Term3Band26 recurrence6Term3Row0Band26 recurrence6Term3Row1Band26
  unfold recurrence6Term3Row2Band26 recurrence6Term3Row3Band26 normalizedResidual6Term3Block26
  ring

def recurrence6Term3Band27 : Coefficient :=
  recurrence6Term3Row0Band27 +
  recurrence6Term3Row1Band27 +
  recurrence6Term3Row2Band27 +
  recurrence6Term3Row3Band27

theorem recurrence6Term3Band27_eq :
    recurrence6Term3Band27 = normalizedResidual6Term3Block27 := by
  unfold recurrence6Term3Band27 recurrence6Term3Row0Band27 recurrence6Term3Row1Band27
  unfold recurrence6Term3Row2Band27 recurrence6Term3Row3Band27 normalizedResidual6Term3Block27
  ring

def recurrence6Term3Band28 : Coefficient :=
  recurrence6Term3Row0Band28 +
  recurrence6Term3Row1Band28 +
  recurrence6Term3Row2Band28 +
  recurrence6Term3Row3Band28

theorem recurrence6Term3Band28_eq :
    recurrence6Term3Band28 = normalizedResidual6Term3Block28 := by
  unfold recurrence6Term3Band28 recurrence6Term3Row0Band28 recurrence6Term3Row1Band28
  unfold recurrence6Term3Row2Band28 recurrence6Term3Row3Band28 normalizedResidual6Term3Block28
  ring

def recurrence6Term3Band29 : Coefficient :=
  recurrence6Term3Row0Band29 +
  recurrence6Term3Row1Band29 +
  recurrence6Term3Row2Band29 +
  recurrence6Term3Row3Band29

theorem recurrence6Term3Band29_eq :
    recurrence6Term3Band29 = normalizedResidual6Term3Block29 := by
  unfold recurrence6Term3Band29 recurrence6Term3Row0Band29 recurrence6Term3Row1Band29
  unfold recurrence6Term3Row2Band29 recurrence6Term3Row3Band29 normalizedResidual6Term3Block29
  ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
