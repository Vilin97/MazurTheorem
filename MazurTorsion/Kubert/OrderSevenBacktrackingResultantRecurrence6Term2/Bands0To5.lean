/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term2.Rows0To1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term2.Rows2To3
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term2.Rows4To5
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6BlockData.NormalizedResidualTerm2
import Mathlib.Tactic.Ring

/-!
# Recurrence 6 Term2 bands 0–5

This file checks bands 0 through 5 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

/-- Internal datum. -/ def recurrence6Term2Band0 : Coefficient :=
  recurrence6Term2Row0Band0

theorem recurrence6Term2Band0_eq :
    recurrence6Term2Band0 = normalizedResidual6Term2Block0 := by
  unfold recurrence6Term2Band0 recurrence6Term2Row0Band0 normalizedResidual6Term2Block0
  ring

/-- Internal datum. -/ def recurrence6Term2Band1 : Coefficient :=
  recurrence6Term2Row0Band1 +
  recurrence6Term2Row1Band1

theorem recurrence6Term2Band1_eq :
    recurrence6Term2Band1 = normalizedResidual6Term2Block1 := by
  unfold recurrence6Term2Band1 recurrence6Term2Row0Band1 recurrence6Term2Row1Band1
  unfold normalizedResidual6Term2Block1
  ring

/-- Internal datum. -/ def recurrence6Term2Band2 : Coefficient :=
  recurrence6Term2Row0Band2 +
  recurrence6Term2Row1Band2 +
  recurrence6Term2Row2Band2

theorem recurrence6Term2Band2_eq :
    recurrence6Term2Band2 = normalizedResidual6Term2Block2 := by
  unfold recurrence6Term2Band2 recurrence6Term2Row0Band2 recurrence6Term2Row1Band2
  unfold recurrence6Term2Row2Band2 normalizedResidual6Term2Block2
  ring

/-- Internal datum. -/ def recurrence6Term2Band3 : Coefficient :=
  recurrence6Term2Row0Band3 +
  recurrence6Term2Row1Band3 +
  recurrence6Term2Row2Band3 +
  recurrence6Term2Row3Band3

theorem recurrence6Term2Band3_eq :
    recurrence6Term2Band3 = normalizedResidual6Term2Block3 := by
  unfold recurrence6Term2Band3 recurrence6Term2Row0Band3 recurrence6Term2Row1Band3
  unfold recurrence6Term2Row2Band3 recurrence6Term2Row3Band3 normalizedResidual6Term2Block3
  ring

/-- Internal datum. -/ def recurrence6Term2Band4 : Coefficient :=
  recurrence6Term2Row0Band4 +
  recurrence6Term2Row1Band4 +
  recurrence6Term2Row2Band4 +
  recurrence6Term2Row3Band4 +
  recurrence6Term2Row4Band4

theorem recurrence6Term2Band4_eq :
    recurrence6Term2Band4 = normalizedResidual6Term2Block4 := by
  unfold recurrence6Term2Band4 recurrence6Term2Row0Band4 recurrence6Term2Row1Band4
  unfold recurrence6Term2Row2Band4 recurrence6Term2Row3Band4 recurrence6Term2Row4Band4
  unfold normalizedResidual6Term2Block4
  ring

/-- Internal datum. -/ def recurrence6Term2Band5 : Coefficient :=
  recurrence6Term2Row0Band5 +
  recurrence6Term2Row1Band5 +
  recurrence6Term2Row2Band5 +
  recurrence6Term2Row3Band5 +
  recurrence6Term2Row4Band5 +
  recurrence6Term2Row5Band5

theorem recurrence6Term2Band5_eq :
    recurrence6Term2Band5 = normalizedResidual6Term2Block5 := by
  unfold recurrence6Term2Band5 recurrence6Term2Row0Band5 recurrence6Term2Row1Band5
  unfold recurrence6Term2Row2Band5 recurrence6Term2Row3Band5 recurrence6Term2Row4Band5
  unfold recurrence6Term2Row5Band5 normalizedResidual6Term2Block5
  ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
