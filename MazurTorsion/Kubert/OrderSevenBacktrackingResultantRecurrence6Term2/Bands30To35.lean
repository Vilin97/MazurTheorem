/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term2.Rows4To5
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term2.Rows6To7
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term2.Rows8To9
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6BlockData.NormalizedResidualTerm2
import Mathlib.Tactic.Ring

/-!
# Recurrence 6 Term2 bands 30–35

This file checks bands 30 through 35 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

/-- Internal datum. -/ def recurrence6Term2Band30 : Coefficient :=
  recurrence6Term2Row4Band30 +
  recurrence6Term2Row5Band30 +
  recurrence6Term2Row6Band30 +
  recurrence6Term2Row7Band30 +
  recurrence6Term2Row8Band30 +
  recurrence6Term2Row9Band30

theorem recurrence6Term2Band30_eq :
    recurrence6Term2Band30 = normalizedResidual6Term2Block30 := by
  unfold recurrence6Term2Band30 recurrence6Term2Row4Band30 recurrence6Term2Row5Band30
  unfold recurrence6Term2Row6Band30 recurrence6Term2Row7Band30 recurrence6Term2Row8Band30
  unfold recurrence6Term2Row9Band30 normalizedResidual6Term2Block30
  ring

/-- Internal datum. -/ def recurrence6Term2Band31 : Coefficient :=
  recurrence6Term2Row5Band31 +
  recurrence6Term2Row6Band31 +
  recurrence6Term2Row7Band31 +
  recurrence6Term2Row8Band31 +
  recurrence6Term2Row9Band31

theorem recurrence6Term2Band31_eq :
    recurrence6Term2Band31 = normalizedResidual6Term2Block31 := by
  unfold recurrence6Term2Band31 recurrence6Term2Row5Band31 recurrence6Term2Row6Band31
  unfold recurrence6Term2Row7Band31 recurrence6Term2Row8Band31 recurrence6Term2Row9Band31
  unfold normalizedResidual6Term2Block31
  ring

/-- Internal datum. -/ def recurrence6Term2Band32 : Coefficient :=
  recurrence6Term2Row6Band32 +
  recurrence6Term2Row7Band32 +
  recurrence6Term2Row8Band32 +
  recurrence6Term2Row9Band32

theorem recurrence6Term2Band32_eq :
    recurrence6Term2Band32 = normalizedResidual6Term2Block32 := by
  unfold recurrence6Term2Band32 recurrence6Term2Row6Band32 recurrence6Term2Row7Band32
  unfold recurrence6Term2Row8Band32 recurrence6Term2Row9Band32 normalizedResidual6Term2Block32
  ring

/-- Internal datum. -/ def recurrence6Term2Band33 : Coefficient :=
  recurrence6Term2Row7Band33 +
  recurrence6Term2Row8Band33 +
  recurrence6Term2Row9Band33

theorem recurrence6Term2Band33_eq :
    recurrence6Term2Band33 = normalizedResidual6Term2Block33 := by
  unfold recurrence6Term2Band33 recurrence6Term2Row7Band33 recurrence6Term2Row8Band33
  unfold recurrence6Term2Row9Band33 normalizedResidual6Term2Block33
  ring

/-- Internal datum. -/ def recurrence6Term2Band34 : Coefficient :=
  recurrence6Term2Row8Band34 +
  recurrence6Term2Row9Band34

theorem recurrence6Term2Band34_eq :
    recurrence6Term2Band34 = normalizedResidual6Term2Block34 := by
  unfold recurrence6Term2Band34 recurrence6Term2Row8Band34 recurrence6Term2Row9Band34
  unfold normalizedResidual6Term2Block34
  ring

/-- Internal datum. -/ def recurrence6Term2Band35 : Coefficient :=
  recurrence6Term2Row9Band35

theorem recurrence6Term2Band35_eq :
    recurrence6Term2Band35 = normalizedResidual6Term2Block35 := by
  unfold recurrence6Term2Band35 recurrence6Term2Row9Band35 normalizedResidual6Term2Block35
  ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
