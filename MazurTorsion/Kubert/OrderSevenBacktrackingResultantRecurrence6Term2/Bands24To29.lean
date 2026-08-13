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
# Recurrence 6 Term2 bands 24–29

This file checks bands 24 through 29 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

/-- Internal datum. -/ def recurrence6Term2Band24 : Coefficient :=
  recurrence6Term2Row0Band24 +
  recurrence6Term2Row1Band24 +
  recurrence6Term2Row2Band24 +
  recurrence6Term2Row3Band24 +
  recurrence6Term2Row4Band24 +
  recurrence6Term2Row5Band24 +
  recurrence6Term2Row6Band24 +
  recurrence6Term2Row7Band24 +
  recurrence6Term2Row8Band24 +
  recurrence6Term2Row9Band24

theorem recurrence6Term2Band24_eq :
    recurrence6Term2Band24 = normalizedResidual6Term2Block24 := by
  unfold recurrence6Term2Band24 recurrence6Term2Row0Band24 recurrence6Term2Row1Band24
  unfold recurrence6Term2Row2Band24 recurrence6Term2Row3Band24 recurrence6Term2Row4Band24
  unfold recurrence6Term2Row5Band24 recurrence6Term2Row6Band24 recurrence6Term2Row7Band24
  unfold recurrence6Term2Row8Band24 recurrence6Term2Row9Band24 normalizedResidual6Term2Block24
  ring

/-- Internal datum. -/ def recurrence6Term2Band25 : Coefficient :=
  recurrence6Term2Row0Band25 +
  recurrence6Term2Row1Band25 +
  recurrence6Term2Row2Band25 +
  recurrence6Term2Row3Band25 +
  recurrence6Term2Row4Band25 +
  recurrence6Term2Row5Band25 +
  recurrence6Term2Row6Band25 +
  recurrence6Term2Row7Band25 +
  recurrence6Term2Row8Band25 +
  recurrence6Term2Row9Band25

theorem recurrence6Term2Band25_eq :
    recurrence6Term2Band25 = normalizedResidual6Term2Block25 := by
  unfold recurrence6Term2Band25 recurrence6Term2Row0Band25 recurrence6Term2Row1Band25
  unfold recurrence6Term2Row2Band25 recurrence6Term2Row3Band25 recurrence6Term2Row4Band25
  unfold recurrence6Term2Row5Band25 recurrence6Term2Row6Band25 recurrence6Term2Row7Band25
  unfold recurrence6Term2Row8Band25 recurrence6Term2Row9Band25 normalizedResidual6Term2Block25
  ring

/-- Internal datum. -/ def recurrence6Term2Band26 : Coefficient :=
  recurrence6Term2Row0Band26 +
  recurrence6Term2Row1Band26 +
  recurrence6Term2Row2Band26 +
  recurrence6Term2Row3Band26 +
  recurrence6Term2Row4Band26 +
  recurrence6Term2Row5Band26 +
  recurrence6Term2Row6Band26 +
  recurrence6Term2Row7Band26 +
  recurrence6Term2Row8Band26 +
  recurrence6Term2Row9Band26

theorem recurrence6Term2Band26_eq :
    recurrence6Term2Band26 = normalizedResidual6Term2Block26 := by
  unfold recurrence6Term2Band26 recurrence6Term2Row0Band26 recurrence6Term2Row1Band26
  unfold recurrence6Term2Row2Band26 recurrence6Term2Row3Band26 recurrence6Term2Row4Band26
  unfold recurrence6Term2Row5Band26 recurrence6Term2Row6Band26 recurrence6Term2Row7Band26
  unfold recurrence6Term2Row8Band26 recurrence6Term2Row9Band26 normalizedResidual6Term2Block26
  ring

/-- Internal datum. -/ def recurrence6Term2Band27 : Coefficient :=
  recurrence6Term2Row1Band27 +
  recurrence6Term2Row2Band27 +
  recurrence6Term2Row3Band27 +
  recurrence6Term2Row4Band27 +
  recurrence6Term2Row5Band27 +
  recurrence6Term2Row6Band27 +
  recurrence6Term2Row7Band27 +
  recurrence6Term2Row8Band27 +
  recurrence6Term2Row9Band27

theorem recurrence6Term2Band27_eq :
    recurrence6Term2Band27 = normalizedResidual6Term2Block27 := by
  unfold recurrence6Term2Band27 recurrence6Term2Row1Band27 recurrence6Term2Row2Band27
  unfold recurrence6Term2Row3Band27 recurrence6Term2Row4Band27 recurrence6Term2Row5Band27
  unfold recurrence6Term2Row6Band27 recurrence6Term2Row7Band27 recurrence6Term2Row8Band27
  unfold recurrence6Term2Row9Band27 normalizedResidual6Term2Block27
  ring

/-- Internal datum. -/ def recurrence6Term2Band28 : Coefficient :=
  recurrence6Term2Row2Band28 +
  recurrence6Term2Row3Band28 +
  recurrence6Term2Row4Band28 +
  recurrence6Term2Row5Band28 +
  recurrence6Term2Row6Band28 +
  recurrence6Term2Row7Band28 +
  recurrence6Term2Row8Band28 +
  recurrence6Term2Row9Band28

theorem recurrence6Term2Band28_eq :
    recurrence6Term2Band28 = normalizedResidual6Term2Block28 := by
  unfold recurrence6Term2Band28 recurrence6Term2Row2Band28 recurrence6Term2Row3Band28
  unfold recurrence6Term2Row4Band28 recurrence6Term2Row5Band28 recurrence6Term2Row6Band28
  unfold recurrence6Term2Row7Band28 recurrence6Term2Row8Band28 recurrence6Term2Row9Band28
  unfold normalizedResidual6Term2Block28
  ring

/-- Internal datum. -/ def recurrence6Term2Band29 : Coefficient :=
  recurrence6Term2Row3Band29 +
  recurrence6Term2Row4Band29 +
  recurrence6Term2Row5Band29 +
  recurrence6Term2Row6Band29 +
  recurrence6Term2Row7Band29 +
  recurrence6Term2Row8Band29 +
  recurrence6Term2Row9Band29

theorem recurrence6Term2Band29_eq :
    recurrence6Term2Band29 = normalizedResidual6Term2Block29 := by
  unfold recurrence6Term2Band29 recurrence6Term2Row3Band29 recurrence6Term2Row4Band29
  unfold recurrence6Term2Row5Band29 recurrence6Term2Row6Band29 recurrence6Term2Row7Band29
  unfold recurrence6Term2Row8Band29 recurrence6Term2Row9Band29 normalizedResidual6Term2Block29
  ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
