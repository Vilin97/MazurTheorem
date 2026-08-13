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
# Recurrence 6 Term3 bands 6–11

This file checks bands 6 through 11 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

/-- Internal datum. -/ def recurrence6Term3Band6 : Coefficient :=
  recurrence6Term3Row0Band6 +
  recurrence6Term3Row1Band6 +
  recurrence6Term3Row2Band6 +
  recurrence6Term3Row3Band6

theorem recurrence6Term3Band6_eq :
    recurrence6Term3Band6 = normalizedResidual6Term3Block6 := by
  unfold recurrence6Term3Band6 recurrence6Term3Row0Band6 recurrence6Term3Row1Band6
  unfold recurrence6Term3Row2Band6 recurrence6Term3Row3Band6 normalizedResidual6Term3Block6
  ring

/-- Internal datum. -/ def recurrence6Term3Band7 : Coefficient :=
  recurrence6Term3Row0Band7 +
  recurrence6Term3Row1Band7 +
  recurrence6Term3Row2Band7 +
  recurrence6Term3Row3Band7

theorem recurrence6Term3Band7_eq :
    recurrence6Term3Band7 = normalizedResidual6Term3Block7 := by
  unfold recurrence6Term3Band7 recurrence6Term3Row0Band7 recurrence6Term3Row1Band7
  unfold recurrence6Term3Row2Band7 recurrence6Term3Row3Band7 normalizedResidual6Term3Block7
  ring

/-- Internal datum. -/ def recurrence6Term3Band8 : Coefficient :=
  recurrence6Term3Row0Band8 +
  recurrence6Term3Row1Band8 +
  recurrence6Term3Row2Band8 +
  recurrence6Term3Row3Band8

theorem recurrence6Term3Band8_eq :
    recurrence6Term3Band8 = normalizedResidual6Term3Block8 := by
  unfold recurrence6Term3Band8 recurrence6Term3Row0Band8 recurrence6Term3Row1Band8
  unfold recurrence6Term3Row2Band8 recurrence6Term3Row3Band8 normalizedResidual6Term3Block8
  ring

/-- Internal datum. -/ def recurrence6Term3Band9 : Coefficient :=
  recurrence6Term3Row0Band9 +
  recurrence6Term3Row1Band9 +
  recurrence6Term3Row2Band9 +
  recurrence6Term3Row3Band9

theorem recurrence6Term3Band9_eq :
    recurrence6Term3Band9 = normalizedResidual6Term3Block9 := by
  unfold recurrence6Term3Band9 recurrence6Term3Row0Band9 recurrence6Term3Row1Band9
  unfold recurrence6Term3Row2Band9 recurrence6Term3Row3Band9 normalizedResidual6Term3Block9
  ring

/-- Internal datum. -/ def recurrence6Term3Band10 : Coefficient :=
  recurrence6Term3Row0Band10 +
  recurrence6Term3Row1Band10 +
  recurrence6Term3Row2Band10 +
  recurrence6Term3Row3Band10

theorem recurrence6Term3Band10_eq :
    recurrence6Term3Band10 = normalizedResidual6Term3Block10 := by
  unfold recurrence6Term3Band10 recurrence6Term3Row0Band10 recurrence6Term3Row1Band10
  unfold recurrence6Term3Row2Band10 recurrence6Term3Row3Band10 normalizedResidual6Term3Block10
  ring

/-- Internal datum. -/ def recurrence6Term3Band11 : Coefficient :=
  recurrence6Term3Row0Band11 +
  recurrence6Term3Row1Band11 +
  recurrence6Term3Row2Band11 +
  recurrence6Term3Row3Band11

theorem recurrence6Term3Band11_eq :
    recurrence6Term3Band11 = normalizedResidual6Term3Block11 := by
  unfold recurrence6Term3Band11 recurrence6Term3Row0Band11 recurrence6Term3Row1Band11
  unfold recurrence6Term3Row2Band11 recurrence6Term3Row3Band11 normalizedResidual6Term3Block11
  ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
