/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B0A2.Rows0To1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B0A2.Rows2To3
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B0A2.Rows4To5
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6BlockData.Coefficient0Coefficient2Product
import Mathlib.Tactic.Ring

/-!
# Recurrence 6 B0A2 bands 0–5

This file checks bands 0 through 5 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

/-- Internal datum. -/ def recurrence6B0A2Band0 : Coefficient :=
  recurrence6B0A2Row0Band0

theorem recurrence6B0A2Band0_eq :
    recurrence6B0A2Band0 = remainder7Coefficient0TimesRemainder6Coefficient2Block0 := by
  unfold recurrence6B0A2Band0 recurrence6B0A2Row0Band0
  unfold remainder7Coefficient0TimesRemainder6Coefficient2Block0
  ring

/-- Internal datum. -/ def recurrence6B0A2Band1 : Coefficient :=
  recurrence6B0A2Row0Band1 +
  recurrence6B0A2Row1Band1

theorem recurrence6B0A2Band1_eq :
    recurrence6B0A2Band1 = remainder7Coefficient0TimesRemainder6Coefficient2Block1 := by
  unfold recurrence6B0A2Band1 recurrence6B0A2Row0Band1 recurrence6B0A2Row1Band1
  unfold remainder7Coefficient0TimesRemainder6Coefficient2Block1
  ring

/-- Internal datum. -/ def recurrence6B0A2Band2 : Coefficient :=
  recurrence6B0A2Row0Band2 +
  recurrence6B0A2Row1Band2 +
  recurrence6B0A2Row2Band2

theorem recurrence6B0A2Band2_eq :
    recurrence6B0A2Band2 = remainder7Coefficient0TimesRemainder6Coefficient2Block2 := by
  unfold recurrence6B0A2Band2 recurrence6B0A2Row0Band2 recurrence6B0A2Row1Band2
  unfold recurrence6B0A2Row2Band2 remainder7Coefficient0TimesRemainder6Coefficient2Block2
  ring

/-- Internal datum. -/ def recurrence6B0A2Band3 : Coefficient :=
  recurrence6B0A2Row0Band3 +
  recurrence6B0A2Row1Band3 +
  recurrence6B0A2Row2Band3 +
  recurrence6B0A2Row3Band3

theorem recurrence6B0A2Band3_eq :
    recurrence6B0A2Band3 = remainder7Coefficient0TimesRemainder6Coefficient2Block3 := by
  unfold recurrence6B0A2Band3 recurrence6B0A2Row0Band3 recurrence6B0A2Row1Band3
  unfold recurrence6B0A2Row2Band3 recurrence6B0A2Row3Band3
  unfold remainder7Coefficient0TimesRemainder6Coefficient2Block3
  ring

/-- Internal datum. -/ def recurrence6B0A2Band4 : Coefficient :=
  recurrence6B0A2Row0Band4 +
  recurrence6B0A2Row1Band4 +
  recurrence6B0A2Row2Band4 +
  recurrence6B0A2Row3Band4 +
  recurrence6B0A2Row4Band4

theorem recurrence6B0A2Band4_eq :
    recurrence6B0A2Band4 = remainder7Coefficient0TimesRemainder6Coefficient2Block4 := by
  unfold recurrence6B0A2Band4 recurrence6B0A2Row0Band4 recurrence6B0A2Row1Band4
  unfold recurrence6B0A2Row2Band4 recurrence6B0A2Row3Band4 recurrence6B0A2Row4Band4
  unfold remainder7Coefficient0TimesRemainder6Coefficient2Block4
  ring

/-- Internal datum. -/ def recurrence6B0A2Band5 : Coefficient :=
  recurrence6B0A2Row0Band5 +
  recurrence6B0A2Row1Band5 +
  recurrence6B0A2Row2Band5 +
  recurrence6B0A2Row3Band5 +
  recurrence6B0A2Row4Band5 +
  recurrence6B0A2Row5Band5

theorem recurrence6B0A2Band5_eq :
    recurrence6B0A2Band5 = remainder7Coefficient0TimesRemainder6Coefficient2Block5 := by
  unfold recurrence6B0A2Band5 recurrence6B0A2Row0Band5 recurrence6B0A2Row1Band5
  unfold recurrence6B0A2Row2Band5 recurrence6B0A2Row3Band5 recurrence6B0A2Row4Band5
  unfold recurrence6B0A2Row5Band5 remainder7Coefficient0TimesRemainder6Coefficient2Block5
  ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
