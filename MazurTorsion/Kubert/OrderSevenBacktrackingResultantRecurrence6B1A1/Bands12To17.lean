/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B1A1.Rows0To1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B1A1.Rows2To3
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B1A1.Rows4To5
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B1A1.Rows6To7
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B1A1.Rows8To9
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6BlockData.Coefficient1Product
import Mathlib.Tactic.Ring

/-!
# Recurrence 6 B1A1 bands 12–17

This file checks bands 12 through 17 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

/-- Internal datum. -/ def recurrence6B1A1Band12 : Coefficient :=
  recurrence6B1A1Row0Band12 +
  recurrence6B1A1Row1Band12 +
  recurrence6B1A1Row2Band12 +
  recurrence6B1A1Row3Band12 +
  recurrence6B1A1Row4Band12 +
  recurrence6B1A1Row5Band12 +
  recurrence6B1A1Row6Band12 +
  recurrence6B1A1Row7Band12 +
  recurrence6B1A1Row8Band12 +
  recurrence6B1A1Row9Band12

theorem recurrence6B1A1Band12_eq :
    recurrence6B1A1Band12 = remainder7Coefficient1TimesRemainder6Coefficient1Block12 := by
  unfold recurrence6B1A1Band12 recurrence6B1A1Row0Band12 recurrence6B1A1Row1Band12
  unfold recurrence6B1A1Row2Band12 recurrence6B1A1Row3Band12 recurrence6B1A1Row4Band12
  unfold recurrence6B1A1Row5Band12 recurrence6B1A1Row6Band12 recurrence6B1A1Row7Band12
  unfold recurrence6B1A1Row8Band12 recurrence6B1A1Row9Band12
  unfold remainder7Coefficient1TimesRemainder6Coefficient1Block12
  ring

/-- Internal datum. -/ def recurrence6B1A1Band13 : Coefficient :=
  recurrence6B1A1Row0Band13 +
  recurrence6B1A1Row1Band13 +
  recurrence6B1A1Row2Band13 +
  recurrence6B1A1Row3Band13 +
  recurrence6B1A1Row4Band13 +
  recurrence6B1A1Row5Band13 +
  recurrence6B1A1Row6Band13 +
  recurrence6B1A1Row7Band13 +
  recurrence6B1A1Row8Band13 +
  recurrence6B1A1Row9Band13

theorem recurrence6B1A1Band13_eq :
    recurrence6B1A1Band13 = remainder7Coefficient1TimesRemainder6Coefficient1Block13 := by
  unfold recurrence6B1A1Band13 recurrence6B1A1Row0Band13 recurrence6B1A1Row1Band13
  unfold recurrence6B1A1Row2Band13 recurrence6B1A1Row3Band13 recurrence6B1A1Row4Band13
  unfold recurrence6B1A1Row5Band13 recurrence6B1A1Row6Band13 recurrence6B1A1Row7Band13
  unfold recurrence6B1A1Row8Band13 recurrence6B1A1Row9Band13
  unfold remainder7Coefficient1TimesRemainder6Coefficient1Block13
  ring

/-- Internal datum. -/ def recurrence6B1A1Band14 : Coefficient :=
  recurrence6B1A1Row0Band14 +
  recurrence6B1A1Row1Band14 +
  recurrence6B1A1Row2Band14 +
  recurrence6B1A1Row3Band14 +
  recurrence6B1A1Row4Band14 +
  recurrence6B1A1Row5Band14 +
  recurrence6B1A1Row6Band14 +
  recurrence6B1A1Row7Band14 +
  recurrence6B1A1Row8Band14 +
  recurrence6B1A1Row9Band14

theorem recurrence6B1A1Band14_eq :
    recurrence6B1A1Band14 = remainder7Coefficient1TimesRemainder6Coefficient1Block14 := by
  unfold recurrence6B1A1Band14 recurrence6B1A1Row0Band14 recurrence6B1A1Row1Band14
  unfold recurrence6B1A1Row2Band14 recurrence6B1A1Row3Band14 recurrence6B1A1Row4Band14
  unfold recurrence6B1A1Row5Band14 recurrence6B1A1Row6Band14 recurrence6B1A1Row7Band14
  unfold recurrence6B1A1Row8Band14 recurrence6B1A1Row9Band14
  unfold remainder7Coefficient1TimesRemainder6Coefficient1Block14
  ring

/-- Internal datum. -/ def recurrence6B1A1Band15 : Coefficient :=
  recurrence6B1A1Row0Band15 +
  recurrence6B1A1Row1Band15 +
  recurrence6B1A1Row2Band15 +
  recurrence6B1A1Row3Band15 +
  recurrence6B1A1Row4Band15 +
  recurrence6B1A1Row5Band15 +
  recurrence6B1A1Row6Band15 +
  recurrence6B1A1Row7Band15 +
  recurrence6B1A1Row8Band15 +
  recurrence6B1A1Row9Band15

theorem recurrence6B1A1Band15_eq :
    recurrence6B1A1Band15 = remainder7Coefficient1TimesRemainder6Coefficient1Block15 := by
  unfold recurrence6B1A1Band15 recurrence6B1A1Row0Band15 recurrence6B1A1Row1Band15
  unfold recurrence6B1A1Row2Band15 recurrence6B1A1Row3Band15 recurrence6B1A1Row4Band15
  unfold recurrence6B1A1Row5Band15 recurrence6B1A1Row6Band15 recurrence6B1A1Row7Band15
  unfold recurrence6B1A1Row8Band15 recurrence6B1A1Row9Band15
  unfold remainder7Coefficient1TimesRemainder6Coefficient1Block15
  ring

/-- Internal datum. -/ def recurrence6B1A1Band16 : Coefficient :=
  recurrence6B1A1Row0Band16 +
  recurrence6B1A1Row1Band16 +
  recurrence6B1A1Row2Band16 +
  recurrence6B1A1Row3Band16 +
  recurrence6B1A1Row4Band16 +
  recurrence6B1A1Row5Band16 +
  recurrence6B1A1Row6Band16 +
  recurrence6B1A1Row7Band16 +
  recurrence6B1A1Row8Band16 +
  recurrence6B1A1Row9Band16

theorem recurrence6B1A1Band16_eq :
    recurrence6B1A1Band16 = remainder7Coefficient1TimesRemainder6Coefficient1Block16 := by
  unfold recurrence6B1A1Band16 recurrence6B1A1Row0Band16 recurrence6B1A1Row1Band16
  unfold recurrence6B1A1Row2Band16 recurrence6B1A1Row3Band16 recurrence6B1A1Row4Band16
  unfold recurrence6B1A1Row5Band16 recurrence6B1A1Row6Band16 recurrence6B1A1Row7Band16
  unfold recurrence6B1A1Row8Band16 recurrence6B1A1Row9Band16
  unfold remainder7Coefficient1TimesRemainder6Coefficient1Block16
  ring

/-- Internal datum. -/ def recurrence6B1A1Band17 : Coefficient :=
  recurrence6B1A1Row0Band17 +
  recurrence6B1A1Row1Band17 +
  recurrence6B1A1Row2Band17 +
  recurrence6B1A1Row3Band17 +
  recurrence6B1A1Row4Band17 +
  recurrence6B1A1Row5Band17 +
  recurrence6B1A1Row6Band17 +
  recurrence6B1A1Row7Band17 +
  recurrence6B1A1Row8Band17 +
  recurrence6B1A1Row9Band17

theorem recurrence6B1A1Band17_eq :
    recurrence6B1A1Band17 = remainder7Coefficient1TimesRemainder6Coefficient1Block17 := by
  unfold recurrence6B1A1Band17 recurrence6B1A1Row0Band17 recurrence6B1A1Row1Band17
  unfold recurrence6B1A1Row2Band17 recurrence6B1A1Row3Band17 recurrence6B1A1Row4Band17
  unfold recurrence6B1A1Row5Band17 recurrence6B1A1Row6Band17 recurrence6B1A1Row7Band17
  unfold recurrence6B1A1Row8Band17 recurrence6B1A1Row9Band17
  unfold remainder7Coefficient1TimesRemainder6Coefficient1Block17
  ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
