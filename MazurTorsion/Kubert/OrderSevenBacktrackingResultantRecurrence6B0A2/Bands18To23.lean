/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B0A2.Rows0To1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B0A2.Rows2To3
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B0A2.Rows4To5
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B0A2.Rows6To7
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B0A2.Rows8To9
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6BlockData.Coefficient0Coefficient2Product
import Mathlib.Tactic.Ring

/-!
# Recurrence 6 B0A2 bands 18–23

This file checks bands 18 through 23 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

/-- Internal datum. -/ def recurrence6B0A2Band18 : Coefficient :=
  recurrence6B0A2Row1Band18 +
  recurrence6B0A2Row2Band18 +
  recurrence6B0A2Row3Band18 +
  recurrence6B0A2Row4Band18 +
  recurrence6B0A2Row5Band18 +
  recurrence6B0A2Row6Band18 +
  recurrence6B0A2Row7Band18 +
  recurrence6B0A2Row8Band18 +
  recurrence6B0A2Row9Band18

theorem recurrence6B0A2Band18_eq :
    recurrence6B0A2Band18 = remainder7Coefficient0TimesRemainder6Coefficient2Block18 := by
  unfold recurrence6B0A2Band18 recurrence6B0A2Row1Band18 recurrence6B0A2Row2Band18
  unfold recurrence6B0A2Row3Band18 recurrence6B0A2Row4Band18 recurrence6B0A2Row5Band18
  unfold recurrence6B0A2Row6Band18 recurrence6B0A2Row7Band18 recurrence6B0A2Row8Band18
  unfold recurrence6B0A2Row9Band18 remainder7Coefficient0TimesRemainder6Coefficient2Block18
  ring

/-- Internal datum. -/ def recurrence6B0A2Band19 : Coefficient :=
  recurrence6B0A2Row2Band19 +
  recurrence6B0A2Row3Band19 +
  recurrence6B0A2Row4Band19 +
  recurrence6B0A2Row5Band19 +
  recurrence6B0A2Row6Band19 +
  recurrence6B0A2Row7Band19 +
  recurrence6B0A2Row8Band19 +
  recurrence6B0A2Row9Band19

theorem recurrence6B0A2Band19_eq :
    recurrence6B0A2Band19 = remainder7Coefficient0TimesRemainder6Coefficient2Block19 := by
  unfold recurrence6B0A2Band19 recurrence6B0A2Row2Band19 recurrence6B0A2Row3Band19
  unfold recurrence6B0A2Row4Band19 recurrence6B0A2Row5Band19 recurrence6B0A2Row6Band19
  unfold recurrence6B0A2Row7Band19 recurrence6B0A2Row8Band19 recurrence6B0A2Row9Band19
  unfold remainder7Coefficient0TimesRemainder6Coefficient2Block19
  ring

/-- Internal datum. -/ def recurrence6B0A2Band20 : Coefficient :=
  recurrence6B0A2Row3Band20 +
  recurrence6B0A2Row4Band20 +
  recurrence6B0A2Row5Band20 +
  recurrence6B0A2Row6Band20 +
  recurrence6B0A2Row7Band20 +
  recurrence6B0A2Row8Band20 +
  recurrence6B0A2Row9Band20

theorem recurrence6B0A2Band20_eq :
    recurrence6B0A2Band20 = remainder7Coefficient0TimesRemainder6Coefficient2Block20 := by
  unfold recurrence6B0A2Band20 recurrence6B0A2Row3Band20 recurrence6B0A2Row4Band20
  unfold recurrence6B0A2Row5Band20 recurrence6B0A2Row6Band20 recurrence6B0A2Row7Band20
  unfold recurrence6B0A2Row8Band20 recurrence6B0A2Row9Band20
  unfold remainder7Coefficient0TimesRemainder6Coefficient2Block20
  ring

/-- Internal datum. -/ def recurrence6B0A2Band21 : Coefficient :=
  recurrence6B0A2Row4Band21 +
  recurrence6B0A2Row5Band21 +
  recurrence6B0A2Row6Band21 +
  recurrence6B0A2Row7Band21 +
  recurrence6B0A2Row8Band21 +
  recurrence6B0A2Row9Band21

theorem recurrence6B0A2Band21_eq :
    recurrence6B0A2Band21 = remainder7Coefficient0TimesRemainder6Coefficient2Block21 := by
  unfold recurrence6B0A2Band21 recurrence6B0A2Row4Band21 recurrence6B0A2Row5Band21
  unfold recurrence6B0A2Row6Band21 recurrence6B0A2Row7Band21 recurrence6B0A2Row8Band21
  unfold recurrence6B0A2Row9Band21 remainder7Coefficient0TimesRemainder6Coefficient2Block21
  ring

/-- Internal datum. -/ def recurrence6B0A2Band22 : Coefficient :=
  recurrence6B0A2Row5Band22 +
  recurrence6B0A2Row6Band22 +
  recurrence6B0A2Row7Band22 +
  recurrence6B0A2Row8Band22 +
  recurrence6B0A2Row9Band22

theorem recurrence6B0A2Band22_eq :
    recurrence6B0A2Band22 = remainder7Coefficient0TimesRemainder6Coefficient2Block22 := by
  unfold recurrence6B0A2Band22 recurrence6B0A2Row5Band22 recurrence6B0A2Row6Band22
  unfold recurrence6B0A2Row7Band22 recurrence6B0A2Row8Band22 recurrence6B0A2Row9Band22
  unfold remainder7Coefficient0TimesRemainder6Coefficient2Block22
  ring

/-- Internal datum. -/ def recurrence6B0A2Band23 : Coefficient :=
  recurrence6B0A2Row6Band23 +
  recurrence6B0A2Row7Band23 +
  recurrence6B0A2Row8Band23 +
  recurrence6B0A2Row9Band23

theorem recurrence6B0A2Band23_eq :
    recurrence6B0A2Band23 = remainder7Coefficient0TimesRemainder6Coefficient2Block23 := by
  unfold recurrence6B0A2Band23 recurrence6B0A2Row6Band23 recurrence6B0A2Row7Band23
  unfold recurrence6B0A2Row8Band23 recurrence6B0A2Row9Band23
  unfold remainder7Coefficient0TimesRemainder6Coefficient2Block23
  ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
