/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B1A1.Rows0To1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B1A1.Rows2To3
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B1A1.Rows4To5
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6BlockData.Coefficient1Product
import Mathlib.Tactic.Ring

/-!
# Recurrence 6 B1A1 bands 0–5

This file checks bands 0 through 5 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

def recurrence6B1A1Band0 : Coefficient :=
  recurrence6B1A1Row0Band0

theorem recurrence6B1A1Band0_eq :
    recurrence6B1A1Band0 = remainder7Coefficient1TimesRemainder6Coefficient1Block0 := by
  unfold recurrence6B1A1Band0 recurrence6B1A1Row0Band0
  unfold remainder7Coefficient1TimesRemainder6Coefficient1Block0
  ring

def recurrence6B1A1Band1 : Coefficient :=
  recurrence6B1A1Row0Band1 +
  recurrence6B1A1Row1Band1

theorem recurrence6B1A1Band1_eq :
    recurrence6B1A1Band1 = remainder7Coefficient1TimesRemainder6Coefficient1Block1 := by
  unfold recurrence6B1A1Band1 recurrence6B1A1Row0Band1 recurrence6B1A1Row1Band1
  unfold remainder7Coefficient1TimesRemainder6Coefficient1Block1
  ring

def recurrence6B1A1Band2 : Coefficient :=
  recurrence6B1A1Row0Band2 +
  recurrence6B1A1Row1Band2 +
  recurrence6B1A1Row2Band2

theorem recurrence6B1A1Band2_eq :
    recurrence6B1A1Band2 = remainder7Coefficient1TimesRemainder6Coefficient1Block2 := by
  unfold recurrence6B1A1Band2 recurrence6B1A1Row0Band2 recurrence6B1A1Row1Band2
  unfold recurrence6B1A1Row2Band2 remainder7Coefficient1TimesRemainder6Coefficient1Block2
  ring

def recurrence6B1A1Band3 : Coefficient :=
  recurrence6B1A1Row0Band3 +
  recurrence6B1A1Row1Band3 +
  recurrence6B1A1Row2Band3 +
  recurrence6B1A1Row3Band3

theorem recurrence6B1A1Band3_eq :
    recurrence6B1A1Band3 = remainder7Coefficient1TimesRemainder6Coefficient1Block3 := by
  unfold recurrence6B1A1Band3 recurrence6B1A1Row0Band3 recurrence6B1A1Row1Band3
  unfold recurrence6B1A1Row2Band3 recurrence6B1A1Row3Band3
  unfold remainder7Coefficient1TimesRemainder6Coefficient1Block3
  ring

def recurrence6B1A1Band4 : Coefficient :=
  recurrence6B1A1Row0Band4 +
  recurrence6B1A1Row1Band4 +
  recurrence6B1A1Row2Band4 +
  recurrence6B1A1Row3Band4 +
  recurrence6B1A1Row4Band4

theorem recurrence6B1A1Band4_eq :
    recurrence6B1A1Band4 = remainder7Coefficient1TimesRemainder6Coefficient1Block4 := by
  unfold recurrence6B1A1Band4 recurrence6B1A1Row0Band4 recurrence6B1A1Row1Band4
  unfold recurrence6B1A1Row2Band4 recurrence6B1A1Row3Band4 recurrence6B1A1Row4Band4
  unfold remainder7Coefficient1TimesRemainder6Coefficient1Block4
  ring

def recurrence6B1A1Band5 : Coefficient :=
  recurrence6B1A1Row0Band5 +
  recurrence6B1A1Row1Band5 +
  recurrence6B1A1Row2Band5 +
  recurrence6B1A1Row3Band5 +
  recurrence6B1A1Row4Band5 +
  recurrence6B1A1Row5Band5

theorem recurrence6B1A1Band5_eq :
    recurrence6B1A1Band5 = remainder7Coefficient1TimesRemainder6Coefficient1Block5 := by
  unfold recurrence6B1A1Band5 recurrence6B1A1Row0Band5 recurrence6B1A1Row1Band5
  unfold recurrence6B1A1Row2Band5 recurrence6B1A1Row3Band5 recurrence6B1A1Row4Band5
  unfold recurrence6B1A1Row5Band5 remainder7Coefficient1TimesRemainder6Coefficient1Block5
  ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
