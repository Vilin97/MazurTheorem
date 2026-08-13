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
# Recurrence 6 B1A1 bands 6–11

This file checks bands 6 through 11 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

def recurrence6B1A1Band6 : Coefficient :=
  recurrence6B1A1Row0Band6 +
  recurrence6B1A1Row1Band6 +
  recurrence6B1A1Row2Band6 +
  recurrence6B1A1Row3Band6 +
  recurrence6B1A1Row4Band6 +
  recurrence6B1A1Row5Band6 +
  recurrence6B1A1Row6Band6

theorem recurrence6B1A1Band6_eq :
    recurrence6B1A1Band6 = remainder7Coefficient1TimesRemainder6Coefficient1Block6 := by
  unfold recurrence6B1A1Band6 recurrence6B1A1Row0Band6 recurrence6B1A1Row1Band6
  unfold recurrence6B1A1Row2Band6 recurrence6B1A1Row3Band6 recurrence6B1A1Row4Band6
  unfold recurrence6B1A1Row5Band6 recurrence6B1A1Row6Band6
  unfold remainder7Coefficient1TimesRemainder6Coefficient1Block6
  ring

def recurrence6B1A1Band7 : Coefficient :=
  recurrence6B1A1Row0Band7 +
  recurrence6B1A1Row1Band7 +
  recurrence6B1A1Row2Band7 +
  recurrence6B1A1Row3Band7 +
  recurrence6B1A1Row4Band7 +
  recurrence6B1A1Row5Band7 +
  recurrence6B1A1Row6Band7 +
  recurrence6B1A1Row7Band7

theorem recurrence6B1A1Band7_eq :
    recurrence6B1A1Band7 = remainder7Coefficient1TimesRemainder6Coefficient1Block7 := by
  unfold recurrence6B1A1Band7 recurrence6B1A1Row0Band7 recurrence6B1A1Row1Band7
  unfold recurrence6B1A1Row2Band7 recurrence6B1A1Row3Band7 recurrence6B1A1Row4Band7
  unfold recurrence6B1A1Row5Band7 recurrence6B1A1Row6Band7 recurrence6B1A1Row7Band7
  unfold remainder7Coefficient1TimesRemainder6Coefficient1Block7
  ring

def recurrence6B1A1Band8 : Coefficient :=
  recurrence6B1A1Row0Band8 +
  recurrence6B1A1Row1Band8 +
  recurrence6B1A1Row2Band8 +
  recurrence6B1A1Row3Band8 +
  recurrence6B1A1Row4Band8 +
  recurrence6B1A1Row5Band8 +
  recurrence6B1A1Row6Band8 +
  recurrence6B1A1Row7Band8 +
  recurrence6B1A1Row8Band8

theorem recurrence6B1A1Band8_eq :
    recurrence6B1A1Band8 = remainder7Coefficient1TimesRemainder6Coefficient1Block8 := by
  unfold recurrence6B1A1Band8 recurrence6B1A1Row0Band8 recurrence6B1A1Row1Band8
  unfold recurrence6B1A1Row2Band8 recurrence6B1A1Row3Band8 recurrence6B1A1Row4Band8
  unfold recurrence6B1A1Row5Band8 recurrence6B1A1Row6Band8 recurrence6B1A1Row7Band8
  unfold recurrence6B1A1Row8Band8 remainder7Coefficient1TimesRemainder6Coefficient1Block8
  ring

def recurrence6B1A1Band9 : Coefficient :=
  recurrence6B1A1Row0Band9 +
  recurrence6B1A1Row1Band9 +
  recurrence6B1A1Row2Band9 +
  recurrence6B1A1Row3Band9 +
  recurrence6B1A1Row4Band9 +
  recurrence6B1A1Row5Band9 +
  recurrence6B1A1Row6Band9 +
  recurrence6B1A1Row7Band9 +
  recurrence6B1A1Row8Band9 +
  recurrence6B1A1Row9Band9

theorem recurrence6B1A1Band9_eq :
    recurrence6B1A1Band9 = remainder7Coefficient1TimesRemainder6Coefficient1Block9 := by
  unfold recurrence6B1A1Band9 recurrence6B1A1Row0Band9 recurrence6B1A1Row1Band9
  unfold recurrence6B1A1Row2Band9 recurrence6B1A1Row3Band9 recurrence6B1A1Row4Band9
  unfold recurrence6B1A1Row5Band9 recurrence6B1A1Row6Band9 recurrence6B1A1Row7Band9
  unfold recurrence6B1A1Row8Band9 recurrence6B1A1Row9Band9
  unfold remainder7Coefficient1TimesRemainder6Coefficient1Block9
  ring

def recurrence6B1A1Band10 : Coefficient :=
  recurrence6B1A1Row0Band10 +
  recurrence6B1A1Row1Band10 +
  recurrence6B1A1Row2Band10 +
  recurrence6B1A1Row3Band10 +
  recurrence6B1A1Row4Band10 +
  recurrence6B1A1Row5Band10 +
  recurrence6B1A1Row6Band10 +
  recurrence6B1A1Row7Band10 +
  recurrence6B1A1Row8Band10 +
  recurrence6B1A1Row9Band10

theorem recurrence6B1A1Band10_eq :
    recurrence6B1A1Band10 = remainder7Coefficient1TimesRemainder6Coefficient1Block10 := by
  unfold recurrence6B1A1Band10 recurrence6B1A1Row0Band10 recurrence6B1A1Row1Band10
  unfold recurrence6B1A1Row2Band10 recurrence6B1A1Row3Band10 recurrence6B1A1Row4Band10
  unfold recurrence6B1A1Row5Band10 recurrence6B1A1Row6Band10 recurrence6B1A1Row7Band10
  unfold recurrence6B1A1Row8Band10 recurrence6B1A1Row9Band10
  unfold remainder7Coefficient1TimesRemainder6Coefficient1Block10
  ring

def recurrence6B1A1Band11 : Coefficient :=
  recurrence6B1A1Row0Band11 +
  recurrence6B1A1Row1Band11 +
  recurrence6B1A1Row2Band11 +
  recurrence6B1A1Row3Band11 +
  recurrence6B1A1Row4Band11 +
  recurrence6B1A1Row5Band11 +
  recurrence6B1A1Row6Band11 +
  recurrence6B1A1Row7Band11 +
  recurrence6B1A1Row8Band11 +
  recurrence6B1A1Row9Band11

theorem recurrence6B1A1Band11_eq :
    recurrence6B1A1Band11 = remainder7Coefficient1TimesRemainder6Coefficient1Block11 := by
  unfold recurrence6B1A1Band11 recurrence6B1A1Row0Band11 recurrence6B1A1Row1Band11
  unfold recurrence6B1A1Row2Band11 recurrence6B1A1Row3Band11 recurrence6B1A1Row4Band11
  unfold recurrence6B1A1Row5Band11 recurrence6B1A1Row6Band11 recurrence6B1A1Row7Band11
  unfold recurrence6B1A1Row8Band11 recurrence6B1A1Row9Band11
  unfold remainder7Coefficient1TimesRemainder6Coefficient1Block11
  ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
