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
# Recurrence 6 B0A2 bands 6–11

This file checks bands 6 through 11 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

def recurrence6B0A2Band6 : Coefficient :=
  recurrence6B0A2Row0Band6 +
  recurrence6B0A2Row1Band6 +
  recurrence6B0A2Row2Band6 +
  recurrence6B0A2Row3Band6 +
  recurrence6B0A2Row4Band6 +
  recurrence6B0A2Row5Band6 +
  recurrence6B0A2Row6Band6

theorem recurrence6B0A2Band6_eq :
    recurrence6B0A2Band6 = remainder7Coefficient0TimesRemainder6Coefficient2Block6 := by
  unfold recurrence6B0A2Band6 recurrence6B0A2Row0Band6 recurrence6B0A2Row1Band6
  unfold recurrence6B0A2Row2Band6 recurrence6B0A2Row3Band6 recurrence6B0A2Row4Band6
  unfold recurrence6B0A2Row5Band6 recurrence6B0A2Row6Band6
  unfold remainder7Coefficient0TimesRemainder6Coefficient2Block6
  ring

def recurrence6B0A2Band7 : Coefficient :=
  recurrence6B0A2Row0Band7 +
  recurrence6B0A2Row1Band7 +
  recurrence6B0A2Row2Band7 +
  recurrence6B0A2Row3Band7 +
  recurrence6B0A2Row4Band7 +
  recurrence6B0A2Row5Band7 +
  recurrence6B0A2Row6Band7 +
  recurrence6B0A2Row7Band7

theorem recurrence6B0A2Band7_eq :
    recurrence6B0A2Band7 = remainder7Coefficient0TimesRemainder6Coefficient2Block7 := by
  unfold recurrence6B0A2Band7 recurrence6B0A2Row0Band7 recurrence6B0A2Row1Band7
  unfold recurrence6B0A2Row2Band7 recurrence6B0A2Row3Band7 recurrence6B0A2Row4Band7
  unfold recurrence6B0A2Row5Band7 recurrence6B0A2Row6Band7 recurrence6B0A2Row7Band7
  unfold remainder7Coefficient0TimesRemainder6Coefficient2Block7
  ring

def recurrence6B0A2Band8 : Coefficient :=
  recurrence6B0A2Row0Band8 +
  recurrence6B0A2Row1Band8 +
  recurrence6B0A2Row2Band8 +
  recurrence6B0A2Row3Band8 +
  recurrence6B0A2Row4Band8 +
  recurrence6B0A2Row5Band8 +
  recurrence6B0A2Row6Band8 +
  recurrence6B0A2Row7Band8 +
  recurrence6B0A2Row8Band8

theorem recurrence6B0A2Band8_eq :
    recurrence6B0A2Band8 = remainder7Coefficient0TimesRemainder6Coefficient2Block8 := by
  unfold recurrence6B0A2Band8 recurrence6B0A2Row0Band8 recurrence6B0A2Row1Band8
  unfold recurrence6B0A2Row2Band8 recurrence6B0A2Row3Band8 recurrence6B0A2Row4Band8
  unfold recurrence6B0A2Row5Band8 recurrence6B0A2Row6Band8 recurrence6B0A2Row7Band8
  unfold recurrence6B0A2Row8Band8 remainder7Coefficient0TimesRemainder6Coefficient2Block8
  ring

def recurrence6B0A2Band9 : Coefficient :=
  recurrence6B0A2Row0Band9 +
  recurrence6B0A2Row1Band9 +
  recurrence6B0A2Row2Band9 +
  recurrence6B0A2Row3Band9 +
  recurrence6B0A2Row4Band9 +
  recurrence6B0A2Row5Band9 +
  recurrence6B0A2Row6Band9 +
  recurrence6B0A2Row7Band9 +
  recurrence6B0A2Row8Band9 +
  recurrence6B0A2Row9Band9

theorem recurrence6B0A2Band9_eq :
    recurrence6B0A2Band9 = remainder7Coefficient0TimesRemainder6Coefficient2Block9 := by
  unfold recurrence6B0A2Band9 recurrence6B0A2Row0Band9 recurrence6B0A2Row1Band9
  unfold recurrence6B0A2Row2Band9 recurrence6B0A2Row3Band9 recurrence6B0A2Row4Band9
  unfold recurrence6B0A2Row5Band9 recurrence6B0A2Row6Band9 recurrence6B0A2Row7Band9
  unfold recurrence6B0A2Row8Band9 recurrence6B0A2Row9Band9
  unfold remainder7Coefficient0TimesRemainder6Coefficient2Block9
  ring

def recurrence6B0A2Band10 : Coefficient :=
  recurrence6B0A2Row0Band10 +
  recurrence6B0A2Row1Band10 +
  recurrence6B0A2Row2Band10 +
  recurrence6B0A2Row3Band10 +
  recurrence6B0A2Row4Band10 +
  recurrence6B0A2Row5Band10 +
  recurrence6B0A2Row6Band10 +
  recurrence6B0A2Row7Band10 +
  recurrence6B0A2Row8Band10 +
  recurrence6B0A2Row9Band10

theorem recurrence6B0A2Band10_eq :
    recurrence6B0A2Band10 = remainder7Coefficient0TimesRemainder6Coefficient2Block10 := by
  unfold recurrence6B0A2Band10 recurrence6B0A2Row0Band10 recurrence6B0A2Row1Band10
  unfold recurrence6B0A2Row2Band10 recurrence6B0A2Row3Band10 recurrence6B0A2Row4Band10
  unfold recurrence6B0A2Row5Band10 recurrence6B0A2Row6Band10 recurrence6B0A2Row7Band10
  unfold recurrence6B0A2Row8Band10 recurrence6B0A2Row9Band10
  unfold remainder7Coefficient0TimesRemainder6Coefficient2Block10
  ring

def recurrence6B0A2Band11 : Coefficient :=
  recurrence6B0A2Row0Band11 +
  recurrence6B0A2Row1Band11 +
  recurrence6B0A2Row2Band11 +
  recurrence6B0A2Row3Band11 +
  recurrence6B0A2Row4Band11 +
  recurrence6B0A2Row5Band11 +
  recurrence6B0A2Row6Band11 +
  recurrence6B0A2Row7Band11 +
  recurrence6B0A2Row8Band11 +
  recurrence6B0A2Row9Band11

theorem recurrence6B0A2Band11_eq :
    recurrence6B0A2Band11 = remainder7Coefficient0TimesRemainder6Coefficient2Block11 := by
  unfold recurrence6B0A2Band11 recurrence6B0A2Row0Band11 recurrence6B0A2Row1Band11
  unfold recurrence6B0A2Row2Band11 recurrence6B0A2Row3Band11 recurrence6B0A2Row4Band11
  unfold recurrence6B0A2Row5Band11 recurrence6B0A2Row6Band11 recurrence6B0A2Row7Band11
  unfold recurrence6B0A2Row8Band11 recurrence6B0A2Row9Band11
  unfold remainder7Coefficient0TimesRemainder6Coefficient2Block11
  ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
