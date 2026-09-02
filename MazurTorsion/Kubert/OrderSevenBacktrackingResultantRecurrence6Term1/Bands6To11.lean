/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term1.Rows0To2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term1.Rows3To5
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term1.Rows6To8
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term1.Rows9To11
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6BlockData.NormalizedResidualTerm1
import Mathlib.Tactic.Ring

/-!
# Recurrence 6 Term1 bands 6–11

This file checks an independent group of band identities for Term1 of the sixth
pseudo-division recurrence.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

def recurrence6Term1Band6 : Coefficient :=
  recurrence6Term1Row0Band6 +
  recurrence6Term1Row1Band6 +
  recurrence6Term1Row2Band6 +
  recurrence6Term1Row3Band6 +
  recurrence6Term1Row4Band6 +
  recurrence6Term1Row5Band6 +
  recurrence6Term1Row6Band6

theorem recurrence6Term1Band6_eq :
    recurrence6Term1Band6 = normalizedResidual6Term1Block6 := by
  unfold recurrence6Term1Band6 recurrence6Term1Row0Band6 recurrence6Term1Row1Band6
  unfold recurrence6Term1Row2Band6 recurrence6Term1Row3Band6 recurrence6Term1Row4Band6
  unfold recurrence6Term1Row5Band6 recurrence6Term1Row6Band6 normalizedResidual6Term1Block6
  ring

def recurrence6Term1Band7 : Coefficient :=
  recurrence6Term1Row0Band7 +
  recurrence6Term1Row1Band7 +
  recurrence6Term1Row2Band7 +
  recurrence6Term1Row3Band7 +
  recurrence6Term1Row4Band7 +
  recurrence6Term1Row5Band7 +
  recurrence6Term1Row6Band7 +
  recurrence6Term1Row7Band7

theorem recurrence6Term1Band7_eq :
    recurrence6Term1Band7 = normalizedResidual6Term1Block7 := by
  unfold recurrence6Term1Band7 recurrence6Term1Row0Band7 recurrence6Term1Row1Band7
  unfold recurrence6Term1Row2Band7 recurrence6Term1Row3Band7 recurrence6Term1Row4Band7
  unfold recurrence6Term1Row5Band7 recurrence6Term1Row6Band7 recurrence6Term1Row7Band7
  unfold normalizedResidual6Term1Block7
  ring

def recurrence6Term1Band8 : Coefficient :=
  recurrence6Term1Row0Band8 +
  recurrence6Term1Row1Band8 +
  recurrence6Term1Row2Band8 +
  recurrence6Term1Row3Band8 +
  recurrence6Term1Row4Band8 +
  recurrence6Term1Row5Band8 +
  recurrence6Term1Row6Band8 +
  recurrence6Term1Row7Band8 +
  recurrence6Term1Row8Band8

theorem recurrence6Term1Band8_eq :
    recurrence6Term1Band8 = normalizedResidual6Term1Block8 := by
  unfold recurrence6Term1Band8 recurrence6Term1Row0Band8 recurrence6Term1Row1Band8
  unfold recurrence6Term1Row2Band8 recurrence6Term1Row3Band8 recurrence6Term1Row4Band8
  unfold recurrence6Term1Row5Band8 recurrence6Term1Row6Band8 recurrence6Term1Row7Band8
  unfold recurrence6Term1Row8Band8 normalizedResidual6Term1Block8
  ring

def recurrence6Term1Band9 : Coefficient :=
  recurrence6Term1Row0Band9 +
  recurrence6Term1Row1Band9 +
  recurrence6Term1Row2Band9 +
  recurrence6Term1Row3Band9 +
  recurrence6Term1Row4Band9 +
  recurrence6Term1Row5Band9 +
  recurrence6Term1Row6Band9 +
  recurrence6Term1Row7Band9 +
  recurrence6Term1Row8Band9 +
  recurrence6Term1Row9Band9

theorem recurrence6Term1Band9_eq :
    recurrence6Term1Band9 = normalizedResidual6Term1Block9 := by
  unfold recurrence6Term1Band9 recurrence6Term1Row0Band9 recurrence6Term1Row1Band9
  unfold recurrence6Term1Row2Band9 recurrence6Term1Row3Band9 recurrence6Term1Row4Band9
  unfold recurrence6Term1Row5Band9 recurrence6Term1Row6Band9 recurrence6Term1Row7Band9
  unfold recurrence6Term1Row8Band9 recurrence6Term1Row9Band9 normalizedResidual6Term1Block9
  ring

def recurrence6Term1Band10 : Coefficient :=
  recurrence6Term1Row0Band10 +
  recurrence6Term1Row1Band10 +
  recurrence6Term1Row2Band10 +
  recurrence6Term1Row3Band10 +
  recurrence6Term1Row4Band10 +
  recurrence6Term1Row5Band10 +
  recurrence6Term1Row6Band10 +
  recurrence6Term1Row7Band10 +
  recurrence6Term1Row8Band10 +
  recurrence6Term1Row9Band10 +
  recurrence6Term1Row10Band10

theorem recurrence6Term1Band10_eq :
    recurrence6Term1Band10 = normalizedResidual6Term1Block10 := by
  unfold recurrence6Term1Band10 recurrence6Term1Row0Band10 recurrence6Term1Row1Band10
  unfold recurrence6Term1Row2Band10 recurrence6Term1Row3Band10 recurrence6Term1Row4Band10
  unfold recurrence6Term1Row5Band10 recurrence6Term1Row6Band10 recurrence6Term1Row7Band10
  unfold recurrence6Term1Row8Band10 recurrence6Term1Row9Band10 recurrence6Term1Row10Band10
  unfold normalizedResidual6Term1Block10
  ring

def recurrence6Term1Band11 : Coefficient :=
  recurrence6Term1Row0Band11 +
  recurrence6Term1Row1Band11 +
  recurrence6Term1Row2Band11 +
  recurrence6Term1Row3Band11 +
  recurrence6Term1Row4Band11 +
  recurrence6Term1Row5Band11 +
  recurrence6Term1Row6Band11 +
  recurrence6Term1Row7Band11 +
  recurrence6Term1Row8Band11 +
  recurrence6Term1Row9Band11 +
  recurrence6Term1Row10Band11 +
  recurrence6Term1Row11Band11

theorem recurrence6Term1Band11_eq :
    recurrence6Term1Band11 = normalizedResidual6Term1Block11 := by
  unfold recurrence6Term1Band11 recurrence6Term1Row0Band11 recurrence6Term1Row1Band11
  unfold recurrence6Term1Row2Band11 recurrence6Term1Row3Band11 recurrence6Term1Row4Band11
  unfold recurrence6Term1Row5Band11 recurrence6Term1Row6Band11 recurrence6Term1Row7Band11
  unfold recurrence6Term1Row8Band11 recurrence6Term1Row9Band11 recurrence6Term1Row10Band11
  unfold recurrence6Term1Row11Band11 normalizedResidual6Term1Block11
  ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
