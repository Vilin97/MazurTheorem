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
# Recurrence 6 Term2 bands 18–23

This file checks bands 18 through 23 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

def recurrence6Term2Band18 : Coefficient :=
  recurrence6Term2Row0Band18 +
  recurrence6Term2Row1Band18 +
  recurrence6Term2Row2Band18 +
  recurrence6Term2Row3Band18 +
  recurrence6Term2Row4Band18 +
  recurrence6Term2Row5Band18 +
  recurrence6Term2Row6Band18 +
  recurrence6Term2Row7Band18 +
  recurrence6Term2Row8Band18 +
  recurrence6Term2Row9Band18

theorem recurrence6Term2Band18_eq :
    recurrence6Term2Band18 = normalizedResidual6Term2Block18 := by
  unfold recurrence6Term2Band18 recurrence6Term2Row0Band18 recurrence6Term2Row1Band18
  unfold recurrence6Term2Row2Band18 recurrence6Term2Row3Band18 recurrence6Term2Row4Band18
  unfold recurrence6Term2Row5Band18 recurrence6Term2Row6Band18 recurrence6Term2Row7Band18
  unfold recurrence6Term2Row8Band18 recurrence6Term2Row9Band18 normalizedResidual6Term2Block18
  ring

def recurrence6Term2Band19 : Coefficient :=
  recurrence6Term2Row0Band19 +
  recurrence6Term2Row1Band19 +
  recurrence6Term2Row2Band19 +
  recurrence6Term2Row3Band19 +
  recurrence6Term2Row4Band19 +
  recurrence6Term2Row5Band19 +
  recurrence6Term2Row6Band19 +
  recurrence6Term2Row7Band19 +
  recurrence6Term2Row8Band19 +
  recurrence6Term2Row9Band19

theorem recurrence6Term2Band19_eq :
    recurrence6Term2Band19 = normalizedResidual6Term2Block19 := by
  unfold recurrence6Term2Band19 recurrence6Term2Row0Band19 recurrence6Term2Row1Band19
  unfold recurrence6Term2Row2Band19 recurrence6Term2Row3Band19 recurrence6Term2Row4Band19
  unfold recurrence6Term2Row5Band19 recurrence6Term2Row6Band19 recurrence6Term2Row7Band19
  unfold recurrence6Term2Row8Band19 recurrence6Term2Row9Band19 normalizedResidual6Term2Block19
  ring

def recurrence6Term2Band20 : Coefficient :=
  recurrence6Term2Row0Band20 +
  recurrence6Term2Row1Band20 +
  recurrence6Term2Row2Band20 +
  recurrence6Term2Row3Band20 +
  recurrence6Term2Row4Band20 +
  recurrence6Term2Row5Band20 +
  recurrence6Term2Row6Band20 +
  recurrence6Term2Row7Band20 +
  recurrence6Term2Row8Band20 +
  recurrence6Term2Row9Band20

theorem recurrence6Term2Band20_eq :
    recurrence6Term2Band20 = normalizedResidual6Term2Block20 := by
  unfold recurrence6Term2Band20 recurrence6Term2Row0Band20 recurrence6Term2Row1Band20
  unfold recurrence6Term2Row2Band20 recurrence6Term2Row3Band20 recurrence6Term2Row4Band20
  unfold recurrence6Term2Row5Band20 recurrence6Term2Row6Band20 recurrence6Term2Row7Band20
  unfold recurrence6Term2Row8Band20 recurrence6Term2Row9Band20 normalizedResidual6Term2Block20
  ring

def recurrence6Term2Band21 : Coefficient :=
  recurrence6Term2Row0Band21 +
  recurrence6Term2Row1Band21 +
  recurrence6Term2Row2Band21 +
  recurrence6Term2Row3Band21 +
  recurrence6Term2Row4Band21 +
  recurrence6Term2Row5Band21 +
  recurrence6Term2Row6Band21 +
  recurrence6Term2Row7Band21 +
  recurrence6Term2Row8Band21 +
  recurrence6Term2Row9Band21

theorem recurrence6Term2Band21_eq :
    recurrence6Term2Band21 = normalizedResidual6Term2Block21 := by
  unfold recurrence6Term2Band21 recurrence6Term2Row0Band21 recurrence6Term2Row1Band21
  unfold recurrence6Term2Row2Band21 recurrence6Term2Row3Band21 recurrence6Term2Row4Band21
  unfold recurrence6Term2Row5Band21 recurrence6Term2Row6Band21 recurrence6Term2Row7Band21
  unfold recurrence6Term2Row8Band21 recurrence6Term2Row9Band21 normalizedResidual6Term2Block21
  ring

def recurrence6Term2Band22 : Coefficient :=
  recurrence6Term2Row0Band22 +
  recurrence6Term2Row1Band22 +
  recurrence6Term2Row2Band22 +
  recurrence6Term2Row3Band22 +
  recurrence6Term2Row4Band22 +
  recurrence6Term2Row5Band22 +
  recurrence6Term2Row6Band22 +
  recurrence6Term2Row7Band22 +
  recurrence6Term2Row8Band22 +
  recurrence6Term2Row9Band22

theorem recurrence6Term2Band22_eq :
    recurrence6Term2Band22 = normalizedResidual6Term2Block22 := by
  unfold recurrence6Term2Band22 recurrence6Term2Row0Band22 recurrence6Term2Row1Band22
  unfold recurrence6Term2Row2Band22 recurrence6Term2Row3Band22 recurrence6Term2Row4Band22
  unfold recurrence6Term2Row5Band22 recurrence6Term2Row6Band22 recurrence6Term2Row7Band22
  unfold recurrence6Term2Row8Band22 recurrence6Term2Row9Band22 normalizedResidual6Term2Block22
  ring

def recurrence6Term2Band23 : Coefficient :=
  recurrence6Term2Row0Band23 +
  recurrence6Term2Row1Band23 +
  recurrence6Term2Row2Band23 +
  recurrence6Term2Row3Band23 +
  recurrence6Term2Row4Band23 +
  recurrence6Term2Row5Band23 +
  recurrence6Term2Row6Band23 +
  recurrence6Term2Row7Band23 +
  recurrence6Term2Row8Band23 +
  recurrence6Term2Row9Band23

theorem recurrence6Term2Band23_eq :
    recurrence6Term2Band23 = normalizedResidual6Term2Block23 := by
  unfold recurrence6Term2Band23 recurrence6Term2Row0Band23 recurrence6Term2Row1Band23
  unfold recurrence6Term2Row2Band23 recurrence6Term2Row3Band23 recurrence6Term2Row4Band23
  unfold recurrence6Term2Row5Band23 recurrence6Term2Row6Band23 recurrence6Term2Row7Band23
  unfold recurrence6Term2Row8Band23 recurrence6Term2Row9Band23 normalizedResidual6Term2Block23
  ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
