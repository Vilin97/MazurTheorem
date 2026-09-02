/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1Remainder2Data
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1RowData1

import Mathlib.Tactic.Ring

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1ShiftTerm1.Rows0To2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1ShiftTerm1.Rows3To5
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1ShiftTerm1.Rows6To7
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1ShiftTerm1.Rows8To10

/-!
# Recurrence 1 certificate: ShiftTerm1

This file is a checked bounded-band arithmetic shard for the first
pseudo-division recurrence in the order-seven branch-zero resultant certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

def recurrence1ShiftTerm1Band0 : Coefficient :=
  recurrence1ShiftTerm1Row0Band0

theorem recurrence1ShiftTerm1Band0_eq :
    recurrence1ShiftTerm1Band0 = recurrence1ShiftTerm1Block0 := by
  unfold recurrence1ShiftTerm1Band0 recurrence1ShiftTerm1Row0Band0 recurrence1ShiftTerm1Block0
  ring

def recurrence1ShiftTerm1Band1 : Coefficient :=
  recurrence1ShiftTerm1Row0Band1 +
  recurrence1ShiftTerm1Row1Band1

theorem recurrence1ShiftTerm1Band1_eq :
    recurrence1ShiftTerm1Band1 = recurrence1ShiftTerm1Block1 := by
  unfold recurrence1ShiftTerm1Band1 recurrence1ShiftTerm1Row0Band1 recurrence1ShiftTerm1Row1Band1
  unfold recurrence1ShiftTerm1Block1
  ring

def recurrence1ShiftTerm1Band2 : Coefficient :=
  recurrence1ShiftTerm1Row0Band2 +
  recurrence1ShiftTerm1Row1Band2 +
  recurrence1ShiftTerm1Row2Band2

theorem recurrence1ShiftTerm1Band2_eq :
    recurrence1ShiftTerm1Band2 = recurrence1ShiftTerm1Block2 := by
  unfold recurrence1ShiftTerm1Band2 recurrence1ShiftTerm1Row0Band2 recurrence1ShiftTerm1Row1Band2
  unfold recurrence1ShiftTerm1Row2Band2 recurrence1ShiftTerm1Block2
  ring

def recurrence1ShiftTerm1Band3 : Coefficient :=
  recurrence1ShiftTerm1Row0Band3 +
  recurrence1ShiftTerm1Row1Band3 +
  recurrence1ShiftTerm1Row2Band3 +
  recurrence1ShiftTerm1Row3Band3

theorem recurrence1ShiftTerm1Band3_eq :
    recurrence1ShiftTerm1Band3 = recurrence1ShiftTerm1Block3 := by
  unfold recurrence1ShiftTerm1Band3 recurrence1ShiftTerm1Row0Band3 recurrence1ShiftTerm1Row1Band3
  unfold recurrence1ShiftTerm1Row2Band3 recurrence1ShiftTerm1Row3Band3 recurrence1ShiftTerm1Block3
  ring

def recurrence1ShiftTerm1Band4 : Coefficient :=
  recurrence1ShiftTerm1Row0Band4 +
  recurrence1ShiftTerm1Row1Band4 +
  recurrence1ShiftTerm1Row2Band4 +
  recurrence1ShiftTerm1Row3Band4 +
  recurrence1ShiftTerm1Row4Band4

theorem recurrence1ShiftTerm1Band4_eq :
    recurrence1ShiftTerm1Band4 = recurrence1ShiftTerm1Block4 := by
  unfold recurrence1ShiftTerm1Band4 recurrence1ShiftTerm1Row0Band4 recurrence1ShiftTerm1Row1Band4
  unfold recurrence1ShiftTerm1Row2Band4 recurrence1ShiftTerm1Row3Band4
  unfold recurrence1ShiftTerm1Row4Band4 recurrence1ShiftTerm1Block4
  ring

def recurrence1ShiftTerm1Band5 : Coefficient :=
  recurrence1ShiftTerm1Row0Band5 +
  recurrence1ShiftTerm1Row1Band5 +
  recurrence1ShiftTerm1Row2Band5 +
  recurrence1ShiftTerm1Row3Band5 +
  recurrence1ShiftTerm1Row4Band5 +
  recurrence1ShiftTerm1Row5Band5

theorem recurrence1ShiftTerm1Band5_eq :
    recurrence1ShiftTerm1Band5 = recurrence1ShiftTerm1Block5 := by
  unfold recurrence1ShiftTerm1Band5 recurrence1ShiftTerm1Row0Band5 recurrence1ShiftTerm1Row1Band5
  unfold recurrence1ShiftTerm1Row2Band5 recurrence1ShiftTerm1Row3Band5
  unfold recurrence1ShiftTerm1Row4Band5 recurrence1ShiftTerm1Row5Band5 recurrence1ShiftTerm1Block5
  ring

def recurrence1ShiftTerm1Band6 : Coefficient :=
  recurrence1ShiftTerm1Row0Band6 +
  recurrence1ShiftTerm1Row1Band6 +
  recurrence1ShiftTerm1Row2Band6 +
  recurrence1ShiftTerm1Row3Band6 +
  recurrence1ShiftTerm1Row4Band6 +
  recurrence1ShiftTerm1Row5Band6 +
  recurrence1ShiftTerm1Row6Band6

theorem recurrence1ShiftTerm1Band6_eq :
    recurrence1ShiftTerm1Band6 = recurrence1ShiftTerm1Block6 := by
  unfold recurrence1ShiftTerm1Band6 recurrence1ShiftTerm1Row0Band6 recurrence1ShiftTerm1Row1Band6
  unfold recurrence1ShiftTerm1Row2Band6 recurrence1ShiftTerm1Row3Band6
  unfold recurrence1ShiftTerm1Row4Band6 recurrence1ShiftTerm1Row5Band6
  unfold recurrence1ShiftTerm1Row6Band6 recurrence1ShiftTerm1Block6
  ring

def recurrence1ShiftTerm1Band7 : Coefficient :=
  recurrence1ShiftTerm1Row0Band7 +
  recurrence1ShiftTerm1Row1Band7 +
  recurrence1ShiftTerm1Row2Band7 +
  recurrence1ShiftTerm1Row3Band7 +
  recurrence1ShiftTerm1Row4Band7 +
  recurrence1ShiftTerm1Row5Band7 +
  recurrence1ShiftTerm1Row6Band7 +
  recurrence1ShiftTerm1Row7Band7

theorem recurrence1ShiftTerm1Band7_eq :
    recurrence1ShiftTerm1Band7 = recurrence1ShiftTerm1Block7 := by
  unfold recurrence1ShiftTerm1Band7 recurrence1ShiftTerm1Row0Band7 recurrence1ShiftTerm1Row1Band7
  unfold recurrence1ShiftTerm1Row2Band7 recurrence1ShiftTerm1Row3Band7
  unfold recurrence1ShiftTerm1Row4Band7 recurrence1ShiftTerm1Row5Band7
  unfold recurrence1ShiftTerm1Row6Band7 recurrence1ShiftTerm1Row7Band7 recurrence1ShiftTerm1Block7
  ring

def recurrence1ShiftTerm1Band8 : Coefficient :=
  recurrence1ShiftTerm1Row0Band8 +
  recurrence1ShiftTerm1Row1Band8 +
  recurrence1ShiftTerm1Row2Band8 +
  recurrence1ShiftTerm1Row3Band8 +
  recurrence1ShiftTerm1Row4Band8 +
  recurrence1ShiftTerm1Row5Band8 +
  recurrence1ShiftTerm1Row6Band8 +
  recurrence1ShiftTerm1Row7Band8 +
  recurrence1ShiftTerm1Row8Band8

theorem recurrence1ShiftTerm1Band8_eq :
    recurrence1ShiftTerm1Band8 = recurrence1ShiftTerm1Block8 := by
  unfold recurrence1ShiftTerm1Band8 recurrence1ShiftTerm1Row0Band8 recurrence1ShiftTerm1Row1Band8
  unfold recurrence1ShiftTerm1Row2Band8 recurrence1ShiftTerm1Row3Band8
  unfold recurrence1ShiftTerm1Row4Band8 recurrence1ShiftTerm1Row5Band8
  unfold recurrence1ShiftTerm1Row6Band8 recurrence1ShiftTerm1Row7Band8
  unfold recurrence1ShiftTerm1Row8Band8 recurrence1ShiftTerm1Block8
  ring

def recurrence1ShiftTerm1Band9 : Coefficient :=
  recurrence1ShiftTerm1Row0Band9 +
  recurrence1ShiftTerm1Row1Band9 +
  recurrence1ShiftTerm1Row2Band9 +
  recurrence1ShiftTerm1Row3Band9 +
  recurrence1ShiftTerm1Row4Band9 +
  recurrence1ShiftTerm1Row5Band9 +
  recurrence1ShiftTerm1Row6Band9 +
  recurrence1ShiftTerm1Row7Band9 +
  recurrence1ShiftTerm1Row8Band9 +
  recurrence1ShiftTerm1Row9Band9

theorem recurrence1ShiftTerm1Band9_eq :
    recurrence1ShiftTerm1Band9 = recurrence1ShiftTerm1Block9 := by
  unfold recurrence1ShiftTerm1Band9 recurrence1ShiftTerm1Row0Band9 recurrence1ShiftTerm1Row1Band9
  unfold recurrence1ShiftTerm1Row2Band9 recurrence1ShiftTerm1Row3Band9
  unfold recurrence1ShiftTerm1Row4Band9 recurrence1ShiftTerm1Row5Band9
  unfold recurrence1ShiftTerm1Row6Band9 recurrence1ShiftTerm1Row7Band9
  unfold recurrence1ShiftTerm1Row8Band9 recurrence1ShiftTerm1Row9Band9 recurrence1ShiftTerm1Block9
  ring

def recurrence1ShiftTerm1Band10 : Coefficient :=
  recurrence1ShiftTerm1Row0Band10 +
  recurrence1ShiftTerm1Row1Band10 +
  recurrence1ShiftTerm1Row2Band10 +
  recurrence1ShiftTerm1Row3Band10 +
  recurrence1ShiftTerm1Row4Band10 +
  recurrence1ShiftTerm1Row5Band10 +
  recurrence1ShiftTerm1Row6Band10 +
  recurrence1ShiftTerm1Row7Band10 +
  recurrence1ShiftTerm1Row8Band10 +
  recurrence1ShiftTerm1Row9Band10 +
  recurrence1ShiftTerm1Row10Band10

theorem recurrence1ShiftTerm1Band10_eq :
    recurrence1ShiftTerm1Band10 = recurrence1ShiftTerm1Block10 := by
  unfold recurrence1ShiftTerm1Band10 recurrence1ShiftTerm1Row0Band10 recurrence1ShiftTerm1Row1Band10
  unfold recurrence1ShiftTerm1Row2Band10 recurrence1ShiftTerm1Row3Band10
  unfold recurrence1ShiftTerm1Row4Band10 recurrence1ShiftTerm1Row5Band10
  unfold recurrence1ShiftTerm1Row6Band10 recurrence1ShiftTerm1Row7Band10
  unfold recurrence1ShiftTerm1Row8Band10 recurrence1ShiftTerm1Row9Band10
  unfold recurrence1ShiftTerm1Row10Band10 recurrence1ShiftTerm1Block10
  ring

def recurrence1ShiftTerm1Band11 : Coefficient :=
  recurrence1ShiftTerm1Row0Band11 +
  recurrence1ShiftTerm1Row1Band11 +
  recurrence1ShiftTerm1Row2Band11 +
  recurrence1ShiftTerm1Row3Band11 +
  recurrence1ShiftTerm1Row4Band11 +
  recurrence1ShiftTerm1Row5Band11 +
  recurrence1ShiftTerm1Row6Band11 +
  recurrence1ShiftTerm1Row7Band11 +
  recurrence1ShiftTerm1Row8Band11 +
  recurrence1ShiftTerm1Row9Band11 +
  recurrence1ShiftTerm1Row10Band11

theorem recurrence1ShiftTerm1Band11_eq :
    recurrence1ShiftTerm1Band11 = recurrence1ShiftTerm1Block11 := by
  unfold recurrence1ShiftTerm1Band11 recurrence1ShiftTerm1Row0Band11 recurrence1ShiftTerm1Row1Band11
  unfold recurrence1ShiftTerm1Row2Band11 recurrence1ShiftTerm1Row3Band11
  unfold recurrence1ShiftTerm1Row4Band11 recurrence1ShiftTerm1Row5Band11
  unfold recurrence1ShiftTerm1Row6Band11 recurrence1ShiftTerm1Row7Band11
  unfold recurrence1ShiftTerm1Row8Band11 recurrence1ShiftTerm1Row9Band11
  unfold recurrence1ShiftTerm1Row10Band11 recurrence1ShiftTerm1Block11
  ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
