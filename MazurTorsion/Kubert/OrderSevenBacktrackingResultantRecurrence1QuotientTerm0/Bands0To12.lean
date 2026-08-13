/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1Remainder2Data
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1CommonData
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1RowData0

import Mathlib.Tactic.Ring

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1QuotientTerm0.Rows0To2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1QuotientTerm0.Rows3To5
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1QuotientTerm0.Rows6To7
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1QuotientTerm0.Rows8To10

/-!
# Recurrence 1 certificate: QuotientTerm0

This file is a checked bounded-band arithmetic shard for the first
pseudo-division recurrence in the order-seven branch-zero resultant certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

def recurrence1QuotientTerm0Band0 : Coefficient :=
  recurrence1QuotientTerm0Row0Band0

theorem recurrence1QuotientTerm0Band0_eq :
    recurrence1QuotientTerm0Band0 = recurrence1QuotientTerm0Block0 := by
  unfold recurrence1QuotientTerm0Band0 recurrence1QuotientTerm0Row0Band0
  unfold recurrence1QuotientTerm0Block0
  ring

def recurrence1QuotientTerm0Band1 : Coefficient :=
  recurrence1QuotientTerm0Row0Band1 +
  recurrence1QuotientTerm0Row1Band1

theorem recurrence1QuotientTerm0Band1_eq :
    recurrence1QuotientTerm0Band1 = recurrence1QuotientTerm0Block1 := by
  unfold recurrence1QuotientTerm0Band1 recurrence1QuotientTerm0Row0Band1
  unfold recurrence1QuotientTerm0Row1Band1 recurrence1QuotientTerm0Block1
  ring

def recurrence1QuotientTerm0Band2 : Coefficient :=
  recurrence1QuotientTerm0Row0Band2 +
  recurrence1QuotientTerm0Row1Band2 +
  recurrence1QuotientTerm0Row2Band2

theorem recurrence1QuotientTerm0Band2_eq :
    recurrence1QuotientTerm0Band2 = recurrence1QuotientTerm0Block2 := by
  unfold recurrence1QuotientTerm0Band2 recurrence1QuotientTerm0Row0Band2
  unfold recurrence1QuotientTerm0Row1Band2 recurrence1QuotientTerm0Row2Band2
  unfold recurrence1QuotientTerm0Block2
  ring

def recurrence1QuotientTerm0Band3 : Coefficient :=
  recurrence1QuotientTerm0Row0Band3 +
  recurrence1QuotientTerm0Row1Band3 +
  recurrence1QuotientTerm0Row2Band3 +
  recurrence1QuotientTerm0Row3Band3

theorem recurrence1QuotientTerm0Band3_eq :
    recurrence1QuotientTerm0Band3 = recurrence1QuotientTerm0Block3 := by
  unfold recurrence1QuotientTerm0Band3 recurrence1QuotientTerm0Row0Band3
  unfold recurrence1QuotientTerm0Row1Band3 recurrence1QuotientTerm0Row2Band3
  unfold recurrence1QuotientTerm0Row3Band3 recurrence1QuotientTerm0Block3
  ring

def recurrence1QuotientTerm0Band4 : Coefficient :=
  recurrence1QuotientTerm0Row0Band4 +
  recurrence1QuotientTerm0Row1Band4 +
  recurrence1QuotientTerm0Row2Band4 +
  recurrence1QuotientTerm0Row3Band4 +
  recurrence1QuotientTerm0Row4Band4

theorem recurrence1QuotientTerm0Band4_eq :
    recurrence1QuotientTerm0Band4 = recurrence1QuotientTerm0Block4 := by
  unfold recurrence1QuotientTerm0Band4 recurrence1QuotientTerm0Row0Band4
  unfold recurrence1QuotientTerm0Row1Band4 recurrence1QuotientTerm0Row2Band4
  unfold recurrence1QuotientTerm0Row3Band4 recurrence1QuotientTerm0Row4Band4
  unfold recurrence1QuotientTerm0Block4
  ring

def recurrence1QuotientTerm0Band5 : Coefficient :=
  recurrence1QuotientTerm0Row0Band5 +
  recurrence1QuotientTerm0Row1Band5 +
  recurrence1QuotientTerm0Row2Band5 +
  recurrence1QuotientTerm0Row3Band5 +
  recurrence1QuotientTerm0Row4Band5 +
  recurrence1QuotientTerm0Row5Band5

theorem recurrence1QuotientTerm0Band5_eq :
    recurrence1QuotientTerm0Band5 = recurrence1QuotientTerm0Block5 := by
  unfold recurrence1QuotientTerm0Band5 recurrence1QuotientTerm0Row0Band5
  unfold recurrence1QuotientTerm0Row1Band5 recurrence1QuotientTerm0Row2Band5
  unfold recurrence1QuotientTerm0Row3Band5 recurrence1QuotientTerm0Row4Band5
  unfold recurrence1QuotientTerm0Row5Band5 recurrence1QuotientTerm0Block5
  ring

def recurrence1QuotientTerm0Band6 : Coefficient :=
  recurrence1QuotientTerm0Row0Band6 +
  recurrence1QuotientTerm0Row1Band6 +
  recurrence1QuotientTerm0Row2Band6 +
  recurrence1QuotientTerm0Row3Band6 +
  recurrence1QuotientTerm0Row4Band6 +
  recurrence1QuotientTerm0Row5Band6 +
  recurrence1QuotientTerm0Row6Band6

theorem recurrence1QuotientTerm0Band6_eq :
    recurrence1QuotientTerm0Band6 = recurrence1QuotientTerm0Block6 := by
  unfold recurrence1QuotientTerm0Band6 recurrence1QuotientTerm0Row0Band6
  unfold recurrence1QuotientTerm0Row1Band6 recurrence1QuotientTerm0Row2Band6
  unfold recurrence1QuotientTerm0Row3Band6 recurrence1QuotientTerm0Row4Band6
  unfold recurrence1QuotientTerm0Row5Band6 recurrence1QuotientTerm0Row6Band6
  unfold recurrence1QuotientTerm0Block6
  ring

def recurrence1QuotientTerm0Band7 : Coefficient :=
  recurrence1QuotientTerm0Row0Band7 +
  recurrence1QuotientTerm0Row1Band7 +
  recurrence1QuotientTerm0Row2Band7 +
  recurrence1QuotientTerm0Row3Band7 +
  recurrence1QuotientTerm0Row4Band7 +
  recurrence1QuotientTerm0Row5Band7 +
  recurrence1QuotientTerm0Row6Band7 +
  recurrence1QuotientTerm0Row7Band7

theorem recurrence1QuotientTerm0Band7_eq :
    recurrence1QuotientTerm0Band7 = recurrence1QuotientTerm0Block7 := by
  unfold recurrence1QuotientTerm0Band7 recurrence1QuotientTerm0Row0Band7
  unfold recurrence1QuotientTerm0Row1Band7 recurrence1QuotientTerm0Row2Band7
  unfold recurrence1QuotientTerm0Row3Band7 recurrence1QuotientTerm0Row4Band7
  unfold recurrence1QuotientTerm0Row5Band7 recurrence1QuotientTerm0Row6Band7
  unfold recurrence1QuotientTerm0Row7Band7 recurrence1QuotientTerm0Block7
  ring

def recurrence1QuotientTerm0Band8 : Coefficient :=
  recurrence1QuotientTerm0Row0Band8 +
  recurrence1QuotientTerm0Row1Band8 +
  recurrence1QuotientTerm0Row2Band8 +
  recurrence1QuotientTerm0Row3Band8 +
  recurrence1QuotientTerm0Row4Band8 +
  recurrence1QuotientTerm0Row5Band8 +
  recurrence1QuotientTerm0Row6Band8 +
  recurrence1QuotientTerm0Row7Band8 +
  recurrence1QuotientTerm0Row8Band8

theorem recurrence1QuotientTerm0Band8_eq :
    recurrence1QuotientTerm0Band8 = recurrence1QuotientTerm0Block8 := by
  unfold recurrence1QuotientTerm0Band8 recurrence1QuotientTerm0Row0Band8
  unfold recurrence1QuotientTerm0Row1Band8 recurrence1QuotientTerm0Row2Band8
  unfold recurrence1QuotientTerm0Row3Band8 recurrence1QuotientTerm0Row4Band8
  unfold recurrence1QuotientTerm0Row5Band8 recurrence1QuotientTerm0Row6Band8
  unfold recurrence1QuotientTerm0Row7Band8 recurrence1QuotientTerm0Row8Band8
  unfold recurrence1QuotientTerm0Block8
  ring

def recurrence1QuotientTerm0Band9 : Coefficient :=
  recurrence1QuotientTerm0Row0Band9 +
  recurrence1QuotientTerm0Row1Band9 +
  recurrence1QuotientTerm0Row2Band9 +
  recurrence1QuotientTerm0Row3Band9 +
  recurrence1QuotientTerm0Row4Band9 +
  recurrence1QuotientTerm0Row5Band9 +
  recurrence1QuotientTerm0Row6Band9 +
  recurrence1QuotientTerm0Row7Band9 +
  recurrence1QuotientTerm0Row8Band9 +
  recurrence1QuotientTerm0Row9Band9

theorem recurrence1QuotientTerm0Band9_eq :
    recurrence1QuotientTerm0Band9 = recurrence1QuotientTerm0Block9 := by
  unfold recurrence1QuotientTerm0Band9 recurrence1QuotientTerm0Row0Band9
  unfold recurrence1QuotientTerm0Row1Band9 recurrence1QuotientTerm0Row2Band9
  unfold recurrence1QuotientTerm0Row3Band9 recurrence1QuotientTerm0Row4Band9
  unfold recurrence1QuotientTerm0Row5Band9 recurrence1QuotientTerm0Row6Band9
  unfold recurrence1QuotientTerm0Row7Band9 recurrence1QuotientTerm0Row8Band9
  unfold recurrence1QuotientTerm0Row9Band9 recurrence1QuotientTerm0Block9
  ring

def recurrence1QuotientTerm0Band10 : Coefficient :=
  recurrence1QuotientTerm0Row0Band10 +
  recurrence1QuotientTerm0Row1Band10 +
  recurrence1QuotientTerm0Row2Band10 +
  recurrence1QuotientTerm0Row3Band10 +
  recurrence1QuotientTerm0Row4Band10 +
  recurrence1QuotientTerm0Row5Band10 +
  recurrence1QuotientTerm0Row6Band10 +
  recurrence1QuotientTerm0Row7Band10 +
  recurrence1QuotientTerm0Row8Band10 +
  recurrence1QuotientTerm0Row9Band10 +
  recurrence1QuotientTerm0Row10Band10

theorem recurrence1QuotientTerm0Band10_eq :
    recurrence1QuotientTerm0Band10 = recurrence1QuotientTerm0Block10 := by
  unfold recurrence1QuotientTerm0Band10 recurrence1QuotientTerm0Row0Band10
  unfold recurrence1QuotientTerm0Row1Band10 recurrence1QuotientTerm0Row2Band10
  unfold recurrence1QuotientTerm0Row3Band10 recurrence1QuotientTerm0Row4Band10
  unfold recurrence1QuotientTerm0Row5Band10 recurrence1QuotientTerm0Row6Band10
  unfold recurrence1QuotientTerm0Row7Band10 recurrence1QuotientTerm0Row8Band10
  unfold recurrence1QuotientTerm0Row9Band10 recurrence1QuotientTerm0Row10Band10
  unfold recurrence1QuotientTerm0Block10
  ring

def recurrence1QuotientTerm0Band11 : Coefficient :=
  recurrence1QuotientTerm0Row0Band11 +
  recurrence1QuotientTerm0Row1Band11 +
  recurrence1QuotientTerm0Row2Band11 +
  recurrence1QuotientTerm0Row3Band11 +
  recurrence1QuotientTerm0Row4Band11 +
  recurrence1QuotientTerm0Row5Band11 +
  recurrence1QuotientTerm0Row6Band11 +
  recurrence1QuotientTerm0Row7Band11 +
  recurrence1QuotientTerm0Row8Band11 +
  recurrence1QuotientTerm0Row9Band11 +
  recurrence1QuotientTerm0Row10Band11

theorem recurrence1QuotientTerm0Band11_eq :
    recurrence1QuotientTerm0Band11 = recurrence1QuotientTerm0Block11 := by
  unfold recurrence1QuotientTerm0Band11 recurrence1QuotientTerm0Row0Band11
  unfold recurrence1QuotientTerm0Row1Band11 recurrence1QuotientTerm0Row2Band11
  unfold recurrence1QuotientTerm0Row3Band11 recurrence1QuotientTerm0Row4Band11
  unfold recurrence1QuotientTerm0Row5Band11 recurrence1QuotientTerm0Row6Band11
  unfold recurrence1QuotientTerm0Row7Band11 recurrence1QuotientTerm0Row8Band11
  unfold recurrence1QuotientTerm0Row9Band11 recurrence1QuotientTerm0Row10Band11
  unfold recurrence1QuotientTerm0Block11
  ring

def recurrence1QuotientTerm0Band12 : Coefficient :=
  recurrence1QuotientTerm0Row0Band12 +
  recurrence1QuotientTerm0Row1Band12 +
  recurrence1QuotientTerm0Row2Band12 +
  recurrence1QuotientTerm0Row3Band12 +
  recurrence1QuotientTerm0Row4Band12 +
  recurrence1QuotientTerm0Row5Band12 +
  recurrence1QuotientTerm0Row6Band12 +
  recurrence1QuotientTerm0Row7Band12 +
  recurrence1QuotientTerm0Row8Band12 +
  recurrence1QuotientTerm0Row9Band12 +
  recurrence1QuotientTerm0Row10Band12

theorem recurrence1QuotientTerm0Band12_eq :
    recurrence1QuotientTerm0Band12 = recurrence1QuotientTerm0Block12 := by
  unfold recurrence1QuotientTerm0Band12 recurrence1QuotientTerm0Row0Band12
  unfold recurrence1QuotientTerm0Row1Band12 recurrence1QuotientTerm0Row2Band12
  unfold recurrence1QuotientTerm0Row3Band12 recurrence1QuotientTerm0Row4Band12
  unfold recurrence1QuotientTerm0Row5Band12 recurrence1QuotientTerm0Row6Band12
  unfold recurrence1QuotientTerm0Row7Band12 recurrence1QuotientTerm0Row8Band12
  unfold recurrence1QuotientTerm0Row9Band12 recurrence1QuotientTerm0Row10Band12
  unfold recurrence1QuotientTerm0Block12
  ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
