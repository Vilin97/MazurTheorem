/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1Remainder2Data
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1CommonData
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1RowData1

import Mathlib.Tactic.Ring

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1QuotientTerm1.Rows0To2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1QuotientTerm1.Rows3To5
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1QuotientTerm1.Rows6To7
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1QuotientTerm1.Rows8To10

/-!
# Recurrence 1 certificate: QuotientTerm1

This file is a checked bounded-band arithmetic shard for the first
pseudo-division recurrence in the order-seven branch-zero resultant certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

def recurrence1QuotientTerm1Band12 : Coefficient :=
  recurrence1QuotientTerm1Row0Band12 +
  recurrence1QuotientTerm1Row1Band12 +
  recurrence1QuotientTerm1Row2Band12 +
  recurrence1QuotientTerm1Row3Band12 +
  recurrence1QuotientTerm1Row4Band12 +
  recurrence1QuotientTerm1Row5Band12 +
  recurrence1QuotientTerm1Row6Band12 +
  recurrence1QuotientTerm1Row7Band12 +
  recurrence1QuotientTerm1Row8Band12 +
  recurrence1QuotientTerm1Row9Band12 +
  recurrence1QuotientTerm1Row10Band12

theorem recurrence1QuotientTerm1Band12_eq :
    recurrence1QuotientTerm1Band12 = recurrence1QuotientTerm1Block12 := by
  unfold recurrence1QuotientTerm1Band12 recurrence1QuotientTerm1Row0Band12
  unfold recurrence1QuotientTerm1Row1Band12 recurrence1QuotientTerm1Row2Band12
  unfold recurrence1QuotientTerm1Row3Band12 recurrence1QuotientTerm1Row4Band12
  unfold recurrence1QuotientTerm1Row5Band12 recurrence1QuotientTerm1Row6Band12
  unfold recurrence1QuotientTerm1Row7Band12 recurrence1QuotientTerm1Row8Band12
  unfold recurrence1QuotientTerm1Row9Band12 recurrence1QuotientTerm1Row10Band12
  unfold recurrence1QuotientTerm1Block12
  ring

def recurrence1QuotientTerm1Band13 : Coefficient :=
  recurrence1QuotientTerm1Row0Band13 +
  recurrence1QuotientTerm1Row1Band13 +
  recurrence1QuotientTerm1Row2Band13 +
  recurrence1QuotientTerm1Row3Band13 +
  recurrence1QuotientTerm1Row4Band13 +
  recurrence1QuotientTerm1Row5Band13 +
  recurrence1QuotientTerm1Row6Band13 +
  recurrence1QuotientTerm1Row7Band13 +
  recurrence1QuotientTerm1Row8Band13 +
  recurrence1QuotientTerm1Row9Band13 +
  recurrence1QuotientTerm1Row10Band13

theorem recurrence1QuotientTerm1Band13_eq :
    recurrence1QuotientTerm1Band13 = recurrence1QuotientTerm1Block13 := by
  unfold recurrence1QuotientTerm1Band13 recurrence1QuotientTerm1Row0Band13
  unfold recurrence1QuotientTerm1Row1Band13 recurrence1QuotientTerm1Row2Band13
  unfold recurrence1QuotientTerm1Row3Band13 recurrence1QuotientTerm1Row4Band13
  unfold recurrence1QuotientTerm1Row5Band13 recurrence1QuotientTerm1Row6Band13
  unfold recurrence1QuotientTerm1Row7Band13 recurrence1QuotientTerm1Row8Band13
  unfold recurrence1QuotientTerm1Row9Band13 recurrence1QuotientTerm1Row10Band13
  unfold recurrence1QuotientTerm1Block13
  ring

def recurrence1QuotientTerm1Band14 : Coefficient :=
  recurrence1QuotientTerm1Row1Band14 +
  recurrence1QuotientTerm1Row2Band14 +
  recurrence1QuotientTerm1Row3Band14 +
  recurrence1QuotientTerm1Row4Band14 +
  recurrence1QuotientTerm1Row5Band14 +
  recurrence1QuotientTerm1Row6Band14 +
  recurrence1QuotientTerm1Row7Band14 +
  recurrence1QuotientTerm1Row8Band14 +
  recurrence1QuotientTerm1Row9Band14 +
  recurrence1QuotientTerm1Row10Band14

theorem recurrence1QuotientTerm1Band14_eq :
    recurrence1QuotientTerm1Band14 = recurrence1QuotientTerm1Block14 := by
  unfold recurrence1QuotientTerm1Band14 recurrence1QuotientTerm1Row1Band14
  unfold recurrence1QuotientTerm1Row2Band14 recurrence1QuotientTerm1Row3Band14
  unfold recurrence1QuotientTerm1Row4Band14 recurrence1QuotientTerm1Row5Band14
  unfold recurrence1QuotientTerm1Row6Band14 recurrence1QuotientTerm1Row7Band14
  unfold recurrence1QuotientTerm1Row8Band14 recurrence1QuotientTerm1Row9Band14
  unfold recurrence1QuotientTerm1Row10Band14 recurrence1QuotientTerm1Block14
  ring

def recurrence1QuotientTerm1Band15 : Coefficient :=
  recurrence1QuotientTerm1Row2Band15 +
  recurrence1QuotientTerm1Row3Band15 +
  recurrence1QuotientTerm1Row4Band15 +
  recurrence1QuotientTerm1Row5Band15 +
  recurrence1QuotientTerm1Row6Band15 +
  recurrence1QuotientTerm1Row7Band15 +
  recurrence1QuotientTerm1Row8Band15 +
  recurrence1QuotientTerm1Row9Band15 +
  recurrence1QuotientTerm1Row10Band15

theorem recurrence1QuotientTerm1Band15_eq :
    recurrence1QuotientTerm1Band15 = recurrence1QuotientTerm1Block15 := by
  unfold recurrence1QuotientTerm1Band15 recurrence1QuotientTerm1Row2Band15
  unfold recurrence1QuotientTerm1Row3Band15 recurrence1QuotientTerm1Row4Band15
  unfold recurrence1QuotientTerm1Row5Band15 recurrence1QuotientTerm1Row6Band15
  unfold recurrence1QuotientTerm1Row7Band15 recurrence1QuotientTerm1Row8Band15
  unfold recurrence1QuotientTerm1Row9Band15 recurrence1QuotientTerm1Row10Band15
  unfold recurrence1QuotientTerm1Block15
  ring

def recurrence1QuotientTerm1Band16 : Coefficient :=
  recurrence1QuotientTerm1Row3Band16 +
  recurrence1QuotientTerm1Row4Band16 +
  recurrence1QuotientTerm1Row5Band16 +
  recurrence1QuotientTerm1Row6Band16 +
  recurrence1QuotientTerm1Row7Band16 +
  recurrence1QuotientTerm1Row8Band16 +
  recurrence1QuotientTerm1Row9Band16 +
  recurrence1QuotientTerm1Row10Band16

theorem recurrence1QuotientTerm1Band16_eq :
    recurrence1QuotientTerm1Band16 = recurrence1QuotientTerm1Block16 := by
  unfold recurrence1QuotientTerm1Band16 recurrence1QuotientTerm1Row3Band16
  unfold recurrence1QuotientTerm1Row4Band16 recurrence1QuotientTerm1Row5Band16
  unfold recurrence1QuotientTerm1Row6Band16 recurrence1QuotientTerm1Row7Band16
  unfold recurrence1QuotientTerm1Row8Band16 recurrence1QuotientTerm1Row9Band16
  unfold recurrence1QuotientTerm1Row10Band16 recurrence1QuotientTerm1Block16
  ring

def recurrence1QuotientTerm1Band17 : Coefficient :=
  recurrence1QuotientTerm1Row4Band17 +
  recurrence1QuotientTerm1Row5Band17 +
  recurrence1QuotientTerm1Row6Band17 +
  recurrence1QuotientTerm1Row7Band17 +
  recurrence1QuotientTerm1Row8Band17 +
  recurrence1QuotientTerm1Row9Band17 +
  recurrence1QuotientTerm1Row10Band17

theorem recurrence1QuotientTerm1Band17_eq :
    recurrence1QuotientTerm1Band17 = recurrence1QuotientTerm1Block17 := by
  unfold recurrence1QuotientTerm1Band17 recurrence1QuotientTerm1Row4Band17
  unfold recurrence1QuotientTerm1Row5Band17 recurrence1QuotientTerm1Row6Band17
  unfold recurrence1QuotientTerm1Row7Band17 recurrence1QuotientTerm1Row8Band17
  unfold recurrence1QuotientTerm1Row9Band17 recurrence1QuotientTerm1Row10Band17
  unfold recurrence1QuotientTerm1Block17
  ring

def recurrence1QuotientTerm1Band18 : Coefficient :=
  recurrence1QuotientTerm1Row5Band18 +
  recurrence1QuotientTerm1Row6Band18 +
  recurrence1QuotientTerm1Row7Band18 +
  recurrence1QuotientTerm1Row8Band18 +
  recurrence1QuotientTerm1Row9Band18 +
  recurrence1QuotientTerm1Row10Band18

theorem recurrence1QuotientTerm1Band18_eq :
    recurrence1QuotientTerm1Band18 = recurrence1QuotientTerm1Block18 := by
  unfold recurrence1QuotientTerm1Band18 recurrence1QuotientTerm1Row5Band18
  unfold recurrence1QuotientTerm1Row6Band18 recurrence1QuotientTerm1Row7Band18
  unfold recurrence1QuotientTerm1Row8Band18 recurrence1QuotientTerm1Row9Band18
  unfold recurrence1QuotientTerm1Row10Band18 recurrence1QuotientTerm1Block18
  ring

def recurrence1QuotientTerm1Band19 : Coefficient :=
  recurrence1QuotientTerm1Row6Band19 +
  recurrence1QuotientTerm1Row7Band19 +
  recurrence1QuotientTerm1Row8Band19 +
  recurrence1QuotientTerm1Row9Band19 +
  recurrence1QuotientTerm1Row10Band19

theorem recurrence1QuotientTerm1Band19_eq :
    recurrence1QuotientTerm1Band19 = recurrence1QuotientTerm1Block19 := by
  unfold recurrence1QuotientTerm1Band19 recurrence1QuotientTerm1Row6Band19
  unfold recurrence1QuotientTerm1Row7Band19 recurrence1QuotientTerm1Row8Band19
  unfold recurrence1QuotientTerm1Row9Band19 recurrence1QuotientTerm1Row10Band19
  unfold recurrence1QuotientTerm1Block19
  ring

def recurrence1QuotientTerm1Band20 : Coefficient :=
  recurrence1QuotientTerm1Row7Band20 +
  recurrence1QuotientTerm1Row8Band20 +
  recurrence1QuotientTerm1Row9Band20 +
  recurrence1QuotientTerm1Row10Band20

theorem recurrence1QuotientTerm1Band20_eq :
    recurrence1QuotientTerm1Band20 = recurrence1QuotientTerm1Block20 := by
  unfold recurrence1QuotientTerm1Band20 recurrence1QuotientTerm1Row7Band20
  unfold recurrence1QuotientTerm1Row8Band20 recurrence1QuotientTerm1Row9Band20
  unfold recurrence1QuotientTerm1Row10Band20 recurrence1QuotientTerm1Block20
  ring

def recurrence1QuotientTerm1Band21 : Coefficient :=
  recurrence1QuotientTerm1Row8Band21 +
  recurrence1QuotientTerm1Row9Band21 +
  recurrence1QuotientTerm1Row10Band21

theorem recurrence1QuotientTerm1Band21_eq :
    recurrence1QuotientTerm1Band21 = recurrence1QuotientTerm1Block21 := by
  unfold recurrence1QuotientTerm1Band21 recurrence1QuotientTerm1Row8Band21
  unfold recurrence1QuotientTerm1Row9Band21 recurrence1QuotientTerm1Row10Band21
  unfold recurrence1QuotientTerm1Block21
  ring

def recurrence1QuotientTerm1Band22 : Coefficient :=
  recurrence1QuotientTerm1Row9Band22 +
  recurrence1QuotientTerm1Row10Band22

theorem recurrence1QuotientTerm1Band22_eq :
    recurrence1QuotientTerm1Band22 = recurrence1QuotientTerm1Block22 := by
  unfold recurrence1QuotientTerm1Band22 recurrence1QuotientTerm1Row9Band22
  unfold recurrence1QuotientTerm1Row10Band22 recurrence1QuotientTerm1Block22
  ring

def recurrence1QuotientTerm1Band23 : Coefficient :=
  recurrence1QuotientTerm1Row10Band23

theorem recurrence1QuotientTerm1Band23_eq :
    recurrence1QuotientTerm1Band23 = recurrence1QuotientTerm1Block23 := by
  unfold recurrence1QuotientTerm1Band23 recurrence1QuotientTerm1Row10Band23
  unfold recurrence1QuotientTerm1Block23
  ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
