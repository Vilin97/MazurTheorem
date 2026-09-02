/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1Remainder3Data
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1CommonData
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1RowData1

import Mathlib.Tactic.Ring

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1ExceptionalTerm1.Rows0To1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1ExceptionalTerm1.Rows2To3
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1ExceptionalTerm1.Rows4To5
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1ExceptionalTerm1.Rows6To7

/-!
# Recurrence 1 certificate: ExceptionalTerm1

This file is a checked bounded-band arithmetic shard for the first
pseudo-division recurrence in the order-seven branch-zero resultant certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

def recurrence1ExceptionalTerm1Band12 : Coefficient :=
  recurrence1ExceptionalTerm1Row0Band12 +
  recurrence1ExceptionalTerm1Row1Band12 +
  recurrence1ExceptionalTerm1Row2Band12 +
  recurrence1ExceptionalTerm1Row3Band12 +
  recurrence1ExceptionalTerm1Row4Band12 +
  recurrence1ExceptionalTerm1Row5Band12 +
  recurrence1ExceptionalTerm1Row6Band12 +
  recurrence1ExceptionalTerm1Row7Band12

theorem recurrence1ExceptionalTerm1Band12_eq :
    recurrence1ExceptionalTerm1Band12 = recurrence1ExceptionalTerm1Block12 := by
  unfold recurrence1ExceptionalTerm1Band12 recurrence1ExceptionalTerm1Row0Band12
  unfold recurrence1ExceptionalTerm1Row1Band12 recurrence1ExceptionalTerm1Row2Band12
  unfold recurrence1ExceptionalTerm1Row3Band12 recurrence1ExceptionalTerm1Row4Band12
  unfold recurrence1ExceptionalTerm1Row5Band12 recurrence1ExceptionalTerm1Row6Band12
  unfold recurrence1ExceptionalTerm1Row7Band12 recurrence1ExceptionalTerm1Block12
  ring

def recurrence1ExceptionalTerm1Band13 : Coefficient :=
  recurrence1ExceptionalTerm1Row0Band13 +
  recurrence1ExceptionalTerm1Row1Band13 +
  recurrence1ExceptionalTerm1Row2Band13 +
  recurrence1ExceptionalTerm1Row3Band13 +
  recurrence1ExceptionalTerm1Row4Band13 +
  recurrence1ExceptionalTerm1Row5Band13 +
  recurrence1ExceptionalTerm1Row6Band13 +
  recurrence1ExceptionalTerm1Row7Band13

theorem recurrence1ExceptionalTerm1Band13_eq :
    recurrence1ExceptionalTerm1Band13 = recurrence1ExceptionalTerm1Block13 := by
  unfold recurrence1ExceptionalTerm1Band13 recurrence1ExceptionalTerm1Row0Band13
  unfold recurrence1ExceptionalTerm1Row1Band13 recurrence1ExceptionalTerm1Row2Band13
  unfold recurrence1ExceptionalTerm1Row3Band13 recurrence1ExceptionalTerm1Row4Band13
  unfold recurrence1ExceptionalTerm1Row5Band13 recurrence1ExceptionalTerm1Row6Band13
  unfold recurrence1ExceptionalTerm1Row7Band13 recurrence1ExceptionalTerm1Block13
  ring

def recurrence1ExceptionalTerm1Band14 : Coefficient :=
  recurrence1ExceptionalTerm1Row0Band14 +
  recurrence1ExceptionalTerm1Row1Band14 +
  recurrence1ExceptionalTerm1Row2Band14 +
  recurrence1ExceptionalTerm1Row3Band14 +
  recurrence1ExceptionalTerm1Row4Band14 +
  recurrence1ExceptionalTerm1Row5Band14 +
  recurrence1ExceptionalTerm1Row6Band14 +
  recurrence1ExceptionalTerm1Row7Band14

theorem recurrence1ExceptionalTerm1Band14_eq :
    recurrence1ExceptionalTerm1Band14 = recurrence1ExceptionalTerm1Block14 := by
  unfold recurrence1ExceptionalTerm1Band14 recurrence1ExceptionalTerm1Row0Band14
  unfold recurrence1ExceptionalTerm1Row1Band14 recurrence1ExceptionalTerm1Row2Band14
  unfold recurrence1ExceptionalTerm1Row3Band14 recurrence1ExceptionalTerm1Row4Band14
  unfold recurrence1ExceptionalTerm1Row5Band14 recurrence1ExceptionalTerm1Row6Band14
  unfold recurrence1ExceptionalTerm1Row7Band14 recurrence1ExceptionalTerm1Block14
  ring

def recurrence1ExceptionalTerm1Band15 : Coefficient :=
  recurrence1ExceptionalTerm1Row0Band15 +
  recurrence1ExceptionalTerm1Row1Band15 +
  recurrence1ExceptionalTerm1Row2Band15 +
  recurrence1ExceptionalTerm1Row3Band15 +
  recurrence1ExceptionalTerm1Row4Band15 +
  recurrence1ExceptionalTerm1Row5Band15 +
  recurrence1ExceptionalTerm1Row6Band15 +
  recurrence1ExceptionalTerm1Row7Band15

theorem recurrence1ExceptionalTerm1Band15_eq :
    recurrence1ExceptionalTerm1Band15 = recurrence1ExceptionalTerm1Block15 := by
  unfold recurrence1ExceptionalTerm1Band15 recurrence1ExceptionalTerm1Row0Band15
  unfold recurrence1ExceptionalTerm1Row1Band15 recurrence1ExceptionalTerm1Row2Band15
  unfold recurrence1ExceptionalTerm1Row3Band15 recurrence1ExceptionalTerm1Row4Band15
  unfold recurrence1ExceptionalTerm1Row5Band15 recurrence1ExceptionalTerm1Row6Band15
  unfold recurrence1ExceptionalTerm1Row7Band15 recurrence1ExceptionalTerm1Block15
  ring

def recurrence1ExceptionalTerm1Band16 : Coefficient :=
  recurrence1ExceptionalTerm1Row0Band16 +
  recurrence1ExceptionalTerm1Row1Band16 +
  recurrence1ExceptionalTerm1Row2Band16 +
  recurrence1ExceptionalTerm1Row3Band16 +
  recurrence1ExceptionalTerm1Row4Band16 +
  recurrence1ExceptionalTerm1Row5Band16 +
  recurrence1ExceptionalTerm1Row6Band16 +
  recurrence1ExceptionalTerm1Row7Band16

theorem recurrence1ExceptionalTerm1Band16_eq :
    recurrence1ExceptionalTerm1Band16 = recurrence1ExceptionalTerm1Block16 := by
  unfold recurrence1ExceptionalTerm1Band16 recurrence1ExceptionalTerm1Row0Band16
  unfold recurrence1ExceptionalTerm1Row1Band16 recurrence1ExceptionalTerm1Row2Band16
  unfold recurrence1ExceptionalTerm1Row3Band16 recurrence1ExceptionalTerm1Row4Band16
  unfold recurrence1ExceptionalTerm1Row5Band16 recurrence1ExceptionalTerm1Row6Band16
  unfold recurrence1ExceptionalTerm1Row7Band16 recurrence1ExceptionalTerm1Block16
  ring

def recurrence1ExceptionalTerm1Band17 : Coefficient :=
  recurrence1ExceptionalTerm1Row0Band17 +
  recurrence1ExceptionalTerm1Row1Band17 +
  recurrence1ExceptionalTerm1Row2Band17 +
  recurrence1ExceptionalTerm1Row3Band17 +
  recurrence1ExceptionalTerm1Row4Band17 +
  recurrence1ExceptionalTerm1Row5Band17 +
  recurrence1ExceptionalTerm1Row6Band17 +
  recurrence1ExceptionalTerm1Row7Band17

theorem recurrence1ExceptionalTerm1Band17_eq :
    recurrence1ExceptionalTerm1Band17 = recurrence1ExceptionalTerm1Block17 := by
  unfold recurrence1ExceptionalTerm1Band17 recurrence1ExceptionalTerm1Row0Band17
  unfold recurrence1ExceptionalTerm1Row1Band17 recurrence1ExceptionalTerm1Row2Band17
  unfold recurrence1ExceptionalTerm1Row3Band17 recurrence1ExceptionalTerm1Row4Band17
  unfold recurrence1ExceptionalTerm1Row5Band17 recurrence1ExceptionalTerm1Row6Band17
  unfold recurrence1ExceptionalTerm1Row7Band17 recurrence1ExceptionalTerm1Block17
  ring

def recurrence1ExceptionalTerm1Band18 : Coefficient :=
  recurrence1ExceptionalTerm1Row1Band18 +
  recurrence1ExceptionalTerm1Row2Band18 +
  recurrence1ExceptionalTerm1Row3Band18 +
  recurrence1ExceptionalTerm1Row4Band18 +
  recurrence1ExceptionalTerm1Row5Band18 +
  recurrence1ExceptionalTerm1Row6Band18 +
  recurrence1ExceptionalTerm1Row7Band18

theorem recurrence1ExceptionalTerm1Band18_eq :
    recurrence1ExceptionalTerm1Band18 = recurrence1ExceptionalTerm1Block18 := by
  unfold recurrence1ExceptionalTerm1Band18 recurrence1ExceptionalTerm1Row1Band18
  unfold recurrence1ExceptionalTerm1Row2Band18 recurrence1ExceptionalTerm1Row3Band18
  unfold recurrence1ExceptionalTerm1Row4Band18 recurrence1ExceptionalTerm1Row5Band18
  unfold recurrence1ExceptionalTerm1Row6Band18 recurrence1ExceptionalTerm1Row7Band18
  unfold recurrence1ExceptionalTerm1Block18
  ring

def recurrence1ExceptionalTerm1Band19 : Coefficient :=
  recurrence1ExceptionalTerm1Row2Band19 +
  recurrence1ExceptionalTerm1Row3Band19 +
  recurrence1ExceptionalTerm1Row4Band19 +
  recurrence1ExceptionalTerm1Row5Band19 +
  recurrence1ExceptionalTerm1Row6Band19 +
  recurrence1ExceptionalTerm1Row7Band19

theorem recurrence1ExceptionalTerm1Band19_eq :
    recurrence1ExceptionalTerm1Band19 = recurrence1ExceptionalTerm1Block19 := by
  unfold recurrence1ExceptionalTerm1Band19 recurrence1ExceptionalTerm1Row2Band19
  unfold recurrence1ExceptionalTerm1Row3Band19 recurrence1ExceptionalTerm1Row4Band19
  unfold recurrence1ExceptionalTerm1Row5Band19 recurrence1ExceptionalTerm1Row6Band19
  unfold recurrence1ExceptionalTerm1Row7Band19 recurrence1ExceptionalTerm1Block19
  ring

def recurrence1ExceptionalTerm1Band20 : Coefficient :=
  recurrence1ExceptionalTerm1Row3Band20 +
  recurrence1ExceptionalTerm1Row4Band20 +
  recurrence1ExceptionalTerm1Row5Band20 +
  recurrence1ExceptionalTerm1Row6Band20 +
  recurrence1ExceptionalTerm1Row7Band20

theorem recurrence1ExceptionalTerm1Band20_eq :
    recurrence1ExceptionalTerm1Band20 = recurrence1ExceptionalTerm1Block20 := by
  unfold recurrence1ExceptionalTerm1Band20 recurrence1ExceptionalTerm1Row3Band20
  unfold recurrence1ExceptionalTerm1Row4Band20 recurrence1ExceptionalTerm1Row5Band20
  unfold recurrence1ExceptionalTerm1Row6Band20 recurrence1ExceptionalTerm1Row7Band20
  unfold recurrence1ExceptionalTerm1Block20
  ring

def recurrence1ExceptionalTerm1Band21 : Coefficient :=
  recurrence1ExceptionalTerm1Row4Band21 +
  recurrence1ExceptionalTerm1Row5Band21 +
  recurrence1ExceptionalTerm1Row6Band21 +
  recurrence1ExceptionalTerm1Row7Band21

theorem recurrence1ExceptionalTerm1Band21_eq :
    recurrence1ExceptionalTerm1Band21 = recurrence1ExceptionalTerm1Block21 := by
  unfold recurrence1ExceptionalTerm1Band21 recurrence1ExceptionalTerm1Row4Band21
  unfold recurrence1ExceptionalTerm1Row5Band21 recurrence1ExceptionalTerm1Row6Band21
  unfold recurrence1ExceptionalTerm1Row7Band21 recurrence1ExceptionalTerm1Block21
  ring

def recurrence1ExceptionalTerm1Band22 : Coefficient :=
  recurrence1ExceptionalTerm1Row5Band22 +
  recurrence1ExceptionalTerm1Row6Band22 +
  recurrence1ExceptionalTerm1Row7Band22

theorem recurrence1ExceptionalTerm1Band22_eq :
    recurrence1ExceptionalTerm1Band22 = recurrence1ExceptionalTerm1Block22 := by
  unfold recurrence1ExceptionalTerm1Band22 recurrence1ExceptionalTerm1Row5Band22
  unfold recurrence1ExceptionalTerm1Row6Band22 recurrence1ExceptionalTerm1Row7Band22
  unfold recurrence1ExceptionalTerm1Block22
  ring

def recurrence1ExceptionalTerm1Band23 : Coefficient :=
  recurrence1ExceptionalTerm1Row6Band23 +
  recurrence1ExceptionalTerm1Row7Band23

theorem recurrence1ExceptionalTerm1Band23_eq :
    recurrence1ExceptionalTerm1Band23 = recurrence1ExceptionalTerm1Block23 := by
  unfold recurrence1ExceptionalTerm1Band23 recurrence1ExceptionalTerm1Row6Band23
  unfold recurrence1ExceptionalTerm1Row7Band23 recurrence1ExceptionalTerm1Block23
  ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
