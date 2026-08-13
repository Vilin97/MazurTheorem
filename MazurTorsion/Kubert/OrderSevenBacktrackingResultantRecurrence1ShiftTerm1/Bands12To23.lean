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

/-- Internal datum. -/ def recurrence1ShiftTerm1Band12 : Coefficient :=
  recurrence1ShiftTerm1Row0Band12 +
  recurrence1ShiftTerm1Row1Band12 +
  recurrence1ShiftTerm1Row2Band12 +
  recurrence1ShiftTerm1Row3Band12 +
  recurrence1ShiftTerm1Row4Band12 +
  recurrence1ShiftTerm1Row5Band12 +
  recurrence1ShiftTerm1Row6Band12 +
  recurrence1ShiftTerm1Row7Band12 +
  recurrence1ShiftTerm1Row8Band12 +
  recurrence1ShiftTerm1Row9Band12 +
  recurrence1ShiftTerm1Row10Band12

theorem recurrence1ShiftTerm1Band12_eq :
    recurrence1ShiftTerm1Band12 = recurrence1ShiftTerm1Block12 := by
  unfold recurrence1ShiftTerm1Band12 recurrence1ShiftTerm1Row0Band12 recurrence1ShiftTerm1Row1Band12
  unfold recurrence1ShiftTerm1Row2Band12 recurrence1ShiftTerm1Row3Band12
  unfold recurrence1ShiftTerm1Row4Band12 recurrence1ShiftTerm1Row5Band12
  unfold recurrence1ShiftTerm1Row6Band12 recurrence1ShiftTerm1Row7Band12
  unfold recurrence1ShiftTerm1Row8Band12 recurrence1ShiftTerm1Row9Band12
  unfold recurrence1ShiftTerm1Row10Band12 recurrence1ShiftTerm1Block12
  ring

/-- Internal datum. -/ def recurrence1ShiftTerm1Band13 : Coefficient :=
  recurrence1ShiftTerm1Row0Band13 +
  recurrence1ShiftTerm1Row1Band13 +
  recurrence1ShiftTerm1Row2Band13 +
  recurrence1ShiftTerm1Row3Band13 +
  recurrence1ShiftTerm1Row4Band13 +
  recurrence1ShiftTerm1Row5Band13 +
  recurrence1ShiftTerm1Row6Band13 +
  recurrence1ShiftTerm1Row7Band13 +
  recurrence1ShiftTerm1Row8Band13 +
  recurrence1ShiftTerm1Row9Band13 +
  recurrence1ShiftTerm1Row10Band13

theorem recurrence1ShiftTerm1Band13_eq :
    recurrence1ShiftTerm1Band13 = recurrence1ShiftTerm1Block13 := by
  unfold recurrence1ShiftTerm1Band13 recurrence1ShiftTerm1Row0Band13 recurrence1ShiftTerm1Row1Band13
  unfold recurrence1ShiftTerm1Row2Band13 recurrence1ShiftTerm1Row3Band13
  unfold recurrence1ShiftTerm1Row4Band13 recurrence1ShiftTerm1Row5Band13
  unfold recurrence1ShiftTerm1Row6Band13 recurrence1ShiftTerm1Row7Band13
  unfold recurrence1ShiftTerm1Row8Band13 recurrence1ShiftTerm1Row9Band13
  unfold recurrence1ShiftTerm1Row10Band13 recurrence1ShiftTerm1Block13
  ring

/-- Internal datum. -/ def recurrence1ShiftTerm1Band14 : Coefficient :=
  recurrence1ShiftTerm1Row0Band14 +
  recurrence1ShiftTerm1Row1Band14 +
  recurrence1ShiftTerm1Row2Band14 +
  recurrence1ShiftTerm1Row3Band14 +
  recurrence1ShiftTerm1Row4Band14 +
  recurrence1ShiftTerm1Row5Band14 +
  recurrence1ShiftTerm1Row6Band14 +
  recurrence1ShiftTerm1Row7Band14 +
  recurrence1ShiftTerm1Row8Band14 +
  recurrence1ShiftTerm1Row9Band14 +
  recurrence1ShiftTerm1Row10Band14

theorem recurrence1ShiftTerm1Band14_eq :
    recurrence1ShiftTerm1Band14 = recurrence1ShiftTerm1Block14 := by
  unfold recurrence1ShiftTerm1Band14 recurrence1ShiftTerm1Row0Band14 recurrence1ShiftTerm1Row1Band14
  unfold recurrence1ShiftTerm1Row2Band14 recurrence1ShiftTerm1Row3Band14
  unfold recurrence1ShiftTerm1Row4Band14 recurrence1ShiftTerm1Row5Band14
  unfold recurrence1ShiftTerm1Row6Band14 recurrence1ShiftTerm1Row7Band14
  unfold recurrence1ShiftTerm1Row8Band14 recurrence1ShiftTerm1Row9Band14
  unfold recurrence1ShiftTerm1Row10Band14 recurrence1ShiftTerm1Block14
  ring

/-- Internal datum. -/ def recurrence1ShiftTerm1Band15 : Coefficient :=
  recurrence1ShiftTerm1Row1Band15 +
  recurrence1ShiftTerm1Row2Band15 +
  recurrence1ShiftTerm1Row3Band15 +
  recurrence1ShiftTerm1Row4Band15 +
  recurrence1ShiftTerm1Row5Band15 +
  recurrence1ShiftTerm1Row6Band15 +
  recurrence1ShiftTerm1Row7Band15 +
  recurrence1ShiftTerm1Row8Band15 +
  recurrence1ShiftTerm1Row9Band15 +
  recurrence1ShiftTerm1Row10Band15

theorem recurrence1ShiftTerm1Band15_eq :
    recurrence1ShiftTerm1Band15 = recurrence1ShiftTerm1Block15 := by
  unfold recurrence1ShiftTerm1Band15 recurrence1ShiftTerm1Row1Band15 recurrence1ShiftTerm1Row2Band15
  unfold recurrence1ShiftTerm1Row3Band15 recurrence1ShiftTerm1Row4Band15
  unfold recurrence1ShiftTerm1Row5Band15 recurrence1ShiftTerm1Row6Band15
  unfold recurrence1ShiftTerm1Row7Band15 recurrence1ShiftTerm1Row8Band15
  unfold recurrence1ShiftTerm1Row9Band15 recurrence1ShiftTerm1Row10Band15
  unfold recurrence1ShiftTerm1Block15
  ring

/-- Internal datum. -/ def recurrence1ShiftTerm1Band16 : Coefficient :=
  recurrence1ShiftTerm1Row2Band16 +
  recurrence1ShiftTerm1Row3Band16 +
  recurrence1ShiftTerm1Row4Band16 +
  recurrence1ShiftTerm1Row5Band16 +
  recurrence1ShiftTerm1Row6Band16 +
  recurrence1ShiftTerm1Row7Band16 +
  recurrence1ShiftTerm1Row8Band16 +
  recurrence1ShiftTerm1Row9Band16 +
  recurrence1ShiftTerm1Row10Band16

theorem recurrence1ShiftTerm1Band16_eq :
    recurrence1ShiftTerm1Band16 = recurrence1ShiftTerm1Block16 := by
  unfold recurrence1ShiftTerm1Band16 recurrence1ShiftTerm1Row2Band16 recurrence1ShiftTerm1Row3Band16
  unfold recurrence1ShiftTerm1Row4Band16 recurrence1ShiftTerm1Row5Band16
  unfold recurrence1ShiftTerm1Row6Band16 recurrence1ShiftTerm1Row7Band16
  unfold recurrence1ShiftTerm1Row8Band16 recurrence1ShiftTerm1Row9Band16
  unfold recurrence1ShiftTerm1Row10Band16 recurrence1ShiftTerm1Block16
  ring

/-- Internal datum. -/ def recurrence1ShiftTerm1Band17 : Coefficient :=
  recurrence1ShiftTerm1Row3Band17 +
  recurrence1ShiftTerm1Row4Band17 +
  recurrence1ShiftTerm1Row5Band17 +
  recurrence1ShiftTerm1Row6Band17 +
  recurrence1ShiftTerm1Row7Band17 +
  recurrence1ShiftTerm1Row8Band17 +
  recurrence1ShiftTerm1Row9Band17 +
  recurrence1ShiftTerm1Row10Band17

theorem recurrence1ShiftTerm1Band17_eq :
    recurrence1ShiftTerm1Band17 = recurrence1ShiftTerm1Block17 := by
  unfold recurrence1ShiftTerm1Band17 recurrence1ShiftTerm1Row3Band17 recurrence1ShiftTerm1Row4Band17
  unfold recurrence1ShiftTerm1Row5Band17 recurrence1ShiftTerm1Row6Band17
  unfold recurrence1ShiftTerm1Row7Band17 recurrence1ShiftTerm1Row8Band17
  unfold recurrence1ShiftTerm1Row9Band17 recurrence1ShiftTerm1Row10Band17
  unfold recurrence1ShiftTerm1Block17
  ring

/-- Internal datum. -/ def recurrence1ShiftTerm1Band18 : Coefficient :=
  recurrence1ShiftTerm1Row4Band18 +
  recurrence1ShiftTerm1Row5Band18 +
  recurrence1ShiftTerm1Row6Band18 +
  recurrence1ShiftTerm1Row7Band18 +
  recurrence1ShiftTerm1Row8Band18 +
  recurrence1ShiftTerm1Row9Band18 +
  recurrence1ShiftTerm1Row10Band18

theorem recurrence1ShiftTerm1Band18_eq :
    recurrence1ShiftTerm1Band18 = recurrence1ShiftTerm1Block18 := by
  unfold recurrence1ShiftTerm1Band18 recurrence1ShiftTerm1Row4Band18 recurrence1ShiftTerm1Row5Band18
  unfold recurrence1ShiftTerm1Row6Band18 recurrence1ShiftTerm1Row7Band18
  unfold recurrence1ShiftTerm1Row8Band18 recurrence1ShiftTerm1Row9Band18
  unfold recurrence1ShiftTerm1Row10Band18 recurrence1ShiftTerm1Block18
  ring

/-- Internal datum. -/ def recurrence1ShiftTerm1Band19 : Coefficient :=
  recurrence1ShiftTerm1Row5Band19 +
  recurrence1ShiftTerm1Row6Band19 +
  recurrence1ShiftTerm1Row7Band19 +
  recurrence1ShiftTerm1Row8Band19 +
  recurrence1ShiftTerm1Row9Band19 +
  recurrence1ShiftTerm1Row10Band19

theorem recurrence1ShiftTerm1Band19_eq :
    recurrence1ShiftTerm1Band19 = recurrence1ShiftTerm1Block19 := by
  unfold recurrence1ShiftTerm1Band19 recurrence1ShiftTerm1Row5Band19 recurrence1ShiftTerm1Row6Band19
  unfold recurrence1ShiftTerm1Row7Band19 recurrence1ShiftTerm1Row8Band19
  unfold recurrence1ShiftTerm1Row9Band19 recurrence1ShiftTerm1Row10Band19
  unfold recurrence1ShiftTerm1Block19
  ring

/-- Internal datum. -/ def recurrence1ShiftTerm1Band20 : Coefficient :=
  recurrence1ShiftTerm1Row6Band20 +
  recurrence1ShiftTerm1Row7Band20 +
  recurrence1ShiftTerm1Row8Band20 +
  recurrence1ShiftTerm1Row9Band20 +
  recurrence1ShiftTerm1Row10Band20

theorem recurrence1ShiftTerm1Band20_eq :
    recurrence1ShiftTerm1Band20 = recurrence1ShiftTerm1Block20 := by
  unfold recurrence1ShiftTerm1Band20 recurrence1ShiftTerm1Row6Band20 recurrence1ShiftTerm1Row7Band20
  unfold recurrence1ShiftTerm1Row8Band20 recurrence1ShiftTerm1Row9Band20
  unfold recurrence1ShiftTerm1Row10Band20 recurrence1ShiftTerm1Block20
  ring

/-- Internal datum. -/ def recurrence1ShiftTerm1Band21 : Coefficient :=
  recurrence1ShiftTerm1Row7Band21 +
  recurrence1ShiftTerm1Row8Band21 +
  recurrence1ShiftTerm1Row9Band21 +
  recurrence1ShiftTerm1Row10Band21

theorem recurrence1ShiftTerm1Band21_eq :
    recurrence1ShiftTerm1Band21 = recurrence1ShiftTerm1Block21 := by
  unfold recurrence1ShiftTerm1Band21 recurrence1ShiftTerm1Row7Band21 recurrence1ShiftTerm1Row8Band21
  unfold recurrence1ShiftTerm1Row9Band21 recurrence1ShiftTerm1Row10Band21
  unfold recurrence1ShiftTerm1Block21
  ring

/-- Internal datum. -/ def recurrence1ShiftTerm1Band22 : Coefficient :=
  recurrence1ShiftTerm1Row8Band22 +
  recurrence1ShiftTerm1Row9Band22 +
  recurrence1ShiftTerm1Row10Band22

theorem recurrence1ShiftTerm1Band22_eq :
    recurrence1ShiftTerm1Band22 = recurrence1ShiftTerm1Block22 := by
  unfold recurrence1ShiftTerm1Band22 recurrence1ShiftTerm1Row8Band22 recurrence1ShiftTerm1Row9Band22
  unfold recurrence1ShiftTerm1Row10Band22 recurrence1ShiftTerm1Block22
  ring

/-- Internal datum. -/ def recurrence1ShiftTerm1Band23 : Coefficient :=
  recurrence1ShiftTerm1Row9Band23 +
  recurrence1ShiftTerm1Row10Band23

theorem recurrence1ShiftTerm1Band23_eq :
    recurrence1ShiftTerm1Band23 = recurrence1ShiftTerm1Block23 := by
  unfold recurrence1ShiftTerm1Band23 recurrence1ShiftTerm1Row9Band23
  unfold recurrence1ShiftTerm1Row10Band23 recurrence1ShiftTerm1Block23
  ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
