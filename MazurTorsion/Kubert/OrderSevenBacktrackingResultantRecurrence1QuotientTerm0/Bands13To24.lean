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

/-- Internal datum. -/ def recurrence1QuotientTerm0Band13 : Coefficient :=
  recurrence1QuotientTerm0Row0Band13 +
  recurrence1QuotientTerm0Row1Band13 +
  recurrence1QuotientTerm0Row2Band13 +
  recurrence1QuotientTerm0Row3Band13 +
  recurrence1QuotientTerm0Row4Band13 +
  recurrence1QuotientTerm0Row5Band13 +
  recurrence1QuotientTerm0Row6Band13 +
  recurrence1QuotientTerm0Row7Band13 +
  recurrence1QuotientTerm0Row8Band13 +
  recurrence1QuotientTerm0Row9Band13 +
  recurrence1QuotientTerm0Row10Band13

theorem recurrence1QuotientTerm0Band13_eq :
    recurrence1QuotientTerm0Band13 = recurrence1QuotientTerm0Block13 := by
  unfold recurrence1QuotientTerm0Band13 recurrence1QuotientTerm0Row0Band13
  unfold recurrence1QuotientTerm0Row1Band13 recurrence1QuotientTerm0Row2Band13
  unfold recurrence1QuotientTerm0Row3Band13 recurrence1QuotientTerm0Row4Band13
  unfold recurrence1QuotientTerm0Row5Band13 recurrence1QuotientTerm0Row6Band13
  unfold recurrence1QuotientTerm0Row7Band13 recurrence1QuotientTerm0Row8Band13
  unfold recurrence1QuotientTerm0Row9Band13 recurrence1QuotientTerm0Row10Band13
  unfold recurrence1QuotientTerm0Block13
  ring

/-- Internal datum. -/ def recurrence1QuotientTerm0Band14 : Coefficient :=
  recurrence1QuotientTerm0Row0Band14 +
  recurrence1QuotientTerm0Row1Band14 +
  recurrence1QuotientTerm0Row2Band14 +
  recurrence1QuotientTerm0Row3Band14 +
  recurrence1QuotientTerm0Row4Band14 +
  recurrence1QuotientTerm0Row5Band14 +
  recurrence1QuotientTerm0Row6Band14 +
  recurrence1QuotientTerm0Row7Band14 +
  recurrence1QuotientTerm0Row8Band14 +
  recurrence1QuotientTerm0Row9Band14 +
  recurrence1QuotientTerm0Row10Band14

theorem recurrence1QuotientTerm0Band14_eq :
    recurrence1QuotientTerm0Band14 = recurrence1QuotientTerm0Block14 := by
  unfold recurrence1QuotientTerm0Band14 recurrence1QuotientTerm0Row0Band14
  unfold recurrence1QuotientTerm0Row1Band14 recurrence1QuotientTerm0Row2Band14
  unfold recurrence1QuotientTerm0Row3Band14 recurrence1QuotientTerm0Row4Band14
  unfold recurrence1QuotientTerm0Row5Band14 recurrence1QuotientTerm0Row6Band14
  unfold recurrence1QuotientTerm0Row7Band14 recurrence1QuotientTerm0Row8Band14
  unfold recurrence1QuotientTerm0Row9Band14 recurrence1QuotientTerm0Row10Band14
  unfold recurrence1QuotientTerm0Block14
  ring

/-- Internal datum. -/ def recurrence1QuotientTerm0Band15 : Coefficient :=
  recurrence1QuotientTerm0Row1Band15 +
  recurrence1QuotientTerm0Row2Band15 +
  recurrence1QuotientTerm0Row3Band15 +
  recurrence1QuotientTerm0Row4Band15 +
  recurrence1QuotientTerm0Row5Band15 +
  recurrence1QuotientTerm0Row6Band15 +
  recurrence1QuotientTerm0Row7Band15 +
  recurrence1QuotientTerm0Row8Band15 +
  recurrence1QuotientTerm0Row9Band15 +
  recurrence1QuotientTerm0Row10Band15

theorem recurrence1QuotientTerm0Band15_eq :
    recurrence1QuotientTerm0Band15 = recurrence1QuotientTerm0Block15 := by
  unfold recurrence1QuotientTerm0Band15 recurrence1QuotientTerm0Row1Band15
  unfold recurrence1QuotientTerm0Row2Band15 recurrence1QuotientTerm0Row3Band15
  unfold recurrence1QuotientTerm0Row4Band15 recurrence1QuotientTerm0Row5Band15
  unfold recurrence1QuotientTerm0Row6Band15 recurrence1QuotientTerm0Row7Band15
  unfold recurrence1QuotientTerm0Row8Band15 recurrence1QuotientTerm0Row9Band15
  unfold recurrence1QuotientTerm0Row10Band15 recurrence1QuotientTerm0Block15
  ring

/-- Internal datum. -/ def recurrence1QuotientTerm0Band16 : Coefficient :=
  recurrence1QuotientTerm0Row2Band16 +
  recurrence1QuotientTerm0Row3Band16 +
  recurrence1QuotientTerm0Row4Band16 +
  recurrence1QuotientTerm0Row5Band16 +
  recurrence1QuotientTerm0Row6Band16 +
  recurrence1QuotientTerm0Row7Band16 +
  recurrence1QuotientTerm0Row8Band16 +
  recurrence1QuotientTerm0Row9Band16 +
  recurrence1QuotientTerm0Row10Band16

theorem recurrence1QuotientTerm0Band16_eq :
    recurrence1QuotientTerm0Band16 = recurrence1QuotientTerm0Block16 := by
  unfold recurrence1QuotientTerm0Band16 recurrence1QuotientTerm0Row2Band16
  unfold recurrence1QuotientTerm0Row3Band16 recurrence1QuotientTerm0Row4Band16
  unfold recurrence1QuotientTerm0Row5Band16 recurrence1QuotientTerm0Row6Band16
  unfold recurrence1QuotientTerm0Row7Band16 recurrence1QuotientTerm0Row8Band16
  unfold recurrence1QuotientTerm0Row9Band16 recurrence1QuotientTerm0Row10Band16
  unfold recurrence1QuotientTerm0Block16
  ring

/-- Internal datum. -/ def recurrence1QuotientTerm0Band17 : Coefficient :=
  recurrence1QuotientTerm0Row3Band17 +
  recurrence1QuotientTerm0Row4Band17 +
  recurrence1QuotientTerm0Row5Band17 +
  recurrence1QuotientTerm0Row6Band17 +
  recurrence1QuotientTerm0Row7Band17 +
  recurrence1QuotientTerm0Row8Band17 +
  recurrence1QuotientTerm0Row9Band17 +
  recurrence1QuotientTerm0Row10Band17

theorem recurrence1QuotientTerm0Band17_eq :
    recurrence1QuotientTerm0Band17 = recurrence1QuotientTerm0Block17 := by
  unfold recurrence1QuotientTerm0Band17 recurrence1QuotientTerm0Row3Band17
  unfold recurrence1QuotientTerm0Row4Band17 recurrence1QuotientTerm0Row5Band17
  unfold recurrence1QuotientTerm0Row6Band17 recurrence1QuotientTerm0Row7Band17
  unfold recurrence1QuotientTerm0Row8Band17 recurrence1QuotientTerm0Row9Band17
  unfold recurrence1QuotientTerm0Row10Band17 recurrence1QuotientTerm0Block17
  ring

/-- Internal datum. -/ def recurrence1QuotientTerm0Band18 : Coefficient :=
  recurrence1QuotientTerm0Row4Band18 +
  recurrence1QuotientTerm0Row5Band18 +
  recurrence1QuotientTerm0Row6Band18 +
  recurrence1QuotientTerm0Row7Band18 +
  recurrence1QuotientTerm0Row8Band18 +
  recurrence1QuotientTerm0Row9Band18 +
  recurrence1QuotientTerm0Row10Band18

theorem recurrence1QuotientTerm0Band18_eq :
    recurrence1QuotientTerm0Band18 = recurrence1QuotientTerm0Block18 := by
  unfold recurrence1QuotientTerm0Band18 recurrence1QuotientTerm0Row4Band18
  unfold recurrence1QuotientTerm0Row5Band18 recurrence1QuotientTerm0Row6Band18
  unfold recurrence1QuotientTerm0Row7Band18 recurrence1QuotientTerm0Row8Band18
  unfold recurrence1QuotientTerm0Row9Band18 recurrence1QuotientTerm0Row10Band18
  unfold recurrence1QuotientTerm0Block18
  ring

/-- Internal datum. -/ def recurrence1QuotientTerm0Band19 : Coefficient :=
  recurrence1QuotientTerm0Row5Band19 +
  recurrence1QuotientTerm0Row6Band19 +
  recurrence1QuotientTerm0Row7Band19 +
  recurrence1QuotientTerm0Row8Band19 +
  recurrence1QuotientTerm0Row9Band19 +
  recurrence1QuotientTerm0Row10Band19

theorem recurrence1QuotientTerm0Band19_eq :
    recurrence1QuotientTerm0Band19 = recurrence1QuotientTerm0Block19 := by
  unfold recurrence1QuotientTerm0Band19 recurrence1QuotientTerm0Row5Band19
  unfold recurrence1QuotientTerm0Row6Band19 recurrence1QuotientTerm0Row7Band19
  unfold recurrence1QuotientTerm0Row8Band19 recurrence1QuotientTerm0Row9Band19
  unfold recurrence1QuotientTerm0Row10Band19 recurrence1QuotientTerm0Block19
  ring

/-- Internal datum. -/ def recurrence1QuotientTerm0Band20 : Coefficient :=
  recurrence1QuotientTerm0Row6Band20 +
  recurrence1QuotientTerm0Row7Band20 +
  recurrence1QuotientTerm0Row8Band20 +
  recurrence1QuotientTerm0Row9Band20 +
  recurrence1QuotientTerm0Row10Band20

theorem recurrence1QuotientTerm0Band20_eq :
    recurrence1QuotientTerm0Band20 = recurrence1QuotientTerm0Block20 := by
  unfold recurrence1QuotientTerm0Band20 recurrence1QuotientTerm0Row6Band20
  unfold recurrence1QuotientTerm0Row7Band20 recurrence1QuotientTerm0Row8Band20
  unfold recurrence1QuotientTerm0Row9Band20 recurrence1QuotientTerm0Row10Band20
  unfold recurrence1QuotientTerm0Block20
  ring

/-- Internal datum. -/ def recurrence1QuotientTerm0Band21 : Coefficient :=
  recurrence1QuotientTerm0Row7Band21 +
  recurrence1QuotientTerm0Row8Band21 +
  recurrence1QuotientTerm0Row9Band21 +
  recurrence1QuotientTerm0Row10Band21

theorem recurrence1QuotientTerm0Band21_eq :
    recurrence1QuotientTerm0Band21 = recurrence1QuotientTerm0Block21 := by
  unfold recurrence1QuotientTerm0Band21 recurrence1QuotientTerm0Row7Band21
  unfold recurrence1QuotientTerm0Row8Band21 recurrence1QuotientTerm0Row9Band21
  unfold recurrence1QuotientTerm0Row10Band21 recurrence1QuotientTerm0Block21
  ring

/-- Internal datum. -/ def recurrence1QuotientTerm0Band22 : Coefficient :=
  recurrence1QuotientTerm0Row8Band22 +
  recurrence1QuotientTerm0Row9Band22 +
  recurrence1QuotientTerm0Row10Band22

theorem recurrence1QuotientTerm0Band22_eq :
    recurrence1QuotientTerm0Band22 = recurrence1QuotientTerm0Block22 := by
  unfold recurrence1QuotientTerm0Band22 recurrence1QuotientTerm0Row8Band22
  unfold recurrence1QuotientTerm0Row9Band22 recurrence1QuotientTerm0Row10Band22
  unfold recurrence1QuotientTerm0Block22
  ring

/-- Internal datum. -/ def recurrence1QuotientTerm0Band23 : Coefficient :=
  recurrence1QuotientTerm0Row9Band23 +
  recurrence1QuotientTerm0Row10Band23

theorem recurrence1QuotientTerm0Band23_eq :
    recurrence1QuotientTerm0Band23 = recurrence1QuotientTerm0Block23 := by
  unfold recurrence1QuotientTerm0Band23 recurrence1QuotientTerm0Row9Band23
  unfold recurrence1QuotientTerm0Row10Band23 recurrence1QuotientTerm0Block23
  ring

/-- Internal datum. -/ def recurrence1QuotientTerm0Band24 : Coefficient :=
  recurrence1QuotientTerm0Row10Band24

theorem recurrence1QuotientTerm0Band24_eq :
    recurrence1QuotientTerm0Band24 = recurrence1QuotientTerm0Block24 := by
  unfold recurrence1QuotientTerm0Band24 recurrence1QuotientTerm0Row10Band24
  unfold recurrence1QuotientTerm0Block24
  ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
