/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1Remainder2Data
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1RowData1

import Mathlib.Tactic.Ring

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1ShiftTerm1.Bands0To11
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1ShiftTerm1.Bands12To23

/-!
# Recurrence 1 certificate: ShiftTerm1

This file is a checked bounded-band arithmetic shard for the first
pseudo-division recurrence in the order-seven branch-zero resultant certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

/-- Internal datum. -/ def recurrence1ShiftTerm1Rows : Coefficient :=
  recurrence1ShiftTerm1Row0 +
  recurrence1ShiftTerm1Row1 +
  recurrence1ShiftTerm1Row2 +
  recurrence1ShiftTerm1Row3 +
  recurrence1ShiftTerm1Row4 +
  recurrence1ShiftTerm1Row5 +
  recurrence1ShiftTerm1Row6 +
  recurrence1ShiftTerm1Row7 +
  recurrence1ShiftTerm1Row8 +
  recurrence1ShiftTerm1Row9 +
  recurrence1ShiftTerm1Row10

/-- Internal datum. -/ def recurrence1ShiftTerm1Bands : Coefficient :=
  recurrence1ShiftTerm1Band0 +
  recurrence1ShiftTerm1Band1 +
  recurrence1ShiftTerm1Band2 +
  recurrence1ShiftTerm1Band3 +
  recurrence1ShiftTerm1Band4 +
  recurrence1ShiftTerm1Band5 +
  recurrence1ShiftTerm1Band6 +
  recurrence1ShiftTerm1Band7 +
  recurrence1ShiftTerm1Band8 +
  recurrence1ShiftTerm1Band9 +
  recurrence1ShiftTerm1Band10 +
  recurrence1ShiftTerm1Band11 +
  recurrence1ShiftTerm1Band12 +
  recurrence1ShiftTerm1Band13 +
  recurrence1ShiftTerm1Band14 +
  recurrence1ShiftTerm1Band15 +
  recurrence1ShiftTerm1Band16 +
  recurrence1ShiftTerm1Band17 +
  recurrence1ShiftTerm1Band18 +
  recurrence1ShiftTerm1Band19 +
  recurrence1ShiftTerm1Band20 +
  recurrence1ShiftTerm1Band21 +
  recurrence1ShiftTerm1Band22 +
  recurrence1ShiftTerm1Band23

theorem recurrence1ShiftTerm1_eq :
    recurrence1Remainder26 * recurrence1Remainder20 =
      recurrence1ShiftTerm1 := by
  have rows :
      recurrence1Remainder26 * recurrence1Remainder20 =
        recurrence1ShiftTerm1Rows := by
    unfold recurrence1Remainder26 recurrence1ShiftTerm1Rows
    rw [← recurrence1ShiftTerm1Row0_eq]
    rw [← recurrence1ShiftTerm1Row1_eq]
    rw [← recurrence1ShiftTerm1Row2_eq]
    rw [← recurrence1ShiftTerm1Row3_eq]
    rw [← recurrence1ShiftTerm1Row4_eq]
    rw [← recurrence1ShiftTerm1Row5_eq]
    rw [← recurrence1ShiftTerm1Row6_eq]
    rw [← recurrence1ShiftTerm1Row7_eq]
    rw [← recurrence1ShiftTerm1Row8_eq]
    rw [← recurrence1ShiftTerm1Row9_eq]
    rw [← recurrence1ShiftTerm1Row10_eq]
    unfold recurrence1Remainder20
    ring
  rw [rows]
  have rearrange : recurrence1ShiftTerm1Rows = recurrence1ShiftTerm1Bands := by
    unfold recurrence1ShiftTerm1Rows recurrence1ShiftTerm1Bands recurrence1ShiftTerm1Row0
    unfold recurrence1ShiftTerm1Row1 recurrence1ShiftTerm1Row2 recurrence1ShiftTerm1Row3
    unfold recurrence1ShiftTerm1Row4 recurrence1ShiftTerm1Row5 recurrence1ShiftTerm1Row6
    unfold recurrence1ShiftTerm1Row7 recurrence1ShiftTerm1Row8 recurrence1ShiftTerm1Row9
    unfold recurrence1ShiftTerm1Row10 recurrence1ShiftTerm1Band0 recurrence1ShiftTerm1Band1
    unfold recurrence1ShiftTerm1Band2 recurrence1ShiftTerm1Band3 recurrence1ShiftTerm1Band4
    unfold recurrence1ShiftTerm1Band5 recurrence1ShiftTerm1Band6 recurrence1ShiftTerm1Band7
    unfold recurrence1ShiftTerm1Band8 recurrence1ShiftTerm1Band9 recurrence1ShiftTerm1Band10
    unfold recurrence1ShiftTerm1Band11 recurrence1ShiftTerm1Band12 recurrence1ShiftTerm1Band13
    unfold recurrence1ShiftTerm1Band14 recurrence1ShiftTerm1Band15 recurrence1ShiftTerm1Band16
    unfold recurrence1ShiftTerm1Band17 recurrence1ShiftTerm1Band18 recurrence1ShiftTerm1Band19
    unfold recurrence1ShiftTerm1Band20 recurrence1ShiftTerm1Band21 recurrence1ShiftTerm1Band22
    unfold recurrence1ShiftTerm1Band23
    ring
  rw [rearrange]
  unfold recurrence1ShiftTerm1Bands recurrence1ShiftTerm1
  rw [recurrence1ShiftTerm1Band0_eq]
  rw [recurrence1ShiftTerm1Band1_eq]
  rw [recurrence1ShiftTerm1Band2_eq]
  rw [recurrence1ShiftTerm1Band3_eq]
  rw [recurrence1ShiftTerm1Band4_eq]
  rw [recurrence1ShiftTerm1Band5_eq]
  rw [recurrence1ShiftTerm1Band6_eq]
  rw [recurrence1ShiftTerm1Band7_eq]
  rw [recurrence1ShiftTerm1Band8_eq]
  rw [recurrence1ShiftTerm1Band9_eq]
  rw [recurrence1ShiftTerm1Band10_eq]
  rw [recurrence1ShiftTerm1Band11_eq]
  rw [recurrence1ShiftTerm1Band12_eq]
  rw [recurrence1ShiftTerm1Band13_eq]
  rw [recurrence1ShiftTerm1Band14_eq]
  rw [recurrence1ShiftTerm1Band15_eq]
  rw [recurrence1ShiftTerm1Band16_eq]
  rw [recurrence1ShiftTerm1Band17_eq]
  rw [recurrence1ShiftTerm1Band18_eq]
  rw [recurrence1ShiftTerm1Band19_eq]
  rw [recurrence1ShiftTerm1Band20_eq]
  rw [recurrence1ShiftTerm1Band21_eq]
  rw [recurrence1ShiftTerm1Band22_eq]
  rw [recurrence1ShiftTerm1Band23_eq]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
