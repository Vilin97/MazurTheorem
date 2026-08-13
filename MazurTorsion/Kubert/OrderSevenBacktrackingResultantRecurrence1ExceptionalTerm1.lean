/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1Remainder3Data
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1CommonData
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1RowData1

import Mathlib.Tactic.Ring

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1ExceptionalTerm1.Bands0To11
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1ExceptionalTerm1.Bands12To23

/-!
# Recurrence 1 certificate: ExceptionalTerm1

This file is a checked bounded-band arithmetic shard for the first
pseudo-division recurrence in the order-seven branch-zero resultant certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

/-- Internal datum. -/ def recurrence1ExceptionalTerm1Rows : Coefficient :=
  recurrence1ExceptionalTerm1Row0 +
  recurrence1ExceptionalTerm1Row1 +
  recurrence1ExceptionalTerm1Row2 +
  recurrence1ExceptionalTerm1Row3 +
  recurrence1ExceptionalTerm1Row4 +
  recurrence1ExceptionalTerm1Row5 +
  recurrence1ExceptionalTerm1Row6 +
  recurrence1ExceptionalTerm1Row7

/-- Internal datum. -/ def recurrence1ExceptionalTerm1Bands : Coefficient :=
  recurrence1ExceptionalTerm1Band0 +
  recurrence1ExceptionalTerm1Band1 +
  recurrence1ExceptionalTerm1Band2 +
  recurrence1ExceptionalTerm1Band3 +
  recurrence1ExceptionalTerm1Band4 +
  recurrence1ExceptionalTerm1Band5 +
  recurrence1ExceptionalTerm1Band6 +
  recurrence1ExceptionalTerm1Band7 +
  recurrence1ExceptionalTerm1Band8 +
  recurrence1ExceptionalTerm1Band9 +
  recurrence1ExceptionalTerm1Band10 +
  recurrence1ExceptionalTerm1Band11 +
  recurrence1ExceptionalTerm1Band12 +
  recurrence1ExceptionalTerm1Band13 +
  recurrence1ExceptionalTerm1Band14 +
  recurrence1ExceptionalTerm1Band15 +
  recurrence1ExceptionalTerm1Band16 +
  recurrence1ExceptionalTerm1Band17 +
  recurrence1ExceptionalTerm1Band18 +
  recurrence1ExceptionalTerm1Band19 +
  recurrence1ExceptionalTerm1Band20 +
  recurrence1ExceptionalTerm1Band21 +
  recurrence1ExceptionalTerm1Band22 +
  recurrence1ExceptionalTerm1Band23

theorem recurrence1ExceptionalTerm1_eq :
    recurrence1Exceptional * recurrence1Remainder31 =
      recurrence1ExceptionalTerm1 := by
  have rows :
      recurrence1Exceptional * recurrence1Remainder31 =
        recurrence1ExceptionalTerm1Rows := by
    unfold recurrence1Exceptional recurrence1ExceptionalTerm1Rows
    rw [← recurrence1ExceptionalTerm1Row0_eq]
    rw [← recurrence1ExceptionalTerm1Row1_eq]
    rw [← recurrence1ExceptionalTerm1Row2_eq]
    rw [← recurrence1ExceptionalTerm1Row3_eq]
    rw [← recurrence1ExceptionalTerm1Row4_eq]
    rw [← recurrence1ExceptionalTerm1Row5_eq]
    rw [← recurrence1ExceptionalTerm1Row6_eq]
    rw [← recurrence1ExceptionalTerm1Row7_eq]
    unfold recurrence1Remainder31
    ring
  rw [rows]
  have rearrange : recurrence1ExceptionalTerm1Rows = recurrence1ExceptionalTerm1Bands := by
    unfold recurrence1ExceptionalTerm1Rows recurrence1ExceptionalTerm1Bands
    unfold recurrence1ExceptionalTerm1Row0 recurrence1ExceptionalTerm1Row1
    unfold recurrence1ExceptionalTerm1Row2 recurrence1ExceptionalTerm1Row3
    unfold recurrence1ExceptionalTerm1Row4 recurrence1ExceptionalTerm1Row5
    unfold recurrence1ExceptionalTerm1Row6 recurrence1ExceptionalTerm1Row7
    unfold recurrence1ExceptionalTerm1Band0 recurrence1ExceptionalTerm1Band1
    unfold recurrence1ExceptionalTerm1Band2 recurrence1ExceptionalTerm1Band3
    unfold recurrence1ExceptionalTerm1Band4 recurrence1ExceptionalTerm1Band5
    unfold recurrence1ExceptionalTerm1Band6 recurrence1ExceptionalTerm1Band7
    unfold recurrence1ExceptionalTerm1Band8 recurrence1ExceptionalTerm1Band9
    unfold recurrence1ExceptionalTerm1Band10 recurrence1ExceptionalTerm1Band11
    unfold recurrence1ExceptionalTerm1Band12 recurrence1ExceptionalTerm1Band13
    unfold recurrence1ExceptionalTerm1Band14 recurrence1ExceptionalTerm1Band15
    unfold recurrence1ExceptionalTerm1Band16 recurrence1ExceptionalTerm1Band17
    unfold recurrence1ExceptionalTerm1Band18 recurrence1ExceptionalTerm1Band19
    unfold recurrence1ExceptionalTerm1Band20 recurrence1ExceptionalTerm1Band21
    unfold recurrence1ExceptionalTerm1Band22 recurrence1ExceptionalTerm1Band23
    ring
  rw [rearrange]
  unfold recurrence1ExceptionalTerm1Bands recurrence1ExceptionalTerm1
  rw [recurrence1ExceptionalTerm1Band0_eq]
  rw [recurrence1ExceptionalTerm1Band1_eq]
  rw [recurrence1ExceptionalTerm1Band2_eq]
  rw [recurrence1ExceptionalTerm1Band3_eq]
  rw [recurrence1ExceptionalTerm1Band4_eq]
  rw [recurrence1ExceptionalTerm1Band5_eq]
  rw [recurrence1ExceptionalTerm1Band6_eq]
  rw [recurrence1ExceptionalTerm1Band7_eq]
  rw [recurrence1ExceptionalTerm1Band8_eq]
  rw [recurrence1ExceptionalTerm1Band9_eq]
  rw [recurrence1ExceptionalTerm1Band10_eq]
  rw [recurrence1ExceptionalTerm1Band11_eq]
  rw [recurrence1ExceptionalTerm1Band12_eq]
  rw [recurrence1ExceptionalTerm1Band13_eq]
  rw [recurrence1ExceptionalTerm1Band14_eq]
  rw [recurrence1ExceptionalTerm1Band15_eq]
  rw [recurrence1ExceptionalTerm1Band16_eq]
  rw [recurrence1ExceptionalTerm1Band17_eq]
  rw [recurrence1ExceptionalTerm1Band18_eq]
  rw [recurrence1ExceptionalTerm1Band19_eq]
  rw [recurrence1ExceptionalTerm1Band20_eq]
  rw [recurrence1ExceptionalTerm1Band21_eq]
  rw [recurrence1ExceptionalTerm1Band22_eq]
  rw [recurrence1ExceptionalTerm1Band23_eq]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
