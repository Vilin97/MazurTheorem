/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1Remainder2Data
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1CommonData
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1RowData1

import Mathlib.Tactic.Ring

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1QuotientTerm1.Bands0To11
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1QuotientTerm1.Bands12To23

/-!
# Recurrence 1 certificate: QuotientTerm1

This file is a checked bounded-band arithmetic shard for the first
pseudo-division recurrence in the order-seven branch-zero resultant certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

/-- Internal datum. -/ def recurrence1QuotientTerm1Rows : Coefficient :=
  recurrence1QuotientTerm1Row0 +
  recurrence1QuotientTerm1Row1 +
  recurrence1QuotientTerm1Row2 +
  recurrence1QuotientTerm1Row3 +
  recurrence1QuotientTerm1Row4 +
  recurrence1QuotientTerm1Row5 +
  recurrence1QuotientTerm1Row6 +
  recurrence1QuotientTerm1Row7 +
  recurrence1QuotientTerm1Row8 +
  recurrence1QuotientTerm1Row9 +
  recurrence1QuotientTerm1Row10

/-- Internal datum. -/ def recurrence1QuotientTerm1Bands : Coefficient :=
  recurrence1QuotientTerm1Band0 +
  recurrence1QuotientTerm1Band1 +
  recurrence1QuotientTerm1Band2 +
  recurrence1QuotientTerm1Band3 +
  recurrence1QuotientTerm1Band4 +
  recurrence1QuotientTerm1Band5 +
  recurrence1QuotientTerm1Band6 +
  recurrence1QuotientTerm1Band7 +
  recurrence1QuotientTerm1Band8 +
  recurrence1QuotientTerm1Band9 +
  recurrence1QuotientTerm1Band10 +
  recurrence1QuotientTerm1Band11 +
  recurrence1QuotientTerm1Band12 +
  recurrence1QuotientTerm1Band13 +
  recurrence1QuotientTerm1Band14 +
  recurrence1QuotientTerm1Band15 +
  recurrence1QuotientTerm1Band16 +
  recurrence1QuotientTerm1Band17 +
  recurrence1QuotientTerm1Band18 +
  recurrence1QuotientTerm1Band19 +
  recurrence1QuotientTerm1Band20 +
  recurrence1QuotientTerm1Band21 +
  recurrence1QuotientTerm1Band22 +
  recurrence1QuotientTerm1Band23

theorem recurrence1QuotientTerm1_eq :
    recurrence1QuotientConstant * recurrence1Remainder21 =
      recurrence1QuotientTerm1 := by
  have rows :
      recurrence1QuotientConstant * recurrence1Remainder21 =
        recurrence1QuotientTerm1Rows := by
    unfold recurrence1QuotientConstant recurrence1QuotientTerm1Rows
    rw [← recurrence1QuotientTerm1Row0_eq]
    rw [← recurrence1QuotientTerm1Row1_eq]
    rw [← recurrence1QuotientTerm1Row2_eq]
    rw [← recurrence1QuotientTerm1Row3_eq]
    rw [← recurrence1QuotientTerm1Row4_eq]
    rw [← recurrence1QuotientTerm1Row5_eq]
    rw [← recurrence1QuotientTerm1Row6_eq]
    rw [← recurrence1QuotientTerm1Row7_eq]
    rw [← recurrence1QuotientTerm1Row8_eq]
    rw [← recurrence1QuotientTerm1Row9_eq]
    rw [← recurrence1QuotientTerm1Row10_eq]
    unfold recurrence1Remainder21
    ring
  rw [rows]
  have rearrange : recurrence1QuotientTerm1Rows = recurrence1QuotientTerm1Bands := by
    unfold recurrence1QuotientTerm1Rows recurrence1QuotientTerm1Bands recurrence1QuotientTerm1Row0
    unfold recurrence1QuotientTerm1Row1 recurrence1QuotientTerm1Row2 recurrence1QuotientTerm1Row3
    unfold recurrence1QuotientTerm1Row4 recurrence1QuotientTerm1Row5 recurrence1QuotientTerm1Row6
    unfold recurrence1QuotientTerm1Row7 recurrence1QuotientTerm1Row8 recurrence1QuotientTerm1Row9
    unfold recurrence1QuotientTerm1Row10 recurrence1QuotientTerm1Band0 recurrence1QuotientTerm1Band1
    unfold recurrence1QuotientTerm1Band2 recurrence1QuotientTerm1Band3 recurrence1QuotientTerm1Band4
    unfold recurrence1QuotientTerm1Band5 recurrence1QuotientTerm1Band6 recurrence1QuotientTerm1Band7
    unfold recurrence1QuotientTerm1Band8 recurrence1QuotientTerm1Band9
    unfold recurrence1QuotientTerm1Band10 recurrence1QuotientTerm1Band11
    unfold recurrence1QuotientTerm1Band12 recurrence1QuotientTerm1Band13
    unfold recurrence1QuotientTerm1Band14 recurrence1QuotientTerm1Band15
    unfold recurrence1QuotientTerm1Band16 recurrence1QuotientTerm1Band17
    unfold recurrence1QuotientTerm1Band18 recurrence1QuotientTerm1Band19
    unfold recurrence1QuotientTerm1Band20 recurrence1QuotientTerm1Band21
    unfold recurrence1QuotientTerm1Band22 recurrence1QuotientTerm1Band23
    ring
  rw [rearrange]
  unfold recurrence1QuotientTerm1Bands recurrence1QuotientTerm1
  rw [recurrence1QuotientTerm1Band0_eq]
  rw [recurrence1QuotientTerm1Band1_eq]
  rw [recurrence1QuotientTerm1Band2_eq]
  rw [recurrence1QuotientTerm1Band3_eq]
  rw [recurrence1QuotientTerm1Band4_eq]
  rw [recurrence1QuotientTerm1Band5_eq]
  rw [recurrence1QuotientTerm1Band6_eq]
  rw [recurrence1QuotientTerm1Band7_eq]
  rw [recurrence1QuotientTerm1Band8_eq]
  rw [recurrence1QuotientTerm1Band9_eq]
  rw [recurrence1QuotientTerm1Band10_eq]
  rw [recurrence1QuotientTerm1Band11_eq]
  rw [recurrence1QuotientTerm1Band12_eq]
  rw [recurrence1QuotientTerm1Band13_eq]
  rw [recurrence1QuotientTerm1Band14_eq]
  rw [recurrence1QuotientTerm1Band15_eq]
  rw [recurrence1QuotientTerm1Band16_eq]
  rw [recurrence1QuotientTerm1Band17_eq]
  rw [recurrence1QuotientTerm1Band18_eq]
  rw [recurrence1QuotientTerm1Band19_eq]
  rw [recurrence1QuotientTerm1Band20_eq]
  rw [recurrence1QuotientTerm1Band21_eq]
  rw [recurrence1QuotientTerm1Band22_eq]
  rw [recurrence1QuotientTerm1Band23_eq]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
