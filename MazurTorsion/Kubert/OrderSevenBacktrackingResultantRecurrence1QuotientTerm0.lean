/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1Remainder2Data
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1CommonData
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1RowData0

import Mathlib.Tactic.Ring

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1QuotientTerm0.Bands0To12
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1QuotientTerm0.Bands13To24

/-!
# Recurrence 1 certificate: QuotientTerm0

This file is a checked bounded-band arithmetic shard for the first
pseudo-division recurrence in the order-seven branch-zero resultant certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

def recurrence1QuotientTerm0Rows : Coefficient :=
  recurrence1QuotientTerm0Row0 +
  recurrence1QuotientTerm0Row1 +
  recurrence1QuotientTerm0Row2 +
  recurrence1QuotientTerm0Row3 +
  recurrence1QuotientTerm0Row4 +
  recurrence1QuotientTerm0Row5 +
  recurrence1QuotientTerm0Row6 +
  recurrence1QuotientTerm0Row7 +
  recurrence1QuotientTerm0Row8 +
  recurrence1QuotientTerm0Row9 +
  recurrence1QuotientTerm0Row10

def recurrence1QuotientTerm0Bands : Coefficient :=
  recurrence1QuotientTerm0Band0 +
  recurrence1QuotientTerm0Band1 +
  recurrence1QuotientTerm0Band2 +
  recurrence1QuotientTerm0Band3 +
  recurrence1QuotientTerm0Band4 +
  recurrence1QuotientTerm0Band5 +
  recurrence1QuotientTerm0Band6 +
  recurrence1QuotientTerm0Band7 +
  recurrence1QuotientTerm0Band8 +
  recurrence1QuotientTerm0Band9 +
  recurrence1QuotientTerm0Band10 +
  recurrence1QuotientTerm0Band11 +
  recurrence1QuotientTerm0Band12 +
  recurrence1QuotientTerm0Band13 +
  recurrence1QuotientTerm0Band14 +
  recurrence1QuotientTerm0Band15 +
  recurrence1QuotientTerm0Band16 +
  recurrence1QuotientTerm0Band17 +
  recurrence1QuotientTerm0Band18 +
  recurrence1QuotientTerm0Band19 +
  recurrence1QuotientTerm0Band20 +
  recurrence1QuotientTerm0Band21 +
  recurrence1QuotientTerm0Band22 +
  recurrence1QuotientTerm0Band23 +
  recurrence1QuotientTerm0Band24

theorem recurrence1QuotientTerm0_eq :
    recurrence1QuotientConstant * recurrence1Remainder20 =
      recurrence1QuotientTerm0 := by
  have rows :
      recurrence1QuotientConstant * recurrence1Remainder20 =
        recurrence1QuotientTerm0Rows := by
    unfold recurrence1QuotientConstant recurrence1QuotientTerm0Rows
    rw [← recurrence1QuotientTerm0Row0_eq]
    rw [← recurrence1QuotientTerm0Row1_eq]
    rw [← recurrence1QuotientTerm0Row2_eq]
    rw [← recurrence1QuotientTerm0Row3_eq]
    rw [← recurrence1QuotientTerm0Row4_eq]
    rw [← recurrence1QuotientTerm0Row5_eq]
    rw [← recurrence1QuotientTerm0Row6_eq]
    rw [← recurrence1QuotientTerm0Row7_eq]
    rw [← recurrence1QuotientTerm0Row8_eq]
    rw [← recurrence1QuotientTerm0Row9_eq]
    rw [← recurrence1QuotientTerm0Row10_eq]
    unfold recurrence1Remainder20
    ring
  rw [rows]
  have rearrange : recurrence1QuotientTerm0Rows = recurrence1QuotientTerm0Bands := by
    unfold recurrence1QuotientTerm0Rows recurrence1QuotientTerm0Bands recurrence1QuotientTerm0Row0
    unfold recurrence1QuotientTerm0Row1 recurrence1QuotientTerm0Row2 recurrence1QuotientTerm0Row3
    unfold recurrence1QuotientTerm0Row4 recurrence1QuotientTerm0Row5 recurrence1QuotientTerm0Row6
    unfold recurrence1QuotientTerm0Row7 recurrence1QuotientTerm0Row8 recurrence1QuotientTerm0Row9
    unfold recurrence1QuotientTerm0Row10 recurrence1QuotientTerm0Band0 recurrence1QuotientTerm0Band1
    unfold recurrence1QuotientTerm0Band2 recurrence1QuotientTerm0Band3 recurrence1QuotientTerm0Band4
    unfold recurrence1QuotientTerm0Band5 recurrence1QuotientTerm0Band6 recurrence1QuotientTerm0Band7
    unfold recurrence1QuotientTerm0Band8 recurrence1QuotientTerm0Band9
    unfold recurrence1QuotientTerm0Band10 recurrence1QuotientTerm0Band11
    unfold recurrence1QuotientTerm0Band12 recurrence1QuotientTerm0Band13
    unfold recurrence1QuotientTerm0Band14 recurrence1QuotientTerm0Band15
    unfold recurrence1QuotientTerm0Band16 recurrence1QuotientTerm0Band17
    unfold recurrence1QuotientTerm0Band18 recurrence1QuotientTerm0Band19
    unfold recurrence1QuotientTerm0Band20 recurrence1QuotientTerm0Band21
    unfold recurrence1QuotientTerm0Band22 recurrence1QuotientTerm0Band23
    unfold recurrence1QuotientTerm0Band24
    ring
  rw [rearrange]
  unfold recurrence1QuotientTerm0Bands recurrence1QuotientTerm0
  rw [recurrence1QuotientTerm0Band0_eq]
  rw [recurrence1QuotientTerm0Band1_eq]
  rw [recurrence1QuotientTerm0Band2_eq]
  rw [recurrence1QuotientTerm0Band3_eq]
  rw [recurrence1QuotientTerm0Band4_eq]
  rw [recurrence1QuotientTerm0Band5_eq]
  rw [recurrence1QuotientTerm0Band6_eq]
  rw [recurrence1QuotientTerm0Band7_eq]
  rw [recurrence1QuotientTerm0Band8_eq]
  rw [recurrence1QuotientTerm0Band9_eq]
  rw [recurrence1QuotientTerm0Band10_eq]
  rw [recurrence1QuotientTerm0Band11_eq]
  rw [recurrence1QuotientTerm0Band12_eq]
  rw [recurrence1QuotientTerm0Band13_eq]
  rw [recurrence1QuotientTerm0Band14_eq]
  rw [recurrence1QuotientTerm0Band15_eq]
  rw [recurrence1QuotientTerm0Band16_eq]
  rw [recurrence1QuotientTerm0Band17_eq]
  rw [recurrence1QuotientTerm0Band18_eq]
  rw [recurrence1QuotientTerm0Band19_eq]
  rw [recurrence1QuotientTerm0Band20_eq]
  rw [recurrence1QuotientTerm0Band21_eq]
  rw [recurrence1QuotientTerm0Band22_eq]
  rw [recurrence1QuotientTerm0Band23_eq]
  rw [recurrence1QuotientTerm0Band24_eq]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
