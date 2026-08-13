/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term1.Bands0To5
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term1.Bands6To11
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term1.Bands12To17
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term1.Bands18To23
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term1.Bands24To29
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term1.Bands30To35
import Mathlib.Tactic.Ring

/-!
# Recurrence 6 certificate: Term1

This compatibility module combines the independently checked row and band shards
for Term1 of the sixth pseudo-division recurrence.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

def recurrence6Term1Rows : Coefficient :=
  recurrence6Term1Row0 +
  recurrence6Term1Row1 +
  recurrence6Term1Row2 +
  recurrence6Term1Row3 +
  recurrence6Term1Row4 +
  recurrence6Term1Row5 +
  recurrence6Term1Row6 +
  recurrence6Term1Row7 +
  recurrence6Term1Row8 +
  recurrence6Term1Row9 +
  recurrence6Term1Row10 +
  recurrence6Term1Row11 +
  recurrence6Term1Row12 +
  recurrence6Term1Row13 +
  recurrence6Term1Row14 +
  recurrence6Term1Row15 +
  recurrence6Term1Row16 +
  recurrence6Term1Row17

def recurrence6Term1Bands : Coefficient :=
  recurrence6Term1Band0 +
  recurrence6Term1Band1 +
  recurrence6Term1Band2 +
  recurrence6Term1Band3 +
  recurrence6Term1Band4 +
  recurrence6Term1Band5 +
  recurrence6Term1Band6 +
  recurrence6Term1Band7 +
  recurrence6Term1Band8 +
  recurrence6Term1Band9 +
  recurrence6Term1Band10 +
  recurrence6Term1Band11 +
  recurrence6Term1Band12 +
  recurrence6Term1Band13 +
  recurrence6Term1Band14 +
  recurrence6Term1Band15 +
  recurrence6Term1Band16 +
  recurrence6Term1Band17 +
  recurrence6Term1Band18 +
  recurrence6Term1Band19 +
  recurrence6Term1Band20 +
  recurrence6Term1Band21 +
  recurrence6Term1Band22 +
  recurrence6Term1Band23 +
  recurrence6Term1Band24 +
  recurrence6Term1Band25 +
  recurrence6Term1Band26 +
  recurrence6Term1Band27 +
  recurrence6Term1Band28 +
  recurrence6Term1Band29 +
  recurrence6Term1Band30 +
  recurrence6Term1Band31 +
  recurrence6Term1Band32 +
  recurrence6Term1Band33 +
  recurrence6Term1Band34 +
  recurrence6Term1Band35

theorem normalizedResidual6Term1_eq :
    remainder6Coefficient0Normalized * remainder7Coefficient1Square =
      normalizedResidual6Term1 := by
  have rows :
      remainder6Coefficient0Normalized * remainder7Coefficient1Square =
        recurrence6Term1Rows := by
    unfold remainder6Coefficient0Normalized recurrence6Term1Rows
    rw [← recurrence6Term1Row0_eq]
    rw [← recurrence6Term1Row1_eq]
    rw [← recurrence6Term1Row2_eq]
    rw [← recurrence6Term1Row3_eq]
    rw [← recurrence6Term1Row4_eq]
    rw [← recurrence6Term1Row5_eq]
    rw [← recurrence6Term1Row6_eq]
    rw [← recurrence6Term1Row7_eq]
    rw [← recurrence6Term1Row8_eq]
    rw [← recurrence6Term1Row9_eq]
    rw [← recurrence6Term1Row10_eq]
    rw [← recurrence6Term1Row11_eq]
    rw [← recurrence6Term1Row12_eq]
    rw [← recurrence6Term1Row13_eq]
    rw [← recurrence6Term1Row14_eq]
    rw [← recurrence6Term1Row15_eq]
    rw [← recurrence6Term1Row16_eq]
    rw [← recurrence6Term1Row17_eq]
    unfold remainder7Coefficient1Square
    ring
  rw [rows]
  have rearrange : recurrence6Term1Rows = recurrence6Term1Bands := by
    unfold recurrence6Term1Rows recurrence6Term1Bands recurrence6Term1Row0 recurrence6Term1Row1
    unfold recurrence6Term1Row2 recurrence6Term1Row3 recurrence6Term1Row4 recurrence6Term1Row5
    unfold recurrence6Term1Row6 recurrence6Term1Row7 recurrence6Term1Row8 recurrence6Term1Row9
    unfold recurrence6Term1Row10 recurrence6Term1Row11 recurrence6Term1Row12 recurrence6Term1Row13
    unfold recurrence6Term1Row14 recurrence6Term1Row15 recurrence6Term1Row16 recurrence6Term1Row17
    unfold recurrence6Term1Band0 recurrence6Term1Band1 recurrence6Term1Band2 recurrence6Term1Band3
    unfold recurrence6Term1Band4 recurrence6Term1Band5 recurrence6Term1Band6 recurrence6Term1Band7
    unfold recurrence6Term1Band8 recurrence6Term1Band9 recurrence6Term1Band10 recurrence6Term1Band11
    unfold recurrence6Term1Band12 recurrence6Term1Band13 recurrence6Term1Band14
    unfold recurrence6Term1Band15 recurrence6Term1Band16 recurrence6Term1Band17
    unfold recurrence6Term1Band18 recurrence6Term1Band19 recurrence6Term1Band20
    unfold recurrence6Term1Band21 recurrence6Term1Band22 recurrence6Term1Band23
    unfold recurrence6Term1Band24 recurrence6Term1Band25 recurrence6Term1Band26
    unfold recurrence6Term1Band27 recurrence6Term1Band28 recurrence6Term1Band29
    unfold recurrence6Term1Band30 recurrence6Term1Band31 recurrence6Term1Band32
    unfold recurrence6Term1Band33 recurrence6Term1Band34 recurrence6Term1Band35
    ring
  rw [rearrange]
  unfold recurrence6Term1Bands normalizedResidual6Term1
  rw [recurrence6Term1Band0_eq]
  rw [recurrence6Term1Band1_eq]
  rw [recurrence6Term1Band2_eq]
  rw [recurrence6Term1Band3_eq]
  rw [recurrence6Term1Band4_eq]
  rw [recurrence6Term1Band5_eq]
  rw [recurrence6Term1Band6_eq]
  rw [recurrence6Term1Band7_eq]
  rw [recurrence6Term1Band8_eq]
  rw [recurrence6Term1Band9_eq]
  rw [recurrence6Term1Band10_eq]
  rw [recurrence6Term1Band11_eq]
  rw [recurrence6Term1Band12_eq]
  rw [recurrence6Term1Band13_eq]
  rw [recurrence6Term1Band14_eq]
  rw [recurrence6Term1Band15_eq]
  rw [recurrence6Term1Band16_eq]
  rw [recurrence6Term1Band17_eq]
  rw [recurrence6Term1Band18_eq]
  rw [recurrence6Term1Band19_eq]
  rw [recurrence6Term1Band20_eq]
  rw [recurrence6Term1Band21_eq]
  rw [recurrence6Term1Band22_eq]
  rw [recurrence6Term1Band23_eq]
  rw [recurrence6Term1Band24_eq]
  rw [recurrence6Term1Band25_eq]
  rw [recurrence6Term1Band26_eq]
  rw [recurrence6Term1Band27_eq]
  rw [recurrence6Term1Band28_eq]
  rw [recurrence6Term1Band29_eq]
  rw [recurrence6Term1Band30_eq]
  rw [recurrence6Term1Band31_eq]
  rw [recurrence6Term1Band32_eq]
  rw [recurrence6Term1Band33_eq]
  rw [recurrence6Term1Band34_eq]
  rw [recurrence6Term1Band35_eq]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
