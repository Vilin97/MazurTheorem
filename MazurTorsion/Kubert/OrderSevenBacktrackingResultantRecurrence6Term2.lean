/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term2.Bands0To5
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term2.Bands6To11
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term2.Bands12To17
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term2.Bands18To23
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term2.Bands24To29
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term2.Bands30To35
import Mathlib.Tactic.Ring

/-!
# Recurrence 6 certificate: Term2

This compatibility module combines independently checked row and band
shards for the recurrence-6 Term2 arithmetic product.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

/-- Internal datum. -/ def recurrence6Term2Rows : Coefficient :=
  recurrence6Term2Row0 +
  recurrence6Term2Row1 +
  recurrence6Term2Row2 +
  recurrence6Term2Row3 +
  recurrence6Term2Row4 +
  recurrence6Term2Row5 +
  recurrence6Term2Row6 +
  recurrence6Term2Row7 +
  recurrence6Term2Row8 +
  recurrence6Term2Row9

/-- Internal datum. -/ def recurrence6Term2Bands : Coefficient :=
  recurrence6Term2Band0 +
  recurrence6Term2Band1 +
  recurrence6Term2Band2 +
  recurrence6Term2Band3 +
  recurrence6Term2Band4 +
  recurrence6Term2Band5 +
  recurrence6Term2Band6 +
  recurrence6Term2Band7 +
  recurrence6Term2Band8 +
  recurrence6Term2Band9 +
  recurrence6Term2Band10 +
  recurrence6Term2Band11 +
  recurrence6Term2Band12 +
  recurrence6Term2Band13 +
  recurrence6Term2Band14 +
  recurrence6Term2Band15 +
  recurrence6Term2Band16 +
  recurrence6Term2Band17 +
  recurrence6Term2Band18 +
  recurrence6Term2Band19 +
  recurrence6Term2Band20 +
  recurrence6Term2Band21 +
  recurrence6Term2Band22 +
  recurrence6Term2Band23 +
  recurrence6Term2Band24 +
  recurrence6Term2Band25 +
  recurrence6Term2Band26 +
  recurrence6Term2Band27 +
  recurrence6Term2Band28 +
  recurrence6Term2Band29 +
  recurrence6Term2Band30 +
  recurrence6Term2Band31 +
  recurrence6Term2Band32 +
  recurrence6Term2Band33 +
  recurrence6Term2Band34 +
  recurrence6Term2Band35

theorem normalizedResidual6Term2_eq :
    remainder7Coefficient0Normalized * normalizedResidual6Inner =
      normalizedResidual6Term2 := by
  have rows :
      remainder7Coefficient0Normalized * normalizedResidual6Inner =
        recurrence6Term2Rows := by
    unfold remainder7Coefficient0Normalized recurrence6Term2Rows
    rw [← recurrence6Term2Row0_eq]
    rw [← recurrence6Term2Row1_eq]
    rw [← recurrence6Term2Row2_eq]
    rw [← recurrence6Term2Row3_eq]
    rw [← recurrence6Term2Row4_eq]
    rw [← recurrence6Term2Row5_eq]
    rw [← recurrence6Term2Row6_eq]
    rw [← recurrence6Term2Row7_eq]
    rw [← recurrence6Term2Row8_eq]
    rw [← recurrence6Term2Row9_eq]
    unfold normalizedResidual6Inner
    ring
  rw [rows]
  have rearrange : recurrence6Term2Rows = recurrence6Term2Bands := by
    unfold recurrence6Term2Rows recurrence6Term2Bands recurrence6Term2Row0 recurrence6Term2Row1
    unfold recurrence6Term2Row2 recurrence6Term2Row3 recurrence6Term2Row4 recurrence6Term2Row5
    unfold recurrence6Term2Row6 recurrence6Term2Row7 recurrence6Term2Row8 recurrence6Term2Row9
    unfold recurrence6Term2Band0 recurrence6Term2Band1 recurrence6Term2Band2 recurrence6Term2Band3
    unfold recurrence6Term2Band4 recurrence6Term2Band5 recurrence6Term2Band6 recurrence6Term2Band7
    unfold recurrence6Term2Band8 recurrence6Term2Band9 recurrence6Term2Band10 recurrence6Term2Band11
    unfold recurrence6Term2Band12 recurrence6Term2Band13 recurrence6Term2Band14
    unfold recurrence6Term2Band15 recurrence6Term2Band16 recurrence6Term2Band17
    unfold recurrence6Term2Band18 recurrence6Term2Band19 recurrence6Term2Band20
    unfold recurrence6Term2Band21 recurrence6Term2Band22 recurrence6Term2Band23
    unfold recurrence6Term2Band24 recurrence6Term2Band25 recurrence6Term2Band26
    unfold recurrence6Term2Band27 recurrence6Term2Band28 recurrence6Term2Band29
    unfold recurrence6Term2Band30 recurrence6Term2Band31 recurrence6Term2Band32
    unfold recurrence6Term2Band33 recurrence6Term2Band34 recurrence6Term2Band35
    ring
  rw [rearrange]
  unfold recurrence6Term2Bands normalizedResidual6Term2
  rw [recurrence6Term2Band0_eq]
  rw [recurrence6Term2Band1_eq]
  rw [recurrence6Term2Band2_eq]
  rw [recurrence6Term2Band3_eq]
  rw [recurrence6Term2Band4_eq]
  rw [recurrence6Term2Band5_eq]
  rw [recurrence6Term2Band6_eq]
  rw [recurrence6Term2Band7_eq]
  rw [recurrence6Term2Band8_eq]
  rw [recurrence6Term2Band9_eq]
  rw [recurrence6Term2Band10_eq]
  rw [recurrence6Term2Band11_eq]
  rw [recurrence6Term2Band12_eq]
  rw [recurrence6Term2Band13_eq]
  rw [recurrence6Term2Band14_eq]
  rw [recurrence6Term2Band15_eq]
  rw [recurrence6Term2Band16_eq]
  rw [recurrence6Term2Band17_eq]
  rw [recurrence6Term2Band18_eq]
  rw [recurrence6Term2Band19_eq]
  rw [recurrence6Term2Band20_eq]
  rw [recurrence6Term2Band21_eq]
  rw [recurrence6Term2Band22_eq]
  rw [recurrence6Term2Band23_eq]
  rw [recurrence6Term2Band24_eq]
  rw [recurrence6Term2Band25_eq]
  rw [recurrence6Term2Band26_eq]
  rw [recurrence6Term2Band27_eq]
  rw [recurrence6Term2Band28_eq]
  rw [recurrence6Term2Band29_eq]
  rw [recurrence6Term2Band30_eq]
  rw [recurrence6Term2Band31_eq]
  rw [recurrence6Term2Band32_eq]
  rw [recurrence6Term2Band33_eq]
  rw [recurrence6Term2Band34_eq]
  rw [recurrence6Term2Band35_eq]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
