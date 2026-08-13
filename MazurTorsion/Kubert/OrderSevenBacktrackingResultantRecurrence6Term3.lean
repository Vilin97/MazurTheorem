/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term3.Bands0To5
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term3.Bands6To11
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term3.Bands12To17
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term3.Bands18To23
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term3.Bands24To29
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term3.Bands30To35
import Mathlib.Tactic.Ring

/-!
# Recurrence 6 certificate: Term3

This compatibility module combines independently checked row and band
shards for the recurrence-6 Term3 arithmetic product.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

/-- Internal datum. -/ def recurrence6Term3Rows : Coefficient :=
  recurrence6Term3Row0 +
  recurrence6Term3Row1 +
  recurrence6Term3Row2 +
  recurrence6Term3Row3

/-- Internal datum. -/ def recurrence6Term3Bands : Coefficient :=
  recurrence6Term3Band0 +
  recurrence6Term3Band1 +
  recurrence6Term3Band2 +
  recurrence6Term3Band3 +
  recurrence6Term3Band4 +
  recurrence6Term3Band5 +
  recurrence6Term3Band6 +
  recurrence6Term3Band7 +
  recurrence6Term3Band8 +
  recurrence6Term3Band9 +
  recurrence6Term3Band10 +
  recurrence6Term3Band11 +
  recurrence6Term3Band12 +
  recurrence6Term3Band13 +
  recurrence6Term3Band14 +
  recurrence6Term3Band15 +
  recurrence6Term3Band16 +
  recurrence6Term3Band17 +
  recurrence6Term3Band18 +
  recurrence6Term3Band19 +
  recurrence6Term3Band20 +
  recurrence6Term3Band21 +
  recurrence6Term3Band22 +
  recurrence6Term3Band23 +
  recurrence6Term3Band24 +
  recurrence6Term3Band25 +
  recurrence6Term3Band26 +
  recurrence6Term3Band27 +
  recurrence6Term3Band28 +
  recurrence6Term3Band29 +
  recurrence6Term3Band30 +
  recurrence6Term3Band31 +
  recurrence6Term3Band32 +
  recurrence6Term3Band33 +
  recurrence6Term3Band34 +
  recurrence6Term3Band35

theorem normalizedResidual6Term3_eq :
    normalizedExceptional6 * remainder6Coefficient2Square =
      normalizedResidual6Term3 := by
  have rows :
      normalizedExceptional6 * remainder6Coefficient2Square =
        recurrence6Term3Rows := by
    unfold normalizedExceptional6 recurrence6Term3Rows
    rw [← recurrence6Term3Row0_eq]
    rw [← recurrence6Term3Row1_eq]
    rw [← recurrence6Term3Row2_eq]
    rw [← recurrence6Term3Row3_eq]
    unfold remainder6Coefficient2Square
    ring
  rw [rows]
  have rearrange : recurrence6Term3Rows = recurrence6Term3Bands := by
    unfold recurrence6Term3Rows recurrence6Term3Bands recurrence6Term3Row0 recurrence6Term3Row1
    unfold recurrence6Term3Row2 recurrence6Term3Row3 recurrence6Term3Band0 recurrence6Term3Band1
    unfold recurrence6Term3Band2 recurrence6Term3Band3 recurrence6Term3Band4 recurrence6Term3Band5
    unfold recurrence6Term3Band6 recurrence6Term3Band7 recurrence6Term3Band8 recurrence6Term3Band9
    unfold recurrence6Term3Band10 recurrence6Term3Band11 recurrence6Term3Band12
    unfold recurrence6Term3Band13 recurrence6Term3Band14 recurrence6Term3Band15
    unfold recurrence6Term3Band16 recurrence6Term3Band17 recurrence6Term3Band18
    unfold recurrence6Term3Band19 recurrence6Term3Band20 recurrence6Term3Band21
    unfold recurrence6Term3Band22 recurrence6Term3Band23 recurrence6Term3Band24
    unfold recurrence6Term3Band25 recurrence6Term3Band26 recurrence6Term3Band27
    unfold recurrence6Term3Band28 recurrence6Term3Band29 recurrence6Term3Band30
    unfold recurrence6Term3Band31 recurrence6Term3Band32 recurrence6Term3Band33
    unfold recurrence6Term3Band34 recurrence6Term3Band35
    ring
  rw [rearrange]
  unfold recurrence6Term3Bands normalizedResidual6Term3
  rw [recurrence6Term3Band0_eq]
  rw [recurrence6Term3Band1_eq]
  rw [recurrence6Term3Band2_eq]
  rw [recurrence6Term3Band3_eq]
  rw [recurrence6Term3Band4_eq]
  rw [recurrence6Term3Band5_eq]
  rw [recurrence6Term3Band6_eq]
  rw [recurrence6Term3Band7_eq]
  rw [recurrence6Term3Band8_eq]
  rw [recurrence6Term3Band9_eq]
  rw [recurrence6Term3Band10_eq]
  rw [recurrence6Term3Band11_eq]
  rw [recurrence6Term3Band12_eq]
  rw [recurrence6Term3Band13_eq]
  rw [recurrence6Term3Band14_eq]
  rw [recurrence6Term3Band15_eq]
  rw [recurrence6Term3Band16_eq]
  rw [recurrence6Term3Band17_eq]
  rw [recurrence6Term3Band18_eq]
  rw [recurrence6Term3Band19_eq]
  rw [recurrence6Term3Band20_eq]
  rw [recurrence6Term3Band21_eq]
  rw [recurrence6Term3Band22_eq]
  rw [recurrence6Term3Band23_eq]
  rw [recurrence6Term3Band24_eq]
  rw [recurrence6Term3Band25_eq]
  rw [recurrence6Term3Band26_eq]
  rw [recurrence6Term3Band27_eq]
  rw [recurrence6Term3Band28_eq]
  rw [recurrence6Term3Band29_eq]
  rw [recurrence6Term3Band30_eq]
  rw [recurrence6Term3Band31_eq]
  rw [recurrence6Term3Band32_eq]
  rw [recurrence6Term3Band33_eq]
  rw [recurrence6Term3Band34_eq]
  rw [recurrence6Term3Band35_eq]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
