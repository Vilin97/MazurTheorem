/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B0A2.Bands0To5
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B0A2.Bands6To11
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B0A2.Bands12To17
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B0A2.Bands18To23
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B0A2.Bands24To25
import Mathlib.Tactic.Ring

/-!
# Recurrence 6 certificate: B0A2

This compatibility module combines independently checked row and band
shards for the recurrence-6 B0A2 arithmetic product.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

def recurrence6B0A2Rows : Coefficient :=
  recurrence6B0A2Row0 +
  recurrence6B0A2Row1 +
  recurrence6B0A2Row2 +
  recurrence6B0A2Row3 +
  recurrence6B0A2Row4 +
  recurrence6B0A2Row5 +
  recurrence6B0A2Row6 +
  recurrence6B0A2Row7 +
  recurrence6B0A2Row8 +
  recurrence6B0A2Row9

def recurrence6B0A2Bands : Coefficient :=
  recurrence6B0A2Band0 +
  recurrence6B0A2Band1 +
  recurrence6B0A2Band2 +
  recurrence6B0A2Band3 +
  recurrence6B0A2Band4 +
  recurrence6B0A2Band5 +
  recurrence6B0A2Band6 +
  recurrence6B0A2Band7 +
  recurrence6B0A2Band8 +
  recurrence6B0A2Band9 +
  recurrence6B0A2Band10 +
  recurrence6B0A2Band11 +
  recurrence6B0A2Band12 +
  recurrence6B0A2Band13 +
  recurrence6B0A2Band14 +
  recurrence6B0A2Band15 +
  recurrence6B0A2Band16 +
  recurrence6B0A2Band17 +
  recurrence6B0A2Band18 +
  recurrence6B0A2Band19 +
  recurrence6B0A2Band20 +
  recurrence6B0A2Band21 +
  recurrence6B0A2Band22 +
  recurrence6B0A2Band23 +
  recurrence6B0A2Band24 +
  recurrence6B0A2Band25

theorem remainder7Coefficient0TimesRemainder6Coefficient2_eq :
    remainder7Coefficient0Normalized * remainder6Coefficient2Normalized =
      remainder7Coefficient0TimesRemainder6Coefficient2 := by
  have rows :
      remainder7Coefficient0Normalized * remainder6Coefficient2Normalized =
        recurrence6B0A2Rows := by
    unfold remainder7Coefficient0Normalized recurrence6B0A2Rows
    rw [← recurrence6B0A2Row0_eq]
    rw [← recurrence6B0A2Row1_eq]
    rw [← recurrence6B0A2Row2_eq]
    rw [← recurrence6B0A2Row3_eq]
    rw [← recurrence6B0A2Row4_eq]
    rw [← recurrence6B0A2Row5_eq]
    rw [← recurrence6B0A2Row6_eq]
    rw [← recurrence6B0A2Row7_eq]
    rw [← recurrence6B0A2Row8_eq]
    rw [← recurrence6B0A2Row9_eq]
    unfold remainder6Coefficient2Normalized
    ring
  rw [rows]
  have rearrange : recurrence6B0A2Rows = recurrence6B0A2Bands := by
    unfold recurrence6B0A2Rows recurrence6B0A2Bands recurrence6B0A2Row0 recurrence6B0A2Row1
    unfold recurrence6B0A2Row2 recurrence6B0A2Row3 recurrence6B0A2Row4 recurrence6B0A2Row5
    unfold recurrence6B0A2Row6 recurrence6B0A2Row7 recurrence6B0A2Row8 recurrence6B0A2Row9
    unfold recurrence6B0A2Band0 recurrence6B0A2Band1 recurrence6B0A2Band2 recurrence6B0A2Band3
    unfold recurrence6B0A2Band4 recurrence6B0A2Band5 recurrence6B0A2Band6 recurrence6B0A2Band7
    unfold recurrence6B0A2Band8 recurrence6B0A2Band9 recurrence6B0A2Band10 recurrence6B0A2Band11
    unfold recurrence6B0A2Band12 recurrence6B0A2Band13 recurrence6B0A2Band14 recurrence6B0A2Band15
    unfold recurrence6B0A2Band16 recurrence6B0A2Band17 recurrence6B0A2Band18 recurrence6B0A2Band19
    unfold recurrence6B0A2Band20 recurrence6B0A2Band21 recurrence6B0A2Band22 recurrence6B0A2Band23
    unfold recurrence6B0A2Band24 recurrence6B0A2Band25
    ring
  rw [rearrange]
  unfold recurrence6B0A2Bands remainder7Coefficient0TimesRemainder6Coefficient2
  rw [recurrence6B0A2Band0_eq]
  rw [recurrence6B0A2Band1_eq]
  rw [recurrence6B0A2Band2_eq]
  rw [recurrence6B0A2Band3_eq]
  rw [recurrence6B0A2Band4_eq]
  rw [recurrence6B0A2Band5_eq]
  rw [recurrence6B0A2Band6_eq]
  rw [recurrence6B0A2Band7_eq]
  rw [recurrence6B0A2Band8_eq]
  rw [recurrence6B0A2Band9_eq]
  rw [recurrence6B0A2Band10_eq]
  rw [recurrence6B0A2Band11_eq]
  rw [recurrence6B0A2Band12_eq]
  rw [recurrence6B0A2Band13_eq]
  rw [recurrence6B0A2Band14_eq]
  rw [recurrence6B0A2Band15_eq]
  rw [recurrence6B0A2Band16_eq]
  rw [recurrence6B0A2Band17_eq]
  rw [recurrence6B0A2Band18_eq]
  rw [recurrence6B0A2Band19_eq]
  rw [recurrence6B0A2Band20_eq]
  rw [recurrence6B0A2Band21_eq]
  rw [recurrence6B0A2Band22_eq]
  rw [recurrence6B0A2Band23_eq]
  rw [recurrence6B0A2Band24_eq]
  rw [recurrence6B0A2Band25_eq]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
