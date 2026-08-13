/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B1A1.Bands0To5
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B1A1.Bands6To11
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B1A1.Bands12To17
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B1A1.Bands18To23
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B1A1.Bands24To25
import Mathlib.Tactic.Ring

/-!
# Recurrence 6 certificate: B1A1

This compatibility module combines independently checked row and band
shards for the recurrence-6 B1A1 arithmetic product.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

def recurrence6B1A1Rows : Coefficient :=
  recurrence6B1A1Row0 +
  recurrence6B1A1Row1 +
  recurrence6B1A1Row2 +
  recurrence6B1A1Row3 +
  recurrence6B1A1Row4 +
  recurrence6B1A1Row5 +
  recurrence6B1A1Row6 +
  recurrence6B1A1Row7 +
  recurrence6B1A1Row8 +
  recurrence6B1A1Row9

def recurrence6B1A1Bands : Coefficient :=
  recurrence6B1A1Band0 +
  recurrence6B1A1Band1 +
  recurrence6B1A1Band2 +
  recurrence6B1A1Band3 +
  recurrence6B1A1Band4 +
  recurrence6B1A1Band5 +
  recurrence6B1A1Band6 +
  recurrence6B1A1Band7 +
  recurrence6B1A1Band8 +
  recurrence6B1A1Band9 +
  recurrence6B1A1Band10 +
  recurrence6B1A1Band11 +
  recurrence6B1A1Band12 +
  recurrence6B1A1Band13 +
  recurrence6B1A1Band14 +
  recurrence6B1A1Band15 +
  recurrence6B1A1Band16 +
  recurrence6B1A1Band17 +
  recurrence6B1A1Band18 +
  recurrence6B1A1Band19 +
  recurrence6B1A1Band20 +
  recurrence6B1A1Band21 +
  recurrence6B1A1Band22 +
  recurrence6B1A1Band23 +
  recurrence6B1A1Band24 +
  recurrence6B1A1Band25

theorem remainder7Coefficient1TimesRemainder6Coefficient1_eq :
    remainder7Coefficient1Normalized * remainder6Coefficient1Normalized =
      remainder7Coefficient1TimesRemainder6Coefficient1 := by
  have rows :
      remainder7Coefficient1Normalized * remainder6Coefficient1Normalized =
        recurrence6B1A1Rows := by
    unfold remainder7Coefficient1Normalized recurrence6B1A1Rows
    rw [← recurrence6B1A1Row0_eq]
    rw [← recurrence6B1A1Row1_eq]
    rw [← recurrence6B1A1Row2_eq]
    rw [← recurrence6B1A1Row3_eq]
    rw [← recurrence6B1A1Row4_eq]
    rw [← recurrence6B1A1Row5_eq]
    rw [← recurrence6B1A1Row6_eq]
    rw [← recurrence6B1A1Row7_eq]
    rw [← recurrence6B1A1Row8_eq]
    rw [← recurrence6B1A1Row9_eq]
    unfold remainder6Coefficient1Normalized
    ring
  rw [rows]
  have rearrange : recurrence6B1A1Rows = recurrence6B1A1Bands := by
    unfold recurrence6B1A1Rows recurrence6B1A1Bands recurrence6B1A1Row0 recurrence6B1A1Row1
    unfold recurrence6B1A1Row2 recurrence6B1A1Row3 recurrence6B1A1Row4 recurrence6B1A1Row5
    unfold recurrence6B1A1Row6 recurrence6B1A1Row7 recurrence6B1A1Row8 recurrence6B1A1Row9
    unfold recurrence6B1A1Band0 recurrence6B1A1Band1 recurrence6B1A1Band2 recurrence6B1A1Band3
    unfold recurrence6B1A1Band4 recurrence6B1A1Band5 recurrence6B1A1Band6 recurrence6B1A1Band7
    unfold recurrence6B1A1Band8 recurrence6B1A1Band9 recurrence6B1A1Band10 recurrence6B1A1Band11
    unfold recurrence6B1A1Band12 recurrence6B1A1Band13 recurrence6B1A1Band14 recurrence6B1A1Band15
    unfold recurrence6B1A1Band16 recurrence6B1A1Band17 recurrence6B1A1Band18 recurrence6B1A1Band19
    unfold recurrence6B1A1Band20 recurrence6B1A1Band21 recurrence6B1A1Band22 recurrence6B1A1Band23
    unfold recurrence6B1A1Band24 recurrence6B1A1Band25
    ring
  rw [rearrange]
  unfold recurrence6B1A1Bands remainder7Coefficient1TimesRemainder6Coefficient1
  rw [recurrence6B1A1Band0_eq]
  rw [recurrence6B1A1Band1_eq]
  rw [recurrence6B1A1Band2_eq]
  rw [recurrence6B1A1Band3_eq]
  rw [recurrence6B1A1Band4_eq]
  rw [recurrence6B1A1Band5_eq]
  rw [recurrence6B1A1Band6_eq]
  rw [recurrence6B1A1Band7_eq]
  rw [recurrence6B1A1Band8_eq]
  rw [recurrence6B1A1Band9_eq]
  rw [recurrence6B1A1Band10_eq]
  rw [recurrence6B1A1Band11_eq]
  rw [recurrence6B1A1Band12_eq]
  rw [recurrence6B1A1Band13_eq]
  rw [recurrence6B1A1Band14_eq]
  rw [recurrence6B1A1Band15_eq]
  rw [recurrence6B1A1Band16_eq]
  rw [recurrence6B1A1Band17_eq]
  rw [recurrence6B1A1Band18_eq]
  rw [recurrence6B1A1Band19_eq]
  rw [recurrence6B1A1Band20_eq]
  rw [recurrence6B1A1Band21_eq]
  rw [recurrence6B1A1Band22_eq]
  rw [recurrence6B1A1Band23_eq]
  rw [recurrence6B1A1Band24_eq]
  rw [recurrence6B1A1Band25_eq]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
