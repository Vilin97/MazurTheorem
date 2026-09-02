/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6A2Square.Bands0To5
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6A2Square.Bands6To11
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6A2Square.Bands12To17
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6A2Square.Bands18To23
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6A2Square.Bands24To29
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6A2Square.Bands30To32
import Mathlib.Tactic.Ring

/-!
# Recurrence 6 certificate: A2Square

This compatibility module combines independently checked row and band
shards for the recurrence-6 A2Square arithmetic product.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

def recurrence6A2SquareRows : Coefficient :=
  recurrence6A2SquareRow0 +
  recurrence6A2SquareRow1 +
  recurrence6A2SquareRow2 +
  recurrence6A2SquareRow3 +
  recurrence6A2SquareRow4 +
  recurrence6A2SquareRow5 +
  recurrence6A2SquareRow6 +
  recurrence6A2SquareRow7 +
  recurrence6A2SquareRow8 +
  recurrence6A2SquareRow9 +
  recurrence6A2SquareRow10 +
  recurrence6A2SquareRow11 +
  recurrence6A2SquareRow12 +
  recurrence6A2SquareRow13 +
  recurrence6A2SquareRow14 +
  recurrence6A2SquareRow15 +
  recurrence6A2SquareRow16

def recurrence6A2SquareBands : Coefficient :=
  recurrence6A2SquareBand0 +
  recurrence6A2SquareBand1 +
  recurrence6A2SquareBand2 +
  recurrence6A2SquareBand3 +
  recurrence6A2SquareBand4 +
  recurrence6A2SquareBand5 +
  recurrence6A2SquareBand6 +
  recurrence6A2SquareBand7 +
  recurrence6A2SquareBand8 +
  recurrence6A2SquareBand9 +
  recurrence6A2SquareBand10 +
  recurrence6A2SquareBand11 +
  recurrence6A2SquareBand12 +
  recurrence6A2SquareBand13 +
  recurrence6A2SquareBand14 +
  recurrence6A2SquareBand15 +
  recurrence6A2SquareBand16 +
  recurrence6A2SquareBand17 +
  recurrence6A2SquareBand18 +
  recurrence6A2SquareBand19 +
  recurrence6A2SquareBand20 +
  recurrence6A2SquareBand21 +
  recurrence6A2SquareBand22 +
  recurrence6A2SquareBand23 +
  recurrence6A2SquareBand24 +
  recurrence6A2SquareBand25 +
  recurrence6A2SquareBand26 +
  recurrence6A2SquareBand27 +
  recurrence6A2SquareBand28 +
  recurrence6A2SquareBand29 +
  recurrence6A2SquareBand30 +
  recurrence6A2SquareBand31 +
  recurrence6A2SquareBand32

theorem remainder6Coefficient2Square_eq :
    remainder6Coefficient2Normalized * remainder6Coefficient2Normalized =
      remainder6Coefficient2Square := by
  have rows :
      remainder6Coefficient2Normalized * remainder6Coefficient2Normalized =
        recurrence6A2SquareRows := by
    unfold remainder6Coefficient2Normalized recurrence6A2SquareRows
    rw [← recurrence6A2SquareRow0_eq]
    rw [← recurrence6A2SquareRow1_eq]
    rw [← recurrence6A2SquareRow2_eq]
    rw [← recurrence6A2SquareRow3_eq]
    rw [← recurrence6A2SquareRow4_eq]
    rw [← recurrence6A2SquareRow5_eq]
    rw [← recurrence6A2SquareRow6_eq]
    rw [← recurrence6A2SquareRow7_eq]
    rw [← recurrence6A2SquareRow8_eq]
    rw [← recurrence6A2SquareRow9_eq]
    rw [← recurrence6A2SquareRow10_eq]
    rw [← recurrence6A2SquareRow11_eq]
    rw [← recurrence6A2SquareRow12_eq]
    rw [← recurrence6A2SquareRow13_eq]
    rw [← recurrence6A2SquareRow14_eq]
    rw [← recurrence6A2SquareRow15_eq]
    rw [← recurrence6A2SquareRow16_eq]
    unfold remainder6Coefficient2Normalized
    ring
  rw [rows]
  have rearrange : recurrence6A2SquareRows = recurrence6A2SquareBands := by
    unfold recurrence6A2SquareRows recurrence6A2SquareBands recurrence6A2SquareRow0
    unfold recurrence6A2SquareRow1 recurrence6A2SquareRow2 recurrence6A2SquareRow3
    unfold recurrence6A2SquareRow4 recurrence6A2SquareRow5 recurrence6A2SquareRow6
    unfold recurrence6A2SquareRow7 recurrence6A2SquareRow8 recurrence6A2SquareRow9
    unfold recurrence6A2SquareRow10 recurrence6A2SquareRow11 recurrence6A2SquareRow12
    unfold recurrence6A2SquareRow13 recurrence6A2SquareRow14 recurrence6A2SquareRow15
    unfold recurrence6A2SquareRow16 recurrence6A2SquareBand0 recurrence6A2SquareBand1
    unfold recurrence6A2SquareBand2 recurrence6A2SquareBand3 recurrence6A2SquareBand4
    unfold recurrence6A2SquareBand5 recurrence6A2SquareBand6 recurrence6A2SquareBand7
    unfold recurrence6A2SquareBand8 recurrence6A2SquareBand9 recurrence6A2SquareBand10
    unfold recurrence6A2SquareBand11 recurrence6A2SquareBand12 recurrence6A2SquareBand13
    unfold recurrence6A2SquareBand14 recurrence6A2SquareBand15 recurrence6A2SquareBand16
    unfold recurrence6A2SquareBand17 recurrence6A2SquareBand18 recurrence6A2SquareBand19
    unfold recurrence6A2SquareBand20 recurrence6A2SquareBand21 recurrence6A2SquareBand22
    unfold recurrence6A2SquareBand23 recurrence6A2SquareBand24 recurrence6A2SquareBand25
    unfold recurrence6A2SquareBand26 recurrence6A2SquareBand27 recurrence6A2SquareBand28
    unfold recurrence6A2SquareBand29 recurrence6A2SquareBand30 recurrence6A2SquareBand31
    unfold recurrence6A2SquareBand32
    ring
  rw [rearrange]
  unfold recurrence6A2SquareBands remainder6Coefficient2Square
  rw [recurrence6A2SquareBand0_eq]
  rw [recurrence6A2SquareBand1_eq]
  rw [recurrence6A2SquareBand2_eq]
  rw [recurrence6A2SquareBand3_eq]
  rw [recurrence6A2SquareBand4_eq]
  rw [recurrence6A2SquareBand5_eq]
  rw [recurrence6A2SquareBand6_eq]
  rw [recurrence6A2SquareBand7_eq]
  rw [recurrence6A2SquareBand8_eq]
  rw [recurrence6A2SquareBand9_eq]
  rw [recurrence6A2SquareBand10_eq]
  rw [recurrence6A2SquareBand11_eq]
  rw [recurrence6A2SquareBand12_eq]
  rw [recurrence6A2SquareBand13_eq]
  rw [recurrence6A2SquareBand14_eq]
  rw [recurrence6A2SquareBand15_eq]
  rw [recurrence6A2SquareBand16_eq]
  rw [recurrence6A2SquareBand17_eq]
  rw [recurrence6A2SquareBand18_eq]
  rw [recurrence6A2SquareBand19_eq]
  rw [recurrence6A2SquareBand20_eq]
  rw [recurrence6A2SquareBand21_eq]
  rw [recurrence6A2SquareBand22_eq]
  rw [recurrence6A2SquareBand23_eq]
  rw [recurrence6A2SquareBand24_eq]
  rw [recurrence6A2SquareBand25_eq]
  rw [recurrence6A2SquareBand26_eq]
  rw [recurrence6A2SquareBand27_eq]
  rw [recurrence6A2SquareBand28_eq]
  rw [recurrence6A2SquareBand29_eq]
  rw [recurrence6A2SquareBand30_eq]
  rw [recurrence6A2SquareBand31_eq]
  rw [recurrence6A2SquareBand32_eq]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
