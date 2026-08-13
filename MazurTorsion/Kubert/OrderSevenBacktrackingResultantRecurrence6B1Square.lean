/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6BlockData

import Mathlib.Tactic.Ring

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B1Square.Bands0To9
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B1Square.Bands10To18

/-!
# Recurrence 6 certificate: B1Square

This file is a checked arithmetic shard for the sixth pseudo-division
recurrence in the order-seven branch-zero resultant certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

/-- Internal datum. -/ def recurrence6B1SquareRows : Coefficient :=
  recurrence6B1SquareRow0 +
  recurrence6B1SquareRow1 +
  recurrence6B1SquareRow2 +
  recurrence6B1SquareRow3 +
  recurrence6B1SquareRow4 +
  recurrence6B1SquareRow5 +
  recurrence6B1SquareRow6 +
  recurrence6B1SquareRow7 +
  recurrence6B1SquareRow8 +
  recurrence6B1SquareRow9

/-- Internal datum. -/ def recurrence6B1SquareBands : Coefficient :=
  recurrence6B1SquareBand0 +
  recurrence6B1SquareBand1 +
  recurrence6B1SquareBand2 +
  recurrence6B1SquareBand3 +
  recurrence6B1SquareBand4 +
  recurrence6B1SquareBand5 +
  recurrence6B1SquareBand6 +
  recurrence6B1SquareBand7 +
  recurrence6B1SquareBand8 +
  recurrence6B1SquareBand9 +
  recurrence6B1SquareBand10 +
  recurrence6B1SquareBand11 +
  recurrence6B1SquareBand12 +
  recurrence6B1SquareBand13 +
  recurrence6B1SquareBand14 +
  recurrence6B1SquareBand15 +
  recurrence6B1SquareBand16 +
  recurrence6B1SquareBand17 +
  recurrence6B1SquareBand18

theorem remainder7Coefficient1Square_eq :
    remainder7Coefficient1Normalized * remainder7Coefficient1Normalized =
      remainder7Coefficient1Square := by
  have rows :
      remainder7Coefficient1Normalized * remainder7Coefficient1Normalized =
        recurrence6B1SquareRows := by
    unfold remainder7Coefficient1Normalized recurrence6B1SquareRows
    rw [← recurrence6B1SquareRow0_eq]
    rw [← recurrence6B1SquareRow1_eq]
    rw [← recurrence6B1SquareRow2_eq]
    rw [← recurrence6B1SquareRow3_eq]
    rw [← recurrence6B1SquareRow4_eq]
    rw [← recurrence6B1SquareRow5_eq]
    rw [← recurrence6B1SquareRow6_eq]
    rw [← recurrence6B1SquareRow7_eq]
    rw [← recurrence6B1SquareRow8_eq]
    rw [← recurrence6B1SquareRow9_eq]
    unfold remainder7Coefficient1Normalized
    ring
  rw [rows]
  have rearrange : recurrence6B1SquareRows = recurrence6B1SquareBands := by
    unfold recurrence6B1SquareRows recurrence6B1SquareBands recurrence6B1SquareRow0
    unfold recurrence6B1SquareRow1 recurrence6B1SquareRow2 recurrence6B1SquareRow3
    unfold recurrence6B1SquareRow4 recurrence6B1SquareRow5 recurrence6B1SquareRow6
    unfold recurrence6B1SquareRow7 recurrence6B1SquareRow8 recurrence6B1SquareRow9
    unfold recurrence6B1SquareBand0 recurrence6B1SquareBand1 recurrence6B1SquareBand2
    unfold recurrence6B1SquareBand3 recurrence6B1SquareBand4 recurrence6B1SquareBand5
    unfold recurrence6B1SquareBand6 recurrence6B1SquareBand7 recurrence6B1SquareBand8
    unfold recurrence6B1SquareBand9 recurrence6B1SquareBand10 recurrence6B1SquareBand11
    unfold recurrence6B1SquareBand12 recurrence6B1SquareBand13 recurrence6B1SquareBand14
    unfold recurrence6B1SquareBand15 recurrence6B1SquareBand16 recurrence6B1SquareBand17
    unfold recurrence6B1SquareBand18
    ring
  rw [rearrange]
  unfold recurrence6B1SquareBands remainder7Coefficient1Square
  rw [recurrence6B1SquareBand0_eq]
  rw [recurrence6B1SquareBand1_eq]
  rw [recurrence6B1SquareBand2_eq]
  rw [recurrence6B1SquareBand3_eq]
  rw [recurrence6B1SquareBand4_eq]
  rw [recurrence6B1SquareBand5_eq]
  rw [recurrence6B1SquareBand6_eq]
  rw [recurrence6B1SquareBand7_eq]
  rw [recurrence6B1SquareBand8_eq]
  rw [recurrence6B1SquareBand9_eq]
  rw [recurrence6B1SquareBand10_eq]
  rw [recurrence6B1SquareBand11_eq]
  rw [recurrence6B1SquareBand12_eq]
  rw [recurrence6B1SquareBand13_eq]
  rw [recurrence6B1SquareBand14_eq]
  rw [recurrence6B1SquareBand15_eq]
  rw [recurrence6B1SquareBand16_eq]
  rw [recurrence6B1SquareBand17_eq]
  rw [recurrence6B1SquareBand18_eq]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
