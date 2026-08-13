/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6BlockData

import Mathlib.Tactic.Ring

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B1Square.Rows0To2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B1Square.Rows3To5
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B1Square.Rows6To9

/-!
# Recurrence 6 certificate: B1Square

This file is a checked arithmetic shard for the sixth pseudo-division
recurrence in the order-seven branch-zero resultant certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

/-- Internal datum. -/ def recurrence6B1SquareBand0 : Coefficient :=
  recurrence6B1SquareRow0Band0

theorem recurrence6B1SquareBand0_eq :
    recurrence6B1SquareBand0 = remainder7Coefficient1SquareBlock0 := by
  unfold recurrence6B1SquareBand0 recurrence6B1SquareRow0Band0 remainder7Coefficient1SquareBlock0
  ring

/-- Internal datum. -/ def recurrence6B1SquareBand1 : Coefficient :=
  recurrence6B1SquareRow0Band1 +
  recurrence6B1SquareRow1Band1

theorem recurrence6B1SquareBand1_eq :
    recurrence6B1SquareBand1 = remainder7Coefficient1SquareBlock1 := by
  unfold recurrence6B1SquareBand1 recurrence6B1SquareRow0Band1 recurrence6B1SquareRow1Band1
  unfold remainder7Coefficient1SquareBlock1
  ring

/-- Internal datum. -/ def recurrence6B1SquareBand2 : Coefficient :=
  recurrence6B1SquareRow0Band2 +
  recurrence6B1SquareRow1Band2 +
  recurrence6B1SquareRow2Band2

theorem recurrence6B1SquareBand2_eq :
    recurrence6B1SquareBand2 = remainder7Coefficient1SquareBlock2 := by
  unfold recurrence6B1SquareBand2 recurrence6B1SquareRow0Band2 recurrence6B1SquareRow1Band2
  unfold recurrence6B1SquareRow2Band2 remainder7Coefficient1SquareBlock2
  ring

/-- Internal datum. -/ def recurrence6B1SquareBand3 : Coefficient :=
  recurrence6B1SquareRow0Band3 +
  recurrence6B1SquareRow1Band3 +
  recurrence6B1SquareRow2Band3 +
  recurrence6B1SquareRow3Band3

theorem recurrence6B1SquareBand3_eq :
    recurrence6B1SquareBand3 = remainder7Coefficient1SquareBlock3 := by
  unfold recurrence6B1SquareBand3 recurrence6B1SquareRow0Band3 recurrence6B1SquareRow1Band3
  unfold recurrence6B1SquareRow2Band3 recurrence6B1SquareRow3Band3
  unfold remainder7Coefficient1SquareBlock3
  ring

/-- Internal datum. -/ def recurrence6B1SquareBand4 : Coefficient :=
  recurrence6B1SquareRow0Band4 +
  recurrence6B1SquareRow1Band4 +
  recurrence6B1SquareRow2Band4 +
  recurrence6B1SquareRow3Band4 +
  recurrence6B1SquareRow4Band4

theorem recurrence6B1SquareBand4_eq :
    recurrence6B1SquareBand4 = remainder7Coefficient1SquareBlock4 := by
  unfold recurrence6B1SquareBand4 recurrence6B1SquareRow0Band4 recurrence6B1SquareRow1Band4
  unfold recurrence6B1SquareRow2Band4 recurrence6B1SquareRow3Band4 recurrence6B1SquareRow4Band4
  unfold remainder7Coefficient1SquareBlock4
  ring

/-- Internal datum. -/ def recurrence6B1SquareBand5 : Coefficient :=
  recurrence6B1SquareRow0Band5 +
  recurrence6B1SquareRow1Band5 +
  recurrence6B1SquareRow2Band5 +
  recurrence6B1SquareRow3Band5 +
  recurrence6B1SquareRow4Band5 +
  recurrence6B1SquareRow5Band5

theorem recurrence6B1SquareBand5_eq :
    recurrence6B1SquareBand5 = remainder7Coefficient1SquareBlock5 := by
  unfold recurrence6B1SquareBand5 recurrence6B1SquareRow0Band5 recurrence6B1SquareRow1Band5
  unfold recurrence6B1SquareRow2Band5 recurrence6B1SquareRow3Band5 recurrence6B1SquareRow4Band5
  unfold recurrence6B1SquareRow5Band5 remainder7Coefficient1SquareBlock5
  ring

/-- Internal datum. -/ def recurrence6B1SquareBand6 : Coefficient :=
  recurrence6B1SquareRow0Band6 +
  recurrence6B1SquareRow1Band6 +
  recurrence6B1SquareRow2Band6 +
  recurrence6B1SquareRow3Band6 +
  recurrence6B1SquareRow4Band6 +
  recurrence6B1SquareRow5Band6 +
  recurrence6B1SquareRow6Band6

theorem recurrence6B1SquareBand6_eq :
    recurrence6B1SquareBand6 = remainder7Coefficient1SquareBlock6 := by
  unfold recurrence6B1SquareBand6 recurrence6B1SquareRow0Band6 recurrence6B1SquareRow1Band6
  unfold recurrence6B1SquareRow2Band6 recurrence6B1SquareRow3Band6 recurrence6B1SquareRow4Band6
  unfold recurrence6B1SquareRow5Band6 recurrence6B1SquareRow6Band6
  unfold remainder7Coefficient1SquareBlock6
  ring

/-- Internal datum. -/ def recurrence6B1SquareBand7 : Coefficient :=
  recurrence6B1SquareRow0Band7 +
  recurrence6B1SquareRow1Band7 +
  recurrence6B1SquareRow2Band7 +
  recurrence6B1SquareRow3Band7 +
  recurrence6B1SquareRow4Band7 +
  recurrence6B1SquareRow5Band7 +
  recurrence6B1SquareRow6Band7 +
  recurrence6B1SquareRow7Band7

theorem recurrence6B1SquareBand7_eq :
    recurrence6B1SquareBand7 = remainder7Coefficient1SquareBlock7 := by
  unfold recurrence6B1SquareBand7 recurrence6B1SquareRow0Band7 recurrence6B1SquareRow1Band7
  unfold recurrence6B1SquareRow2Band7 recurrence6B1SquareRow3Band7 recurrence6B1SquareRow4Band7
  unfold recurrence6B1SquareRow5Band7 recurrence6B1SquareRow6Band7 recurrence6B1SquareRow7Band7
  unfold remainder7Coefficient1SquareBlock7
  ring

/-- Internal datum. -/ def recurrence6B1SquareBand8 : Coefficient :=
  recurrence6B1SquareRow0Band8 +
  recurrence6B1SquareRow1Band8 +
  recurrence6B1SquareRow2Band8 +
  recurrence6B1SquareRow3Band8 +
  recurrence6B1SquareRow4Band8 +
  recurrence6B1SquareRow5Band8 +
  recurrence6B1SquareRow6Band8 +
  recurrence6B1SquareRow7Band8 +
  recurrence6B1SquareRow8Band8

theorem recurrence6B1SquareBand8_eq :
    recurrence6B1SquareBand8 = remainder7Coefficient1SquareBlock8 := by
  unfold recurrence6B1SquareBand8 recurrence6B1SquareRow0Band8 recurrence6B1SquareRow1Band8
  unfold recurrence6B1SquareRow2Band8 recurrence6B1SquareRow3Band8 recurrence6B1SquareRow4Band8
  unfold recurrence6B1SquareRow5Band8 recurrence6B1SquareRow6Band8 recurrence6B1SquareRow7Band8
  unfold recurrence6B1SquareRow8Band8 remainder7Coefficient1SquareBlock8
  ring

/-- Internal datum. -/ def recurrence6B1SquareBand9 : Coefficient :=
  recurrence6B1SquareRow0Band9 +
  recurrence6B1SquareRow1Band9 +
  recurrence6B1SquareRow2Band9 +
  recurrence6B1SquareRow3Band9 +
  recurrence6B1SquareRow4Band9 +
  recurrence6B1SquareRow5Band9 +
  recurrence6B1SquareRow6Band9 +
  recurrence6B1SquareRow7Band9 +
  recurrence6B1SquareRow8Band9 +
  recurrence6B1SquareRow9Band9

theorem recurrence6B1SquareBand9_eq :
    recurrence6B1SquareBand9 = remainder7Coefficient1SquareBlock9 := by
  unfold recurrence6B1SquareBand9 recurrence6B1SquareRow0Band9 recurrence6B1SquareRow1Band9
  unfold recurrence6B1SquareRow2Band9 recurrence6B1SquareRow3Band9 recurrence6B1SquareRow4Band9
  unfold recurrence6B1SquareRow5Band9 recurrence6B1SquareRow6Band9 recurrence6B1SquareRow7Band9
  unfold recurrence6B1SquareRow8Band9 recurrence6B1SquareRow9Band9
  unfold remainder7Coefficient1SquareBlock9
  ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
