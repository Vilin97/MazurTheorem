/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6A2Square.Rows0To2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6A2Square.Rows3To5
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6A2Square.Rows6To8
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6A2Square.Rows9To11
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6BlockData.Coefficient2Square
import Mathlib.Tactic.Ring

/-!
# Recurrence 6 A2Square bands 6–11

This file checks bands 6 through 11 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

def recurrence6A2SquareBand6 : Coefficient :=
  recurrence6A2SquareRow0Band6 +
  recurrence6A2SquareRow1Band6 +
  recurrence6A2SquareRow2Band6 +
  recurrence6A2SquareRow3Band6 +
  recurrence6A2SquareRow4Band6 +
  recurrence6A2SquareRow5Band6 +
  recurrence6A2SquareRow6Band6

theorem recurrence6A2SquareBand6_eq :
    recurrence6A2SquareBand6 = remainder6Coefficient2SquareBlock6 := by
  unfold recurrence6A2SquareBand6 recurrence6A2SquareRow0Band6 recurrence6A2SquareRow1Band6
  unfold recurrence6A2SquareRow2Band6 recurrence6A2SquareRow3Band6 recurrence6A2SquareRow4Band6
  unfold recurrence6A2SquareRow5Band6 recurrence6A2SquareRow6Band6
  unfold remainder6Coefficient2SquareBlock6
  ring

def recurrence6A2SquareBand7 : Coefficient :=
  recurrence6A2SquareRow0Band7 +
  recurrence6A2SquareRow1Band7 +
  recurrence6A2SquareRow2Band7 +
  recurrence6A2SquareRow3Band7 +
  recurrence6A2SquareRow4Band7 +
  recurrence6A2SquareRow5Band7 +
  recurrence6A2SquareRow6Band7 +
  recurrence6A2SquareRow7Band7

theorem recurrence6A2SquareBand7_eq :
    recurrence6A2SquareBand7 = remainder6Coefficient2SquareBlock7 := by
  unfold recurrence6A2SquareBand7 recurrence6A2SquareRow0Band7 recurrence6A2SquareRow1Band7
  unfold recurrence6A2SquareRow2Band7 recurrence6A2SquareRow3Band7 recurrence6A2SquareRow4Band7
  unfold recurrence6A2SquareRow5Band7 recurrence6A2SquareRow6Band7 recurrence6A2SquareRow7Band7
  unfold remainder6Coefficient2SquareBlock7
  ring

def recurrence6A2SquareBand8 : Coefficient :=
  recurrence6A2SquareRow0Band8 +
  recurrence6A2SquareRow1Band8 +
  recurrence6A2SquareRow2Band8 +
  recurrence6A2SquareRow3Band8 +
  recurrence6A2SquareRow4Band8 +
  recurrence6A2SquareRow5Band8 +
  recurrence6A2SquareRow6Band8 +
  recurrence6A2SquareRow7Band8 +
  recurrence6A2SquareRow8Band8

theorem recurrence6A2SquareBand8_eq :
    recurrence6A2SquareBand8 = remainder6Coefficient2SquareBlock8 := by
  unfold recurrence6A2SquareBand8 recurrence6A2SquareRow0Band8 recurrence6A2SquareRow1Band8
  unfold recurrence6A2SquareRow2Band8 recurrence6A2SquareRow3Band8 recurrence6A2SquareRow4Band8
  unfold recurrence6A2SquareRow5Band8 recurrence6A2SquareRow6Band8 recurrence6A2SquareRow7Band8
  unfold recurrence6A2SquareRow8Band8 remainder6Coefficient2SquareBlock8
  ring

def recurrence6A2SquareBand9 : Coefficient :=
  recurrence6A2SquareRow0Band9 +
  recurrence6A2SquareRow1Band9 +
  recurrence6A2SquareRow2Band9 +
  recurrence6A2SquareRow3Band9 +
  recurrence6A2SquareRow4Band9 +
  recurrence6A2SquareRow5Band9 +
  recurrence6A2SquareRow6Band9 +
  recurrence6A2SquareRow7Band9 +
  recurrence6A2SquareRow8Band9 +
  recurrence6A2SquareRow9Band9

theorem recurrence6A2SquareBand9_eq :
    recurrence6A2SquareBand9 = remainder6Coefficient2SquareBlock9 := by
  unfold recurrence6A2SquareBand9 recurrence6A2SquareRow0Band9 recurrence6A2SquareRow1Band9
  unfold recurrence6A2SquareRow2Band9 recurrence6A2SquareRow3Band9 recurrence6A2SquareRow4Band9
  unfold recurrence6A2SquareRow5Band9 recurrence6A2SquareRow6Band9 recurrence6A2SquareRow7Band9
  unfold recurrence6A2SquareRow8Band9 recurrence6A2SquareRow9Band9
  unfold remainder6Coefficient2SquareBlock9
  ring

def recurrence6A2SquareBand10 : Coefficient :=
  recurrence6A2SquareRow0Band10 +
  recurrence6A2SquareRow1Band10 +
  recurrence6A2SquareRow2Band10 +
  recurrence6A2SquareRow3Band10 +
  recurrence6A2SquareRow4Band10 +
  recurrence6A2SquareRow5Band10 +
  recurrence6A2SquareRow6Band10 +
  recurrence6A2SquareRow7Band10 +
  recurrence6A2SquareRow8Band10 +
  recurrence6A2SquareRow9Band10 +
  recurrence6A2SquareRow10Band10

theorem recurrence6A2SquareBand10_eq :
    recurrence6A2SquareBand10 = remainder6Coefficient2SquareBlock10 := by
  unfold recurrence6A2SquareBand10 recurrence6A2SquareRow0Band10 recurrence6A2SquareRow1Band10
  unfold recurrence6A2SquareRow2Band10 recurrence6A2SquareRow3Band10 recurrence6A2SquareRow4Band10
  unfold recurrence6A2SquareRow5Band10 recurrence6A2SquareRow6Band10 recurrence6A2SquareRow7Band10
  unfold recurrence6A2SquareRow8Band10 recurrence6A2SquareRow9Band10 recurrence6A2SquareRow10Band10
  unfold remainder6Coefficient2SquareBlock10
  ring

def recurrence6A2SquareBand11 : Coefficient :=
  recurrence6A2SquareRow0Band11 +
  recurrence6A2SquareRow1Band11 +
  recurrence6A2SquareRow2Band11 +
  recurrence6A2SquareRow3Band11 +
  recurrence6A2SquareRow4Band11 +
  recurrence6A2SquareRow5Band11 +
  recurrence6A2SquareRow6Band11 +
  recurrence6A2SquareRow7Band11 +
  recurrence6A2SquareRow8Band11 +
  recurrence6A2SquareRow9Band11 +
  recurrence6A2SquareRow10Band11 +
  recurrence6A2SquareRow11Band11

theorem recurrence6A2SquareBand11_eq :
    recurrence6A2SquareBand11 = remainder6Coefficient2SquareBlock11 := by
  unfold recurrence6A2SquareBand11 recurrence6A2SquareRow0Band11 recurrence6A2SquareRow1Band11
  unfold recurrence6A2SquareRow2Band11 recurrence6A2SquareRow3Band11 recurrence6A2SquareRow4Band11
  unfold recurrence6A2SquareRow5Band11 recurrence6A2SquareRow6Band11 recurrence6A2SquareRow7Band11
  unfold recurrence6A2SquareRow8Band11 recurrence6A2SquareRow9Band11 recurrence6A2SquareRow10Band11
  unfold recurrence6A2SquareRow11Band11 remainder6Coefficient2SquareBlock11
  ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
