/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6A2Square.Rows0To2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6A2Square.Rows3To5
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6BlockData.Coefficient2Square
import Mathlib.Tactic.Ring

/-!
# Recurrence 6 A2Square bands 0–5

This file checks bands 0 through 5 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

def recurrence6A2SquareBand0 : Coefficient :=
  recurrence6A2SquareRow0Band0

theorem recurrence6A2SquareBand0_eq :
    recurrence6A2SquareBand0 = remainder6Coefficient2SquareBlock0 := by
  unfold recurrence6A2SquareBand0 recurrence6A2SquareRow0Band0 remainder6Coefficient2SquareBlock0
  ring

def recurrence6A2SquareBand1 : Coefficient :=
  recurrence6A2SquareRow0Band1 +
  recurrence6A2SquareRow1Band1

theorem recurrence6A2SquareBand1_eq :
    recurrence6A2SquareBand1 = remainder6Coefficient2SquareBlock1 := by
  unfold recurrence6A2SquareBand1 recurrence6A2SquareRow0Band1 recurrence6A2SquareRow1Band1
  unfold remainder6Coefficient2SquareBlock1
  ring

def recurrence6A2SquareBand2 : Coefficient :=
  recurrence6A2SquareRow0Band2 +
  recurrence6A2SquareRow1Band2 +
  recurrence6A2SquareRow2Band2

theorem recurrence6A2SquareBand2_eq :
    recurrence6A2SquareBand2 = remainder6Coefficient2SquareBlock2 := by
  unfold recurrence6A2SquareBand2 recurrence6A2SquareRow0Band2 recurrence6A2SquareRow1Band2
  unfold recurrence6A2SquareRow2Band2 remainder6Coefficient2SquareBlock2
  ring

def recurrence6A2SquareBand3 : Coefficient :=
  recurrence6A2SquareRow0Band3 +
  recurrence6A2SquareRow1Band3 +
  recurrence6A2SquareRow2Band3 +
  recurrence6A2SquareRow3Band3

theorem recurrence6A2SquareBand3_eq :
    recurrence6A2SquareBand3 = remainder6Coefficient2SquareBlock3 := by
  unfold recurrence6A2SquareBand3 recurrence6A2SquareRow0Band3 recurrence6A2SquareRow1Band3
  unfold recurrence6A2SquareRow2Band3 recurrence6A2SquareRow3Band3
  unfold remainder6Coefficient2SquareBlock3
  ring

def recurrence6A2SquareBand4 : Coefficient :=
  recurrence6A2SquareRow0Band4 +
  recurrence6A2SquareRow1Band4 +
  recurrence6A2SquareRow2Band4 +
  recurrence6A2SquareRow3Band4 +
  recurrence6A2SquareRow4Band4

theorem recurrence6A2SquareBand4_eq :
    recurrence6A2SquareBand4 = remainder6Coefficient2SquareBlock4 := by
  unfold recurrence6A2SquareBand4 recurrence6A2SquareRow0Band4 recurrence6A2SquareRow1Band4
  unfold recurrence6A2SquareRow2Band4 recurrence6A2SquareRow3Band4 recurrence6A2SquareRow4Band4
  unfold remainder6Coefficient2SquareBlock4
  ring

def recurrence6A2SquareBand5 : Coefficient :=
  recurrence6A2SquareRow0Band5 +
  recurrence6A2SquareRow1Band5 +
  recurrence6A2SquareRow2Band5 +
  recurrence6A2SquareRow3Band5 +
  recurrence6A2SquareRow4Band5 +
  recurrence6A2SquareRow5Band5

theorem recurrence6A2SquareBand5_eq :
    recurrence6A2SquareBand5 = remainder6Coefficient2SquareBlock5 := by
  unfold recurrence6A2SquareBand5 recurrence6A2SquareRow0Band5 recurrence6A2SquareRow1Band5
  unfold recurrence6A2SquareRow2Band5 recurrence6A2SquareRow3Band5 recurrence6A2SquareRow4Band5
  unfold recurrence6A2SquareRow5Band5 remainder6Coefficient2SquareBlock5
  ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
