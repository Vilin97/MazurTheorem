/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6A2Square.Rows12To14
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6A2Square.Rows15To16
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6BlockData.Coefficient2Square
import Mathlib.Tactic.Ring

/-!
# Recurrence 6 A2Square bands 30–32

This file checks bands 30 through 32 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

def recurrence6A2SquareBand30 : Coefficient :=
  recurrence6A2SquareRow13Band30 +
  recurrence6A2SquareRow14Band30 +
  recurrence6A2SquareRow15Band30 +
  recurrence6A2SquareRow16Band30

theorem recurrence6A2SquareBand30_eq :
    recurrence6A2SquareBand30 = remainder6Coefficient2SquareBlock30 := by
  unfold recurrence6A2SquareBand30 recurrence6A2SquareRow13Band30 recurrence6A2SquareRow14Band30
  unfold recurrence6A2SquareRow15Band30 recurrence6A2SquareRow16Band30
  unfold remainder6Coefficient2SquareBlock30
  ring

def recurrence6A2SquareBand31 : Coefficient :=
  recurrence6A2SquareRow14Band31 +
  recurrence6A2SquareRow15Band31 +
  recurrence6A2SquareRow16Band31

theorem recurrence6A2SquareBand31_eq :
    recurrence6A2SquareBand31 = remainder6Coefficient2SquareBlock31 := by
  unfold recurrence6A2SquareBand31 recurrence6A2SquareRow14Band31 recurrence6A2SquareRow15Band31
  unfold recurrence6A2SquareRow16Band31 remainder6Coefficient2SquareBlock31
  ring

def recurrence6A2SquareBand32 : Coefficient :=
  recurrence6A2SquareRow15Band32 +
  recurrence6A2SquareRow16Band32

theorem recurrence6A2SquareBand32_eq :
    recurrence6A2SquareBand32 = remainder6Coefficient2SquareBlock32 := by
  unfold recurrence6A2SquareBand32 recurrence6A2SquareRow15Band32 recurrence6A2SquareRow16Band32
  unfold remainder6Coefficient2SquareBlock32
  ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
