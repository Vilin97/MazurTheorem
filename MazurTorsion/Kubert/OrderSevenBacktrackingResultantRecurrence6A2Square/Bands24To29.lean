/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6A2Square.Rows6To8
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6A2Square.Rows9To11
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6A2Square.Rows12To14
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6A2Square.Rows15To16
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6BlockData.Coefficient2Square
import Mathlib.Tactic.Ring

/-!
# Recurrence 6 A2Square bands 24–29

This file checks bands 24 through 29 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

/-- Internal datum. -/ def recurrence6A2SquareBand24 : Coefficient :=
  recurrence6A2SquareRow7Band24 +
  recurrence6A2SquareRow8Band24 +
  recurrence6A2SquareRow9Band24 +
  recurrence6A2SquareRow10Band24 +
  recurrence6A2SquareRow11Band24 +
  recurrence6A2SquareRow12Band24 +
  recurrence6A2SquareRow13Band24 +
  recurrence6A2SquareRow14Band24 +
  recurrence6A2SquareRow15Band24 +
  recurrence6A2SquareRow16Band24

theorem recurrence6A2SquareBand24_eq :
    recurrence6A2SquareBand24 = remainder6Coefficient2SquareBlock24 := by
  unfold recurrence6A2SquareBand24 recurrence6A2SquareRow7Band24 recurrence6A2SquareRow8Band24
  unfold recurrence6A2SquareRow9Band24 recurrence6A2SquareRow10Band24 recurrence6A2SquareRow11Band24
  unfold recurrence6A2SquareRow12Band24 recurrence6A2SquareRow13Band24
  unfold recurrence6A2SquareRow14Band24 recurrence6A2SquareRow15Band24
  unfold recurrence6A2SquareRow16Band24 remainder6Coefficient2SquareBlock24
  ring

/-- Internal datum. -/ def recurrence6A2SquareBand25 : Coefficient :=
  recurrence6A2SquareRow8Band25 +
  recurrence6A2SquareRow9Band25 +
  recurrence6A2SquareRow10Band25 +
  recurrence6A2SquareRow11Band25 +
  recurrence6A2SquareRow12Band25 +
  recurrence6A2SquareRow13Band25 +
  recurrence6A2SquareRow14Band25 +
  recurrence6A2SquareRow15Band25 +
  recurrence6A2SquareRow16Band25

theorem recurrence6A2SquareBand25_eq :
    recurrence6A2SquareBand25 = remainder6Coefficient2SquareBlock25 := by
  unfold recurrence6A2SquareBand25 recurrence6A2SquareRow8Band25 recurrence6A2SquareRow9Band25
  unfold recurrence6A2SquareRow10Band25 recurrence6A2SquareRow11Band25
  unfold recurrence6A2SquareRow12Band25 recurrence6A2SquareRow13Band25
  unfold recurrence6A2SquareRow14Band25 recurrence6A2SquareRow15Band25
  unfold recurrence6A2SquareRow16Band25 remainder6Coefficient2SquareBlock25
  ring

/-- Internal datum. -/ def recurrence6A2SquareBand26 : Coefficient :=
  recurrence6A2SquareRow9Band26 +
  recurrence6A2SquareRow10Band26 +
  recurrence6A2SquareRow11Band26 +
  recurrence6A2SquareRow12Band26 +
  recurrence6A2SquareRow13Band26 +
  recurrence6A2SquareRow14Band26 +
  recurrence6A2SquareRow15Band26 +
  recurrence6A2SquareRow16Band26

theorem recurrence6A2SquareBand26_eq :
    recurrence6A2SquareBand26 = remainder6Coefficient2SquareBlock26 := by
  unfold recurrence6A2SquareBand26 recurrence6A2SquareRow9Band26 recurrence6A2SquareRow10Band26
  unfold recurrence6A2SquareRow11Band26 recurrence6A2SquareRow12Band26
  unfold recurrence6A2SquareRow13Band26 recurrence6A2SquareRow14Band26
  unfold recurrence6A2SquareRow15Band26 recurrence6A2SquareRow16Band26
  unfold remainder6Coefficient2SquareBlock26
  ring

/-- Internal datum. -/ def recurrence6A2SquareBand27 : Coefficient :=
  recurrence6A2SquareRow10Band27 +
  recurrence6A2SquareRow11Band27 +
  recurrence6A2SquareRow12Band27 +
  recurrence6A2SquareRow13Band27 +
  recurrence6A2SquareRow14Band27 +
  recurrence6A2SquareRow15Band27 +
  recurrence6A2SquareRow16Band27

theorem recurrence6A2SquareBand27_eq :
    recurrence6A2SquareBand27 = remainder6Coefficient2SquareBlock27 := by
  unfold recurrence6A2SquareBand27 recurrence6A2SquareRow10Band27 recurrence6A2SquareRow11Band27
  unfold recurrence6A2SquareRow12Band27 recurrence6A2SquareRow13Band27
  unfold recurrence6A2SquareRow14Band27 recurrence6A2SquareRow15Band27
  unfold recurrence6A2SquareRow16Band27 remainder6Coefficient2SquareBlock27
  ring

/-- Internal datum. -/ def recurrence6A2SquareBand28 : Coefficient :=
  recurrence6A2SquareRow11Band28 +
  recurrence6A2SquareRow12Band28 +
  recurrence6A2SquareRow13Band28 +
  recurrence6A2SquareRow14Band28 +
  recurrence6A2SquareRow15Band28 +
  recurrence6A2SquareRow16Band28

theorem recurrence6A2SquareBand28_eq :
    recurrence6A2SquareBand28 = remainder6Coefficient2SquareBlock28 := by
  unfold recurrence6A2SquareBand28 recurrence6A2SquareRow11Band28 recurrence6A2SquareRow12Band28
  unfold recurrence6A2SquareRow13Band28 recurrence6A2SquareRow14Band28
  unfold recurrence6A2SquareRow15Band28 recurrence6A2SquareRow16Band28
  unfold remainder6Coefficient2SquareBlock28
  ring

/-- Internal datum. -/ def recurrence6A2SquareBand29 : Coefficient :=
  recurrence6A2SquareRow12Band29 +
  recurrence6A2SquareRow13Band29 +
  recurrence6A2SquareRow14Band29 +
  recurrence6A2SquareRow15Band29 +
  recurrence6A2SquareRow16Band29

theorem recurrence6A2SquareBand29_eq :
    recurrence6A2SquareBand29 = remainder6Coefficient2SquareBlock29 := by
  unfold recurrence6A2SquareBand29 recurrence6A2SquareRow12Band29 recurrence6A2SquareRow13Band29
  unfold recurrence6A2SquareRow14Band29 recurrence6A2SquareRow15Band29
  unfold recurrence6A2SquareRow16Band29 remainder6Coefficient2SquareBlock29
  ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
