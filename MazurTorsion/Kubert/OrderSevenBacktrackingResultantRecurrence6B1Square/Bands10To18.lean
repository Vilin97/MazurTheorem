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

/-- Internal datum. -/ def recurrence6B1SquareBand10 : Coefficient :=
  recurrence6B1SquareRow0Band10 +
  recurrence6B1SquareRow1Band10 +
  recurrence6B1SquareRow2Band10 +
  recurrence6B1SquareRow3Band10 +
  recurrence6B1SquareRow4Band10 +
  recurrence6B1SquareRow5Band10 +
  recurrence6B1SquareRow6Band10 +
  recurrence6B1SquareRow7Band10 +
  recurrence6B1SquareRow8Band10 +
  recurrence6B1SquareRow9Band10

theorem recurrence6B1SquareBand10_eq :
    recurrence6B1SquareBand10 = remainder7Coefficient1SquareBlock10 := by
  unfold recurrence6B1SquareBand10 recurrence6B1SquareRow0Band10 recurrence6B1SquareRow1Band10
  unfold recurrence6B1SquareRow2Band10 recurrence6B1SquareRow3Band10 recurrence6B1SquareRow4Band10
  unfold recurrence6B1SquareRow5Band10 recurrence6B1SquareRow6Band10 recurrence6B1SquareRow7Band10
  unfold recurrence6B1SquareRow8Band10 recurrence6B1SquareRow9Band10
  unfold remainder7Coefficient1SquareBlock10
  ring

/-- Internal datum. -/ def recurrence6B1SquareBand11 : Coefficient :=
  recurrence6B1SquareRow1Band11 +
  recurrence6B1SquareRow2Band11 +
  recurrence6B1SquareRow3Band11 +
  recurrence6B1SquareRow4Band11 +
  recurrence6B1SquareRow5Band11 +
  recurrence6B1SquareRow6Band11 +
  recurrence6B1SquareRow7Band11 +
  recurrence6B1SquareRow8Band11 +
  recurrence6B1SquareRow9Band11

theorem recurrence6B1SquareBand11_eq :
    recurrence6B1SquareBand11 = remainder7Coefficient1SquareBlock11 := by
  unfold recurrence6B1SquareBand11 recurrence6B1SquareRow1Band11 recurrence6B1SquareRow2Band11
  unfold recurrence6B1SquareRow3Band11 recurrence6B1SquareRow4Band11 recurrence6B1SquareRow5Band11
  unfold recurrence6B1SquareRow6Band11 recurrence6B1SquareRow7Band11 recurrence6B1SquareRow8Band11
  unfold recurrence6B1SquareRow9Band11 remainder7Coefficient1SquareBlock11
  ring

/-- Internal datum. -/ def recurrence6B1SquareBand12 : Coefficient :=
  recurrence6B1SquareRow2Band12 +
  recurrence6B1SquareRow3Band12 +
  recurrence6B1SquareRow4Band12 +
  recurrence6B1SquareRow5Band12 +
  recurrence6B1SquareRow6Band12 +
  recurrence6B1SquareRow7Band12 +
  recurrence6B1SquareRow8Band12 +
  recurrence6B1SquareRow9Band12

theorem recurrence6B1SquareBand12_eq :
    recurrence6B1SquareBand12 = remainder7Coefficient1SquareBlock12 := by
  unfold recurrence6B1SquareBand12 recurrence6B1SquareRow2Band12 recurrence6B1SquareRow3Band12
  unfold recurrence6B1SquareRow4Band12 recurrence6B1SquareRow5Band12 recurrence6B1SquareRow6Band12
  unfold recurrence6B1SquareRow7Band12 recurrence6B1SquareRow8Band12 recurrence6B1SquareRow9Band12
  unfold remainder7Coefficient1SquareBlock12
  ring

/-- Internal datum. -/ def recurrence6B1SquareBand13 : Coefficient :=
  recurrence6B1SquareRow3Band13 +
  recurrence6B1SquareRow4Band13 +
  recurrence6B1SquareRow5Band13 +
  recurrence6B1SquareRow6Band13 +
  recurrence6B1SquareRow7Band13 +
  recurrence6B1SquareRow8Band13 +
  recurrence6B1SquareRow9Band13

theorem recurrence6B1SquareBand13_eq :
    recurrence6B1SquareBand13 = remainder7Coefficient1SquareBlock13 := by
  unfold recurrence6B1SquareBand13 recurrence6B1SquareRow3Band13 recurrence6B1SquareRow4Band13
  unfold recurrence6B1SquareRow5Band13 recurrence6B1SquareRow6Band13 recurrence6B1SquareRow7Band13
  unfold recurrence6B1SquareRow8Band13 recurrence6B1SquareRow9Band13
  unfold remainder7Coefficient1SquareBlock13
  ring

/-- Internal datum. -/ def recurrence6B1SquareBand14 : Coefficient :=
  recurrence6B1SquareRow4Band14 +
  recurrence6B1SquareRow5Band14 +
  recurrence6B1SquareRow6Band14 +
  recurrence6B1SquareRow7Band14 +
  recurrence6B1SquareRow8Band14 +
  recurrence6B1SquareRow9Band14

theorem recurrence6B1SquareBand14_eq :
    recurrence6B1SquareBand14 = remainder7Coefficient1SquareBlock14 := by
  unfold recurrence6B1SquareBand14 recurrence6B1SquareRow4Band14 recurrence6B1SquareRow5Band14
  unfold recurrence6B1SquareRow6Band14 recurrence6B1SquareRow7Band14 recurrence6B1SquareRow8Band14
  unfold recurrence6B1SquareRow9Band14 remainder7Coefficient1SquareBlock14
  ring

/-- Internal datum. -/ def recurrence6B1SquareBand15 : Coefficient :=
  recurrence6B1SquareRow5Band15 +
  recurrence6B1SquareRow6Band15 +
  recurrence6B1SquareRow7Band15 +
  recurrence6B1SquareRow8Band15 +
  recurrence6B1SquareRow9Band15

theorem recurrence6B1SquareBand15_eq :
    recurrence6B1SquareBand15 = remainder7Coefficient1SquareBlock15 := by
  unfold recurrence6B1SquareBand15 recurrence6B1SquareRow5Band15 recurrence6B1SquareRow6Band15
  unfold recurrence6B1SquareRow7Band15 recurrence6B1SquareRow8Band15 recurrence6B1SquareRow9Band15
  unfold remainder7Coefficient1SquareBlock15
  ring

/-- Internal datum. -/ def recurrence6B1SquareBand16 : Coefficient :=
  recurrence6B1SquareRow6Band16 +
  recurrence6B1SquareRow7Band16 +
  recurrence6B1SquareRow8Band16 +
  recurrence6B1SquareRow9Band16

theorem recurrence6B1SquareBand16_eq :
    recurrence6B1SquareBand16 = remainder7Coefficient1SquareBlock16 := by
  unfold recurrence6B1SquareBand16 recurrence6B1SquareRow6Band16 recurrence6B1SquareRow7Band16
  unfold recurrence6B1SquareRow8Band16 recurrence6B1SquareRow9Band16
  unfold remainder7Coefficient1SquareBlock16
  ring

/-- Internal datum. -/ def recurrence6B1SquareBand17 : Coefficient :=
  recurrence6B1SquareRow7Band17 +
  recurrence6B1SquareRow8Band17 +
  recurrence6B1SquareRow9Band17

theorem recurrence6B1SquareBand17_eq :
    recurrence6B1SquareBand17 = remainder7Coefficient1SquareBlock17 := by
  unfold recurrence6B1SquareBand17 recurrence6B1SquareRow7Band17 recurrence6B1SquareRow8Band17
  unfold recurrence6B1SquareRow9Band17 remainder7Coefficient1SquareBlock17
  ring

/-- Internal datum. -/ def recurrence6B1SquareBand18 : Coefficient :=
  recurrence6B1SquareRow8Band18 +
  recurrence6B1SquareRow9Band18

theorem recurrence6B1SquareBand18_eq :
    recurrence6B1SquareBand18 = remainder7Coefficient1SquareBlock18 := by
  unfold recurrence6B1SquareBand18 recurrence6B1SquareRow8Band18 recurrence6B1SquareRow9Band18
  unfold remainder7Coefficient1SquareBlock18
  ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
