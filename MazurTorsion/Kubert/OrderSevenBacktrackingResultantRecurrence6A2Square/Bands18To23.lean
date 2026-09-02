/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6A2Square.Rows0To2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6A2Square.Rows3To5
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6A2Square.Rows6To8
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6A2Square.Rows9To11
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6A2Square.Rows12To14
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6A2Square.Rows15To16
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6BlockData.Coefficient2Square
import Mathlib.Tactic.Ring

/-!
# Recurrence 6 A2Square bands 18–23

This file checks bands 18 through 23 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

def recurrence6A2SquareBand18 : Coefficient :=
  recurrence6A2SquareRow1Band18 +
  recurrence6A2SquareRow2Band18 +
  recurrence6A2SquareRow3Band18 +
  recurrence6A2SquareRow4Band18 +
  recurrence6A2SquareRow5Band18 +
  recurrence6A2SquareRow6Band18 +
  recurrence6A2SquareRow7Band18 +
  recurrence6A2SquareRow8Band18 +
  recurrence6A2SquareRow9Band18 +
  recurrence6A2SquareRow10Band18 +
  recurrence6A2SquareRow11Band18 +
  recurrence6A2SquareRow12Band18 +
  recurrence6A2SquareRow13Band18 +
  recurrence6A2SquareRow14Band18 +
  recurrence6A2SquareRow15Band18 +
  recurrence6A2SquareRow16Band18

theorem recurrence6A2SquareBand18_eq :
    recurrence6A2SquareBand18 = remainder6Coefficient2SquareBlock18 := by
  unfold recurrence6A2SquareBand18 recurrence6A2SquareRow1Band18 recurrence6A2SquareRow2Band18
  unfold recurrence6A2SquareRow3Band18 recurrence6A2SquareRow4Band18 recurrence6A2SquareRow5Band18
  unfold recurrence6A2SquareRow6Band18 recurrence6A2SquareRow7Band18 recurrence6A2SquareRow8Band18
  unfold recurrence6A2SquareRow9Band18 recurrence6A2SquareRow10Band18 recurrence6A2SquareRow11Band18
  unfold recurrence6A2SquareRow12Band18 recurrence6A2SquareRow13Band18
  unfold recurrence6A2SquareRow14Band18 recurrence6A2SquareRow15Band18
  unfold recurrence6A2SquareRow16Band18 remainder6Coefficient2SquareBlock18
  ring

def recurrence6A2SquareBand19 : Coefficient :=
  recurrence6A2SquareRow2Band19 +
  recurrence6A2SquareRow3Band19 +
  recurrence6A2SquareRow4Band19 +
  recurrence6A2SquareRow5Band19 +
  recurrence6A2SquareRow6Band19 +
  recurrence6A2SquareRow7Band19 +
  recurrence6A2SquareRow8Band19 +
  recurrence6A2SquareRow9Band19 +
  recurrence6A2SquareRow10Band19 +
  recurrence6A2SquareRow11Band19 +
  recurrence6A2SquareRow12Band19 +
  recurrence6A2SquareRow13Band19 +
  recurrence6A2SquareRow14Band19 +
  recurrence6A2SquareRow15Band19 +
  recurrence6A2SquareRow16Band19

theorem recurrence6A2SquareBand19_eq :
    recurrence6A2SquareBand19 = remainder6Coefficient2SquareBlock19 := by
  unfold recurrence6A2SquareBand19 recurrence6A2SquareRow2Band19 recurrence6A2SquareRow3Band19
  unfold recurrence6A2SquareRow4Band19 recurrence6A2SquareRow5Band19 recurrence6A2SquareRow6Band19
  unfold recurrence6A2SquareRow7Band19 recurrence6A2SquareRow8Band19 recurrence6A2SquareRow9Band19
  unfold recurrence6A2SquareRow10Band19 recurrence6A2SquareRow11Band19
  unfold recurrence6A2SquareRow12Band19 recurrence6A2SquareRow13Band19
  unfold recurrence6A2SquareRow14Band19 recurrence6A2SquareRow15Band19
  unfold recurrence6A2SquareRow16Band19 remainder6Coefficient2SquareBlock19
  ring

def recurrence6A2SquareBand20 : Coefficient :=
  recurrence6A2SquareRow3Band20 +
  recurrence6A2SquareRow4Band20 +
  recurrence6A2SquareRow5Band20 +
  recurrence6A2SquareRow6Band20 +
  recurrence6A2SquareRow7Band20 +
  recurrence6A2SquareRow8Band20 +
  recurrence6A2SquareRow9Band20 +
  recurrence6A2SquareRow10Band20 +
  recurrence6A2SquareRow11Band20 +
  recurrence6A2SquareRow12Band20 +
  recurrence6A2SquareRow13Band20 +
  recurrence6A2SquareRow14Band20 +
  recurrence6A2SquareRow15Band20 +
  recurrence6A2SquareRow16Band20

theorem recurrence6A2SquareBand20_eq :
    recurrence6A2SquareBand20 = remainder6Coefficient2SquareBlock20 := by
  unfold recurrence6A2SquareBand20 recurrence6A2SquareRow3Band20 recurrence6A2SquareRow4Band20
  unfold recurrence6A2SquareRow5Band20 recurrence6A2SquareRow6Band20 recurrence6A2SquareRow7Band20
  unfold recurrence6A2SquareRow8Band20 recurrence6A2SquareRow9Band20 recurrence6A2SquareRow10Band20
  unfold recurrence6A2SquareRow11Band20 recurrence6A2SquareRow12Band20
  unfold recurrence6A2SquareRow13Band20 recurrence6A2SquareRow14Band20
  unfold recurrence6A2SquareRow15Band20 recurrence6A2SquareRow16Band20
  unfold remainder6Coefficient2SquareBlock20
  ring

def recurrence6A2SquareBand21 : Coefficient :=
  recurrence6A2SquareRow4Band21 +
  recurrence6A2SquareRow5Band21 +
  recurrence6A2SquareRow6Band21 +
  recurrence6A2SquareRow7Band21 +
  recurrence6A2SquareRow8Band21 +
  recurrence6A2SquareRow9Band21 +
  recurrence6A2SquareRow10Band21 +
  recurrence6A2SquareRow11Band21 +
  recurrence6A2SquareRow12Band21 +
  recurrence6A2SquareRow13Band21 +
  recurrence6A2SquareRow14Band21 +
  recurrence6A2SquareRow15Band21 +
  recurrence6A2SquareRow16Band21

theorem recurrence6A2SquareBand21_eq :
    recurrence6A2SquareBand21 = remainder6Coefficient2SquareBlock21 := by
  unfold recurrence6A2SquareBand21 recurrence6A2SquareRow4Band21 recurrence6A2SquareRow5Band21
  unfold recurrence6A2SquareRow6Band21 recurrence6A2SquareRow7Band21 recurrence6A2SquareRow8Band21
  unfold recurrence6A2SquareRow9Band21 recurrence6A2SquareRow10Band21 recurrence6A2SquareRow11Band21
  unfold recurrence6A2SquareRow12Band21 recurrence6A2SquareRow13Band21
  unfold recurrence6A2SquareRow14Band21 recurrence6A2SquareRow15Band21
  unfold recurrence6A2SquareRow16Band21 remainder6Coefficient2SquareBlock21
  ring

def recurrence6A2SquareBand22 : Coefficient :=
  recurrence6A2SquareRow5Band22 +
  recurrence6A2SquareRow6Band22 +
  recurrence6A2SquareRow7Band22 +
  recurrence6A2SquareRow8Band22 +
  recurrence6A2SquareRow9Band22 +
  recurrence6A2SquareRow10Band22 +
  recurrence6A2SquareRow11Band22 +
  recurrence6A2SquareRow12Band22 +
  recurrence6A2SquareRow13Band22 +
  recurrence6A2SquareRow14Band22 +
  recurrence6A2SquareRow15Band22 +
  recurrence6A2SquareRow16Band22

theorem recurrence6A2SquareBand22_eq :
    recurrence6A2SquareBand22 = remainder6Coefficient2SquareBlock22 := by
  unfold recurrence6A2SquareBand22 recurrence6A2SquareRow5Band22 recurrence6A2SquareRow6Band22
  unfold recurrence6A2SquareRow7Band22 recurrence6A2SquareRow8Band22 recurrence6A2SquareRow9Band22
  unfold recurrence6A2SquareRow10Band22 recurrence6A2SquareRow11Band22
  unfold recurrence6A2SquareRow12Band22 recurrence6A2SquareRow13Band22
  unfold recurrence6A2SquareRow14Band22 recurrence6A2SquareRow15Band22
  unfold recurrence6A2SquareRow16Band22 remainder6Coefficient2SquareBlock22
  ring

def recurrence6A2SquareBand23 : Coefficient :=
  recurrence6A2SquareRow6Band23 +
  recurrence6A2SquareRow7Band23 +
  recurrence6A2SquareRow8Band23 +
  recurrence6A2SquareRow9Band23 +
  recurrence6A2SquareRow10Band23 +
  recurrence6A2SquareRow11Band23 +
  recurrence6A2SquareRow12Band23 +
  recurrence6A2SquareRow13Band23 +
  recurrence6A2SquareRow14Band23 +
  recurrence6A2SquareRow15Band23 +
  recurrence6A2SquareRow16Band23

theorem recurrence6A2SquareBand23_eq :
    recurrence6A2SquareBand23 = remainder6Coefficient2SquareBlock23 := by
  unfold recurrence6A2SquareBand23 recurrence6A2SquareRow6Band23 recurrence6A2SquareRow7Band23
  unfold recurrence6A2SquareRow8Band23 recurrence6A2SquareRow9Band23 recurrence6A2SquareRow10Band23
  unfold recurrence6A2SquareRow11Band23 recurrence6A2SquareRow12Band23
  unfold recurrence6A2SquareRow13Band23 recurrence6A2SquareRow14Band23
  unfold recurrence6A2SquareRow15Band23 recurrence6A2SquareRow16Band23
  unfold remainder6Coefficient2SquareBlock23
  ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
