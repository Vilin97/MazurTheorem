/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term1.Rows0To2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term1.Rows3To5
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term1.Rows6To8
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term1.Rows9To11
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term1.Rows12To14
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term1.Rows15To17
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6BlockData.NormalizedResidualTerm1
import Mathlib.Tactic.Ring

/-!
# Recurrence 6 Term1 bands 12–17

This file checks an independent group of band identities for Term1 of the sixth
pseudo-division recurrence.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

def recurrence6Term1Band12 : Coefficient :=
  recurrence6Term1Row0Band12 +
  recurrence6Term1Row1Band12 +
  recurrence6Term1Row2Band12 +
  recurrence6Term1Row3Band12 +
  recurrence6Term1Row4Band12 +
  recurrence6Term1Row5Band12 +
  recurrence6Term1Row6Band12 +
  recurrence6Term1Row7Band12 +
  recurrence6Term1Row8Band12 +
  recurrence6Term1Row9Band12 +
  recurrence6Term1Row10Band12 +
  recurrence6Term1Row11Band12 +
  recurrence6Term1Row12Band12

theorem recurrence6Term1Band12_eq :
    recurrence6Term1Band12 = normalizedResidual6Term1Block12 := by
  unfold recurrence6Term1Band12 recurrence6Term1Row0Band12 recurrence6Term1Row1Band12
  unfold recurrence6Term1Row2Band12 recurrence6Term1Row3Band12 recurrence6Term1Row4Band12
  unfold recurrence6Term1Row5Band12 recurrence6Term1Row6Band12 recurrence6Term1Row7Band12
  unfold recurrence6Term1Row8Band12 recurrence6Term1Row9Band12 recurrence6Term1Row10Band12
  unfold recurrence6Term1Row11Band12 recurrence6Term1Row12Band12 normalizedResidual6Term1Block12
  ring

def recurrence6Term1Band13 : Coefficient :=
  recurrence6Term1Row0Band13 +
  recurrence6Term1Row1Band13 +
  recurrence6Term1Row2Band13 +
  recurrence6Term1Row3Band13 +
  recurrence6Term1Row4Band13 +
  recurrence6Term1Row5Band13 +
  recurrence6Term1Row6Band13 +
  recurrence6Term1Row7Band13 +
  recurrence6Term1Row8Band13 +
  recurrence6Term1Row9Band13 +
  recurrence6Term1Row10Band13 +
  recurrence6Term1Row11Band13 +
  recurrence6Term1Row12Band13 +
  recurrence6Term1Row13Band13

theorem recurrence6Term1Band13_eq :
    recurrence6Term1Band13 = normalizedResidual6Term1Block13 := by
  unfold recurrence6Term1Band13 recurrence6Term1Row0Band13 recurrence6Term1Row1Band13
  unfold recurrence6Term1Row2Band13 recurrence6Term1Row3Band13 recurrence6Term1Row4Band13
  unfold recurrence6Term1Row5Band13 recurrence6Term1Row6Band13 recurrence6Term1Row7Band13
  unfold recurrence6Term1Row8Band13 recurrence6Term1Row9Band13 recurrence6Term1Row10Band13
  unfold recurrence6Term1Row11Band13 recurrence6Term1Row12Band13 recurrence6Term1Row13Band13
  unfold normalizedResidual6Term1Block13
  ring

def recurrence6Term1Band14 : Coefficient :=
  recurrence6Term1Row0Band14 +
  recurrence6Term1Row1Band14 +
  recurrence6Term1Row2Band14 +
  recurrence6Term1Row3Band14 +
  recurrence6Term1Row4Band14 +
  recurrence6Term1Row5Band14 +
  recurrence6Term1Row6Band14 +
  recurrence6Term1Row7Band14 +
  recurrence6Term1Row8Band14 +
  recurrence6Term1Row9Band14 +
  recurrence6Term1Row10Band14 +
  recurrence6Term1Row11Band14 +
  recurrence6Term1Row12Band14 +
  recurrence6Term1Row13Band14 +
  recurrence6Term1Row14Band14

theorem recurrence6Term1Band14_eq :
    recurrence6Term1Band14 = normalizedResidual6Term1Block14 := by
  unfold recurrence6Term1Band14 recurrence6Term1Row0Band14 recurrence6Term1Row1Band14
  unfold recurrence6Term1Row2Band14 recurrence6Term1Row3Band14 recurrence6Term1Row4Band14
  unfold recurrence6Term1Row5Band14 recurrence6Term1Row6Band14 recurrence6Term1Row7Band14
  unfold recurrence6Term1Row8Band14 recurrence6Term1Row9Band14 recurrence6Term1Row10Band14
  unfold recurrence6Term1Row11Band14 recurrence6Term1Row12Band14 recurrence6Term1Row13Band14
  unfold recurrence6Term1Row14Band14 normalizedResidual6Term1Block14
  ring

def recurrence6Term1Band15 : Coefficient :=
  recurrence6Term1Row0Band15 +
  recurrence6Term1Row1Band15 +
  recurrence6Term1Row2Band15 +
  recurrence6Term1Row3Band15 +
  recurrence6Term1Row4Band15 +
  recurrence6Term1Row5Band15 +
  recurrence6Term1Row6Band15 +
  recurrence6Term1Row7Band15 +
  recurrence6Term1Row8Band15 +
  recurrence6Term1Row9Band15 +
  recurrence6Term1Row10Band15 +
  recurrence6Term1Row11Band15 +
  recurrence6Term1Row12Band15 +
  recurrence6Term1Row13Band15 +
  recurrence6Term1Row14Band15 +
  recurrence6Term1Row15Band15

theorem recurrence6Term1Band15_eq :
    recurrence6Term1Band15 = normalizedResidual6Term1Block15 := by
  unfold recurrence6Term1Band15 recurrence6Term1Row0Band15 recurrence6Term1Row1Band15
  unfold recurrence6Term1Row2Band15 recurrence6Term1Row3Band15 recurrence6Term1Row4Band15
  unfold recurrence6Term1Row5Band15 recurrence6Term1Row6Band15 recurrence6Term1Row7Band15
  unfold recurrence6Term1Row8Band15 recurrence6Term1Row9Band15 recurrence6Term1Row10Band15
  unfold recurrence6Term1Row11Band15 recurrence6Term1Row12Band15 recurrence6Term1Row13Band15
  unfold recurrence6Term1Row14Band15 recurrence6Term1Row15Band15 normalizedResidual6Term1Block15
  ring

def recurrence6Term1Band16 : Coefficient :=
  recurrence6Term1Row0Band16 +
  recurrence6Term1Row1Band16 +
  recurrence6Term1Row2Band16 +
  recurrence6Term1Row3Band16 +
  recurrence6Term1Row4Band16 +
  recurrence6Term1Row5Band16 +
  recurrence6Term1Row6Band16 +
  recurrence6Term1Row7Band16 +
  recurrence6Term1Row8Band16 +
  recurrence6Term1Row9Band16 +
  recurrence6Term1Row10Band16 +
  recurrence6Term1Row11Band16 +
  recurrence6Term1Row12Band16 +
  recurrence6Term1Row13Band16 +
  recurrence6Term1Row14Band16 +
  recurrence6Term1Row15Band16 +
  recurrence6Term1Row16Band16

theorem recurrence6Term1Band16_eq :
    recurrence6Term1Band16 = normalizedResidual6Term1Block16 := by
  unfold recurrence6Term1Band16 recurrence6Term1Row0Band16 recurrence6Term1Row1Band16
  unfold recurrence6Term1Row2Band16 recurrence6Term1Row3Band16 recurrence6Term1Row4Band16
  unfold recurrence6Term1Row5Band16 recurrence6Term1Row6Band16 recurrence6Term1Row7Band16
  unfold recurrence6Term1Row8Band16 recurrence6Term1Row9Band16 recurrence6Term1Row10Band16
  unfold recurrence6Term1Row11Band16 recurrence6Term1Row12Band16 recurrence6Term1Row13Band16
  unfold recurrence6Term1Row14Band16 recurrence6Term1Row15Band16 recurrence6Term1Row16Band16
  unfold normalizedResidual6Term1Block16
  ring

def recurrence6Term1Band17 : Coefficient :=
  recurrence6Term1Row0Band17 +
  recurrence6Term1Row1Band17 +
  recurrence6Term1Row2Band17 +
  recurrence6Term1Row3Band17 +
  recurrence6Term1Row4Band17 +
  recurrence6Term1Row5Band17 +
  recurrence6Term1Row6Band17 +
  recurrence6Term1Row7Band17 +
  recurrence6Term1Row8Band17 +
  recurrence6Term1Row9Band17 +
  recurrence6Term1Row10Band17 +
  recurrence6Term1Row11Band17 +
  recurrence6Term1Row12Band17 +
  recurrence6Term1Row13Band17 +
  recurrence6Term1Row14Band17 +
  recurrence6Term1Row15Band17 +
  recurrence6Term1Row16Band17 +
  recurrence6Term1Row17Band17

theorem recurrence6Term1Band17_eq :
    recurrence6Term1Band17 = normalizedResidual6Term1Block17 := by
  unfold recurrence6Term1Band17 recurrence6Term1Row0Band17 recurrence6Term1Row1Band17
  unfold recurrence6Term1Row2Band17 recurrence6Term1Row3Band17 recurrence6Term1Row4Band17
  unfold recurrence6Term1Row5Band17 recurrence6Term1Row6Band17 recurrence6Term1Row7Band17
  unfold recurrence6Term1Row8Band17 recurrence6Term1Row9Band17 recurrence6Term1Row10Band17
  unfold recurrence6Term1Row11Band17 recurrence6Term1Row12Band17 recurrence6Term1Row13Band17
  unfold recurrence6Term1Row14Band17 recurrence6Term1Row15Band17 recurrence6Term1Row16Band17
  unfold recurrence6Term1Row17Band17 normalizedResidual6Term1Block17
  ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
