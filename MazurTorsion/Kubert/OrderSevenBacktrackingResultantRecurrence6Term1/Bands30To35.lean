/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term1.Rows9To11
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term1.Rows12To14
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term1.Rows15To17
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6BlockData.NormalizedResidualTerm1
import Mathlib.Tactic.Ring

/-!
# Recurrence 6 Term1 bands 30–35

This file checks an independent group of band identities for Term1 of the sixth
pseudo-division recurrence.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

def recurrence6Term1Band30 : Coefficient :=
  recurrence6Term1Row11Band30 +
  recurrence6Term1Row12Band30 +
  recurrence6Term1Row13Band30 +
  recurrence6Term1Row14Band30 +
  recurrence6Term1Row15Band30 +
  recurrence6Term1Row16Band30 +
  recurrence6Term1Row17Band30

theorem recurrence6Term1Band30_eq :
    recurrence6Term1Band30 = normalizedResidual6Term1Block30 := by
  unfold recurrence6Term1Band30 recurrence6Term1Row11Band30 recurrence6Term1Row12Band30
  unfold recurrence6Term1Row13Band30 recurrence6Term1Row14Band30 recurrence6Term1Row15Band30
  unfold recurrence6Term1Row16Band30 recurrence6Term1Row17Band30 normalizedResidual6Term1Block30
  ring

def recurrence6Term1Band31 : Coefficient :=
  recurrence6Term1Row12Band31 +
  recurrence6Term1Row13Band31 +
  recurrence6Term1Row14Band31 +
  recurrence6Term1Row15Band31 +
  recurrence6Term1Row16Band31 +
  recurrence6Term1Row17Band31

theorem recurrence6Term1Band31_eq :
    recurrence6Term1Band31 = normalizedResidual6Term1Block31 := by
  unfold recurrence6Term1Band31 recurrence6Term1Row12Band31 recurrence6Term1Row13Band31
  unfold recurrence6Term1Row14Band31 recurrence6Term1Row15Band31 recurrence6Term1Row16Band31
  unfold recurrence6Term1Row17Band31 normalizedResidual6Term1Block31
  ring

def recurrence6Term1Band32 : Coefficient :=
  recurrence6Term1Row13Band32 +
  recurrence6Term1Row14Band32 +
  recurrence6Term1Row15Band32 +
  recurrence6Term1Row16Band32 +
  recurrence6Term1Row17Band32

theorem recurrence6Term1Band32_eq :
    recurrence6Term1Band32 = normalizedResidual6Term1Block32 := by
  unfold recurrence6Term1Band32 recurrence6Term1Row13Band32 recurrence6Term1Row14Band32
  unfold recurrence6Term1Row15Band32 recurrence6Term1Row16Band32 recurrence6Term1Row17Band32
  unfold normalizedResidual6Term1Block32
  ring

def recurrence6Term1Band33 : Coefficient :=
  recurrence6Term1Row14Band33 +
  recurrence6Term1Row15Band33 +
  recurrence6Term1Row16Band33 +
  recurrence6Term1Row17Band33

theorem recurrence6Term1Band33_eq :
    recurrence6Term1Band33 = normalizedResidual6Term1Block33 := by
  unfold recurrence6Term1Band33 recurrence6Term1Row14Band33 recurrence6Term1Row15Band33
  unfold recurrence6Term1Row16Band33 recurrence6Term1Row17Band33 normalizedResidual6Term1Block33
  ring

def recurrence6Term1Band34 : Coefficient :=
  recurrence6Term1Row15Band34 +
  recurrence6Term1Row16Band34 +
  recurrence6Term1Row17Band34

theorem recurrence6Term1Band34_eq :
    recurrence6Term1Band34 = normalizedResidual6Term1Block34 := by
  unfold recurrence6Term1Band34 recurrence6Term1Row15Band34 recurrence6Term1Row16Band34
  unfold recurrence6Term1Row17Band34 normalizedResidual6Term1Block34
  ring

def recurrence6Term1Band35 : Coefficient :=
  recurrence6Term1Row16Band35 +
  recurrence6Term1Row17Band35

theorem recurrence6Term1Band35_eq :
    recurrence6Term1Band35 = normalizedResidual6Term1Block35 := by
  unfold recurrence6Term1Band35 recurrence6Term1Row16Band35 recurrence6Term1Row17Band35
  unfold normalizedResidual6Term1Block35
  ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
