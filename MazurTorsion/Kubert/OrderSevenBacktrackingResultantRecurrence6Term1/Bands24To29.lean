/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term1.Rows3To5
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term1.Rows6To8
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term1.Rows9To11
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term1.Rows12To14
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term1.Rows15To17
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6BlockData.NormalizedResidualTerm1
import Mathlib.Tactic.Ring

/-!
# Recurrence 6 Term1 bands 24–29

This file checks an independent group of band identities for Term1 of the sixth
pseudo-division recurrence.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

def recurrence6Term1Band24 : Coefficient :=
  recurrence6Term1Row5Band24 +
  recurrence6Term1Row6Band24 +
  recurrence6Term1Row7Band24 +
  recurrence6Term1Row8Band24 +
  recurrence6Term1Row9Band24 +
  recurrence6Term1Row10Band24 +
  recurrence6Term1Row11Band24 +
  recurrence6Term1Row12Band24 +
  recurrence6Term1Row13Band24 +
  recurrence6Term1Row14Band24 +
  recurrence6Term1Row15Band24 +
  recurrence6Term1Row16Band24 +
  recurrence6Term1Row17Band24

theorem recurrence6Term1Band24_eq :
    recurrence6Term1Band24 = normalizedResidual6Term1Block24 := by
  unfold recurrence6Term1Band24 recurrence6Term1Row5Band24 recurrence6Term1Row6Band24
  unfold recurrence6Term1Row7Band24 recurrence6Term1Row8Band24 recurrence6Term1Row9Band24
  unfold recurrence6Term1Row10Band24 recurrence6Term1Row11Band24 recurrence6Term1Row12Band24
  unfold recurrence6Term1Row13Band24 recurrence6Term1Row14Band24 recurrence6Term1Row15Band24
  unfold recurrence6Term1Row16Band24 recurrence6Term1Row17Band24 normalizedResidual6Term1Block24
  ring

def recurrence6Term1Band25 : Coefficient :=
  recurrence6Term1Row6Band25 +
  recurrence6Term1Row7Band25 +
  recurrence6Term1Row8Band25 +
  recurrence6Term1Row9Band25 +
  recurrence6Term1Row10Band25 +
  recurrence6Term1Row11Band25 +
  recurrence6Term1Row12Band25 +
  recurrence6Term1Row13Band25 +
  recurrence6Term1Row14Band25 +
  recurrence6Term1Row15Band25 +
  recurrence6Term1Row16Band25 +
  recurrence6Term1Row17Band25

theorem recurrence6Term1Band25_eq :
    recurrence6Term1Band25 = normalizedResidual6Term1Block25 := by
  unfold recurrence6Term1Band25 recurrence6Term1Row6Band25 recurrence6Term1Row7Band25
  unfold recurrence6Term1Row8Band25 recurrence6Term1Row9Band25 recurrence6Term1Row10Band25
  unfold recurrence6Term1Row11Band25 recurrence6Term1Row12Band25 recurrence6Term1Row13Band25
  unfold recurrence6Term1Row14Band25 recurrence6Term1Row15Band25 recurrence6Term1Row16Band25
  unfold recurrence6Term1Row17Band25 normalizedResidual6Term1Block25
  ring

def recurrence6Term1Band26 : Coefficient :=
  recurrence6Term1Row7Band26 +
  recurrence6Term1Row8Band26 +
  recurrence6Term1Row9Band26 +
  recurrence6Term1Row10Band26 +
  recurrence6Term1Row11Band26 +
  recurrence6Term1Row12Band26 +
  recurrence6Term1Row13Band26 +
  recurrence6Term1Row14Band26 +
  recurrence6Term1Row15Band26 +
  recurrence6Term1Row16Band26 +
  recurrence6Term1Row17Band26

theorem recurrence6Term1Band26_eq :
    recurrence6Term1Band26 = normalizedResidual6Term1Block26 := by
  unfold recurrence6Term1Band26 recurrence6Term1Row7Band26 recurrence6Term1Row8Band26
  unfold recurrence6Term1Row9Band26 recurrence6Term1Row10Band26 recurrence6Term1Row11Band26
  unfold recurrence6Term1Row12Band26 recurrence6Term1Row13Band26 recurrence6Term1Row14Band26
  unfold recurrence6Term1Row15Band26 recurrence6Term1Row16Band26 recurrence6Term1Row17Band26
  unfold normalizedResidual6Term1Block26
  ring

def recurrence6Term1Band27 : Coefficient :=
  recurrence6Term1Row8Band27 +
  recurrence6Term1Row9Band27 +
  recurrence6Term1Row10Band27 +
  recurrence6Term1Row11Band27 +
  recurrence6Term1Row12Band27 +
  recurrence6Term1Row13Band27 +
  recurrence6Term1Row14Band27 +
  recurrence6Term1Row15Band27 +
  recurrence6Term1Row16Band27 +
  recurrence6Term1Row17Band27

theorem recurrence6Term1Band27_eq :
    recurrence6Term1Band27 = normalizedResidual6Term1Block27 := by
  unfold recurrence6Term1Band27 recurrence6Term1Row8Band27 recurrence6Term1Row9Band27
  unfold recurrence6Term1Row10Band27 recurrence6Term1Row11Band27 recurrence6Term1Row12Band27
  unfold recurrence6Term1Row13Band27 recurrence6Term1Row14Band27 recurrence6Term1Row15Band27
  unfold recurrence6Term1Row16Band27 recurrence6Term1Row17Band27 normalizedResidual6Term1Block27
  ring

def recurrence6Term1Band28 : Coefficient :=
  recurrence6Term1Row9Band28 +
  recurrence6Term1Row10Band28 +
  recurrence6Term1Row11Band28 +
  recurrence6Term1Row12Band28 +
  recurrence6Term1Row13Band28 +
  recurrence6Term1Row14Band28 +
  recurrence6Term1Row15Band28 +
  recurrence6Term1Row16Band28 +
  recurrence6Term1Row17Band28

theorem recurrence6Term1Band28_eq :
    recurrence6Term1Band28 = normalizedResidual6Term1Block28 := by
  unfold recurrence6Term1Band28 recurrence6Term1Row9Band28 recurrence6Term1Row10Band28
  unfold recurrence6Term1Row11Band28 recurrence6Term1Row12Band28 recurrence6Term1Row13Band28
  unfold recurrence6Term1Row14Band28 recurrence6Term1Row15Band28 recurrence6Term1Row16Band28
  unfold recurrence6Term1Row17Band28 normalizedResidual6Term1Block28
  ring

def recurrence6Term1Band29 : Coefficient :=
  recurrence6Term1Row10Band29 +
  recurrence6Term1Row11Band29 +
  recurrence6Term1Row12Band29 +
  recurrence6Term1Row13Band29 +
  recurrence6Term1Row14Band29 +
  recurrence6Term1Row15Band29 +
  recurrence6Term1Row16Band29 +
  recurrence6Term1Row17Band29

theorem recurrence6Term1Band29_eq :
    recurrence6Term1Band29 = normalizedResidual6Term1Block29 := by
  unfold recurrence6Term1Band29 recurrence6Term1Row10Band29 recurrence6Term1Row11Band29
  unfold recurrence6Term1Row12Band29 recurrence6Term1Row13Band29 recurrence6Term1Row14Band29
  unfold recurrence6Term1Row15Band29 recurrence6Term1Row16Band29 recurrence6Term1Row17Band29
  unfold normalizedResidual6Term1Block29
  ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
