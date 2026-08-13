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
# Recurrence 6 Term1 bands 18–23

This file checks an independent group of band identities for Term1 of the sixth
pseudo-division recurrence.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

/-- Internal datum. -/ def recurrence6Term1Band18 : Coefficient :=
  recurrence6Term1Row0Band18 +
  recurrence6Term1Row1Band18 +
  recurrence6Term1Row2Band18 +
  recurrence6Term1Row3Band18 +
  recurrence6Term1Row4Band18 +
  recurrence6Term1Row5Band18 +
  recurrence6Term1Row6Band18 +
  recurrence6Term1Row7Band18 +
  recurrence6Term1Row8Band18 +
  recurrence6Term1Row9Band18 +
  recurrence6Term1Row10Band18 +
  recurrence6Term1Row11Band18 +
  recurrence6Term1Row12Band18 +
  recurrence6Term1Row13Band18 +
  recurrence6Term1Row14Band18 +
  recurrence6Term1Row15Band18 +
  recurrence6Term1Row16Band18 +
  recurrence6Term1Row17Band18

theorem recurrence6Term1Band18_eq :
    recurrence6Term1Band18 = normalizedResidual6Term1Block18 := by
  unfold recurrence6Term1Band18 recurrence6Term1Row0Band18 recurrence6Term1Row1Band18
  unfold recurrence6Term1Row2Band18 recurrence6Term1Row3Band18 recurrence6Term1Row4Band18
  unfold recurrence6Term1Row5Band18 recurrence6Term1Row6Band18 recurrence6Term1Row7Band18
  unfold recurrence6Term1Row8Band18 recurrence6Term1Row9Band18 recurrence6Term1Row10Band18
  unfold recurrence6Term1Row11Band18 recurrence6Term1Row12Band18 recurrence6Term1Row13Band18
  unfold recurrence6Term1Row14Band18 recurrence6Term1Row15Band18 recurrence6Term1Row16Band18
  unfold recurrence6Term1Row17Band18 normalizedResidual6Term1Block18
  ring

/-- Internal datum. -/ def recurrence6Term1Band19 : Coefficient :=
  recurrence6Term1Row0Band19 +
  recurrence6Term1Row1Band19 +
  recurrence6Term1Row2Band19 +
  recurrence6Term1Row3Band19 +
  recurrence6Term1Row4Band19 +
  recurrence6Term1Row5Band19 +
  recurrence6Term1Row6Band19 +
  recurrence6Term1Row7Band19 +
  recurrence6Term1Row8Band19 +
  recurrence6Term1Row9Band19 +
  recurrence6Term1Row10Band19 +
  recurrence6Term1Row11Band19 +
  recurrence6Term1Row12Band19 +
  recurrence6Term1Row13Band19 +
  recurrence6Term1Row14Band19 +
  recurrence6Term1Row15Band19 +
  recurrence6Term1Row16Band19 +
  recurrence6Term1Row17Band19

theorem recurrence6Term1Band19_eq :
    recurrence6Term1Band19 = normalizedResidual6Term1Block19 := by
  unfold recurrence6Term1Band19 recurrence6Term1Row0Band19 recurrence6Term1Row1Band19
  unfold recurrence6Term1Row2Band19 recurrence6Term1Row3Band19 recurrence6Term1Row4Band19
  unfold recurrence6Term1Row5Band19 recurrence6Term1Row6Band19 recurrence6Term1Row7Band19
  unfold recurrence6Term1Row8Band19 recurrence6Term1Row9Band19 recurrence6Term1Row10Band19
  unfold recurrence6Term1Row11Band19 recurrence6Term1Row12Band19 recurrence6Term1Row13Band19
  unfold recurrence6Term1Row14Band19 recurrence6Term1Row15Band19 recurrence6Term1Row16Band19
  unfold recurrence6Term1Row17Band19 normalizedResidual6Term1Block19
  ring

/-- Internal datum. -/ def recurrence6Term1Band20 : Coefficient :=
  recurrence6Term1Row1Band20 +
  recurrence6Term1Row2Band20 +
  recurrence6Term1Row3Band20 +
  recurrence6Term1Row4Band20 +
  recurrence6Term1Row5Band20 +
  recurrence6Term1Row6Band20 +
  recurrence6Term1Row7Band20 +
  recurrence6Term1Row8Band20 +
  recurrence6Term1Row9Band20 +
  recurrence6Term1Row10Band20 +
  recurrence6Term1Row11Band20 +
  recurrence6Term1Row12Band20 +
  recurrence6Term1Row13Band20 +
  recurrence6Term1Row14Band20 +
  recurrence6Term1Row15Band20 +
  recurrence6Term1Row16Band20 +
  recurrence6Term1Row17Band20

theorem recurrence6Term1Band20_eq :
    recurrence6Term1Band20 = normalizedResidual6Term1Block20 := by
  unfold recurrence6Term1Band20 recurrence6Term1Row1Band20 recurrence6Term1Row2Band20
  unfold recurrence6Term1Row3Band20 recurrence6Term1Row4Band20 recurrence6Term1Row5Band20
  unfold recurrence6Term1Row6Band20 recurrence6Term1Row7Band20 recurrence6Term1Row8Band20
  unfold recurrence6Term1Row9Band20 recurrence6Term1Row10Band20 recurrence6Term1Row11Band20
  unfold recurrence6Term1Row12Band20 recurrence6Term1Row13Band20 recurrence6Term1Row14Band20
  unfold recurrence6Term1Row15Band20 recurrence6Term1Row16Band20 recurrence6Term1Row17Band20
  unfold normalizedResidual6Term1Block20
  ring

/-- Internal datum. -/ def recurrence6Term1Band21 : Coefficient :=
  recurrence6Term1Row2Band21 +
  recurrence6Term1Row3Band21 +
  recurrence6Term1Row4Band21 +
  recurrence6Term1Row5Band21 +
  recurrence6Term1Row6Band21 +
  recurrence6Term1Row7Band21 +
  recurrence6Term1Row8Band21 +
  recurrence6Term1Row9Band21 +
  recurrence6Term1Row10Band21 +
  recurrence6Term1Row11Band21 +
  recurrence6Term1Row12Band21 +
  recurrence6Term1Row13Band21 +
  recurrence6Term1Row14Band21 +
  recurrence6Term1Row15Band21 +
  recurrence6Term1Row16Band21 +
  recurrence6Term1Row17Band21

theorem recurrence6Term1Band21_eq :
    recurrence6Term1Band21 = normalizedResidual6Term1Block21 := by
  unfold recurrence6Term1Band21 recurrence6Term1Row2Band21 recurrence6Term1Row3Band21
  unfold recurrence6Term1Row4Band21 recurrence6Term1Row5Band21 recurrence6Term1Row6Band21
  unfold recurrence6Term1Row7Band21 recurrence6Term1Row8Band21 recurrence6Term1Row9Band21
  unfold recurrence6Term1Row10Band21 recurrence6Term1Row11Band21 recurrence6Term1Row12Band21
  unfold recurrence6Term1Row13Band21 recurrence6Term1Row14Band21 recurrence6Term1Row15Band21
  unfold recurrence6Term1Row16Band21 recurrence6Term1Row17Band21 normalizedResidual6Term1Block21
  ring

/-- Internal datum. -/ def recurrence6Term1Band22 : Coefficient :=
  recurrence6Term1Row3Band22 +
  recurrence6Term1Row4Band22 +
  recurrence6Term1Row5Band22 +
  recurrence6Term1Row6Band22 +
  recurrence6Term1Row7Band22 +
  recurrence6Term1Row8Band22 +
  recurrence6Term1Row9Band22 +
  recurrence6Term1Row10Band22 +
  recurrence6Term1Row11Band22 +
  recurrence6Term1Row12Band22 +
  recurrence6Term1Row13Band22 +
  recurrence6Term1Row14Band22 +
  recurrence6Term1Row15Band22 +
  recurrence6Term1Row16Band22 +
  recurrence6Term1Row17Band22

theorem recurrence6Term1Band22_eq :
    recurrence6Term1Band22 = normalizedResidual6Term1Block22 := by
  unfold recurrence6Term1Band22 recurrence6Term1Row3Band22 recurrence6Term1Row4Band22
  unfold recurrence6Term1Row5Band22 recurrence6Term1Row6Band22 recurrence6Term1Row7Band22
  unfold recurrence6Term1Row8Band22 recurrence6Term1Row9Band22 recurrence6Term1Row10Band22
  unfold recurrence6Term1Row11Band22 recurrence6Term1Row12Band22 recurrence6Term1Row13Band22
  unfold recurrence6Term1Row14Band22 recurrence6Term1Row15Band22 recurrence6Term1Row16Band22
  unfold recurrence6Term1Row17Band22 normalizedResidual6Term1Block22
  ring

/-- Internal datum. -/ def recurrence6Term1Band23 : Coefficient :=
  recurrence6Term1Row4Band23 +
  recurrence6Term1Row5Band23 +
  recurrence6Term1Row6Band23 +
  recurrence6Term1Row7Band23 +
  recurrence6Term1Row8Band23 +
  recurrence6Term1Row9Band23 +
  recurrence6Term1Row10Band23 +
  recurrence6Term1Row11Band23 +
  recurrence6Term1Row12Band23 +
  recurrence6Term1Row13Band23 +
  recurrence6Term1Row14Band23 +
  recurrence6Term1Row15Band23 +
  recurrence6Term1Row16Band23 +
  recurrence6Term1Row17Band23

theorem recurrence6Term1Band23_eq :
    recurrence6Term1Band23 = normalizedResidual6Term1Block23 := by
  unfold recurrence6Term1Band23 recurrence6Term1Row4Band23 recurrence6Term1Row5Band23
  unfold recurrence6Term1Row6Band23 recurrence6Term1Row7Band23 recurrence6Term1Row8Band23
  unfold recurrence6Term1Row9Band23 recurrence6Term1Row10Band23 recurrence6Term1Row11Band23
  unfold recurrence6Term1Row12Band23 recurrence6Term1Row13Band23 recurrence6Term1Row14Band23
  unfold recurrence6Term1Row15Band23 recurrence6Term1Row16Band23 recurrence6Term1Row17Band23
  unfold normalizedResidual6Term1Block23
  ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
