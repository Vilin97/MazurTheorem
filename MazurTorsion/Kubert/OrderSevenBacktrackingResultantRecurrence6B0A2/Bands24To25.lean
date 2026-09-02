/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B0A2.Rows6To7
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B0A2.Rows8To9
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6BlockData.Coefficient0Coefficient2Product
import Mathlib.Tactic.Ring

/-!
# Recurrence 6 B0A2 bands 24–25

This file checks bands 24 through 25 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

def recurrence6B0A2Band24 : Coefficient :=
  recurrence6B0A2Row7Band24 +
  recurrence6B0A2Row8Band24 +
  recurrence6B0A2Row9Band24

theorem recurrence6B0A2Band24_eq :
    recurrence6B0A2Band24 = remainder7Coefficient0TimesRemainder6Coefficient2Block24 := by
  unfold recurrence6B0A2Band24 recurrence6B0A2Row7Band24 recurrence6B0A2Row8Band24
  unfold recurrence6B0A2Row9Band24 remainder7Coefficient0TimesRemainder6Coefficient2Block24
  ring

def recurrence6B0A2Band25 : Coefficient :=
  recurrence6B0A2Row8Band25 +
  recurrence6B0A2Row9Band25

theorem recurrence6B0A2Band25_eq :
    recurrence6B0A2Band25 = remainder7Coefficient0TimesRemainder6Coefficient2Block25 := by
  unfold recurrence6B0A2Band25 recurrence6B0A2Row8Band25 recurrence6B0A2Row9Band25
  unfold remainder7Coefficient0TimesRemainder6Coefficient2Block25
  ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
