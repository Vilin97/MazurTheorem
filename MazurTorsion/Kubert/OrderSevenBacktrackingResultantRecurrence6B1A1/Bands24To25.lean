/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B1A1.Rows6To7
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B1A1.Rows8To9
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6BlockData.Coefficient1Product
import Mathlib.Tactic.Ring

/-!
# Recurrence 6 B1A1 bands 24–25

This file checks bands 24 through 25 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

/-- Internal datum. -/ def recurrence6B1A1Band24 : Coefficient :=
  recurrence6B1A1Row7Band24 +
  recurrence6B1A1Row8Band24 +
  recurrence6B1A1Row9Band24

theorem recurrence6B1A1Band24_eq :
    recurrence6B1A1Band24 = remainder7Coefficient1TimesRemainder6Coefficient1Block24 := by
  unfold recurrence6B1A1Band24 recurrence6B1A1Row7Band24 recurrence6B1A1Row8Band24
  unfold recurrence6B1A1Row9Band24 remainder7Coefficient1TimesRemainder6Coefficient1Block24
  ring

/-- Internal datum. -/ def recurrence6B1A1Band25 : Coefficient :=
  recurrence6B1A1Row8Band25 +
  recurrence6B1A1Row9Band25

theorem recurrence6B1A1Band25_eq :
    recurrence6B1A1Band25 = remainder7Coefficient1TimesRemainder6Coefficient1Block25 := by
  unfold recurrence6B1A1Band25 recurrence6B1A1Row8Band25 recurrence6B1A1Row9Band25
  unfold remainder7Coefficient1TimesRemainder6Coefficient1Block25
  ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
