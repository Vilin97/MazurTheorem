/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar1FirstPart0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar1FirstPart1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar1FirstPart2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar1FirstPart3
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar1FirstPart4
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar1First degree bound

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4Scalar1First_coeff_0

theorem recurrence4Scalar1First_coeff_low (n : ℕ) (h : n < 1) :
    recurrence4Scalar1First.coeff n = 0 := by
  have hn : n = 0 := by omega
  subst n
  norm_num

theorem recurrence4Scalar1First_natDegree_le :
    recurrence4Scalar1First.natDegree ≤ 518 := by
  unfold recurrence4Scalar1First
  calc
    (remainder5Coefficient0 * recurrence4B3A4).natDegree ≤
        remainder5Coefficient0.natDegree + recurrence4B3A4.natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 176 + 342 :=
      Nat.add_le_add recurrence4B0_natDegree_le
        recurrence4B3A4_natDegree_le

theorem recurrence4Scalar1First_coeff_high (n : ℕ) (h : 518 < n) :
    recurrence4Scalar1First.coeff n = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt recurrence4Scalar1First_natDegree_le h

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
