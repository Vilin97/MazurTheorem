/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar1ShiftPart0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar1ShiftPart1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar1ShiftPart2

/-!
# Recurrence 2 lookup certificate: Scalar1Shift degree bound

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence2Scalar1Shift_natDegree_le :
    recurrence2Scalar1Shift.natDegree ≤ 383 := by
  unfold recurrence2Scalar1Shift
  calc
    (remainder3Coefficient0 * recurrence2B5A6).natDegree ≤
        remainder3Coefficient0.natDegree + recurrence2B5A6.natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 154 + 229 :=
      Nat.add_le_add recurrence2B0_natDegree_le
        recurrence2B5A6_natDegree_le

theorem recurrence2Scalar1Shift_coeff_high (n : ℕ) (h : 383 < n) :
    recurrence2Scalar1Shift.coeff n = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt recurrence2Scalar1Shift_natDegree_le h

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
