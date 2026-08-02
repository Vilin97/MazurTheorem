/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupScalar1FirstPart0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupScalar1FirstPart1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupScalar1FirstPart2

/-!
# Recurrence 5 lookup certificate: Scalar1First degree bound

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence5Scalar1First_natDegree_le :
    recurrence5Scalar1First.natDegree ≤ 462 := by
  unfold recurrence5Scalar1First
  calc
    (remainder6Coefficient0 * recurrence5B2A3).natDegree ≤
        remainder6Coefficient0.natDegree + recurrence5B2A3.natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 153 + 309 :=
      Nat.add_le_add recurrence5B0_natDegree_le
        recurrence5B2A3_natDegree_le

theorem recurrence5Scalar1First_coeff_high (n : ℕ) (h : 462 < n) :
    recurrence5Scalar1First.coeff n = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt recurrence5Scalar1First_natDegree_le h

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
