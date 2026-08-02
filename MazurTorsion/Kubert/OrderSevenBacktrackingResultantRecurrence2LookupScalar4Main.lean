/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar4MainPart0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar4MainPart1

/-!
# Recurrence 2 lookup certificate: Scalar4Main degree bound

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence2Scalar4Main_natDegree_le :
    recurrence2Scalar4Main.natDegree ≤ 371 := by
  unfold recurrence2Scalar4Main
  calc
    (remainder3Coefficient4 * recurrence2QuotientConstant).natDegree ≤
        remainder3Coefficient4.natDegree + recurrence2QuotientConstant.natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 138 + 233 :=
      Nat.add_le_add recurrence2B4_natDegree_le
        recurrence2QuotientConstant_natDegree_le

theorem recurrence2Scalar4Main_coeff_high (n : ℕ) (h : 371 < n) :
    recurrence2Scalar4Main.coeff n = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt recurrence2Scalar4Main_natDegree_le h

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
