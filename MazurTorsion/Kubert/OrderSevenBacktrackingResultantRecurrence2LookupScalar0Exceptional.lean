/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar0ExceptionalPart0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar0ExceptionalPart1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar0ExceptionalPart2

/-!
# Recurrence 2 lookup certificate: Scalar0Exceptional degree bound

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence2Scalar0Exceptional_natDegree_le :
    recurrence2Scalar0Exceptional.natDegree ≤ 387 := by
  unfold recurrence2Scalar0Exceptional
  calc
    (recurrence2ExceptionalProduct * remainder4Coefficient0).natDegree ≤
        recurrence2ExceptionalProduct.natDegree + remainder4Coefficient0.natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 193 + 194 :=
      Nat.add_le_add recurrence2ExceptionalProduct_natDegree_le
        recurrence2C0_natDegree_le

theorem recurrence2Scalar0Exceptional_coeff_high (n : ℕ) (h : 387 < n) :
    recurrence2Scalar0Exceptional.coeff n = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt recurrence2Scalar0Exceptional_natDegree_le h

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
