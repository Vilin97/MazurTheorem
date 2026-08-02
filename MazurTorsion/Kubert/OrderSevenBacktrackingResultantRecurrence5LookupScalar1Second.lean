/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupScalar1SecondPart0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupScalar1SecondPart1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupScalar1SecondPart2

/-!
# Recurrence 5 lookup certificate: Scalar1Second degree bound

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence5Scalar1Second_natDegree_le :
    recurrence5Scalar1Second.natDegree ≤ 462 := by
  unfold recurrence5Scalar1Second
  calc
    (remainder6Coefficient1 * recurrence5QuotientConstant).natDegree ≤
        remainder6Coefficient1.natDegree + recurrence5QuotientConstant.natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 149 + 313 :=
      Nat.add_le_add recurrence5B1_natDegree_le
        recurrence5QuotientConstant_natDegree_le

theorem recurrence5Scalar1Second_coeff_high (n : ℕ) (h : 462 < n) :
    recurrence5Scalar1Second.coeff n = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt recurrence5Scalar1Second_natDegree_le h

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
