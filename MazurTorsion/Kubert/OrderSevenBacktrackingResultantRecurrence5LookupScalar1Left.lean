/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupScalar1LeftPart0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupScalar1LeftPart1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupScalar1LeftPart2

/-!
# Recurrence 5 lookup certificate: Scalar1Left degree bound

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence5Scalar1Left_natDegree_le :
    recurrence5Scalar1Left.natDegree ≤ 462 := by
  unfold recurrence5Scalar1Left
  calc
    (recurrence5LeadingSquare * remainder5Coefficient1).natDegree ≤
        recurrence5LeadingSquare.natDegree + remainder5Coefficient1.natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 290 + 172 :=
      Nat.add_le_add recurrence5LeadingSquare_natDegree_le
        recurrence5A1_natDegree_le

theorem recurrence5Scalar1Left_coeff_high (n : ℕ) (h : 462 < n) :
    recurrence5Scalar1Left.coeff n = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt recurrence5Scalar1Left_natDegree_le h

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
