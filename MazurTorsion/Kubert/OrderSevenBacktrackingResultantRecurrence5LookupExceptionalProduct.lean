/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupExceptionalProductPart0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupExceptionalProductPart1

/-!
# Recurrence 5 lookup certificate: ExceptionalProduct degree bound

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence5ExceptionalProduct_natDegree_le :
    recurrence5ExceptionalProduct.natDegree ≤ 378 := by
  unfold recurrence5ExceptionalProduct
  calc
    (recurrence5A3Square * exceptional5).natDegree ≤
        recurrence5A3Square.natDegree + exceptional5.natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 328 + 50 :=
      Nat.add_le_add recurrence5A3Square_natDegree_le
        recurrence5Exceptional_natDegree_le

theorem recurrence5ExceptionalProduct_coeff_high (n : ℕ) (h : 378 < n) :
    recurrence5ExceptionalProduct.coeff n = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt recurrence5ExceptionalProduct_natDegree_le h

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
