/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupExceptionalProductPart0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupExceptionalProductPart1

/-!
# Recurrence 4 lookup certificate: ExceptionalProduct degree bound

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence4ExceptionalProduct_natDegree_le :
    recurrence4ExceptionalProduct.natDegree ≤ 369 := by
  unfold recurrence4ExceptionalProduct
  calc
    (recurrence4A4Square * exceptional4).natDegree ≤
        recurrence4A4Square.natDegree + exceptional4.natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 356 + 13 :=
      Nat.add_le_add recurrence4A4Square_natDegree_le
        recurrence4Exceptional_natDegree_le

theorem recurrence4ExceptionalProduct_coeff_high (n : ℕ) (h : 369 < n) :
    recurrence4ExceptionalProduct.coeff n = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt recurrence4ExceptionalProduct_natDegree_le h

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
