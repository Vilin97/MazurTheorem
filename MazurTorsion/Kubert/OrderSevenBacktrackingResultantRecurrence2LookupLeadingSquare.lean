/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupLeadingSquarePart0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupLeadingSquarePart1

/-!
# Recurrence 2 lookup certificate: LeadingSquare degree bound

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence2LeadingSquare_natDegree_le :
    recurrence2LeadingSquare.natDegree ≤ 268 := by
  unfold recurrence2LeadingSquare
  calc
    (remainder3Coefficient5 * remainder3Coefficient5).natDegree ≤
        remainder3Coefficient5.natDegree + remainder3Coefficient5.natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 134 + 134 :=
      Nat.add_le_add recurrence2B5_natDegree_le
        recurrence2B5_natDegree_le

theorem recurrence2LeadingSquare_coeff_high (n : ℕ) (h : 268 < n) :
    recurrence2LeadingSquare.coeff n = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt recurrence2LeadingSquare_natDegree_le h

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
