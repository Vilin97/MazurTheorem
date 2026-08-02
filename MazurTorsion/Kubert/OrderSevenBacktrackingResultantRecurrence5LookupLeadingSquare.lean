/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupLeadingSquarePart0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupLeadingSquarePart1

/-!
# Recurrence 5 lookup certificate: LeadingSquare degree bound

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence5LeadingSquare_natDegree_le :
    recurrence5LeadingSquare.natDegree ≤ 290 := by
  unfold recurrence5LeadingSquare
  calc
    (remainder6Coefficient2 * remainder6Coefficient2).natDegree ≤
        remainder6Coefficient2.natDegree + remainder6Coefficient2.natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 145 + 145 :=
      Nat.add_le_add recurrence5B2_natDegree_le
        recurrence5B2_natDegree_le

theorem recurrence5LeadingSquare_coeff_high (n : ℕ) (h : 290 < n) :
    recurrence5LeadingSquare.coeff n = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt recurrence5LeadingSquare_natDegree_le h

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
