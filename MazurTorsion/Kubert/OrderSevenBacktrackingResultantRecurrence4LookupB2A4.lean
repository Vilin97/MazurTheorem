/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB2A4Part0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB2A4Part1

/-!
# Recurrence 4 lookup certificate: B2A4 degree bound

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence4B2A4_natDegree_le :
    recurrence4B2A4.natDegree ≤ 346 := by
  unfold recurrence4B2A4
  calc
    (remainder5Coefficient2 * remainder4Coefficient4).natDegree ≤
        remainder5Coefficient2.natDegree + remainder4Coefficient4.natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 168 + 178 :=
      Nat.add_le_add recurrence4B2_natDegree_le
        recurrence4A4_natDegree_le

theorem recurrence4B2A4_coeff_high (n : ℕ) (h : 346 < n) :
    recurrence4B2A4.coeff n = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt recurrence4B2A4_natDegree_le h

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
