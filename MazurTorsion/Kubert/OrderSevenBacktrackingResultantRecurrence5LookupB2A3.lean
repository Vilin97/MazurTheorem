/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB2A3Part0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB2A3Part1

/-!
# Recurrence 5 lookup certificate: B2A3 degree bound

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence5B2A3_natDegree_le :
    recurrence5B2A3.natDegree ≤ 309 := by
  unfold recurrence5B2A3
  calc
    (remainder6Coefficient2 * remainder5Coefficient3).natDegree ≤
        remainder6Coefficient2.natDegree + remainder5Coefficient3.natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 145 + 164 :=
      Nat.add_le_add recurrence5B2_natDegree_le
        recurrence5A3_natDegree_le

theorem recurrence5B2A3_coeff_high (n : ℕ) (h : 309 < n) :
    recurrence5B2A3.coeff n = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt recurrence5B2A3_natDegree_le h

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
