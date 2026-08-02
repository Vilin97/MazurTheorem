/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA4SquarePart0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA4SquarePart1

/-!
# Recurrence 4 lookup certificate: A4Square degree bound

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence4A4Square_natDegree_le :
    recurrence4A4Square.natDegree ≤ 356 := by
  unfold recurrence4A4Square
  calc
    (remainder4Coefficient4 * remainder4Coefficient4).natDegree ≤
        remainder4Coefficient4.natDegree + remainder4Coefficient4.natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 178 + 178 :=
      Nat.add_le_add recurrence4A4_natDegree_le
        recurrence4A4_natDegree_le

theorem recurrence4A4Square_coeff_high (n : ℕ) (h : 356 < n) :
    recurrence4A4Square.coeff n = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt recurrence4A4Square_natDegree_le h

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
