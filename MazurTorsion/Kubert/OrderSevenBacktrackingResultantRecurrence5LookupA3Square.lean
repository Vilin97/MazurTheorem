/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupA3SquarePart0
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupA3SquarePart1

/-!
# Recurrence 5 lookup certificate: A3Square degree bound

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence5A3Square_natDegree_le :
    recurrence5A3Square.natDegree ≤ 328 := by
  unfold recurrence5A3Square
  calc
    (remainder5Coefficient3 * remainder5Coefficient3).natDegree ≤
        remainder5Coefficient3.natDegree + remainder5Coefficient3.natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 164 + 164 :=
      Nat.add_le_add recurrence5A3_natDegree_le
        recurrence5A3_natDegree_le

theorem recurrence5A3Square_coeff_high (n : ℕ) (h : 328 < n) :
    recurrence5A3Square.coeff n = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt recurrence5A3Square_natDegree_le h

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
