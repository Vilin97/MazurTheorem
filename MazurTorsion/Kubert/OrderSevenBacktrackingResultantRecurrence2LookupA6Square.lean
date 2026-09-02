/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupA6SquarePart0

/-!
# Recurrence 2 lookup certificate: A6Square degree bound

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence2A6Square_natDegree_le :
    recurrence2A6Square.natDegree ≤ 190 := by
  unfold recurrence2A6Square
  calc
    (remainder2Coefficient6 * remainder2Coefficient6).natDegree ≤
        remainder2Coefficient6.natDegree + remainder2Coefficient6.natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 95 + 95 :=
      Nat.add_le_add recurrence2A6_natDegree_le
        recurrence2A6_natDegree_le

theorem recurrence2A6Square_coeff_high (n : ℕ) (h : 190 < n) :
    recurrence2A6Square.coeff n = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt recurrence2A6Square_natDegree_le h

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
