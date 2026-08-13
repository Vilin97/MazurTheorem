/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB4A6Part0
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB4A6Part1

/-!
# Recurrence 2 lookup certificate: B4A6 degree bound

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence2B4A6_natDegree_le :
    recurrence2B4A6.natDegree ≤ 233 := by
  unfold recurrence2B4A6
  calc
    (remainder3Coefficient4 * remainder2Coefficient6).natDegree ≤
        remainder3Coefficient4.natDegree + remainder2Coefficient6.natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 138 + 95 :=
      Nat.add_le_add recurrence2B4_natDegree_le
        recurrence2A6_natDegree_le

theorem recurrence2B4A6_coeff_high (n : ℕ) (h : 233 < n) :
    recurrence2B4A6.coeff n = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt recurrence2B4A6_natDegree_le h

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
