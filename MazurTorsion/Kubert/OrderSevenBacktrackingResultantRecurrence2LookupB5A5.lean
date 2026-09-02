/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB5A5Part0
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB5A5Part1

/-!
# Recurrence 2 lookup certificate: B5A5 degree bound

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence2B5A5_natDegree_le :
    recurrence2B5A5.natDegree ≤ 232 := by
  unfold recurrence2B5A5
  calc
    (remainder3Coefficient5 * remainder2Coefficient5).natDegree ≤
        remainder3Coefficient5.natDegree + remainder2Coefficient5.natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 134 + 98 :=
      Nat.add_le_add recurrence2B5_natDegree_le
        recurrence2A5_natDegree_le

theorem recurrence2B5A5_coeff_high (n : ℕ) (h : 232 < n) :
    recurrence2B5A5.coeff n = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt recurrence2B5A5_natDegree_le h

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
