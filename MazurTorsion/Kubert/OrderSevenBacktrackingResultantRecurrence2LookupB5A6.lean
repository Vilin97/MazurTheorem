/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB5A6Part0
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB5A6Part1

/-!
# Recurrence 2 lookup certificate: B5A6 degree bound

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence2B5A6_natDegree_le :
    recurrence2B5A6.natDegree ≤ 229 := by
  unfold recurrence2B5A6
  calc
    (remainder3Coefficient5 * remainder2Coefficient6).natDegree ≤
        remainder3Coefficient5.natDegree + remainder2Coefficient6.natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 134 + 95 :=
      Nat.add_le_add recurrence2B5_natDegree_le
        recurrence2A6_natDegree_le

theorem recurrence2B5A6_coeff_high (n : ℕ) (h : 229 < n) :
    recurrence2B5A6.coeff n = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt recurrence2B5A6_natDegree_le h

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
