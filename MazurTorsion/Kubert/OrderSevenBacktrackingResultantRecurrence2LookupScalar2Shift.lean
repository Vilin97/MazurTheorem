/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar2ShiftPart0
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar2ShiftPart1

/-!
# Recurrence 2 lookup certificate: Scalar2Shift degree bound

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence2Scalar2Shift_natDegree_le :
    recurrence2Scalar2Shift.natDegree ≤ 379 := by
  unfold recurrence2Scalar2Shift
  calc
    (remainder3Coefficient1 * recurrence2B5A6).natDegree ≤
        remainder3Coefficient1.natDegree + recurrence2B5A6.natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 150 + 229 :=
      Nat.add_le_add recurrence2B1_natDegree_le
        recurrence2B5A6_natDegree_le

theorem recurrence2Scalar2Shift_coeff_high (n : ℕ) (h : 379 < n) :
    recurrence2Scalar2Shift.coeff n = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt recurrence2Scalar2Shift_natDegree_le h

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
